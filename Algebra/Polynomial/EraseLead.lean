/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Alex Meiburg
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Degree.Monomial

/-!
# Erase the leading term of a univariate polynomial

## Definition

* `eraseLead f`: the polynomial `f - leading term of f`

`eraseLead` serves as reduction step in an induction, shaving off one monomial from a polynomial.
The definition is set up so that it does not mention subtraction in the definition,
and thus works for polynomials over semirings as well as rings.
-/

@[expose] public section


noncomputable section

open Polynomial

open Polynomial Finset

namespace Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

/-- `eraseLead f` for a polynomial `f` is the polynomial obtained by
subtracting from `f` the leading term of `f`. -/
/-
**Polynomial.eraseLead** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：eraseLead (f : R[X]) : R[X]
参数：f : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`eraseLead f` for a polynomial `f` is the polynomial obtained by
subtracting from `f` the leading term of `f`.
-/
def eraseLead (f : R[X]) : R[X] :=
  Polynomial.erase f.natDegree f

section EraseLead

/-
**Polynomial.eraseLead_support** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eraseLead_support (f : R[X]) : f.eraseLead.support = f.support.erase f.nat
Degree
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.support_erase`：support_erase (p : R[X]) (n : Nat) : support (
p.erase n) = (support p).erase n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eraseLead_support (f : R[X]) : f.eraseLead.support = f.support.erase f.natDegree := by
  simp only [eraseLead, support_erase]
/-
**Polynomial.eraseLead_coeff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eraseLead_coeff (i : Nat) : f.eraseLead.coeff i = if i = f.natDegree then 
0 else f.coeff i
参数：i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_erase`：coeff_erase (p : R[X]) (n i : Nat) : (p.erase n)
.coeff i = if i = n then 0 else p.coeff i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eraseLead_coeff (i : ℕ) :
    f.eraseLead.coeff i = if i = f.natDegree then 0 else f.coeff i := by
  simp only [eraseLead, coeff_erase]

@[simp]
/-
**Polynomial.eraseLead_coeff_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eraseLead_coeff_natDegree : f.eraseLead.coeff f.natDegree = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eraseLead_coeff`：eraseLead_coeff (i : Nat) : f.eraseLead.coef
f i = if i = f.natDegree then 0 else f.coeff i
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eraseLead_coeff_natDegree : f.eraseLead.coeff f.natDegree = 0 := by simp [eraseLead_coeff]
/-
**Polynomial.eraseLead_coeff_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eraseLead_coeff_of_ne (i : Nat) (hi : i != f.natDegree) : f.eraseLead.coef
f i = f.coeff i
参数：i : Nat；hi : i != f.natDegree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eraseLead_coeff`：eraseLead_coeff (i : Nat) : f.eraseLead.coef
f i = if i = f.natDegree then 0 else f.coeff i
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eraseLead_coeff_of_ne (i : ℕ) (hi : i ≠ f.natDegree) : f.eraseLead.coeff i = f.coeff i := by
  simp [eraseLead_coeff, hi]

@[simp]
/-
**Polynomial.eraseLead_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eraseLead_zero : eraseLead (0 : R[X]) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.erase_zero`：erase_zero (n : Nat) : (0 : R[X]).erase n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eraseLead_zero : eraseLead (0 : R[X]) = 0 := by simp only [eraseLead, erase_zero]

@[simp]
/-
**Polynomial.eraseLead_add_monomial_natDegree_leadingCoeff** 是 Mathlib 中的一个定理，位于
命名空间 `Polynomial`。
形式化陈述：eraseLead_add_monomial_natDegree_leadingCoeff (f : R[X]) : f.eraseLead + m
onomial f.natDegree f.leadingCoeff = f
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Polynomial.monomial_add_erase`：monomial_add_erase (p : R[X]) (n : Nat) :
 monomial n (coeff p n) + p.erase n = p
-/
theorem eraseLead_add_monomial_natDegree_leadingCoeff (f : R[X]) :
    f.eraseLead + monomial f.natDegree f.leadingCoeff = f :=
  (add_comm _ _).trans (f.monomial_add_erase _)

@[simp]
/-
**Polynomial.eraseLead_add_C_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eraseLead_add_C_mul_X_pow (f : R[X]) : f.eraseLead + C f.leadingCoeff * X 
^ f.natDegree = f
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.eraseLead_add_monomial_natDegree_leadingCoeff`：eraseLead_add_
monomial_natDegree_leadingCoeff (f : R[X]) : f.eraseLead + monomial f.natDegree 
f.leadingCoeff = f
-/
theorem eraseLead_add_C_mul_X_pow (f : R[X]) :
    f.eraseLead + C f.leadingCoeff * X ^ f.natDegree = f := by
  rw [C_mul_X_pow_eq_monomial, eraseLead_add_monomial_natDegree_leadingCoeff]

@[simp]
/-
**Polynomial.self_sub_monomial_natDegree_leadingCoeff** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial`。
形式化陈述：self_sub_monomial_natDegree_leadingCoeff {R : Type*} [Ring R] (f : R[X]) :
 f - monomial f.natDegree f.leadingCoeff = f.eraseLead
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `Polynomial.eraseLead_add_monomial_natDegree_leadingCoeff`：eraseLead_add_
monomial_natDegree_leadingCoeff (f : R[X]) : f.eraseLead + monomial f.natDegree 
f.leadingCoeff = f
-/
theorem self_sub_monomial_natDegree_leadingCoeff {R : Type*} [Ring R] (f : R[X]) :
    f - monomial f.natDegree f.leadingCoeff = f.eraseLead :=
  (eq_sub_iff_add_eq.mpr (eraseLead_add_monomial_natDegree_leadingCoeff f)).symm

@[simp]
/-
**Polynomial.self_sub_C_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：self_sub_C_mul_X_pow {R : Type*} [Ring R] (f : R[X]) : f - C f.leadingCoef
f * X ^ f.natDegree = f.eraseLead
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.self_sub_monomial_natDegree_leadingCoeff`：self_sub_monomial_n
atDegree_leadingCoeff {R : Type*} [Ring R] (f : R[X]) : f - monomial f.natDegree
 f.leadingCoeff = f.eraseLead
-/
theorem self_sub_C_mul_X_pow {R : Type*} [Ring R] (f : R[X]) :
    f - C f.leadingCoeff * X ^ f.natDegree = f.eraseLead := by
  rw [C_mul_X_pow_eq_monomial, self_sub_monomial_natDegree_leadingCoeff]
/-
**Polynomial.eraseLead_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eraseLead_ne_zero (f0 : 2 <= #f.support) : eraseLead f != 0
参数：f0 : 2 <= #f.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.card_support_eq_zero`：card_support_eq_zero : #p.support = 0 ↔
 p = 0
· 使用定理 `Polynomial.eraseLead_support`：eraseLead_support (f : R[X]) : f.eraseLead
.support = f.support.erase f.natDegree
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `tsub_le_tsub_right`：tsub_le_tsub_right (h : a <= b) (c : α) : a - c <= b
 - c
· 使用定理 `Finset.pred_card_le_card_erase`：pred_card_le_card_erase : #s - 1 <= #(s.
erase a)
-/
theorem eraseLead_ne_zero (f0 : 2 ≤ #f.support) : eraseLead f ≠ 0 := by
  rw [Ne, ← card_support_eq_zero, eraseLead_support]
  exact
    (zero_lt_one.trans_le <| (tsub_le_tsub_right f0 1).trans Finset.pred_card_le_card_erase).ne.symm
/-
**Polynomial.lt_natDegree_of_mem_eraseLead_support** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial`。
形式化陈述：lt_natDegree_of_mem_eraseLead_support {a : Nat} (h : a in (eraseLead f).su
pport) : a < f.natDegree
参数：h : a in (eraseLead f).support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `Polynomial.le_natDegree_of_mem_supp`：le_natDegree_of_mem_supp (a : Nat) 
: a in p.support -> a <= natDegree p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `Polynomial.eraseLead_support`：eraseLead_support (f : R[X]) : f.eraseLead
.support = f.support.erase f.natDegree
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem lt_natDegree_of_mem_eraseLead_support {a : ℕ} (h : a ∈ (eraseLead f).support) :
    a < f.natDegree := by
  rw [eraseLead_support, mem_erase] at h
  exact (le_natDegree_of_mem_supp a h.2).lt_of_ne h.1
/-
**Polynomial.ne_natDegree_of_mem_eraseLead_support** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial`。
形式化陈述：ne_natDegree_of_mem_eraseLead_support {a : Nat} (h : a in (eraseLead f).su
pport) : a != f.natDegree
参数：h : a in (eraseLead f).support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Polynomial.lt_natDegree_of_mem_eraseLead_support`：lt_natDegree_of_mem_er
aseLead_support {a : Nat} (h : a in (eraseLead f).support) : a < f.natDegree
-/
theorem ne_natDegree_of_mem_eraseLead_support {a : ℕ} (h : a ∈ (eraseLead f).support) :
    a ≠ f.natDegree :=
  (lt_natDegree_of_mem_eraseLead_support h).ne
/-
**Polynomial.natDegree_notMem_eraseLead_support** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：natDegree_notMem_eraseLead_support : f.natDegree ∉ (eraseLead f).support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ne_natDegree_of_mem_eraseLead_support`：ne_natDegree_of_mem_er
aseLead_support {a : Nat} (h : a in (eraseLead f).support) : a != f.natDegree
-/
theorem natDegree_notMem_eraseLead_support : f.natDegree ∉ (eraseLead f).support := fun h =>
  ne_natDegree_of_mem_eraseLead_support h rfl
/-
**Polynomial.eraseLead_support_card_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eraseLead_support_card_lt (h : f != 0) : #(eraseLead f).support < #f.suppo
rt
参数：h : f != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eraseLead_support`：eraseLead_support (f : R[X]) : f.eraseLead
.support = f.support.erase f.natDegree
· 使用定理 `Finset.card_lt_card`：∀ {α : Type u_1} {s t : Finset α}, s ⊂ t → s.card <
 t.card
· 使用定理 `Finset.erase_ssubset`：erase_ssubset {a : α} {s : Finset α} (h : a in s) 
: s.erase a ⊂ s
· 使用定理 `Polynomial.natDegree_mem_support_of_nonzero`：natDegree_mem_support_of_no
nzero (H : p != 0) : p.natDegree in p.support
-/
theorem eraseLead_support_card_lt (h : f ≠ 0) : #(eraseLead f).support < #f.support := by
  rw [eraseLead_support]
  exact card_lt_card (erase_ssubset <| natDegree_mem_support_of_nonzero h)
/-
**Polynomial.card_support_eraseLead_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：card_support_eraseLead_add_one (h : f != 0) : #f.eraseLead.support + 1 = #
f.support
参数：h : f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.card_support_eq_zero`：card_support_eq_zero : #p.support = 0 ↔
 p = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eraseLead_support`：eraseLead_support (f : R[X]) : f.eraseLead
.support = f.support.erase f.natDegree
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `Polynomial.natDegree_mem_support_of_nonzero`：natDegree_mem_support_of_no
nzero (H : p != 0) : p.natDegree in p.support
-/
theorem card_support_eraseLead_add_one (h : f ≠ 0) : #f.eraseLead.support + 1 = #f.support := by
  set c := #f.support with hc
  cases h₁ : c
  case zero =>
    by_contra
    exact h (card_support_eq_zero.mp h₁)
  case succ =>
    rw [eraseLead_support, card_erase_of_mem (natDegree_mem_support_of_nonzero h), ← hc, h₁]
    rfl

@[simp]
/-
**Polynomial.card_support_eraseLead** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：card_support_eraseLead : #f.eraseLead.support = #f.support - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eraseLead_zero`：eraseLead_zero : eraseLead (0 : R[X]) = 0
· 使用定理 `Polynomial.support_zero`：support_zero : (0 : R[X]).support = ∅
· 使用定理 `Finset.card_empty`：card_empty : #(∅ : Finset α) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.card_support_eraseLead_add_one`：card_support_eraseLead_add_on
e (h : f != 0) : #f.eraseLead.support + 1 = #f.support
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem card_support_eraseLead : #f.eraseLead.support = #f.support - 1 := by
  by_cases hf : f = 0
  · rw [hf, eraseLead_zero, support_zero, card_empty]
  · rw [← card_support_eraseLead_add_one hf, add_tsub_cancel_right]
/-
**Polynomial.card_support_eraseLead'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：card_support_eraseLead' {c : Nat} (fc : #f.support = c + 1) : #f.eraseLead
.support = c
参数：fc : #f.support = c + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.card_support_eraseLead`：card_support_eraseLead : #f.eraseLead
.support = #f.support - 1
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem card_support_eraseLead' {c : ℕ} (fc : #f.support = c + 1) :
    #f.eraseLead.support = c := by
  rw [card_support_eraseLead, fc, add_tsub_cancel_right]
/-
**Polynomial.card_support_eq_one_of_eraseLead_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial`。
形式化陈述：card_support_eq_one_of_eraseLead_eq_zero (h₀ : f != 0) (h₁ : f.eraseLead =
 0) : #f.support = 1
参数：h₀ : f != 0；h₁ : f.eraseLead = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.card_support_eraseLead_add_one`：card_support_eraseLead_add_on
e (h : f != 0) : #f.eraseLead.support + 1 = #f.support
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.card_support_eq_zero`：card_support_eq_zero : #p.support = 0 ↔
 p = 0
-/
theorem card_support_eq_one_of_eraseLead_eq_zero (h₀ : f ≠ 0) (h₁ : f.eraseLead = 0) :
    #f.support = 1 :=
  (card_support_eq_zero.mpr h₁ ▸ card_support_eraseLead_add_one h₀).symm
/-
**Polynomial.card_support_le_one_of_eraseLead_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial`。
形式化陈述：card_support_le_one_of_eraseLead_eq_zero (h : f.eraseLead = 0) : #f.suppor
t <= 1
参数：h : f.eraseLead = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Polynomial.card_support_eq_one_of_eraseLead_eq_zero`：card_support_eq_one
_of_eraseLead_eq_zero (h₀ : f != 0) (h₁ : f.eraseLead = 0) : #f.support = 1
-/
theorem card_support_le_one_of_eraseLead_eq_zero (h : f.eraseLead = 0) : #f.support ≤ 1 := by
  by_cases hpz : f = 0
  case pos => simp [hpz]
  case neg => exact le_of_eq (card_support_eq_one_of_eraseLead_eq_zero hpz h)

@[simp]
/-
**Polynomial.eraseLead_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eraseLead_monomial (i : Nat) (r : R) : eraseLead (monomial i r) = 0
参数：i : Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.monomial_zero_right`：monomial_zero_right (n : Nat) : monomial
 n (0 : R) = 0
· 使用定理 `Polynomial.eraseLead_zero`：eraseLead_zero : eraseLead (0 : R[X]) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eraseLead.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (f : Pol
ynomial R), f.eraseLead = Polynomial.erase f.natDegree f
· 使用定理 `Polynomial.natDegree_monomial`：natDegree_monomial [DecidableEq R] (i : N
at) (r : R) : natDegree (monomial i r) = if r = 0 then 0 else i
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Polynomial.erase_monomial`：erase_monomial {n : Nat} {a : R} : erase n (m
onomial n a) = 0
-/
theorem eraseLead_monomial (i : ℕ) (r : R) : eraseLead (monomial i r) = 0 := by
  classical
  by_cases hr : r = 0
  · subst r
    simp only [monomial_zero_right, eraseLead_zero]
  · rw [eraseLead, natDegree_monomial, if_neg hr, erase_monomial]

@[simp]
/-
**Polynomial.eraseLead_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eraseLead_C (r : R) : eraseLead (C r) = 0
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eraseLead_monomial`：eraseLead_monomial (i : Nat) (r : R) : er
aseLead (monomial i r) = 0
-/
theorem eraseLead_C (r : R) : eraseLead (C r) = 0 :=
  eraseLead_monomial _ _

@[simp]
/-
**Polynomial.eraseLead_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eraseLead_X : eraseLead (X : R[X]) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eraseLead_monomial`：eraseLead_monomial (i : Nat) (r : R) : er
aseLead (monomial i r) = 0
-/
theorem eraseLead_X : eraseLead (X : R[X]) = 0 :=
  eraseLead_monomial _ _

@[simp]
/-
**Polynomial.eraseLead_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eraseLead_X_pow (n : Nat) : eraseLead (X ^ n : R[X]) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.X_pow_eq_monomial`：X_pow_eq_monomial (n) : X ^ n = monomial n
 (1 : R)
· 使用定理 `Polynomial.eraseLead_monomial`：eraseLead_monomial (i : Nat) (r : R) : er
aseLead (monomial i r) = 0
-/
theorem eraseLead_X_pow (n : ℕ) : eraseLead (X ^ n : R[X]) = 0 := by
  rw [X_pow_eq_monomial, eraseLead_monomial]

@[simp]
/-
**Polynomial.eraseLead_C_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eraseLead_C_mul_X_pow (r : R) (n : Nat) : eraseLead (C r * X ^ n) = 0
参数：r : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.eraseLead_monomial`：eraseLead_monomial (i : Nat) (r : R) : er
aseLead (monomial i r) = 0
-/
theorem eraseLead_C_mul_X_pow (r : R) (n : ℕ) : eraseLead (C r * X ^ n) = 0 := by
  rw [C_mul_X_pow_eq_monomial, eraseLead_monomial]
/-
**Polynomial.eraseLead_C_mul_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] (r : R), (Polynomial.C r * Polynomial
.X).eraseLead = 0
参数：r : R；Polynomial.C r * Polynomial.X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Polynomial.eraseLead_C_mul_X_pow`：eraseLead_C_mul_X_pow (r : R) (n : Nat
) : eraseLead (C r * X ^ n) = 0
-/
@[simp] lemma eraseLead_C_mul_X (r : R) : eraseLead (C r * X) = 0 := by
  simpa using eraseLead_C_mul_X_pow _ 1
/-
**Polynomial.eraseLead_add_of_degree_lt_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：eraseLead_add_of_degree_lt_left {p q : R[X]} (pq : q.degree < p.degree) : 
(p + q).eraseLead = p.eraseLead + q
参数：pq : q.degree < p.degree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eraseLead_coeff`：eraseLead_coeff (i : Nat) : f.eraseLead.coef
f i = if i = f.natDegree then 0 else f.coeff i
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natDegree_add_eq_left_of_degree_lt`：natDegree_add_eq_left_of_
degree_lt (h : degree q < degree p) : natDegree (p + q) = natDegree p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eraseLead_coeff_natDegree`：eraseLead_coeff_natDegree : f.eras
eLead.coeff f.natDegree = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Polynomial.coeff_eq_zero_of_degree_lt`：coeff_eq_zero_of_degree_lt (h : d
egree p < n) : coeff p n = 0
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Polynomial.degree_le_natDegree`：degree_le_natDegree : degree p <= natDeg
ree p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem eraseLead_add_of_degree_lt_left {p q : R[X]} (pq : q.degree < p.degree) :
    (p + q).eraseLead = p.eraseLead + q := by
  ext n
  by_cases nd : n = p.natDegree
  · rw [nd, eraseLead_coeff, if_pos (natDegree_add_eq_left_of_degree_lt pq).symm]
    simpa using (coeff_eq_zero_of_degree_lt (lt_of_lt_of_le pq degree_le_natDegree)).symm
  · rw [eraseLead_coeff, coeff_add, coeff_add, eraseLead_coeff, if_neg, if_neg nd]
    rintro rfl
    exact nd (natDegree_add_eq_left_of_degree_lt pq)
/-
**Polynomial.eraseLead_add_of_natDegree_lt_left** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：eraseLead_add_of_natDegree_lt_left {p q : R[X]} (pq : q.natDegree < p.natD
egree) : (p + q).eraseLead = p.eraseLead + q
参数：pq : q.natDegree < p.natDegree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eraseLead_add_of_degree_lt_left`：eraseLead_add_of_degree_lt_l
eft {p q : R[X]} (pq : q.degree < p.degree) : (p + q).eraseLead = p.eraseLead + 
q
· 使用定理 `Polynomial.degree_lt_degree`：degree_lt_degree (h : natDegree p < natDegr
ee q) : degree p < degree q
-/
theorem eraseLead_add_of_natDegree_lt_left {p q : R[X]} (pq : q.natDegree < p.natDegree) :
    (p + q).eraseLead = p.eraseLead + q :=
  eraseLead_add_of_degree_lt_left (degree_lt_degree pq)
/-
**Polynomial.eraseLead_add_of_degree_lt_right** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：eraseLead_add_of_degree_lt_right {p q : R[X]} (pq : p.degree < q.degree) :
 (p + q).eraseLead = p + q.eraseLead
参数：pq : p.degree < q.degree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eraseLead_coeff`：eraseLead_coeff (i : Nat) : f.eraseLead.coef
f i = if i = f.natDegree then 0 else f.coeff i
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natDegree_add_eq_right_of_degree_lt`：natDegree_add_eq_right_o
f_degree_lt (h : degree p < degree q) : natDegree (p + q) = natDegree q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `Polynomial.eraseLead_coeff_natDegree`：eraseLead_coeff_natDegree : f.eras
eLead.coeff f.natDegree = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Polynomial.coeff_eq_zero_of_degree_lt`：coeff_eq_zero_of_degree_lt (h : d
egree p < n) : coeff p n = 0
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Polynomial.degree_le_natDegree`：degree_le_natDegree : degree p <= natDeg
ree p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem eraseLead_add_of_degree_lt_right {p q : R[X]} (pq : p.degree < q.degree) :
    (p + q).eraseLead = p + q.eraseLead := by
  ext n
  by_cases nd : n = q.natDegree
  · rw [nd, eraseLead_coeff, if_pos (natDegree_add_eq_right_of_degree_lt pq).symm]
    simpa using (coeff_eq_zero_of_degree_lt (lt_of_lt_of_le pq degree_le_natDegree)).symm
  · rw [eraseLead_coeff, coeff_add, coeff_add, eraseLead_coeff, if_neg, if_neg nd]
    rintro rfl
    exact nd (natDegree_add_eq_right_of_degree_lt pq)
/-
**Polynomial.eraseLead_add_of_natDegree_lt_right** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：eraseLead_add_of_natDegree_lt_right {p q : R[X]} (pq : p.natDegree < q.nat
Degree) : (p + q).eraseLead = p + q.eraseLead
参数：pq : p.natDegree < q.natDegree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eraseLead_add_of_degree_lt_right`：eraseLead_add_of_degree_lt_
right {p q : R[X]} (pq : p.degree < q.degree) : (p + q).eraseLead = p + q.eraseL
ead
· 使用定理 `Polynomial.degree_lt_degree`：degree_lt_degree (h : natDegree p < natDegr
ee q) : degree p < degree q
-/
theorem eraseLead_add_of_natDegree_lt_right {p q : R[X]} (pq : p.natDegree < q.natDegree) :
    (p + q).eraseLead = p + q.eraseLead :=
  eraseLead_add_of_degree_lt_right (degree_lt_degree pq)
/-
**Polynomial.eraseLead_degree_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eraseLead_degree_le : (eraseLead f).degree <= f.degree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.degree_erase_le`：degree_erase_le (p : R[X]) (n : Nat) : degre
e (p.erase n) <= degree p
-/
theorem eraseLead_degree_le : (eraseLead f).degree ≤ f.degree :=
  f.degree_erase_le _
/-
**Polynomial.degree_eraseLead_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_eraseLead_lt (hf : f != 0) : (eraseLead f).degree < f.degree
参数：hf : f != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.degree_erase_lt`：degree_erase_lt (hp : p != 0) : degree (p.er
ase (natDegree p)) < degree p
-/
theorem degree_eraseLead_lt (hf : f ≠ 0) : (eraseLead f).degree < f.degree :=
  f.degree_erase_lt hf
/-
**Polynomial.eraseLead_natDegree_le_aux** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eraseLead_natDegree_le_aux : (eraseLead f).natDegree <= f.natDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_le_natDegree`：natDegree_le_natDegree [Semiring S] {
q : S[X]} (hpq : p.degree <= q.degree) : p.natDegree <= q.natDegree
· 使用定理 `Polynomial.eraseLead_degree_le`：eraseLead_degree_le : (eraseLead f).degr
ee <= f.degree
-/
theorem eraseLead_natDegree_le_aux : (eraseLead f).natDegree ≤ f.natDegree :=
  natDegree_le_natDegree eraseLead_degree_le
/-
**Polynomial.eraseLead_natDegree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eraseLead_natDegree_lt (f0 : 2 <= #f.support) : (eraseLead f).natDegree < 
f.natDegree
参数：f0 : 2 <= #f.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Polynomial.eraseLead_natDegree_le_aux`：eraseLead_natDegree_le_aux : (era
seLead f).natDegree <= f.natDegree
· 使用定理 `Polynomial.ne_natDegree_of_mem_eraseLead_support`：ne_natDegree_of_mem_er
aseLead_support {a : Nat} (h : a in (eraseLead f).support) : a != f.natDegree
· 使用定理 `Polynomial.natDegree_mem_support_of_nonzero`：natDegree_mem_support_of_no
nzero (H : p != 0) : p.natDegree in p.support
· 使用定理 `Polynomial.eraseLead_ne_zero`：eraseLead_ne_zero (f0 : 2 <= #f.support) :
 eraseLead f != 0
-/
theorem eraseLead_natDegree_lt (f0 : 2 ≤ #f.support) : (eraseLead f).natDegree < f.natDegree :=
  lt_of_le_of_ne eraseLead_natDegree_le_aux <|
    ne_natDegree_of_mem_eraseLead_support <|
      natDegree_mem_support_of_nonzero <| eraseLead_ne_zero f0
/-
**Polynomial.natDegree_pos_of_eraseLead_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：natDegree_pos_of_eraseLead_ne_zero (h : f.eraseLead != 0) : 0 < f.natDegre
e
参数：h : f.eraseLead != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eraseLead_C`：eraseLead_C (r : R) : eraseLead (C r) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Polynomial.eq_C_of_natDegree_eq_zero`：eq_C_of_natDegree_eq_zero (h : nat
Degree p = 0) : p = C (coeff p 0)
· 使用定理 `Nat.eq_zero_of_not_pos`：∀ {n : ℕ}, ¬0 < n → n = 0
-/
theorem natDegree_pos_of_eraseLead_ne_zero (h : f.eraseLead ≠ 0) : 0 < f.natDegree := by
  by_contra h₂
  rw [eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos h₂)] at h
  simp at h
/-
**Polynomial.eraseLead_natDegree_lt_or_eraseLead_eq_zero** 是 Mathlib 中的一个定理，位于命名
空间 `Polynomial`。
形式化陈述：eraseLead_natDegree_lt_or_eraseLead_eq_zero (f : R[X]) : (eraseLead f).nat
Degree < f.natDegree ∨ f.eraseLead = 0
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_mul_X_pow_eq_self`：C_mul_X_pow_eq_self (h : #p.support <= 1
) : C p.leadingCoeff * X ^ p.natDegree = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eraseLead_C_mul_X_pow`：eraseLead_C_mul_X_pow (r : R) (n : Nat
) : eraseLead (C r * X ^ n) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.eraseLead_natDegree_lt`：eraseLead_natDegree_lt (f0 : 2 <= #f.
support) : (eraseLead f).natDegree < f.natDegree
-/
theorem eraseLead_natDegree_lt_or_eraseLead_eq_zero (f : R[X]) :
    (eraseLead f).natDegree < f.natDegree ∨ f.eraseLead = 0 := by
  by_cases! h : #f.support ≤ 1
  · right
    rw [← C_mul_X_pow_eq_self h]
    simp
  · left
    apply eraseLead_natDegree_lt h
/-
**Polynomial.eraseLead_natDegree_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eraseLead_natDegree_le (f : R[X]) : (eraseLead f).natDegree <= f.natDegree
 - 1
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eraseLead_natDegree_lt_or_eraseLead_eq_zero`：eraseLead_natDeg
ree_lt_or_eraseLead_eq_zero (f : R[X]) : (eraseLead f).natDegree < f.natDegree ∨
 f.eraseLead = 0
· 使用定理 `Nat.le_sub_one_of_lt`：∀ {a b : ℕ}, a < b → a ≤ b - 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem eraseLead_natDegree_le (f : R[X]) : (eraseLead f).natDegree ≤ f.natDegree - 1 := by
  rcases f.eraseLead_natDegree_lt_or_eraseLead_eq_zero with (h | h)
  · exact Nat.le_sub_one_of_lt h
  · simp only [h, natDegree_zero, zero_le]
/-
**Polynomial.natDegree_eraseLead** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_eraseLead (h : f.nextCoeff != 0) : f.eraseLead.natDegree = f.nat
Degree - 1
参数：h : f.nextCoeff != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_pos_of_nextCoeff_ne_zero`：natDegree_pos_of_nextCoef
f_ne_zero (h : p.nextCoeff != 0) : 0 < p.natDegree
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Polynomial.eraseLead_natDegree_le`：eraseLead_natDegree_le (f : R[X]) : (
eraseLead f).natDegree <= f.natDegree - 1
· 使用定理 `Polynomial.le_natDegree_of_ne_zero`：le_natDegree_of_ne_zero (h : coeff p
 n != 0) : n <= natDegree p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eraseLead_coeff_of_ne`：eraseLead_coeff_of_ne (i : Nat) (hi : 
i != f.natDegree) : f.eraseLead.coeff i = f.coeff i
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `tsub_lt_self`：tsub_lt_self : 0 < a -> 0 < b -> a - b < a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.nextCoeff_of_natDegree_pos`：nextCoeff_of_natDegree_pos (hp : 
0 < p.natDegree) : nextCoeff p = p.coeff (p.natDegree - 1)
-/
lemma natDegree_eraseLead (h : f.nextCoeff ≠ 0) : f.eraseLead.natDegree = f.natDegree - 1 := by
  have := natDegree_pos_of_nextCoeff_ne_zero h
  refine f.eraseLead_natDegree_le.antisymm <| le_natDegree_of_ne_zero ?_
  rwa [eraseLead_coeff_of_ne _ (tsub_lt_self _ _).ne, ← nextCoeff_of_natDegree_pos]
  all_goals positivity
/-
**Polynomial.natDegree_eraseLead_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_eraseLead_add_one (h : f.nextCoeff != 0) : f.eraseLead.natDegree
 + 1 = f.natDegree
参数：h : f.nextCoeff != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.natDegree_eraseLead`：natDegree_eraseLead (h : f.nextCoeff != 
0) : f.eraseLead.natDegree = f.natDegree - 1
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Polynomial.natDegree_pos_of_nextCoeff_ne_zero`：natDegree_pos_of_nextCoef
f_ne_zero (h : p.nextCoeff != 0) : 0 < p.natDegree
-/
lemma natDegree_eraseLead_add_one (h : f.nextCoeff ≠ 0) :
    f.eraseLead.natDegree + 1 = f.natDegree := by
  rw [natDegree_eraseLead h, tsub_add_cancel_of_le]
  exact natDegree_pos_of_nextCoeff_ne_zero h
/-
**Polynomial.natDegree_eraseLead_le_of_nextCoeff_eq_zero** 是 Mathlib 中的一个定理，位于命名
空间 `Polynomial`。
形式化陈述：natDegree_eraseLead_le_of_nextCoeff_eq_zero (h : f.nextCoeff = 0) : f.eras
eLead.natDegree <= f.natDegree - 2
参数：h : f.nextCoeff = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.natDegree_le_pred`：natDegree_le_pred (hf : p.natDegree <= n) 
(hn : p.coeff n = 0) : p.natDegree <= n - 1
· 使用定理 `Polynomial.eraseLead_natDegree_le`：eraseLead_natDegree_le (f : R[X]) : (
eraseLead f).natDegree <= f.natDegree - 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.natDegree_eq_zero`：natDegree_eq_zero {p : R[X]} : p.natDegree
 = 0 ↔ exists x, C x = p
· 使用引理 `Polynomial.nextCoeff_eq_zero`：nextCoeff_eq_zero : p.nextCoeff = 0 ↔ p.na
tDegree = 0 ∨ 0 < p.natDegree ∧ p.coeff (p.natDegree - 1) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eraseLead_C`：eraseLead_C (r : R) : eraseLead (C r) = 0
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.eraseLead_coeff_of_ne`：eraseLead_coeff_of_ne (i : Nat) (hi : 
i != f.natDegree) : f.eraseLead.coeff i = f.coeff i
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `tsub_lt_self`：tsub_lt_self : 0 < a -> 0 < b -> a - b < a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.nextCoeff_of_natDegree_pos`：nextCoeff_of_natDegree_pos (hp : 
0 < p.natDegree) : nextCoeff p = p.coeff (p.natDegree - 1)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem natDegree_eraseLead_le_of_nextCoeff_eq_zero (h : f.nextCoeff = 0) :
    f.eraseLead.natDegree ≤ f.natDegree - 2 := by
  refine natDegree_le_pred (n := f.natDegree - 1) (eraseLead_natDegree_le f) ?_
  rw [nextCoeff_eq_zero, natDegree_eq_zero] at h
  obtain ⟨a, rfl⟩ | ⟨hf, h⟩ := h
  · simp
  rw [eraseLead_coeff_of_ne _ (tsub_lt_self hf zero_lt_one).ne, ← nextCoeff_of_natDegree_pos hf]
  simp [nextCoeff_eq_zero, h, eq_zero_or_pos]
/-
**Polynomial.two_le_natDegree_of_nextCoeff_eraseLead** 是 Mathlib 中的一个引理，位于命名空间 `
Polynomial`。
形式化陈述：two_le_natDegree_of_nextCoeff_eraseLead (hlead : f.eraseLead != 0) (hnext 
: f.nextCoeff = 0) : 2 <= f.natDegree
参数：hlead : f.eraseLead != 0；hnext : f.nextCoeff = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.natDegree_eq_one`：natDegree_eq_one : p.natDegree = 1 ↔ exists
 a != 0, exists b, C a * X + C b = p
· 使用引理 `Polynomial.natDegree_eq_zero`：natDegree_eq_zero {p : R[X]} : p.natDegree
 = 0 ↔ exists x, C x = p
· 使用定理 `Nat.le_one_iff_eq_zero_or_eq_one`：∀ {n : ℕ}, n ≤ 1 ↔ n = 0 ∨ n = 1
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eraseLead_C`：eraseLead_C (r : R) : eraseLead (C r) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Polynomial.eraseLead_C_mul_X`：∀ {R : Type u_1} [inst : Semiring R] (r : 
R), (Polynomial.C r * Polynomial.X).eraseLead = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.nextCoeff_C_mul_X_add_C`：nextCoeff_C_mul_X_add_C (ha : a != 0
) (c : R) : nextCoeff (C a * X + C c) = c
-/
lemma two_le_natDegree_of_nextCoeff_eraseLead (hlead : f.eraseLead ≠ 0)
    (hnext : f.nextCoeff = 0) : 2 ≤ f.natDegree := by
  contrapose! hlead
  rw [Nat.lt_succ_iff, Nat.le_one_iff_eq_zero_or_eq_one, natDegree_eq_zero, natDegree_eq_one]
    at hlead
  obtain ⟨a, rfl⟩ | ⟨a, ha, b, rfl⟩ := hlead
  · simp
  · rw [nextCoeff_C_mul_X_add_C ha] at hnext
    subst b
    simp
/-
**Polynomial.leadingCoeff_eraseLead_eq_nextCoeff** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：leadingCoeff_eraseLead_eq_nextCoeff (h : f.nextCoeff != 0) : f.eraseLead.l
eadingCoeff = f.nextCoeff
参数：h : f.nextCoeff != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_pos_of_nextCoeff_ne_zero`：natDegree_pos_of_nextCoef
f_ne_zero (h : p.nextCoeff != 0) : 0 < p.natDegree
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.nextCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polyn
omial R),   p.nextCoeff = if p.natDegree = 0 then 0 else p.coeff (p.natDegree - 
1)
· 使用引理 `Polynomial.natDegree_eraseLead`：natDegree_eraseLead (h : f.nextCoeff != 
0) : f.eraseLead.natDegree = f.natDegree - 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Polynomial.eraseLead_coeff_of_ne`：eraseLead_coeff_of_ne (i : Nat) (hi : 
i != f.natDegree) : f.eraseLead.coeff i = f.coeff i
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `tsub_lt_self`：tsub_lt_self : 0 < a -> 0 < b -> a - b < a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
-/
theorem leadingCoeff_eraseLead_eq_nextCoeff (h : f.nextCoeff ≠ 0) :
    f.eraseLead.leadingCoeff = f.nextCoeff := by
  have := natDegree_pos_of_nextCoeff_ne_zero h
  rw [leadingCoeff, nextCoeff, natDegree_eraseLead h, if_neg,
    eraseLead_coeff_of_ne _ (tsub_lt_self _ _).ne]
  all_goals positivity
/-
**Polynomial.nextCoeff_eq_zero_of_eraseLead_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：nextCoeff_eq_zero_of_eraseLead_eq_zero (h : f.eraseLead = 0) : f.nextCoeff
 = 0
参数：h : f.eraseLead = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.leadingCoeff_eraseLead_eq_nextCoeff`：leadingCoeff_eraseLead_e
q_nextCoeff (h : f.nextCoeff != 0) : f.eraseLead.leadingCoeff = f.nextCoeff
-/
theorem nextCoeff_eq_zero_of_eraseLead_eq_zero (h : f.eraseLead = 0) : f.nextCoeff = 0 := by
  by_contra h₂
  exact leadingCoeff_ne_zero.mp (leadingCoeff_eraseLead_eq_nextCoeff h₂ ▸ h₂) h

/-- If we erase the leading coefficient of a `Polynomial.coeffList` like [+,0,...], and then
multiply by a linear term, it's equivalent to erasing the first two coefficients of the product. -/
/-
**Polynomial.eraseLead_mul_eq_mul_eraseLead_of_nextCoeff_zero** 是 Mathlib 中的一个引理
，位于命名空间 `Polynomial`。
形式化陈述：eraseLead_mul_eq_mul_eraseLead_of_nextCoeff_zero {R : Type*} [Ring R] [NoZ
eroDivisors R] [Nontrivial R] {x : R} {P : R[X]} (hx : x != 0) (h : P.nextCoeff 
= 0) : ((X - C x) * P).eraseLead.eraseLead = (X - C x) * P.eraseLead
参数：hx : x != 0；h : P.nextCoeff = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Polynomial.eraseLead_zero`：eraseLead_zero : eraseLead (0 : R[X]) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.card_support_binomial`：card_support_binomial {k m : Nat} (h :
 k != m) {x y : R} (hx : x != 0) (hy : y != 0) : #(support (C x * X ^ k + C y * 
X ^ m)) = 2
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `Polynomial.card_support_mul_le`：card_support_mul_le : #(p * q).support <
= #p.support * #q.support
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
（共 137 条，此处仅展示前 30 条）

--- 原说明 ---
If we erase the leading coefficient of a `Polynomial.coeffList` like [+,0,...], 
and then
multiply by a linear term, it's equivalent to erasing the first two coefficients
 of the product.
-/
lemma eraseLead_mul_eq_mul_eraseLead_of_nextCoeff_zero {R : Type*} [Ring R] [NoZeroDivisors R]
    [Nontrivial R] {x : R} {P : R[X]} (hx : x ≠ 0) (h : P.nextCoeff = 0) :
    ((X - C x) * P).eraseLead.eraseLead = (X - C x) * P.eraseLead := by
  -- if `P = 0` this is trivial
  by_cases hp : P = 0
  · simp [hp]
  -- can assume eraseLead P ≠ 0, otherwise it's a monomial and both sides are zero.
  by_cases he : P.eraseLead = 0
  · rw [he, mul_zero]
    by_cases he₂ : ((X - C x) * P).eraseLead = 0
    · simp [he₂]
    suffices #((X - C x) * P).support ≤ 2 by
      rw [← card_support_eq_zero]
      linarith [eraseLead_support_card_lt he₂,
        eraseLead_support_card_lt (mul_ne_zero (X_sub_C_ne_zero x) hp)]
    have h₂ : #(X - C x).support = 2 := by
      simpa [← sub_eq_add_neg] using!
        card_support_binomial one_ne_zero one_ne_zero (neg_ne_zero.mpr hx)
    have hmul := card_support_mul_le (p := X - C x) (q := P)
    rw [h₂] at hmul
    linarith [card_support_le_one_of_eraseLead_eq_zero he]
  have h₁ : ((X - C x) * P).natDegree = P.natDegree + 1 := by
    rw [natDegree_mul (X_sub_C_ne_zero x) hp, natDegree_X_sub_C, add_comm]
  -- 2 ≤ P.natDegree
  obtain ⟨dP, hdP⟩ := Nat.exists_eq_add_of_le' (two_le_natDegree_of_nextCoeff_eraseLead he h)
  -- the subleading term of (X - C η) * P is nonzero
  have h₂ : ((X - C x) * P).nextCoeff ≠ 0 := by
    simp only [nextCoeff, hdP, Nat.succ_ne_zero, ite_false, Nat.add_one_sub_one] at h
    rw [nextCoeff, h₁, add_tsub_cancel_right, hdP, coeff_X_sub_C_mul]
    simp [h, hx, ← hdP, hp]
  -- Prove equality by showing coefficients are equal
  ext n
  rcases n.lt_or_ge P.natDegree with hn | hn
  · --n < P.natDegree
    have hd₁ : n < ((X - C x) * P).eraseLead.natDegree := by
      linarith [natDegree_eraseLead_add_one h₂]
    rw [← self_sub_monomial_natDegree_leadingCoeff, coeff_sub, coeff_monomial, if_neg hd₁.ne']
    rw [← self_sub_monomial_natDegree_leadingCoeff, coeff_sub, coeff_monomial, if_neg (by lia)]
    rw [← self_sub_monomial_natDegree_leadingCoeff, mul_sub, coeff_sub,
      sub_zero, sub_zero, eq_sub_iff_add_eq, add_eq_left]
    rcases hn₂ : n
    · simpa [coeff_monomial, hp] using! fun _ ↦ by lia
    · rw [coeff_X_sub_C_mul, coeff_monomial, coeff_monomial, if_neg (by lia),
        if_neg (by lia), mul_zero, sub_zero]
  · --n ≥ P.natDegree, so all the coefficients are zero.
    trans 0 <;> rw [coeff_eq_zero_of_natDegree_lt]
    · grw [eraseLead_natDegree_le, eraseLead_natDegree_le]
      simpa [h₁, hdP] using! hn
    · grw [natDegree_mul (X_sub_C_ne_zero x) he, natDegree_eraseLead_le_of_nextCoeff_eq_zero h]
      simpa [add_comm, hdP] using! hn

end EraseLead

/-- An induction lemma for polynomials. It takes a natural number `N` as a parameter, that is
required to be at least as big as the `natDegree` of the polynomial.  This is useful to prove
results where you want to change each term in a polynomial to something else depending on the
`natDegree` of the polynomial itself and not on the specific `natDegree` of each term. -/
/-
**Polynomial.induction_with_natDegree_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：induction_with_natDegree_le (motive : R[X] -> Prop) (N : Nat) (zero : moti
ve 0) (C_mul_pow : forall n : Nat, forall r : R, r != 0 -> n <= N -> motive (C r
 * X ^ n)) (add : forall f g : R[X], f.natDegree < g.natDegree -> g.natDegree <=
 N -> motive f -> motive g -> motive (f + g)) (f : R[X]) (df : f.natDegree <= N)
 : motive f
参数：motive : R[X] -> Prop；N : Nat；zero : motive 0；C_mul_pow : forall n : Nat, for
all r : R, r != 0 -> n <= N -> motive (C r * X ^ n)；add : forall f g : R[X], f.n
atDegree < g.natDegree -> g.natDegree <= N -> motive f -> motive g -> motive (f 
+ g)；f : R[X]；df : f.natDegree <= N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eraseLead_add_C_mul_X_pow`：eraseLead_add_C_mul_X_pow (f : R[X
]) : f.eraseLead + C f.leadingCoeff * X ^ f.natDegree = f
· 使用定理 `Polynomial.card_support_eq_zero`：card_support_eq_zero : #p.support = 0 ↔
 p = 0
· 使用定理 `Polynomial.card_support_eraseLead'`：card_support_eraseLead' {c : Nat} (f
c : #f.support = c + 1) : #f.eraseLead.support = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Polynomial.eraseLead_natDegree_lt`：eraseLead_natDegree_lt (f0 : 2 <= #f.
support) : (eraseLead f).natDegree < f.natDegree
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.succ_le_succ`：∀ {n m : ℕ}, n ≤ m → n.succ ≤ m.succ
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Polynomial.natDegree_C_mul_X_pow`：natDegree_C_mul_X_pow (n : Nat) (a : R
) (ha : a != 0) : natDegree (C a * X ^ n) = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Polynomial.natDegree_C_mul_X_pow_le`：natDegree_C_mul_X_pow_le (a : R) (n
 : Nat) : natDegree (C a * X ^ n) <= n
· 使用定理 `Polynomial.eraseLead_natDegree_le_aux`：eraseLead_natDegree_le_aux : (era
seLead f).natDegree <= f.natDegree
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0

--- 原说明 ---
An induction lemma for polynomials. It takes a natural number `N` as a parameter
, that is
required to be at least as big as the `natDegree` of the polynomial.  This is us
eful to prove
results where you want to change each term in a polynomial to something else dep
ending on the
`natDegree` of the polynomial itself and not on the specific `natDegree` of each
 term.
-/
theorem induction_with_natDegree_le (motive : R[X] → Prop) (N : ℕ) (zero : motive 0)
    (C_mul_pow : ∀ n : ℕ, ∀ r : R, r ≠ 0 → n ≤ N → motive (C r * X ^ n))
    (add : ∀ f g : R[X], f.natDegree < g.natDegree → g.natDegree ≤ N →
      motive f → motive g → motive (f + g)) (f : R[X]) (df : f.natDegree ≤ N) : motive f := by
  induction hf : #f.support generalizing f with
  | zero =>
    convert! zero
    simpa [support_eq_empty, card_eq_zero] using hf
  | succ c hc =>
    rw [← eraseLead_add_C_mul_X_pow f]
    cases c
    · convert C_mul_pow f.natDegree f.leadingCoeff ?_ df
      · convert! zero_add (C (leadingCoeff f) * X ^ f.natDegree)
        rw [← card_support_eq_zero, card_support_eraseLead' hf]
      · rw [leadingCoeff_ne_zero, Ne, ← card_support_eq_zero, hf]
        exact zero_ne_one.symm
    refine add f.eraseLead _ ?_ ?_ ?_ ?_
    · refine (eraseLead_natDegree_lt ?_).trans_le (le_of_eq ?_)
      · exact (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))).trans hf.ge
      · rw [natDegree_C_mul_X_pow _ _ (leadingCoeff_ne_zero.mpr _)]
        rintro rfl
        simp at hf
    · exact (natDegree_C_mul_X_pow_le f.leadingCoeff f.natDegree).trans df
    · exact hc _ (eraseLead_natDegree_le_aux.trans df) (card_support_eraseLead' hf)
    · refine C_mul_pow _ _ ?_ df
      rw [Ne, leadingCoeff_eq_zero, ← card_support_eq_zero, hf]
      exact Nat.succ_ne_zero _

/-- Let `φ : R[x] → S[x]` be an additive map, `k : ℕ` a bound, and `fu : ℕ → ℕ` a
"sufficiently monotone" map.  Assume also that
* `φ` maps to `0` all monomials of degree less than `k`,
* `φ` maps each monomial `m` in `R[x]` to a polynomial `φ m` of degree `fu (deg m)`.

Then, `φ` maps each polynomial `p` in `R[x]` to a polynomial of degree `fu (deg p)`. -/
/-
**Polynomial.mono_map_natDegree_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mono_map_natDegree_eq {S F : Type*} [Semiring S] [FunLike F R[X] S[X]] [Ad
dMonoidHomClass F R[X] S[X]] {φ : F} {p : R[X]} (k : Nat) (fu : Nat -> Nat) (fu0
 : forall {n}, n <= k -> fu n = 0) (fc : forall {n m}, k <= n -> n < m -> fu n <
 fu m) (φ_k : forall {f : R[X]}, f.natDegree < k -> φ f = 0) (φ_mon_nat : forall
 n c, c != 0 -> (φ (monomial n c)).natDegree = fu n) : (φ p).natDegree = fu p.na
tDegree
参数：k : Nat；fu : Nat -> Nat；fu0 : forall {n}, n <= k -> fu n = 0；fc : forall {n m
}, k <= n -> n < m -> fu n < fu m；φ_k : forall {f : R[X]}, f.natDegree < k -> φ 
f = 0；φ_mon_nat : forall n c, c != 0 -> (φ (monomial n c)).natDegree = fu n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_with_natDegree_le`：induction_with_natDegree_le (mot
ive : R[X] -> Prop) (N : Nat) (zero : motive 0) (C_mul_pow : forall n : Nat, for
all r : R, r != 0 -> n <= N …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.natDegree_C_mul_X_pow`：natDegree_C_mul_X_pow (n : Nat) (a : R
) (ha : a != 0) : natDegree (C a * X ^ n) = n
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.natDegree_add_eq_right_of_natDegree_lt`：natDegree_add_eq_righ
t_of_natDegree_lt (h : natDegree p < natDegree q) : natDegree (p + q) = natDegre
e q
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b

--- 原说明 ---
Let `φ : R[x] → S[x]` be an additive map, `k : ℕ` a bound, and `fu : ℕ → ℕ` a
"sufficiently monotone" map.  Assume also that
* `φ` maps to `0` all monomials of degree less than `k`,
* `φ` maps each monomial `m` in `R[x]` to a polynomial `φ m` of degree `fu (deg 
m)`.

Then, `φ` maps each polynomial `p` in `R[x]` to a polynomial of degree `fu (deg 
p)`.
-/
theorem mono_map_natDegree_eq {S F : Type*} [Semiring S]
    [FunLike F R[X] S[X]] [AddMonoidHomClass F R[X] S[X]] {φ : F}
    {p : R[X]} (k : ℕ) (fu : ℕ → ℕ) (fu0 : ∀ {n}, n ≤ k → fu n = 0)
    (fc : ∀ {n m}, k ≤ n → n < m → fu n < fu m) (φ_k : ∀ {f : R[X]}, f.natDegree < k → φ f = 0)
    (φ_mon_nat : ∀ n c, c ≠ 0 → (φ (monomial n c)).natDegree = fu n) :
    (φ p).natDegree = fu p.natDegree := by
  refine induction_with_natDegree_le (fun p => (φ p).natDegree = fu p.natDegree)
    p.natDegree (by simp [fu0]) ?_ ?_ _ rfl.le
  · intro n r r0 _
    rw [natDegree_C_mul_X_pow _ _ r0, C_mul_X_pow_eq_monomial, φ_mon_nat _ _ r0]
  · intro f g fg _ fk gk
    rw [natDegree_add_eq_right_of_natDegree_lt fg, map_add]
    by_cases! FG : k ≤ f.natDegree
    · rw [natDegree_add_eq_right_of_natDegree_lt, gk]
      rw [fk, gk]
      exact fc FG fg
    · cases k
      · nomatch FG
      · rwa [φ_k FG, zero_add]
/-
**Polynomial.map_natDegree_eq_sub** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_natDegree_eq_sub {S F : Type*} [Semiring S] [FunLike F R[X] S[X]] [Add
MonoidHomClass F R[X] S[X]] {φ : F} {p : R[X]} {k : Nat} (φ_k : forall f : R[X],
 f.natDegree < k -> φ f = 0) (φ_mon : forall n c, c != 0 -> (φ (monomial n c)).n
atDegree = n - k) : (φ p).natDegree = p.natDegree - k
参数：φ_k : forall f : R[X], f.natDegree < k -> φ f = 0；φ_mon : forall n c, c != 0 
-> (φ (monomial n c)).natDegree = n - k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.mono_map_natDegree_eq`：mono_map_natDegree_eq {S F : Type*} [S
emiring S] [FunLike F R[X] S[X]] [AddMonoidHomClass F R[X] S[X]] {φ : F} {p : R[
X]} (k : Nat) (fu : Na…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_lt_tsub_iff_right`：tsub_lt_tsub_iff_right (h : c <= a) : a - c < b 
- c ↔ a < b
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem map_natDegree_eq_sub {S F : Type*} [Semiring S]
    [FunLike F R[X] S[X]] [AddMonoidHomClass F R[X] S[X]] {φ : F}
    {p : R[X]} {k : ℕ} (φ_k : ∀ f : R[X], f.natDegree < k → φ f = 0)
    (φ_mon : ∀ n c, c ≠ 0 → (φ (monomial n c)).natDegree = n - k) :
    (φ p).natDegree = p.natDegree - k :=
  mono_map_natDegree_eq k (fun j => j - k) (by simp_all)
    (@fun _ _ h => (tsub_lt_tsub_iff_right h).mpr)
    (φ_k _) φ_mon
/-
**Polynomial.map_natDegree_eq_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_natDegree_eq_natDegree {S F : Type*} [Semiring S] [FunLike F R[X] S[X]
] [AddMonoidHomClass F R[X] S[X]] {φ : F} (p) (φ_mon_nat : forall n c, c != 0 ->
 (φ (monomial n c)).natDegree = n) : (φ p).natDegree = p.natDegree
参数：p；φ_mon_nat : forall n c, c != 0 -> (φ (monomial n c)).natDegree = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.map_natDegree_eq_sub`：map_natDegree_eq_sub {S F : Type*} [Sem
iring S] [FunLike F R[X] S[X]] [AddMonoidHomClass F R[X] S[X]] {φ : F} {p : R[X]
} {k : Nat} (φ_k : fo…
· 使用定理 `Nat.not_lt_zero`：∀ (n : ℕ), ¬n < 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `Nat.sub_zero`：∀ (n : ℕ), n - 0 = n
-/
theorem map_natDegree_eq_natDegree {S F : Type*} [Semiring S]
    [FunLike F R[X] S[X]] [AddMonoidHomClass F R[X] S[X]]
    {φ : F} (p) (φ_mon_nat : ∀ n c, c ≠ 0 → (φ (monomial n c)).natDegree = n) :
    (φ p).natDegree = p.natDegree :=
  (map_natDegree_eq_sub (fun _ h => (Nat.not_lt_zero _ h).elim) (by simpa)).trans
    p.natDegree.sub_zero
/-
**Polynomial.card_support_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：card_support_eq' {n : Nat} (k : Fin n -> Nat) (x : Fin n -> R) (hk : Funct
ion.Injective k) (hx : forall i, x i != 0) : #(∑ i, C (x i) * X ^ k i).support =
 n
参数：k : Fin n -> Nat；x : Fin n -> R；hk : Function.Injective k；hx : forall i, x i 
!= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.finsetSum_coeff`：finsetSum_coeff {ι : Type*} (s : Finset ι) (
f : ι -> R[X]) (n : Nat) : coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.coeff_C_mul_X_pow`：coeff_C_mul_X_pow (x : R) (k n : Nat) : co
eff (C x * X ^ k : R[X]) n = if n = k then x else 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Finset.exists_ne_zero_of_sum_ne_zero`：∀ {ι : Type u_1} {M : Type u_4} {s
 : Finset ι} [inst : AddCommMonoid M] {f : ι → M}, ∑ x ∈ s, f x ≠ 0 → ∃ a ∈ s, f
 a ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ite_ne_right_iff`：ite_ne_right_iff : ite P a b != b ↔ P ∧ a != b
· 使用定理 `Finset.sum_eq_single_of_mem`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] {s : Finset ι} {f : ι → M},   ∀ a ∈ s, (∀ b ∈ s, b ≠ a → f b = 0) 
→ ∑ x ∈ s, f x = …
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.card_image_of_injective`：card_image_of_injective [DecidableEq β] 
(s : Finset α) (H : Injective f) : #(s.image f) = #s
· 使用定理 `Finset.card_fin`：Finset.card_fin (n : Nat) : #(univ : Finset (Fin n)) = 
n
-/
theorem card_support_eq' {n : ℕ} (k : Fin n → ℕ) (x : Fin n → R) (hk : Function.Injective k)
    (hx : ∀ i, x i ≠ 0) : #(∑ i, C (x i) * X ^ k i).support = n := by
  suffices (∑ i, C (x i) * X ^ k i).support = image k univ by
    rw [this, univ.card_image_of_injective hk, card_fin]
  simp_rw [Finset.ext_iff, mem_support_iff, finsetSum_coeff, coeff_C_mul_X_pow, mem_image,
    mem_univ, true_and]
  refine fun i => ⟨fun h => ?_, ?_⟩
  · obtain ⟨j, _, h⟩ := exists_ne_zero_of_sum_ne_zero h
    exact ⟨j, (ite_ne_right_iff.mp h).1.symm⟩
  · rintro ⟨j, _, rfl⟩
    rw [sum_eq_single_of_mem j (mem_univ j), if_pos rfl]
    · exact hx j
    · exact fun m _ hmj => if_neg fun h => hmj.symm (hk h)
/-
**Polynomial.card_support_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：card_support_eq {n : Nat} : #f.support = n ↔ exists (k : Fin n -> Nat) (x 
: Fin n -> R) (_ : StrictMono k) (_ : forall i, x i != 0), f = ∑ i, C (x i) * X 
^ k i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.card_support_eq_zero`：card_support_eq_zero : #p.support = 0 ↔
 p = 0
· 使用定理 `Polynomial.card_support_eraseLead'`：card_support_eraseLead' {c : Nat} (f
c : #f.support = c + 1) : #f.eraseLead.support = c
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Fin.castSucc_lt_last`：∀ {n : ℕ} (a : Fin n), a.castSucc < Fin.last n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.range_castSucc`：range_castSucc {n : Nat} : Set.range (castSucc : Fin
 n -> Fin n.succ) = ({ i | (i : Nat) < n } : Set (Fin n.succ))
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `Fin.strictMono_castSucc`：strictMono_castSucc : StrictMono (castSucc : Fi
n n -> Fin (n + 1))
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.castSucc_lt_castSucc_iff`：∀ {n : ℕ} {a b : Fin n}, a.castSucc < b.ca
stSucc ↔ a < b
· 使用定理 `Function.extend_apply'`：extend_apply' (g : α -> γ) (e' : β -> γ) (b : β)
 (hb : ¬exists a, f a = b) : extend f g e' b = e' b
· 使用定理 `Polynomial.lt_natDegree_of_mem_eraseLead_support`：lt_natDegree_of_mem_er
aseLead_support {a : Nat} (h : a in (eraseLead f).support) : a < f.natDegree
· 使用定理 `Polynomial.mem_support_iff`：mem_support_iff : n in p.support ↔ p.coeff n
 != 0
· 使用定理 `Polynomial.finsetSum_coeff`：finsetSum_coeff {ι : Type*} (s : Finset ι) (
f : ι -> R[X]) (n : Nat) : coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Polynomial.coeff_X_pow_self`：coeff_X_pow_self (n : Nat) : coeff (X ^ n :
 R[X]) n = 1
（共 39 条，此处仅展示前 30 条）
-/
theorem card_support_eq {n : ℕ} :
    #f.support = n ↔
      ∃ (k : Fin n → ℕ) (x : Fin n → R) (_ : StrictMono k) (_ : ∀ i, x i ≠ 0),
        f = ∑ i, C (x i) * X ^ k i := by
  refine ⟨?_, fun ⟨k, x, hk, hx, hf⟩ => hf.symm ▸ card_support_eq' k x hk.injective hx⟩
  induction n generalizing f with
  | zero => exact fun hf => ⟨0, 0, fun x => x.elim0, fun x => x.elim0, card_support_eq_zero.mp hf⟩
  | succ n hn =>
    intro h
    obtain ⟨k, x, hk, hx, hf⟩ := hn (card_support_eraseLead' h)
    have H : ¬∃ k : Fin n, Fin.castSucc k = Fin.last n := by
      rintro ⟨i, hi⟩
      exact i.castSucc_lt_last.ne hi
    refine
      ⟨Function.extend Fin.castSucc k fun _ => f.natDegree,
        Function.extend Fin.castSucc x fun _ => f.leadingCoeff, ?_, ?_, ?_⟩
    · intro i j hij
      have hi : i ∈ Set.range (Fin.castSucc : Fin n → Fin (n + 1)) := by
        simp only [Fin.range_castSucc, Nat.succ_eq_add_one, Set.mem_ofPred_eq]
        exact lt_of_lt_of_le hij (Nat.lt_succ_iff.mp j.2)
      obtain ⟨i, rfl⟩ := hi
      rw [Fin.strictMono_castSucc.injective.extend_apply]
      by_cases hj : ∃ j₀, Fin.castSucc j₀ = j
      · obtain ⟨j, rfl⟩ := hj
        rwa [Fin.strictMono_castSucc.injective.extend_apply, hk.lt_iff_lt,
          ← Fin.castSucc_lt_castSucc_iff]
      · rw [Function.extend_apply' _ _ _ hj]
        apply lt_natDegree_of_mem_eraseLead_support
        rw [mem_support_iff, hf, finsetSum_coeff]
        rw [sum_eq_single, coeff_C_mul, coeff_X_pow_self, mul_one]
        · exact hx i
        · intro j _ hji
          rw [coeff_C_mul, coeff_X_pow, if_neg (hk.injective.ne hji.symm), mul_zero]
        · exact fun hi => (hi (mem_univ i)).elim
    · intro i
      by_cases hi : ∃ i₀, Fin.castSucc i₀ = i
      · obtain ⟨i, rfl⟩ := hi
        rw [Fin.strictMono_castSucc.injective.extend_apply]
        exact hx i
      · rw [Function.extend_apply' _ _ _ hi, Ne, leadingCoeff_eq_zero, ← card_support_eq_zero, h]
        exact n.succ_ne_zero
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.strictMono_castSucc.injective.extend_apply]
      rw [← hf, Function.extend_apply', Function.extend_apply', eraseLead_add_C_mul_X_pow]
      all_goals exact H
/-
**Polynomial.card_support_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：card_support_eq_one : #f.support = 1 ↔ exists (k : Nat) (x : R) (_ : x != 
0), f = C x * X ^ k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.card_support_eq`：card_support_eq {n : Nat} : #f.support = n ↔
 exists (k : Fin n -> Nat) (x : Fin n -> R) (_ : StrictMono k) (_ : forall i, x 
i != 0), f = ∑ i…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.sum_univ_one`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 1 →
 M), ∑ i, f i = f 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.support_C_mul_X_pow`：support_C_mul_X_pow (n : Nat) {c : R} (h
 : c != 0) : Polynomial.support (C c * X ^ n) = singleton n
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
-/
theorem card_support_eq_one : #f.support = 1 ↔
    ∃ (k : ℕ) (x : R) (_ : x ≠ 0), f = C x * X ^ k := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨k, x, _, hx, rfl⟩ := card_support_eq.mp h
    exact ⟨k 0, x 0, hx 0, Fin.sum_univ_one _⟩
  · rintro ⟨k, x, hx, rfl⟩
    rw [support_C_mul_X_pow k hx, card_singleton]
/-
**Polynomial.card_support_eq_two** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：card_support_eq_two : #f.support = 2 ↔ exists (k m : Nat) (_ : k < m) (x y
 : R) (_ : x != 0) (_ : y != 0), f = C x * X ^ k + C y * X ^ m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.card_support_eq`：card_support_eq {n : Nat} : #f.support = n ↔
 exists (k : Fin n -> Nat) (x : Fin n -> R) (_ : StrictMono k) (_ : forall i, x 
i != 0), f = ∑ i…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.zero_lt_one`：0 < 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.sum_univ_castSucc`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ}
 (f : Fin (n + 1) → M), ∑ i, f i = ∑ i, f i.castSucc + f (Fin.last n)
· 使用定理 `Fin.sum_univ_one`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 1 →
 M), ∑ i, f i = f 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.card_support_binomial`：card_support_binomial {k m : Nat} (h :
 k != m) {x y : R} (hx : x != 0) (hy : y != 0) : #(support (C x * X ^ k + C y * 
X ^ m)) = 2
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem card_support_eq_two :
    #f.support = 2 ↔
      ∃ (k m : ℕ) (_ : k < m) (x y : R) (_ : x ≠ 0) (_ : y ≠ 0),
        f = C x * X ^ k + C y * X ^ m := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨k, x, hk, hx, rfl⟩ := card_support_eq.mp h
    refine ⟨k 0, k 1, hk Nat.zero_lt_one, x 0, x 1, hx 0, hx 1, ?_⟩
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_one]
    rfl
  · rintro ⟨k, m, hkm, x, y, hx, hy, rfl⟩
    exact card_support_binomial hkm.ne hx hy
/-
**Polynomial.card_support_eq_three** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：card_support_eq_three : #f.support = 3 ↔ exists (k m n : Nat) (_ : k < m) 
(_ : m < n) (x y z : R) (_ : x != 0) (_ : y != 0) (_ : z != 0), f = C x * X ^ k 
+ C y * X ^ m + C z * X ^ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.card_support_eq`：card_support_eq {n : Nat} : #f.support = n ↔
 exists (k : Fin n -> Nat) (x : Fin n -> R) (_ : StrictMono k) (_ : forall i, x 
i != 0), f = ∑ i…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.zero_lt_one`：0 < 1
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.sum_univ_castSucc`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ}
 (f : Fin (n + 1) → M), ∑ i, f i = ∑ i, f i.castSucc + f (Fin.last n)
· 使用定理 `Fin.sum_univ_one`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 1 →
 M), ∑ i, f i = f 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.card_support_trinomial`：card_support_trinomial {k m n : Nat} 
(hkm : k < m) (hmn : m < n) {x y z : R} (hx : x != 0) (hy : y != 0) (hz : z != 0
) : #(support (C x * X …
-/
theorem card_support_eq_three :
    #f.support = 3 ↔
      ∃ (k m n : ℕ) (_ : k < m) (_ : m < n) (x y z : R) (_ : x ≠ 0) (_ : y ≠ 0) (_ : z ≠ 0),
        f = C x * X ^ k + C y * X ^ m + C z * X ^ n := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨k, x, hk, hx, rfl⟩ := card_support_eq.mp h
    refine
      ⟨k 0, k 1, k 2, hk Nat.zero_lt_one, hk (Nat.lt_succ_self 1), x 0, x 1, x 2, hx 0, hx 1, hx 2,
        ?_⟩
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_one]
    rfl
  · rintro ⟨k, m, n, hkm, hmn, x, y, z, hx, hy, hz, rfl⟩
    exact card_support_trinomial hkm hmn hx hy hz

end Polynomial

