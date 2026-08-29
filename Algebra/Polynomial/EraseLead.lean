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

/--
Definition of `eraseLead` / `eraseLead` 的定义

English:
definition eraseLead
  signature: (f : R[X])
  body: Polynomial.erase f.natDegree f

中文:
定义 eraseLead
  签名: (f : R[X])
  定义体: Polynomial.erase f.natDegree f

Depends on / 依赖: Polynomial, Polynomial.erase, f.natDegree, natDegree
-/
def eraseLead (f : R[X]) : R[X] :=
  Polynomial.erase f.natDegree f

section EraseLead

/--
theorem `eraseLead_support` / 定理 `eraseLead_support`

English:
theorem eraseLead_support
  given: (f : R[X])
  statement: f.eraseLead.support = f.support.erase f.natDegree
  proof: by
  simp only [eraseLead, support_erase]

中文:
定理 eraseLead_support
  条件: (f : R[X])
  结论: f.eraseLead.support = f.support.erase f.natDegree
  证明: by
  simp only [eraseLead, support_erase]

Depends on / 依赖: eraseLead, support_erase
-/
theorem eraseLead_support (f : R[X]) : f.eraseLead.support = f.support.erase f.natDegree := by
  simp only [eraseLead, support_erase]

/--
theorem `eraseLead_coeff` / 定理 `eraseLead_coeff`

English:
theorem eraseLead_coeff
  given: (i : Nat)
  proof: by
  simp only [eraseLead, coeff_erase]

@[simp]

中文:
定理 eraseLead_coeff
  条件: (i : 自然数)
  证明: by
  simp only [eraseLead, coeff_erase]

@[simp]

Depends on / 依赖: coeff_erase, eraseLead
-/
theorem eraseLead_coeff (i : Nat) :
    f.eraseLead.coeff i = if i = f.natDegree then 0 else f.coeff i := by
  simp only [eraseLead, coeff_erase]

@[simp]
/--
theorem `eraseLead_coeff_natDegree` / 定理 `eraseLead_coeff_natDegree`

English:
theorem eraseLead_coeff_natDegree
  statement: f.eraseLead.coeff f.natDegree = 0
  proof: by simp [eraseLead_coeff]

中文:
定理 eraseLead_coeff_natDegree
  结论: f.eraseLead.coeff f.natDegree = 0
  证明: by simp [eraseLead_coeff]

Depends on / 依赖: eraseLead_coeff
-/
theorem eraseLead_coeff_natDegree : f.eraseLead.coeff f.natDegree = 0 := by simp [eraseLead_coeff]

/--
theorem `eraseLead_coeff_of_ne` / 定理 `eraseLead_coeff_of_ne`

English:
theorem eraseLead_coeff_of_ne
  given: (i : Nat) (hi : i != f.natDegree)
  statement: f.eraseLead.coeff i = f.coeff i
  proof: by
  simp [eraseLead_coeff, hi]

@[simp]

中文:
定理 eraseLead_coeff_of_ne
  条件: (i : 自然数) (hi : i != f.natDegree)
  结论: f.eraseLead.coeff i = f.coeff i
  证明: by
  simp [eraseLead_coeff, hi]

@[simp]

Depends on / 依赖: eraseLead_coeff
-/
theorem eraseLead_coeff_of_ne (i : Nat) (hi : i != f.natDegree) : f.eraseLead.coeff i = f.coeff i := by
  simp [eraseLead_coeff, hi]

@[simp]
/--
theorem `eraseLead_zero` / 定理 `eraseLead_zero`

English:
theorem eraseLead_zero
  statement: eraseLead (0 : R[X]) = 0
  proof: by simp only [eraseLead, erase_zero]

@[simp]

中文:
定理 eraseLead_zero
  结论: eraseLead (0 : R[X]) = 0
  证明: by simp only [eraseLead, erase_zero]

@[simp]

Depends on / 依赖: eraseLead, erase_zero
-/
theorem eraseLead_zero : eraseLead (0 : R[X]) = 0 := by simp only [eraseLead, erase_zero]

@[simp]
/--
theorem `eraseLead_add_monomial_natDegree_leadingCoeff` / 定理 `eraseLead_add_monomial_natDegree_leadingCoeff`

English:
theorem eraseLead_add_monomial_natDegree_leadingCoeff
  given: (f : R[X])
  proof: (add_comm _ _).trans (f.monomial_add_erase _)

@[simp]

中文:
定理 eraseLead_add_monomial_natDegree_leadingCoeff
  条件: (f : R[X])
  证明: (add_comm _ _).trans (f.monomial_add_erase _)

@[simp]

Depends on / 依赖: add_comm, f.monomial_add_erase, monomial_add_erase
-/
theorem eraseLead_add_monomial_natDegree_leadingCoeff (f : R[X]) :
    f.eraseLead + monomial f.natDegree f.leadingCoeff = f :=
  (add_comm _ _).trans (f.monomial_add_erase _)

@[simp]
/--
theorem `eraseLead_add_C_mul_X_pow` / 定理 `eraseLead_add_C_mul_X_pow`

English:
theorem eraseLead_add_C_mul_X_pow
  given: (f : R[X])
  proof: by
  rw [C_mul_X_pow_eq_monomial]; rw [eraseLead_add_monomial_natDegree_leadingCoeff]

@[simp]

中文:
定理 eraseLead_add_C_mul_X_pow
  条件: (f : R[X])
  证明: by
  rw [C_mul_X_pow_eq_monomial]; rw [eraseLead_add_monomial_natDegree_leadingCoeff]

@[simp]

Depends on / 依赖: C_mul_X_pow_eq_monomial, eraseLead_add_monomial_natDegree_leadingCoeff
-/
theorem eraseLead_add_C_mul_X_pow (f : R[X]) :
    f.eraseLead + C f.leadingCoeff * X ^ f.natDegree = f := by
  rw [C_mul_X_pow_eq_monomial]; rw [eraseLead_add_monomial_natDegree_leadingCoeff]

@[simp]
/--
theorem `self_sub_monomial_natDegree_leadingCoeff` / 定理 `self_sub_monomial_natDegree_leadingCoeff`

English:
theorem self_sub_monomial_natDegree_leadingCoeff
  given: {R : Type*} [Ring R] (f : R[X])
  proof: (eq_sub_iff_add_eq.mpr (eraseLead_add_monomial_natDegree_leadingCoeff f)).symm

@[simp]

中文:
定理 self_sub_monomial_natDegree_leadingCoeff
  条件: {R : 类型} [Ring R] (f : R[X])
  证明: (eq_sub_iff_add_eq.mpr (eraseLead_add_monomial_natDegree_leadingCoeff f)).symm

@[simp]

Depends on / 依赖: eq_sub_iff_add_eq, eq_sub_iff_add_eq.mpr, eraseLead_add_monomial_natDegree_leadingCoeff
-/
theorem self_sub_monomial_natDegree_leadingCoeff {R : Type*} [Ring R] (f : R[X]) :
    f - monomial f.natDegree f.leadingCoeff = f.eraseLead :=
  (eq_sub_iff_add_eq.mpr (eraseLead_add_monomial_natDegree_leadingCoeff f)).symm

@[simp]
/--
theorem `self_sub_C_mul_X_pow` / 定理 `self_sub_C_mul_X_pow`

English:
theorem self_sub_C_mul_X_pow
  given: {R : Type*} [Ring R] (f : R[X])
  proof: by
  rw [C_mul_X_pow_eq_monomial]; rw [self_sub_monomial_natDegree_leadingCoeff]

中文:
定理 self_sub_C_mul_X_pow
  条件: {R : 类型} [Ring R] (f : R[X])
  证明: by
  rw [C_mul_X_pow_eq_monomial]; rw [self_sub_monomial_natDegree_leadingCoeff]

Depends on / 依赖: C_mul_X_pow_eq_monomial, self_sub_monomial_natDegree_leadingCoeff
-/
theorem self_sub_C_mul_X_pow {R : Type*} [Ring R] (f : R[X]) :
    f - C f.leadingCoeff * X ^ f.natDegree = f.eraseLead := by
  rw [C_mul_X_pow_eq_monomial]; rw [self_sub_monomial_natDegree_leadingCoeff]

/--
theorem `eraseLead_ne_zero` / 定理 `eraseLead_ne_zero`

English:
theorem eraseLead_ne_zero
  given: (f0 : 2 <= #f.support)
  statement: eraseLead f != 0
  proof: by
  rw [Ne]; rw [← card_support_eq_zero]; rw [eraseLead_support]
  exact
    (zero_lt_one.trans_le <| (tsub_le_tsub_right f0 1).trans Finset.pred_card_le_card_erase).ne.symm

中文:
定理 eraseLead_ne_zero
  条件: (f0 : 2 <= #f.support)
  结论: eraseLead f != 0
  证明: by
  rw [Ne]; rw [← card_support_eq_zero]; rw [eraseLead_support]
  exact
    (zero_lt_one.trans_le <| (tsub_le_tsub_right f0 1).trans Finset.pred_card_le_card_erase).ne.symm

Depends on / 依赖: Finset, Finset.pred_card_le_card_erase, card_support_eq_zero, eraseLead_support, ne.symm, pred_card_le_card_erase, trans_le, tsub_le_tsub_right, zero_lt_one, zero_lt_one.trans_le
-/
theorem eraseLead_ne_zero (f0 : 2 <= #f.support) : eraseLead f != 0 := by
  rw [Ne]; rw [← card_support_eq_zero]; rw [eraseLead_support]
  exact
    (zero_lt_one.trans_le <| (tsub_le_tsub_right f0 1).trans Finset.pred_card_le_card_erase).ne.symm

/--
theorem `lt_natDegree_of_mem_eraseLead_support` / 定理 `lt_natDegree_of_mem_eraseLead_support`

English:
theorem lt_natDegree_of_mem_eraseLead_support
  given: {a : Nat} (h : a in (eraseLead f).support)
  proof: by
  rw [eraseLead_support]; rw [mem_erase] at h
  exact (le_natDegree_of_mem_supp a h.2).lt_of_ne h.1

中文:
定理 lt_natDegree_of_mem_eraseLead_support
  条件: {a : 自然数} (h : a in (eraseLead f).support)
  证明: by
  rw [eraseLead_support]; rw [mem_erase] at h
  exact (le_natDegree_of_mem_supp a h.2).lt_of_ne h.1

Depends on / 依赖: eraseLead_support, le_natDegree_of_mem_supp, lt_of_ne, mem_erase
-/
theorem lt_natDegree_of_mem_eraseLead_support {a : Nat} (h : a in (eraseLead f).support) :
    a < f.natDegree := by
  rw [eraseLead_support]; rw [mem_erase] at h
  exact (le_natDegree_of_mem_supp a h.2).lt_of_ne h.1

/--
theorem `ne_natDegree_of_mem_eraseLead_support` / 定理 `ne_natDegree_of_mem_eraseLead_support`

English:
theorem ne_natDegree_of_mem_eraseLead_support
  given: {a : Nat} (h : a in (eraseLead f).support)
  proof: (lt_natDegree_of_mem_eraseLead_support h).ne

中文:
定理 ne_natDegree_of_mem_eraseLead_support
  条件: {a : 自然数} (h : a in (eraseLead f).support)
  证明: (lt_natDegree_of_mem_eraseLead_support h).ne

Depends on / 依赖: lt_natDegree_of_mem_eraseLead_support
-/
theorem ne_natDegree_of_mem_eraseLead_support {a : Nat} (h : a in (eraseLead f).support) :
    a != f.natDegree :=
  (lt_natDegree_of_mem_eraseLead_support h).ne

/--
theorem `natDegree_notMem_eraseLead_support` / 定理 `natDegree_notMem_eraseLead_support`

English:
theorem natDegree_notMem_eraseLead_support
  statement: f.natDegree ∉ (eraseLead f).support
  proof: fun h =>
  ne_natDegree_of_mem_eraseLead_support h rfl

中文:
定理 natDegree_notMem_eraseLead_support
  结论: f.natDegree ∉ (eraseLead f).support
  证明: fun h =>
  ne_natDegree_of_mem_eraseLead_support h rfl
-/
theorem natDegree_notMem_eraseLead_support : f.natDegree ∉ (eraseLead f).support := fun h =>
  ne_natDegree_of_mem_eraseLead_support h rfl

/--
theorem `eraseLead_support_card_lt` / 定理 `eraseLead_support_card_lt`

English:
theorem eraseLead_support_card_lt
  given: (h : f != 0)
  statement: #(eraseLead f).support < #f.support
  proof: by
  rw [eraseLead_support]
  exact card_lt_card (erase_ssubset <| natDegree_mem_support_of_nonzero h)

中文:
定理 eraseLead_support_card_lt
  条件: (h : f != 0)
  结论: #(eraseLead f).support < #f.support
  证明: by
  rw [eraseLead_support]
  exact card_lt_card (erase_ssubset <| natDegree_mem_support_of_nonzero h)

Depends on / 依赖: card_lt_card, eraseLead_support, erase_ssubset, natDegree_mem_support_of_nonzero
-/
theorem eraseLead_support_card_lt (h : f != 0) : #(eraseLead f).support < #f.support := by
  rw [eraseLead_support]
  exact card_lt_card (erase_ssubset <| natDegree_mem_support_of_nonzero h)

/--
theorem `card_support_eraseLead_add_one` / 定理 `card_support_eraseLead_add_one`

English:
theorem card_support_eraseLead_add_one
  given: (h : f != 0)
  statement: #f.eraseLead.support + 1 = #f.support
  proof: by
  set c := #f.support with hc
  cases h₁ : c
  case zero =>
    by_contra
    exact h (card_support_eq_zero.mp h₁)
  case succ =>
    rw [eraseLead_support]; rw [card_erase_of_mem (natDegree_mem_support_of_nonzero h)]; rw [← hc]; rw [h₁]
    rfl

@[simp]

中文:
定理 card_support_eraseLead_add_one
  条件: (h : f != 0)
  结论: #f.eraseLead.support + 1 = #f.support
  证明: by
  set c := #f.support with hc
  cases h₁ : c
  case zero =>
    by_contra
    exact h (card_support_eq_zero.mp h₁)
  case succ =>
    rw [eraseLead_support]; rw [card_erase_of_mem (natDegree_mem_support_of_nonzero h)]; rw [← hc]; rw [h₁]
    rfl

@[simp]

Depends on / 依赖: Fintype, card_erase_of_mem, card_support_eq_zero, card_support_eq_zero.mp, eraseLead_support, f.support, natDegree_mem_support_of_nonzero, support
-/
theorem card_support_eraseLead_add_one (h : f != 0) : #f.eraseLead.support + 1 = #f.support := by
  set c := #f.support with hc
  cases h₁ : c
  case zero =>
    by_contra
    exact h (card_support_eq_zero.mp h₁)
  case succ =>
    rw [eraseLead_support]; rw [card_erase_of_mem (natDegree_mem_support_of_nonzero h)]; rw [← hc]; rw [h₁]
    rfl

@[simp]
/--
theorem `card_support_eraseLead` / 定理 `card_support_eraseLead`

English:
theorem card_support_eraseLead
  statement: #f.eraseLead.support = #f.support - 1
  proof: by
  by_cases hf : f = 0
  · rw [hf, eraseLead_zero, support_zero, card_empty]
  · rw [← card_support_eraseLead_add_one hf, add_tsub_cancel_right]

中文:
定理 card_support_eraseLead
  结论: #f.eraseLead.support = #f.support - 1
  证明: by
  by_cases hf : f = 0
  · rw [hf, eraseLead_zero, support_zero, card_empty]
  · rw [← card_support_eraseLead_add_one hf, add_tsub_cancel_right]

Depends on / 依赖: add_tsub_cancel_right, card_empty, card_support_eraseLead_add_one, eraseLead_zero, support_zero
-/
theorem card_support_eraseLead : #f.eraseLead.support = #f.support - 1 := by
  by_cases hf : f = 0
  · rw [hf, eraseLead_zero, support_zero, card_empty]
  · rw [← card_support_eraseLead_add_one hf, add_tsub_cancel_right]

/--
theorem `card_support_eraseLead'` / 定理 `card_support_eraseLead'`

English:
theorem card_support_eraseLead'
  given: {c : Nat} (fc : #f.support = c + 1)
  proof: by
  rw [card_support_eraseLead]; rw [fc]; rw [add_tsub_cancel_right]

中文:
定理 card_support_eraseLead'
  条件: {c : 自然数} (fc : #f.support = c + 1)
  证明: by
  rw [card_support_eraseLead]; rw [fc]; rw [add_tsub_cancel_right]

Depends on / 依赖: add_tsub_cancel_right, card_support_eraseLead
-/
theorem card_support_eraseLead' {c : Nat} (fc : #f.support = c + 1) :
    #f.eraseLead.support = c := by
  rw [card_support_eraseLead]; rw [fc]; rw [add_tsub_cancel_right]

/--
theorem `card_support_eq_one_of_eraseLead_eq_zero` / 定理 `card_support_eq_one_of_eraseLead_eq_zero`

English:
theorem card_support_eq_one_of_eraseLead_eq_zero
  given: (h₀ : f != 0) (h₁ : f.eraseLead = 0)
  proof: (card_support_eq_zero.mpr h₁ ▸ card_support_eraseLead_add_one h₀).symm

中文:
定理 card_support_eq_one_of_eraseLead_eq_zero
  条件: (h₀ : f != 0) (h₁ : f.eraseLead = 0)
  证明: (card_support_eq_zero.mpr h₁ ▸ card_support_eraseLead_add_one h₀).symm

Depends on / 依赖: card_support_eq_zero, card_support_eq_zero.mpr, card_support_eraseLead_add_one
-/
theorem card_support_eq_one_of_eraseLead_eq_zero (h₀ : f != 0) (h₁ : f.eraseLead = 0) :
    #f.support = 1 :=
  (card_support_eq_zero.mpr h₁ ▸ card_support_eraseLead_add_one h₀).symm

/--
theorem `card_support_le_one_of_eraseLead_eq_zero` / 定理 `card_support_le_one_of_eraseLead_eq_zero`

English:
theorem card_support_le_one_of_eraseLead_eq_zero
  given: (h : f.eraseLead = 0)
  statement: #f.support <= 1
  proof: by
  by_cases hpz : f = 0
  case pos => simp [hpz]
  case neg => exact le_of_eq (card_support_eq_one_of_eraseLead_eq_zero hpz h)

@[simp]

中文:
定理 card_support_le_one_of_eraseLead_eq_zero
  条件: (h : f.eraseLead = 0)
  结论: #f.support <= 1
  证明: by
  by_cases hpz : f = 0
  case pos => simp [hpz]
  case neg => exact le_of_eq (card_support_eq_one_of_eraseLead_eq_zero hpz h)

@[simp]

Depends on / 依赖: card_support_eq_one_of_eraseLead_eq_zero, le_of_eq
-/
theorem card_support_le_one_of_eraseLead_eq_zero (h : f.eraseLead = 0) : #f.support <= 1 := by
  by_cases hpz : f = 0
  case pos => simp [hpz]
  case neg => exact le_of_eq (card_support_eq_one_of_eraseLead_eq_zero hpz h)

@[simp]
/--
theorem `eraseLead_monomial` / 定理 `eraseLead_monomial`

English:
theorem eraseLead_monomial
  given: (i : Nat) (r : R)
  statement: eraseLead (monomial i r) = 0
  proof: by
  classical
  by_cases hr : r = 0
  · subst r
    simp only [monomial_zero_right, eraseLead_zero]
  · rw [eraseLead, natDegree_monomial, if_neg hr, erase_monomial]

@[simp]

中文:
定理 eraseLead_monomial
  条件: (i : 自然数) (r : R)
  结论: eraseLead (monomial i r) = 0
  证明: by
  classical
  by_cases hr : r = 0
  · subst r
    simp only [monomial_zero_right, eraseLead_zero]
  · rw [eraseLead, natDegree_monomial, if_neg hr, erase_monomial]

@[simp]

Depends on / 依赖: classical, eraseLead, eraseLead_zero, erase_monomial, if_neg, monomial_zero_right, natDegree_monomial
-/
theorem eraseLead_monomial (i : Nat) (r : R) : eraseLead (monomial i r) = 0 := by
  classical
  by_cases hr : r = 0
  · subst r
    simp only [monomial_zero_right, eraseLead_zero]
  · rw [eraseLead, natDegree_monomial, if_neg hr, erase_monomial]

@[simp]
/--
theorem `eraseLead_C` / 定理 `eraseLead_C`

English:
theorem eraseLead_C
  given: (r : R)
  statement: eraseLead (C r) = 0
  proof: eraseLead_monomial _ _

@[simp]

中文:
定理 eraseLead_C
  条件: (r : R)
  结论: eraseLead (C r) = 0
  证明: eraseLead_monomial _ _

@[simp]

Depends on / 依赖: eraseLead_monomial
-/
theorem eraseLead_C (r : R) : eraseLead (C r) = 0 :=
  eraseLead_monomial _ _

@[simp]
/--
theorem `eraseLead_X` / 定理 `eraseLead_X`

English:
theorem eraseLead_X
  statement: eraseLead (X : R[X]) = 0
  proof: eraseLead_monomial _ _

@[simp]

中文:
定理 eraseLead_X
  结论: eraseLead (X : R[X]) = 0
  证明: eraseLead_monomial _ _

@[simp]

Depends on / 依赖: eraseLead_monomial
-/
theorem eraseLead_X : eraseLead (X : R[X]) = 0 :=
  eraseLead_monomial _ _

@[simp]
/--
theorem `eraseLead_X_pow` / 定理 `eraseLead_X_pow`

English:
theorem eraseLead_X_pow
  given: (n : Nat)
  statement: eraseLead (X ^ n : R[X]) = 0
  proof: by
  rw [X_pow_eq_monomial]; rw [eraseLead_monomial]

@[simp]

中文:
定理 eraseLead_X_pow
  条件: (n : 自然数)
  结论: eraseLead (X ^ n : R[X]) = 0
  证明: by
  rw [X_pow_eq_monomial]; rw [eraseLead_monomial]

@[simp]

Depends on / 依赖: X_pow_eq_monomial, eraseLead_monomial
-/
theorem eraseLead_X_pow (n : Nat) : eraseLead (X ^ n : R[X]) = 0 := by
  rw [X_pow_eq_monomial]; rw [eraseLead_monomial]

@[simp]
/--
theorem `eraseLead_C_mul_X_pow` / 定理 `eraseLead_C_mul_X_pow`

English:
theorem eraseLead_C_mul_X_pow
  given: (r : R) (n : Nat)
  statement: eraseLead (C r * X ^ n) = 0
  proof: by
  rw [C_mul_X_pow_eq_monomial]; rw [eraseLead_monomial]

中文:
定理 eraseLead_C_mul_X_pow
  条件: (r : R) (n : 自然数)
  结论: eraseLead (C r * X ^ n) = 0
  证明: by
  rw [C_mul_X_pow_eq_monomial]; rw [eraseLead_monomial]

Depends on / 依赖: C_mul_X_pow_eq_monomial, eraseLead_monomial
-/
theorem eraseLead_C_mul_X_pow (r : R) (n : Nat) : eraseLead (C r * X ^ n) = 0 := by
  rw [C_mul_X_pow_eq_monomial]; rw [eraseLead_monomial]

/--
lemma `eraseLead_C_mul_X` / 引理 `eraseLead_C_mul_X`

English:
lemma eraseLead_C_mul_X
  given: (r : R)
  statement: eraseLead (C r * X) = 0
  proof: by
  simpa using eraseLead_C_mul_X_pow _ 1

中文:
引理 eraseLead_C_mul_X
  条件: (r : R)
  结论: eraseLead (C r * X) = 0
  证明: by
  simpa using eraseLead_C_mul_X_pow _ 1
-/
@[simp] lemma eraseLead_C_mul_X (r : R) : eraseLead (C r * X) = 0 := by
  simpa using eraseLead_C_mul_X_pow _ 1

/--
theorem `eraseLead_add_of_degree_lt_left` / 定理 `eraseLead_add_of_degree_lt_left`

English:
theorem eraseLead_add_of_degree_lt_left
  given: {p q : R[X]} (pq : q.degree < p.degree)
  proof: by
  ext n
  by_cases nd : n = p.natDegree
  · rw [nd, eraseLead_coeff, if_pos (natDegree_add_eq_left_of_degree_lt pq).symm]
    simpa using (coeff_eq_zero_of_degree_lt (lt_of_lt_of_le pq degree_le_natDegree)).symm
  · rw [eraseLead_coeff, coeff_add, coeff_add, eraseLead_coeff, if_neg, if_neg nd]
  

中文:
定理 eraseLead_add_of_degree_lt_left
  条件: {p q : R[X]} (pq : q.degree < p.degree)
  证明: by
  ext n
  by_cases nd : n = p.natDegree
  · rw [nd, eraseLead_coeff, if_pos (natDegree_add_eq_left_of_degree_lt pq).symm]
    simpa using (coeff_eq_zero_of_degree_lt (lt_of_lt_of_le pq degree_le_natDegree)).symm
  · rw [eraseLead_coeff, coeff_add, coeff_add, eraseLead_coeff, if_neg, if_neg nd]
  

Depends on / 依赖: coeff_add, coeff_eq_zero_of_degree_lt, degree_le_natDegree, eraseLead_coeff, if_neg, if_pos, lt_of_lt_of_le, natDegree, natDegree_add_eq_left_of_degree_lt, p.natDegree
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

/--
theorem `eraseLead_add_of_natDegree_lt_left` / 定理 `eraseLead_add_of_natDegree_lt_left`

English:
theorem eraseLead_add_of_natDegree_lt_left
  given: {p q : R[X]} (pq : q.natDegree < p.natDegree)
  proof: eraseLead_add_of_degree_lt_left (degree_lt_degree pq)

中文:
定理 eraseLead_add_of_natDegree_lt_left
  条件: {p q : R[X]} (pq : q.natDegree < p.natDegree)
  证明: eraseLead_add_of_degree_lt_left (degree_lt_degree pq)

Depends on / 依赖: degree_lt_degree, eraseLead_add_of_degree_lt_left
-/
theorem eraseLead_add_of_natDegree_lt_left {p q : R[X]} (pq : q.natDegree < p.natDegree) :
    (p + q).eraseLead = p.eraseLead + q :=
  eraseLead_add_of_degree_lt_left (degree_lt_degree pq)

/--
theorem `eraseLead_add_of_degree_lt_right` / 定理 `eraseLead_add_of_degree_lt_right`

English:
theorem eraseLead_add_of_degree_lt_right
  given: {p q : R[X]} (pq : p.degree < q.degree)
  proof: by
  ext n
  by_cases nd : n = q.natDegree
  · rw [nd, eraseLead_coeff, if_pos (natDegree_add_eq_right_of_degree_lt pq).symm]
    simpa using (coeff_eq_zero_of_degree_lt (lt_of_lt_of_le pq degree_le_natDegree)).symm
  · rw [eraseLead_coeff, coeff_add, coeff_add, eraseLead_coeff, if_neg, if_neg nd]
 

中文:
定理 eraseLead_add_of_degree_lt_right
  条件: {p q : R[X]} (pq : p.degree < q.degree)
  证明: by
  ext n
  by_cases nd : n = q.natDegree
  · rw [nd, eraseLead_coeff, if_pos (natDegree_add_eq_right_of_degree_lt pq).symm]
    simpa using (coeff_eq_zero_of_degree_lt (lt_of_lt_of_le pq degree_le_natDegree)).symm
  · rw [eraseLead_coeff, coeff_add, coeff_add, eraseLead_coeff, if_neg, if_neg nd]
 

Depends on / 依赖: coeff_add, coeff_eq_zero_of_degree_lt, degree_le_natDegree, eraseLead_coeff, if_neg, if_pos, lt_of_lt_of_le, natDegree, natDegree_add_eq_right_of_degree_lt, q.natDegree
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

/--
theorem `eraseLead_add_of_natDegree_lt_right` / 定理 `eraseLead_add_of_natDegree_lt_right`

English:
theorem eraseLead_add_of_natDegree_lt_right
  given: {p q : R[X]} (pq : p.natDegree < q.natDegree)
  proof: eraseLead_add_of_degree_lt_right (degree_lt_degree pq)

中文:
定理 eraseLead_add_of_natDegree_lt_right
  条件: {p q : R[X]} (pq : p.natDegree < q.natDegree)
  证明: eraseLead_add_of_degree_lt_right (degree_lt_degree pq)

Depends on / 依赖: degree_lt_degree, eraseLead_add_of_degree_lt_right
-/
theorem eraseLead_add_of_natDegree_lt_right {p q : R[X]} (pq : p.natDegree < q.natDegree) :
    (p + q).eraseLead = p + q.eraseLead :=
  eraseLead_add_of_degree_lt_right (degree_lt_degree pq)

/--
theorem `eraseLead_degree_le` / 定理 `eraseLead_degree_le`

English:
theorem eraseLead_degree_le
  statement: (eraseLead f).degree <= f.degree
  proof: f.degree_erase_le _

中文:
定理 eraseLead_degree_le
  结论: (eraseLead f).degree <= f.degree
  证明: f.degree_erase_le _

Depends on / 依赖: degree_erase_le, f.degree_erase_le
-/
theorem eraseLead_degree_le : (eraseLead f).degree <= f.degree :=
  f.degree_erase_le _

/--
theorem `degree_eraseLead_lt` / 定理 `degree_eraseLead_lt`

English:
theorem degree_eraseLead_lt
  given: (hf : f != 0)
  statement: (eraseLead f).degree < f.degree
  proof: f.degree_erase_lt hf

中文:
定理 degree_eraseLead_lt
  条件: (hf : f != 0)
  结论: (eraseLead f).degree < f.degree
  证明: f.degree_erase_lt hf

Depends on / 依赖: degree_erase_lt, f.degree_erase_lt
-/
theorem degree_eraseLead_lt (hf : f != 0) : (eraseLead f).degree < f.degree :=
  f.degree_erase_lt hf

/--
theorem `eraseLead_natDegree_le_aux` / 定理 `eraseLead_natDegree_le_aux`

English:
theorem eraseLead_natDegree_le_aux
  statement: (eraseLead f).natDegree <= f.natDegree
  proof: natDegree_le_natDegree eraseLead_degree_le

中文:
定理 eraseLead_natDegree_le_aux
  结论: (eraseLead f).natDegree <= f.natDegree
  证明: natDegree_le_natDegree eraseLead_degree_le

Depends on / 依赖: eraseLead_degree_le, natDegree_le_natDegree
-/
theorem eraseLead_natDegree_le_aux : (eraseLead f).natDegree <= f.natDegree :=
  natDegree_le_natDegree eraseLead_degree_le

/--
theorem `eraseLead_natDegree_lt` / 定理 `eraseLead_natDegree_lt`

English:
theorem eraseLead_natDegree_lt
  given: (f0 : 2 <= #f.support)
  statement: (eraseLead f).natDegree < f.natDegree
  proof: lt_of_le_of_ne eraseLead_natDegree_le_aux
ne_natDegree_of_mem_eraseLead_support
natDegree_mem_support_of_nonzero eraseLead_ne_zero f0

中文:
定理 eraseLead_natDegree_lt
  条件: (f0 : 2 <= #f.support)
  结论: (eraseLead f).natDegree < f.natDegree
  证明: lt_of_le_of_ne eraseLead_natDegree_le_aux
ne_natDegree_of_mem_eraseLead_support
natDegree_mem_support_of_nonzero eraseLead_ne_zero f0

Depends on / 依赖: eraseLead_natDegree_le_aux, eraseLead_ne_zero, lt_of_le_of_ne, natDegree_mem_support_of_nonzero, ne_natDegree_of_mem_eraseLead_support
-/
theorem eraseLead_natDegree_lt (f0 : 2 <= #f.support) : (eraseLead f).natDegree < f.natDegree :=
lt_of_le_of_ne eraseLead_natDegree_le_aux
ne_natDegree_of_mem_eraseLead_support
natDegree_mem_support_of_nonzero eraseLead_ne_zero f0

/--
theorem `natDegree_pos_of_eraseLead_ne_zero` / 定理 `natDegree_pos_of_eraseLead_ne_zero`

English:
theorem natDegree_pos_of_eraseLead_ne_zero
  given: (h : f.eraseLead != 0)
  statement: 0 < f.natDegree
  proof: by
  by_contra h₂
  rw [eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos h₂)] at h
  simp at h

中文:
定理 natDegree_pos_of_eraseLead_ne_zero
  条件: (h : f.eraseLead != 0)
  结论: 0 < f.natDegree
  证明: by
  by_contra h₂
  rw [eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos h₂)] at h
  simp at h

Depends on / 依赖: Nat.eq_zero_of_not_pos, eq_C_of_natDegree_eq_zero, eq_zero_of_not_pos
-/
theorem natDegree_pos_of_eraseLead_ne_zero (h : f.eraseLead != 0) : 0 < f.natDegree := by
  by_contra h₂
  rw [eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos h₂)] at h
  simp at h

/--
theorem `eraseLead_natDegree_lt_or_eraseLead_eq_zero` / 定理 `eraseLead_natDegree_lt_or_eraseLead_eq_zero`

English:
theorem eraseLead_natDegree_lt_or_eraseLead_eq_zero
  given: (f : R[X])
  proof: by
  by_cases! h : #f.support <= 1
  · right
    rw [← C_mul_X_pow_eq_self h]
    simp
  · left
    apply eraseLead_natDegree_lt h

中文:
定理 eraseLead_natDegree_lt_or_eraseLead_eq_zero
  条件: (f : R[X])
  证明: by
  by_cases! h : #f.support <= 1
  · right
    rw [← C_mul_X_pow_eq_self h]
    simp
  · left
    apply eraseLead_natDegree_lt h

Depends on / 依赖: C_mul_X_pow_eq_self, eraseLead_natDegree_lt, f.support, support
-/
theorem eraseLead_natDegree_lt_or_eraseLead_eq_zero (f : R[X]) :
    (eraseLead f).natDegree < f.natDegree ∨ f.eraseLead = 0 := by
  by_cases! h : #f.support <= 1
  · right
    rw [← C_mul_X_pow_eq_self h]
    simp
  · left
    apply eraseLead_natDegree_lt h

/--
theorem `eraseLead_natDegree_le` / 定理 `eraseLead_natDegree_le`

English:
theorem eraseLead_natDegree_le
  given: (f : R[X])
  statement: (eraseLead f).natDegree <= f.natDegree - 1
  proof: by
  rcases f.eraseLead_natDegree_lt_or_eraseLead_eq_zero with (h | h)
  · exact Nat.le_sub_one_of_lt h
  · simp only [h, natDegree_zero, zero_le]

中文:
定理 eraseLead_natDegree_le
  条件: (f : R[X])
  结论: (eraseLead f).natDegree <= f.natDegree - 1
  证明: by
  rcases f.eraseLead_natDegree_lt_or_eraseLead_eq_zero with (h | h)
  · exact Nat.le_sub_one_of_lt h
  · simp only [h, natDegree_zero, zero_le]

Depends on / 依赖: Nat.le_sub_one_of_lt, eraseLead_natDegree_lt_or_eraseLead_eq_zero, f.eraseLead_natDegree_lt_or_eraseLead_eq_zero, le_sub_one_of_lt, natDegree_zero, zero_le
-/
theorem eraseLead_natDegree_le (f : R[X]) : (eraseLead f).natDegree <= f.natDegree - 1 := by
  rcases f.eraseLead_natDegree_lt_or_eraseLead_eq_zero with (h | h)
  · exact Nat.le_sub_one_of_lt h
  · simp only [h, natDegree_zero, zero_le]

/--
lemma `natDegree_eraseLead` / 引理 `natDegree_eraseLead`

English:
lemma natDegree_eraseLead
  given: (h : f.nextCoeff != 0)
  statement: f.eraseLead.natDegree = f.natDegree - 1
  proof: by
  have := natDegree_pos_of_nextCoeff_ne_zero h
refine f.eraseLead_natDegree_le.antisymm le_natDegree_of_ne_zero ?_
  rwa [eraseLead_coeff_of_ne _ (tsub_lt_self _ _).ne, ← nextCoeff_of_natDegree_pos]
  all_goals positivity

中文:
引理 natDegree_eraseLead
  条件: (h : f.nextCoeff != 0)
  结论: f.eraseLead.natDegree = f.natDegree - 1
  证明: by
  have := natDegree_pos_of_nextCoeff_ne_zero h
refine f.eraseLead_natDegree_le.antisymm le_natDegree_of_ne_zero ?_
  rwa [eraseLead_coeff_of_ne _ (tsub_lt_self _ _).ne, ← nextCoeff_of_natDegree_pos]
  all_goals positivity

Depends on / 依赖: all_goals, antisymm, eraseLead_coeff_of_ne, eraseLead_natDegree_le, f.eraseLead_natDegree_le.antisymm, le_natDegree_of_ne_zero, natDegree_pos_of_nextCoeff_ne_zero, nextCoeff_of_natDegree_pos, tsub_lt_self
-/
lemma natDegree_eraseLead (h : f.nextCoeff != 0) : f.eraseLead.natDegree = f.natDegree - 1 := by
  have := natDegree_pos_of_nextCoeff_ne_zero h
refine f.eraseLead_natDegree_le.antisymm le_natDegree_of_ne_zero ?_
  rwa [eraseLead_coeff_of_ne _ (tsub_lt_self _ _).ne, ← nextCoeff_of_natDegree_pos]
  all_goals positivity

/--
lemma `natDegree_eraseLead_add_one` / 引理 `natDegree_eraseLead_add_one`

English:
lemma natDegree_eraseLead_add_one
  given: (h : f.nextCoeff != 0)
  proof: by
  rw [natDegree_eraseLead h]; rw [tsub_add_cancel_of_le]
  exact natDegree_pos_of_nextCoeff_ne_zero h

中文:
引理 natDegree_eraseLead_add_one
  条件: (h : f.nextCoeff != 0)
  证明: by
  rw [natDegree_eraseLead h]; rw [tsub_add_cancel_of_le]
  exact natDegree_pos_of_nextCoeff_ne_zero h

Depends on / 依赖: natDegree_eraseLead, natDegree_pos_of_nextCoeff_ne_zero, tsub_add_cancel_of_le
-/
lemma natDegree_eraseLead_add_one (h : f.nextCoeff != 0) :
    f.eraseLead.natDegree + 1 = f.natDegree := by
  rw [natDegree_eraseLead h]; rw [tsub_add_cancel_of_le]
  exact natDegree_pos_of_nextCoeff_ne_zero h

/--
theorem `natDegree_eraseLead_le_of_nextCoeff_eq_zero` / 定理 `natDegree_eraseLead_le_of_nextCoeff_eq_zero`

English:
theorem natDegree_eraseLead_le_of_nextCoeff_eq_zero
  given: (h : f.nextCoeff = 0)
  proof: by
  refine natDegree_le_pred (n := f.natDegree - 1) (eraseLead_natDegree_le f) ?_
  rw [nextCoeff_eq_zero]; rw [natDegree_eq_zero] at h
  obtain ⟨a, rfl⟩ | ⟨hf, h⟩ := h
  · simp
  rw [eraseLead_coeff_of_ne _ (tsub_lt_self hf zero_lt_one).ne]; rw [← nextCoeff_of_natDegree_pos hf]
  simp [nextCoeff_e

中文:
定理 natDegree_eraseLead_le_of_nextCoeff_eq_zero
  条件: (h : f.nextCoeff = 0)
  证明: by
  refine natDegree_le_pred (n := f.natDegree - 1) (eraseLead_natDegree_le f) ?_
  rw [nextCoeff_eq_zero]; rw [natDegree_eq_zero] at h
  obtain ⟨a, rfl⟩ | ⟨hf, h⟩ := h
  · simp
  rw [eraseLead_coeff_of_ne _ (tsub_lt_self hf zero_lt_one).ne]; rw [← nextCoeff_of_natDegree_pos hf]
  simp [nextCoeff_e

Depends on / 依赖: eq_zero_or_pos, eraseLead_coeff_of_ne, eraseLead_natDegree_le, f.natDegree, natDegree, natDegree_eq_zero, natDegree_le_pred, nextCoeff_eq_zero, nextCoeff_of_natDegree_pos, tsub_lt_self, zero_lt_one
-/
theorem natDegree_eraseLead_le_of_nextCoeff_eq_zero (h : f.nextCoeff = 0) :
    f.eraseLead.natDegree <= f.natDegree - 2 := by
  refine natDegree_le_pred (n := f.natDegree - 1) (eraseLead_natDegree_le f) ?_
  rw [nextCoeff_eq_zero]; rw [natDegree_eq_zero] at h
  obtain ⟨a, rfl⟩ | ⟨hf, h⟩ := h
  · simp
  rw [eraseLead_coeff_of_ne _ (tsub_lt_self hf zero_lt_one).ne]; rw [← nextCoeff_of_natDegree_pos hf]
  simp [nextCoeff_eq_zero, h, eq_zero_or_pos]

/--
lemma `two_le_natDegree_of_nextCoeff_eraseLead` / 引理 `two_le_natDegree_of_nextCoeff_eraseLead`

English:
lemma two_le_natDegree_of_nextCoeff_eraseLead
  statement: (hlead : f.eraseLead != 0)
  proof: by
  contrapose! hlead
  rw [Nat.lt_succ_iff]; rw [Nat.le_one_iff_eq_zero_or_eq_one]; rw [natDegree_eq_zero]; rw [natDegree_eq_one]
    at hlead
  obtain ⟨a, rfl⟩ | ⟨a, ha, b, rfl⟩ := hlead
  · simp
  · rw [nextCoeff_C_mul_X_add_C ha] at hnext
    subst b
    simp

中文:
引理 two_le_natDegree_of_nextCoeff_eraseLead
  结论: (hlead : f.eraseLead != 0)
  证明: by
  contrapose! hlead
  rw [Nat.lt_succ_iff]; rw [Nat.le_one_iff_eq_zero_or_eq_one]; rw [natDegree_eq_zero]; rw [natDegree_eq_one]
    at hlead
  obtain ⟨a, rfl⟩ | ⟨a, ha, b, rfl⟩ := hlead
  · simp
  · rw [nextCoeff_C_mul_X_add_C ha] at hnext
    subst b
    simp

Depends on / 依赖: Nat.le_one_iff_eq_zero_or_eq_one, Nat.lt_succ_iff, contrapose, le_one_iff_eq_zero_or_eq_one, lt_succ_iff, natDegree_eq_one, natDegree_eq_zero, nextCoeff_C_mul_X_add_C
-/
lemma two_le_natDegree_of_nextCoeff_eraseLead (hlead : f.eraseLead != 0)
    (hnext : f.nextCoeff = 0) : 2 <= f.natDegree := by
  contrapose! hlead
  rw [Nat.lt_succ_iff]; rw [Nat.le_one_iff_eq_zero_or_eq_one]; rw [natDegree_eq_zero]; rw [natDegree_eq_one]
    at hlead
  obtain ⟨a, rfl⟩ | ⟨a, ha, b, rfl⟩ := hlead
  · simp
  · rw [nextCoeff_C_mul_X_add_C ha] at hnext
    subst b
    simp

/--
theorem `leadingCoeff_eraseLead_eq_nextCoeff` / 定理 `leadingCoeff_eraseLead_eq_nextCoeff`

English:
theorem leadingCoeff_eraseLead_eq_nextCoeff
  given: (h : f.nextCoeff != 0)
  proof: by
  have := natDegree_pos_of_nextCoeff_ne_zero h
  rw [leadingCoeff]; rw [nextCoeff]; rw [natDegree_eraseLead h]; rw [if_neg]; rw [eraseLead_coeff_of_ne _ (tsub_lt_self _ _).ne]
  all_goals positivity

中文:
定理 leadingCoeff_eraseLead_eq_nextCoeff
  条件: (h : f.nextCoeff != 0)
  证明: by
  have := natDegree_pos_of_nextCoeff_ne_zero h
  rw [leadingCoeff]; rw [nextCoeff]; rw [natDegree_eraseLead h]; rw [if_neg]; rw [eraseLead_coeff_of_ne _ (tsub_lt_self _ _).ne]
  all_goals positivity

Depends on / 依赖: all_goals, eraseLead_coeff_of_ne, if_neg, leadingCoeff, natDegree_eraseLead, natDegree_pos_of_nextCoeff_ne_zero, nextCoeff, tsub_lt_self
-/
theorem leadingCoeff_eraseLead_eq_nextCoeff (h : f.nextCoeff != 0) :
    f.eraseLead.leadingCoeff = f.nextCoeff := by
  have := natDegree_pos_of_nextCoeff_ne_zero h
  rw [leadingCoeff]; rw [nextCoeff]; rw [natDegree_eraseLead h]; rw [if_neg]; rw [eraseLead_coeff_of_ne _ (tsub_lt_self _ _).ne]
  all_goals positivity

/--
theorem `nextCoeff_eq_zero_of_eraseLead_eq_zero` / 定理 `nextCoeff_eq_zero_of_eraseLead_eq_zero`

English:
theorem nextCoeff_eq_zero_of_eraseLead_eq_zero
  given: (h : f.eraseLead = 0)
  statement: f.nextCoeff = 0
  proof: by
  by_contra h₂
  exact leadingCoeff_ne_zero.mp (leadingCoeff_eraseLead_eq_nextCoeff h₂ ▸ h₂) h

中文:
定理 nextCoeff_eq_zero_of_eraseLead_eq_zero
  条件: (h : f.eraseLead = 0)
  结论: f.nextCoeff = 0
  证明: by
  by_contra h₂
  exact leadingCoeff_ne_zero.mp (leadingCoeff_eraseLead_eq_nextCoeff h₂ ▸ h₂) h

Depends on / 依赖: leadingCoeff_eraseLead_eq_nextCoeff, leadingCoeff_ne_zero, leadingCoeff_ne_zero.mp
-/
theorem nextCoeff_eq_zero_of_eraseLead_eq_zero (h : f.eraseLead = 0) : f.nextCoeff = 0 := by
  by_contra h₂
  exact leadingCoeff_ne_zero.mp (leadingCoeff_eraseLead_eq_nextCoeff h₂ ▸ h₂) h

/--
lemma `eraseLead_mul_eq_mul_eraseLead_of_nextCoeff_zero` / 引理 `eraseLead_mul_eq_mul_eraseLead_of_nextCoeff_zero`

English:
lemma eraseLead_mul_eq_mul_eraseLead_of_nextCoeff_zero
  statement: {R : Type*} [Ring R] [NoZeroDivisors R]
  proof: by
  -- if `P = 0` this is trivial
  by_cases hp : P = 0
  · simp [hp]
  -- can assume eraseLead P ≠ 0, otherwise it's a monomial and both sides are zero.
  by_cases he : P.eraseLead = 0
  · rw [he, mul_zero]
    by_cases he₂ : ((X - C x) * P).eraseLead = 0
    · simp [he₂]
    suffices #((X - C x) 

中文:
引理 eraseLead_mul_eq_mul_eraseLead_of_nextCoeff_zero
  结论: {R : 类型} [Ring R] [NoZeroDivisors R]
  证明: by
  -- if `P = 0` this is trivial
  by_cases hp : P = 0
  · simp [hp]
  -- can assume eraseLead P ≠ 0, otherwise it's a monomial and both sides are zero.
  by_cases he : P.eraseLead = 0
  · rw [he, mul_zero]
    by_cases he₂ : ((X - C x) * P).eraseLead = 0
    · simp [he₂]
    suffices #((X - C x) 
-/
lemma eraseLead_mul_eq_mul_eraseLead_of_nextCoeff_zero {R : Type*} [Ring R] [NoZeroDivisors R]
    [Nontrivial R] {x : R} {P : R[X]} (hx : x != 0) (h : P.nextCoeff = 0) :
    ((X - C x) * P).eraseLead.eraseLead = (X - C x) * P.eraseLead := by
  -- if `P = 0` this is trivial
  by_cases hp : P = 0
  · simp [hp]
  -- can assume eraseLead P ≠ 0, otherwise it's a monomial and both sides are zero.
  by_cases he : P.eraseLead = 0
  · rw [he, mul_zero]
    by_cases he₂ : ((X - C x) * P).eraseLead = 0
    · simp [he₂]
    suffices #((X - C x) * P).support <= 2 by
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
    rw [natDegree_mul (X_sub_C_ne_zero x) hp]; rw [natDegree_X_sub_C]; rw [add_comm]
  -- 2 ≤ P.natDegree
  obtain ⟨dP, hdP⟩ := Nat.exists_eq_add_of_le' (two_le_natDegree_of_nextCoeff_eraseLead he h)
  -- the subleading term of (X - C η) * P is nonzero
  have h₂ : ((X - C x) * P).nextCoeff != 0 := by
    simp only [nextCoeff, hdP, Nat.succ_ne_zero, ite_false, Nat.add_one_sub_one] at h
    rw [nextCoeff]; rw [h₁]; rw [add_tsub_cancel_right]; rw [hdP]; rw [coeff_X_sub_C_mul]
    simp [h, hx, ← hdP, hp]
  -- Prove equality by showing coefficients are equal
  ext n
  rcases n.lt_or_ge P.natDegree with hn | hn
  · --n < P.natDegree
    have hd₁ : n < ((X - C x) * P).eraseLead.natDegree := by
      linarith [natDegree_eraseLead_add_one h₂]
    rw [← self_sub_monomial_natDegree_leadingCoeff]; rw [coeff_sub]; rw [coeff_monomial]; rw [if_neg hd₁.ne']
    rw [← self_sub_monomial_natDegree_leadingCoeff]; rw [coeff_sub]; rw [coeff_monomial]; rw [if_neg (by lia)]
    rw [← self_sub_monomial_natDegree_leadingCoeff]; rw [mul_sub]; rw [coeff_sub]; rw [sub_zero]; rw [sub_zero]; rw [eq_sub_iff_add_eq]; rw [add_eq_left]
    rcases hn₂ : n
    · simpa [coeff_monomial, hp] using! fun _ => by lia
    · rw [coeff_X_sub_C_mul, coeff_monomial, coeff_monomial, if_neg (by lia),
        if_neg (by lia), mul_zero, sub_zero]
  · --n ≥ P.natDegree, so all the coefficients are zero.
    trans 0 <;> rw [coeff_eq_zero_of_natDegree_lt]
    · grw [eraseLead_natDegree_le, eraseLead_natDegree_le]
      simpa [h₁, hdP] using! hn
    · grw [natDegree_mul (X_sub_C_ne_zero x) he, natDegree_eraseLead_le_of_nextCoeff_eq_zero h]
      simpa [add_comm, hdP] using! hn

end EraseLead

/--
theorem `induction_with_natDegree_le` / 定理 `induction_with_natDegree_le`

English:
theorem induction_with_natDegree_le
  statement: (motive : R[X] -> Prop) (N : Nat) (zero : motive 0)
  proof: by
  induction hf : #f.support generalizing f with
  | zero =>
    convert! zero
    simpa [support_eq_empty, card_eq_zero] using hf
  | succ c hc =>
    rw [← eraseLead_add_C_mul_X_pow f]
    cases c
    · convert C_mul_pow f.natDegree f.leadingCoeff ?_ df
      · convert! zero_add (C (leadingCoeff

中文:
定理 induction_with_natDegree_le
  结论: (motive : R[X] -> 命题) (N : 自然数) (zero : motive 0)
  证明: by
  induction hf : #f.support generalizing f with
  | zero =>
    convert! zero
    simpa [support_eq_empty, card_eq_zero] using hf
  | succ c hc =>
    rw [← eraseLead_add_C_mul_X_pow f]
    cases c
    · convert C_mul_pow f.natDegree f.leadingCoeff ?_ df
      · convert! zero_add (C (leadingCoeff

Depends on / 依赖: C_mul_pow, card_eq_zero, card_support_eq_zero, card_support_eraseLead, convert, eraseLead, eraseLead_add_C_mul_X_pow, eraseLead_natDegre, f.eraseLead, f.leadingCoeff, f.natDegree, f.support, generalizing, leadingCoeff, leadingCoeff_ne_zero, natDegree, support, support_eq_empty, zero_add, zero_ne_one
-/
theorem induction_with_natDegree_le (motive : R[X] -> Prop) (N : Nat) (zero : motive 0)
    (C_mul_pow : forall n : Nat, forall r : R, r != 0 -> n <= N -> motive (C r * X ^ n))
    (add : forall f g : R[X], f.natDegree < g.natDegree -> g.natDegree <= N ->
      motive f -> motive g -> motive (f + g)) (f : R[X]) (df : f.natDegree <= N) : motive f := by
  induction hf : #f.support generalizing f with
  | zero =>
    convert! zero
    simpa [support_eq_empty, card_eq_zero] using hf
  | succ c hc =>
    rw [← eraseLead_add_C_mul_X_pow f]
    cases c
    · convert C_mul_pow f.natDegree f.leadingCoeff ?_ df
      · convert! zero_add (C (leadingCoeff f) * X ^ f.natDegree)
        rw [← card_support_eq_zero]; rw [card_support_eraseLead' hf]
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
      rw [Ne]; rw [leadingCoeff_eq_zero]; rw [← card_support_eq_zero]; rw [hf]
      exact Nat.succ_ne_zero _

/--
theorem `mono_map_natDegree_eq` / 定理 `mono_map_natDegree_eq`

English:
theorem mono_map_natDegree_eq
  statement: {S F : Type*} [Semiring S]
  proof: by
  refine induction_with_natDegree_le (fun p => (φ p).natDegree = fu p.natDegree)
    p.natDegree (by simp [fu0]) ?_ ?_ _ rfl.le
  · intro n r r0 _
    rw [natDegree_C_mul_X_pow _ _ r0]; rw [C_mul_X_pow_eq_monomial]; rw [φ_mon_nat _ _ r0]
  · intro f g fg _ fk gk
    rw [natDegree_add_eq_right_of_

中文:
定理 mono_map_natDegree_eq
  结论: {S F : 类型} [Semiring S]
  证明: by
  refine induction_with_natDegree_le (fun p => (φ p).natDegree = fu p.natDegree)
    p.natDegree (by simp [fu0]) ?_ ?_ _ rfl.le
  · intro n r r0 _
    rw [natDegree_C_mul_X_pow _ _ r0]; rw [C_mul_X_pow_eq_monomial]; rw [φ_mon_nat _ _ r0]
  · intro f g fg _ fk gk
    rw [natDegree_add_eq_right_of_

Depends on / 依赖: C_mul_X_pow_eq_monomial, f.natDegree, induction_with_natDegree_le, map_add, natDegree, natDegree_C_mul_X_pow, natDegree_add_eq_right_of_natDegree_lt, nomatch, p.natDegree, rfl.le, zero_add
-/
theorem mono_map_natDegree_eq {S F : Type*} [Semiring S]
    [FunLike F R[X] S[X]] [AddMonoidHomClass F R[X] S[X]] {φ : F}
    {p : R[X]} (k : Nat) (fu : Nat -> Nat) (fu0 : forall {n}, n <= k -> fu n = 0)
    (fc : forall {n m}, k <= n -> n < m -> fu n < fu m) (φ_k : forall {f : R[X]}, f.natDegree < k -> φ f = 0)
    (φ_mon_nat : forall n c, c != 0 -> (φ (monomial n c)).natDegree = fu n) :
    (φ p).natDegree = fu p.natDegree := by
  refine induction_with_natDegree_le (fun p => (φ p).natDegree = fu p.natDegree)
    p.natDegree (by simp [fu0]) ?_ ?_ _ rfl.le
  · intro n r r0 _
    rw [natDegree_C_mul_X_pow _ _ r0]; rw [C_mul_X_pow_eq_monomial]; rw [φ_mon_nat _ _ r0]
  · intro f g fg _ fk gk
    rw [natDegree_add_eq_right_of_natDegree_lt fg]; rw [map_add]
    by_cases! FG : k <= f.natDegree
    · rw [natDegree_add_eq_right_of_natDegree_lt, gk]
      rw [fk]; rw [gk]
      exact fc FG fg
    · cases k
      · nomatch FG
      · rwa [φ_k FG, zero_add]

/--
theorem `map_natDegree_eq_sub` / 定理 `map_natDegree_eq_sub`

English:
theorem map_natDegree_eq_sub
  statement: {S F : Type*} [Semiring S]
  proof: mono_map_natDegree_eq k (fun j => j - k) (by simp_all)
    (@fun _ _ h => (tsub_lt_tsub_iff_right h).mpr)
    (φ_k _) φ_mon

中文:
定理 map_natDegree_eq_sub
  结论: {S F : 类型} [Semiring S]
  证明: mono_map_natDegree_eq k (fun j => j - k) (by simp_all)
    (@fun _ _ h => (tsub_lt_tsub_iff_right h).mpr)
    (φ_k _) φ_mon

Depends on / 依赖: mono_map_natDegree_eq, tsub_lt_tsub_iff_right
-/
theorem map_natDegree_eq_sub {S F : Type*} [Semiring S]
    [FunLike F R[X] S[X]] [AddMonoidHomClass F R[X] S[X]] {φ : F}
    {p : R[X]} {k : Nat} (φ_k : forall f : R[X], f.natDegree < k -> φ f = 0)
    (φ_mon : forall n c, c != 0 -> (φ (monomial n c)).natDegree = n - k) :
    (φ p).natDegree = p.natDegree - k :=
  mono_map_natDegree_eq k (fun j => j - k) (by simp_all)
    (@fun _ _ h => (tsub_lt_tsub_iff_right h).mpr)
    (φ_k _) φ_mon

/--
theorem `map_natDegree_eq_natDegree` / 定理 `map_natDegree_eq_natDegree`

English:
theorem map_natDegree_eq_natDegree
  statement: {S F : Type*} [Semiring S]
  proof: (map_natDegree_eq_sub (fun _ h => (Nat.not_lt_zero _ h).elim) (by simpa)).trans
    p.natDegree.sub_zero

中文:
定理 map_natDegree_eq_natDegree
  结论: {S F : 类型} [Semiring S]
  证明: (map_natDegree_eq_sub (fun _ h => (Nat.not_lt_zero _ h).elim) (by simpa)).trans
    p.natDegree.sub_zero

Depends on / 依赖: Nat.not_lt_zero, map_natDegree_eq_sub, natDegree, not_lt_zero, p.natDegree.sub_zero, sub_zero
-/
theorem map_natDegree_eq_natDegree {S F : Type*} [Semiring S]
    [FunLike F R[X] S[X]] [AddMonoidHomClass F R[X] S[X]]
    {φ : F} (p) (φ_mon_nat : forall n c, c != 0 -> (φ (monomial n c)).natDegree = n) :
    (φ p).natDegree = p.natDegree :=
  (map_natDegree_eq_sub (fun _ h => (Nat.not_lt_zero _ h).elim) (by simpa)).trans
    p.natDegree.sub_zero

/--
theorem `card_support_eq'` / 定理 `card_support_eq'`

English:
theorem card_support_eq'
  statement: {n : Nat} (k : Fin n -> Nat) (x : Fin n -> R) (hk : Function.Injective k)
  proof: by
  suffices (∑ i, C (x i) * X ^ k i).support = image k univ by
    rw [this]; rw [univ.card_image_of_injective hk]; rw [card_fin]
  simp_rw [Finset.ext_iff, mem_support_iff, finsetSum_coeff, coeff_C_mul_X_pow, mem_image,
    mem_univ, true_and]
  refine fun i => ⟨fun h => ?_, ?_⟩
  · obtain ⟨j, _,

中文:
定理 card_support_eq'
  结论: {n : 自然数} (k : Fin n -> 自然数) (x : Fin n -> R) (hk : Function.Injective k)
  证明: by
  suffices (∑ i, C (x i) * X ^ k i).support = image k univ by
    rw [this]; rw [univ.card_image_of_injective hk]; rw [card_fin]
  simp_rw [Finset.ext_iff, mem_support_iff, finsetSum_coeff, coeff_C_mul_X_pow, mem_image,
    mem_univ, true_and]
  refine fun i => ⟨fun h => ?_, ?_⟩
  · obtain ⟨j, _,

Depends on / 依赖: Finset, Finset.ext_iff, card_fin, card_image_of_injective, coeff_C_mul_X_pow, exists_ne_zero_of_sum_ne_zero, ext_iff, finsetSum_coeff, if_neg, if_pos, ite_ne_right_iff, ite_ne_right_iff.mp, mem_image, mem_support_iff, mem_univ, simp_rw, sum_eq_single_of_mem, support, true_and, univ.card_image_of_injective
-/
theorem card_support_eq' {n : Nat} (k : Fin n -> Nat) (x : Fin n -> R) (hk : Function.Injective k)
    (hx : forall i, x i != 0) : #(∑ i, C (x i) * X ^ k i).support = n := by
  suffices (∑ i, C (x i) * X ^ k i).support = image k univ by
    rw [this]; rw [univ.card_image_of_injective hk]; rw [card_fin]
  simp_rw [Finset.ext_iff, mem_support_iff, finsetSum_coeff, coeff_C_mul_X_pow, mem_image,
    mem_univ, true_and]
  refine fun i => ⟨fun h => ?_, ?_⟩
  · obtain ⟨j, _, h⟩ := exists_ne_zero_of_sum_ne_zero h
    exact ⟨j, (ite_ne_right_iff.mp h).1.symm⟩
  · rintro ⟨j, _, rfl⟩
    rw [sum_eq_single_of_mem j (mem_univ j)]; rw [if_pos rfl]
    · exact hx j
    · exact fun m _ hmj => if_neg fun h => hmj.symm (hk h)

/--
theorem `card_support_eq` / 定理 `card_support_eq`

English:
theorem card_support_eq
  given: {n : Nat}
  proof: by
  refine ⟨?_, fun ⟨k, x, hk, hx, hf⟩ => hf.symm ▸ card_support_eq' k x hk.injective hx⟩
  induction n generalizing f with
  | zero => exact fun hf => ⟨0, 0, fun x => x.elim0, fun x => x.elim0, card_support_eq_zero.mp hf⟩
  | succ n hn =>
    intro h
    obtain ⟨k, x, hk, hx, hf⟩ := hn (card_suppo

中文:
定理 card_support_eq
  条件: {n : 自然数}
  证明: by
  refine ⟨?_, fun ⟨k, x, hk, hx, hf⟩ => hf.symm ▸ card_support_eq' k x hk.injective hx⟩
  induction n generalizing f with
  | zero => exact fun hf => ⟨0, 0, fun x => x.elim0, fun x => x.elim0, card_support_eq_zero.mp hf⟩
  | succ n hn =>
    intro h
    obtain ⟨k, x, hk, hx, hf⟩ := hn (card_suppo

Depends on / 依赖: Fin.castSucc, Fin.last, Function, Function.extend, card_support_eq, card_support_eq_zero, card_support_eq_zero.mp, card_support_eraseLead, castSucc, castSucc_lt_last, extend, f.natDegree, generalizing, hf.symm, hk.injective, i.castSucc_lt_last.ne, injective, natDegree, x.elim0
-/
theorem card_support_eq {n : Nat} :
    #f.support = n ↔
      exists (k : Fin n -> Nat) (x : Fin n -> R) (_ : StrictMono k) (_ : forall i, x i != 0),
        f = ∑ i, C (x i) * X ^ k i := by
  refine ⟨?_, fun ⟨k, x, hk, hx, hf⟩ => hf.symm ▸ card_support_eq' k x hk.injective hx⟩
  induction n generalizing f with
  | zero => exact fun hf => ⟨0, 0, fun x => x.elim0, fun x => x.elim0, card_support_eq_zero.mp hf⟩
  | succ n hn =>
    intro h
    obtain ⟨k, x, hk, hx, hf⟩ := hn (card_support_eraseLead' h)
    have H : ¬exists k : Fin n, Fin.castSucc k = Fin.last n := by
      rintro ⟨i, hi⟩
      exact i.castSucc_lt_last.ne hi
    refine
      ⟨Function.extend Fin.castSucc k fun _ => f.natDegree,
        Function.extend Fin.castSucc x fun _ => f.leadingCoeff, ?_, ?_, ?_⟩
    · intro i j hij
      have hi : i in Set.range (Fin.castSucc : Fin n -> Fin (n + 1)) := by
        simp only [Fin.range_castSucc, Nat.succ_eq_add_one, Set.mem_ofPred_eq]
        exact lt_of_lt_of_le hij (Nat.lt_succ_iff.mp j.2)
      obtain ⟨i, rfl⟩ := hi
      rw [Fin.strictMono_castSucc.injective.extend_apply]
      by_cases hj : exists j₀, Fin.castSucc j₀ = j
      · obtain ⟨j, rfl⟩ := hj
        rwa [Fin.strictMono_castSucc.injective.extend_apply, hk.lt_iff_lt,
          ← Fin.castSucc_lt_castSucc_iff]
      · rw [Function.extend_apply' _ _ _ hj]
        apply lt_natDegree_of_mem_eraseLead_support
        rw [mem_support_iff]; rw [hf]; rw [finsetSum_coeff]
        rw [sum_eq_single]; rw [coeff_C_mul]; rw [coeff_X_pow_self]; rw [mul_one]
        · exact hx i
        · intro j _ hji
          rw [coeff_C_mul]; rw [coeff_X_pow]; rw [if_neg (hk.injective.ne hji.symm)]; rw [mul_zero]
        · exact fun hi => (hi (mem_univ i)).elim
    · intro i
      by_cases hi : exists i₀, Fin.castSucc i₀ = i
      · obtain ⟨i, rfl⟩ := hi
        rw [Fin.strictMono_castSucc.injective.extend_apply]
        exact hx i
      · rw [Function.extend_apply' _ _ _ hi, Ne, leadingCoeff_eq_zero, ← card_support_eq_zero, h]
        exact n.succ_ne_zero
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.strictMono_castSucc.injective.extend_apply]
      rw [← hf]; rw [Function.extend_apply']; rw [Function.extend_apply']; rw [eraseLead_add_C_mul_X_pow]
      all_goals exact H

/--
theorem `card_support_eq_one` / 定理 `card_support_eq_one`

English:
theorem card_support_eq_one
  statement: #f.support = 1 ↔
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨k, x, _, hx, rfl⟩ := card_support_eq.mp h
    exact ⟨k 0, x 0, hx 0, Fin.sum_univ_one _⟩
  · rintro ⟨k, x, hx, rfl⟩
    rw [support_C_mul_X_pow k hx]; rw [card_singleton]

中文:
定理 card_support_eq_one
  结论: #f.support = 1 ↔
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨k, x, _, hx, rfl⟩ := card_support_eq.mp h
    exact ⟨k 0, x 0, hx 0, Fin.sum_univ_one _⟩
  · rintro ⟨k, x, hx, rfl⟩
    rw [support_C_mul_X_pow k hx]; rw [card_singleton]

Depends on / 依赖: Fin.sum_univ_one, card_singleton, card_support_eq, card_support_eq.mp, sum_univ_one, support_C_mul_X_pow
-/
theorem card_support_eq_one : #f.support = 1 ↔
    exists (k : Nat) (x : R) (_ : x != 0), f = C x * X ^ k := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨k, x, _, hx, rfl⟩ := card_support_eq.mp h
    exact ⟨k 0, x 0, hx 0, Fin.sum_univ_one _⟩
  · rintro ⟨k, x, hx, rfl⟩
    rw [support_C_mul_X_pow k hx]; rw [card_singleton]

/--
theorem `card_support_eq_two` / 定理 `card_support_eq_two`

English:
theorem card_support_eq_two
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨k, x, hk, hx, rfl⟩ := card_support_eq.mp h
    refine ⟨k 0, k 1, hk Nat.zero_lt_one, x 0, x 1, hx 0, hx 1, ?_⟩
    rw [Fin.sum_univ_castSucc]; rw [Fin.sum_univ_one]
    rfl
  · rintro ⟨k, m, hkm, x, y, hx, hy, rfl⟩
    exact card_support_binomial hkm.ne hx h

中文:
定理 card_support_eq_two
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨k, x, hk, hx, rfl⟩ := card_support_eq.mp h
    refine ⟨k 0, k 1, hk Nat.zero_lt_one, x 0, x 1, hx 0, hx 1, ?_⟩
    rw [Fin.sum_univ_castSucc]; rw [Fin.sum_univ_one]
    rfl
  · rintro ⟨k, m, hkm, x, y, hx, hy, rfl⟩
    exact card_support_binomial hkm.ne hx h

Depends on / 依赖: Fin.sum_univ_castSucc, Fin.sum_univ_one, Nat.zero_lt_one, card_support_binomial, card_support_eq, card_support_eq.mp, hkm.ne, sum_univ_castSucc, sum_univ_one, zero_lt_one
-/
theorem card_support_eq_two :
    #f.support = 2 ↔
      exists (k m : Nat) (_ : k < m) (x y : R) (_ : x != 0) (_ : y != 0),
        f = C x * X ^ k + C y * X ^ m := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨k, x, hk, hx, rfl⟩ := card_support_eq.mp h
    refine ⟨k 0, k 1, hk Nat.zero_lt_one, x 0, x 1, hx 0, hx 1, ?_⟩
    rw [Fin.sum_univ_castSucc]; rw [Fin.sum_univ_one]
    rfl
  · rintro ⟨k, m, hkm, x, y, hx, hy, rfl⟩
    exact card_support_binomial hkm.ne hx hy

/--
theorem `card_support_eq_three` / 定理 `card_support_eq_three`

English:
theorem card_support_eq_three
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨k, x, hk, hx, rfl⟩ := card_support_eq.mp h
    refine
      ⟨k 0, k 1, k 2, hk Nat.zero_lt_one, hk (Nat.lt_succ_self 1), x 0, x 1, x 2, hx 0, hx 1, hx 2,
        ?_⟩
    rw [Fin.sum_univ_castSucc]; rw [Fin.sum_univ_castSucc]; rw [Fin.sum_univ_one]
    rfl
  

中文:
定理 card_support_eq_three
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨k, x, hk, hx, rfl⟩ := card_support_eq.mp h
    refine
      ⟨k 0, k 1, k 2, hk Nat.zero_lt_one, hk (Nat.lt_succ_self 1), x 0, x 1, x 2, hx 0, hx 1, hx 2,
        ?_⟩
    rw [Fin.sum_univ_castSucc]; rw [Fin.sum_univ_castSucc]; rw [Fin.sum_univ_one]
    rfl
  

Depends on / 依赖: Fin.sum_univ_castSucc, Fin.sum_univ_one, Nat.lt_succ_self, Nat.zero_lt_one, card_support_eq, card_support_eq.mp, card_support_trinomial, lt_succ_self, sum_univ_castSucc, sum_univ_one, zero_lt_one
-/
theorem card_support_eq_three :
    #f.support = 3 ↔
      exists (k m n : Nat) (_ : k < m) (_ : m < n) (x y z : R) (_ : x != 0) (_ : y != 0) (_ : z != 0),
        f = C x * X ^ k + C y * X ^ m + C z * X ^ n := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨k, x, hk, hx, rfl⟩ := card_support_eq.mp h
    refine
      ⟨k 0, k 1, k 2, hk Nat.zero_lt_one, hk (Nat.lt_succ_self 1), x 0, x 1, x 2, hx 0, hx 1, hx 2,
        ?_⟩
    rw [Fin.sum_univ_castSucc]; rw [Fin.sum_univ_castSucc]; rw [Fin.sum_univ_one]
    rfl
  · rintro ⟨k, m, n, hkm, hmn, x, y, z, hx, hy, hz, rfl⟩
    exact card_support_trinomial hkm hmn hx hy hz

end Polynomial
