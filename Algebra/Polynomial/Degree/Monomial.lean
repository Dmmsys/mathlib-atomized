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

variable {R : Type u} {S : Type v} {a b c d : R} {n m : Nat}

section Semiring

variable [Semiring R] {p q : R[X]} {ι : Type*}

/--
lemma `natDegree_le_pred` / 引理 `natDegree_le_pred`

English:
lemma natDegree_le_pred
  given: (hf : p.natDegree <= n) (hn : p.coeff n = 0)
  statement: p.natDegree <= n - 1
  proof: by
  obtain _ | n := n
  · exact hf
  · refine (Nat.le_succ_iff_eq_or_le.1 hf).resolve_left fun h => ?_
    rw [← Nat.succ_eq_add_one]; rw [← h]; rw [coeff_natDegree]; rw [leadingCoeff_eq_zero] at hn
    simp_all

中文:
引理 natDegree_le_pred
  条件: (hf : p.natDegree <= n) (hn : p.coeff n = 0)
  结论: p.natDegree <= n - 1
  证明: by
  obtain _ | n := n
  · exact hf
  · refine (Nat.le_succ_iff_eq_or_le.1 hf).resolve_left fun h => ?_
    rw [← Nat.succ_eq_add_one]; rw [← h]; rw [coeff_natDegree]; rw [leadingCoeff_eq_zero] at hn
    simp_all

Depends on / 依赖: Nat.le_succ_iff_eq_or_le, Nat.succ_eq_add_one, coeff_natDegree, le_succ_iff_eq_or_le, leadingCoeff_eq_zero, resolve_left, succ_eq_add_one
-/
lemma natDegree_le_pred (hf : p.natDegree <= n) (hn : p.coeff n = 0) : p.natDegree <= n - 1 := by
  obtain _ | n := n
  · exact hf
  · refine (Nat.le_succ_iff_eq_or_le.1 hf).resolve_left fun h => ?_
    rw [← Nat.succ_eq_add_one]; rw [← h]; rw [coeff_natDegree]; rw [leadingCoeff_eq_zero] at hn
    simp_all

/--
theorem `monomial_natDegree_leadingCoeff_eq_self` / 定理 `monomial_natDegree_leadingCoeff_eq_self`

English:
theorem monomial_natDegree_leadingCoeff_eq_self
  given: (h : #p.support <= 1)
  proof: by
  classical
  rcases card_support_le_one_iff_monomial.1 h with ⟨n, a, rfl⟩
  by_cases ha : a = 0 <;> simp [ha]

中文:
定理 monomial_natDegree_leadingCoeff_eq_self
  条件: (h : #p.support <= 1)
  证明: by
  classical
  rcases card_support_le_one_iff_monomial.1 h with ⟨n, a, rfl⟩
  by_cases ha : a = 0 <;> simp [ha]

Depends on / 依赖: card_support_le_one_iff_monomial, classical
-/
theorem monomial_natDegree_leadingCoeff_eq_self (h : #p.support <= 1) :
    monomial p.natDegree p.leadingCoeff = p := by
  classical
  rcases card_support_le_one_iff_monomial.1 h with ⟨n, a, rfl⟩
  by_cases ha : a = 0 <;> simp [ha]

/--
theorem `C_mul_X_pow_eq_self` / 定理 `C_mul_X_pow_eq_self`

English:
theorem C_mul_X_pow_eq_self
  given: (h : #p.support <= 1)
  statement: C p.leadingCoeff * X ^ p.natDegree = p
  proof: by
  rw [C_mul_X_pow_eq_monomial]; rw [monomial_natDegree_leadingCoeff_eq_self h]

中文:
定理 C_mul_X_pow_eq_self
  条件: (h : #p.support <= 1)
  结论: C p.leadingCoeff * X ^ p.natDegree = p
  证明: by
  rw [C_mul_X_pow_eq_monomial]; rw [monomial_natDegree_leadingCoeff_eq_self h]

Depends on / 依赖: C_mul_X_pow_eq_monomial, monomial_natDegree_leadingCoeff_eq_self
-/
theorem C_mul_X_pow_eq_self (h : #p.support <= 1) : C p.leadingCoeff * X ^ p.natDegree = p := by
  rw [C_mul_X_pow_eq_monomial]; rw [monomial_natDegree_leadingCoeff_eq_self h]

end Semiring

end Polynomial
