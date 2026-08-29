/-
Copyright (c) 2026 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Formulas for coefficients of multivariate polynomials

## Main Results

* `MvPolynomial.coeff_add_pow`: the formula for the `d`th coefficient of `(X 0 + X 1) ^ n`.

-/

public section

noncomputable section

namespace MvPolynomial

open Finsupp

variable {R σ : Type*} [CommSemiring R] {s : σ ->₀ Nat}

/--
lemma `coeff_linearCombination_X_pow_of_eq` / 引理 `coeff_linearCombination_X_pow_of_eq`

English:
lemma coeff_linearCombination_X_pow_of_eq
  statement: (a : σ ->₀ R) {n : Nat}
  proof: by
  classical
  simp only [sum, linearCombination_apply, Finset.sum_pow_eq_sum_piAntidiag, coeff_sum,
    ← C_eq_coe_nat, coeff_C_mul, smul_eq_C_mul, mul_pow, Finset.prod_mul_distrib, ← map_pow,
    ← map_prod, coeff_prod_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (s : σ -> Nat)]

中文:
引理 coeff_linearCombination_X_pow_of_eq
  结论: (a : σ ->₀ R) {n : 自然数}
  证明: by
  classical
  simp only [sum, linearCombination_apply, Finset.sum_pow_eq_sum_piAntidiag, coeff_sum,
    ← C_eq_coe_nat, coeff_C_mul, smul_eq_C_mul, mul_pow, Finset.prod_mul_distrib, ← map_pow,
    ← map_prod, coeff_prod_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (s : σ -> Nat)]
-/
private lemma coeff_linearCombination_X_pow_of_eq (a : σ ->₀ R) {n : Nat}
    (hs : s.sum (fun _ m => m) = n) :
    coeff s (((a.linearCombination R X : MvPolynomial σ R)) ^ n) =
      s.multinomial * s.prod (fun r m => a r ^ m) := by
  classical
  simp only [sum, linearCombination_apply, Finset.sum_pow_eq_sum_piAntidiag, coeff_sum,
    ← C_eq_coe_nat, coeff_C_mul, smul_eq_C_mul, mul_pow, Finset.prod_mul_distrib, ← map_pow,
    ← map_prod, coeff_prod_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (s : σ -> Nat)]
  · simp_rw [eq_indicator_self_iff]
    split_ifs with hs'
    · rw [prod_of_support_subset _ hs' _ (by simp), Finsupp.multinomial_of_support_subset hs']
    · rw [Finset.subset_iff] at hs'
      simp only [Finsupp.mem_support_iff, ne_eq, not_forall, Decidable.not_not] at hs'
      obtain ⟨i, hsi, hai⟩ := hs'
      rw [← mul_prod_erase _ i _ (by simpa)]; rw [hai]; rw [zero_pow hsi]; rw [zero_mul]; rw [mul_zero]
  · simp only [Finset.mem_piAntidiag, ne_eq, Finsupp.mem_support_iff, ite_eq_right_iff, and_imp]
    intro _ _ _ _ hed
    simp [Finsupp.ext_iff] at hed
    grind
  · simp_rw [ite_eq_right_iff]
    intro hs' hs''
    rw [eq_indicator_self_iff] at hs''
    exfalso
    rw [Finset.mem_piAntidiag]; rw [not_and_or] at hs'
    rcases hs' with hs' | hs'
    · apply hs'
      rw [← hs]; rw [sum_of_support_subset _ hs'' _ (by simp)]
    · grind

/--
lemma `coeff_linearCombination_X_pow_of_ne` / 引理 `coeff_linearCombination_X_pow_of_ne`

English:
lemma coeff_linearCombination_X_pow_of_ne
  statement: (a : σ ->₀ R) {n : Nat}
  proof: by
  classical
  simp only [sum, linearCombination_apply, Finset.sum_pow_eq_sum_piAntidiag, coeff_sum, ← map_pow,
    ← C_eq_coe_nat, coeff_C_mul, smul_eq_C_mul, mul_pow, Finset.prod_mul_distrib, ← map_prod,
    coeff_prod_X_pow, mul_ite, mul_one, mul_zero]
  apply Finset.sum_eq_zero (fun x hx => ?_

中文:
引理 coeff_linearCombination_X_pow_of_ne
  结论: (a : σ ->₀ R) {n : 自然数}
  证明: by
  classical
  simp only [sum, linearCombination_apply, Finset.sum_pow_eq_sum_piAntidiag, coeff_sum, ← map_pow,
    ← C_eq_coe_nat, coeff_C_mul, smul_eq_C_mul, mul_pow, Finset.prod_mul_distrib, ← map_prod,
    coeff_prod_X_pow, mul_ite, mul_one, mul_zero]
  apply Finset.sum_eq_zero (fun x hx => ?_
-/
private lemma coeff_linearCombination_X_pow_of_ne (a : σ ->₀ R) {n : Nat}
    (hs : s.sum (fun _ m => m) != n) :
    coeff s (((a.linearCombination R X : MvPolynomial σ R)) ^ n) = 0 := by
  classical
  simp only [sum, linearCombination_apply, Finset.sum_pow_eq_sum_piAntidiag, coeff_sum, ← map_pow,
    ← C_eq_coe_nat, coeff_C_mul, smul_eq_C_mul, mul_pow, Finset.prod_mul_distrib, ← map_prod,
    coeff_prod_X_pow, mul_ite, mul_one, mul_zero]
  apply Finset.sum_eq_zero (fun x hx => ?_)
  rw [if_neg]
  rintro ⟨rfl⟩
  apply hs
  simp only [Finset.mem_piAntidiag] at hx
  rw [sum_of_support_subset _ (support_indicator_subset a.support _) _ (by simp)]; rw [← hx.1]
  congr
  ext i
  by_cases hi : i in a.support
  · simp [Finsupp.indicator_of_mem hi]
  · grind [Finsupp.indicator_of_notMem hi]

/--
lemma `coeff_linearCombination_X_pow` / 引理 `coeff_linearCombination_X_pow`

English:
lemma coeff_linearCombination_X_pow
  given: (a : σ ->₀ R) (s : σ ->₀ Nat) (n : Nat)
  proof: by
  split_ifs with hs
  · exact coeff_linearCombination_X_pow_of_eq a hs
  · exact coeff_linearCombination_X_pow_of_ne a hs

中文:
引理 coeff_linearCombination_X_pow
  条件: (a : σ ->₀ R) (s : σ ->₀ 自然数) (n : 自然数)
  证明: by
  split_ifs with hs
  · exact coeff_linearCombination_X_pow_of_eq a hs
  · exact coeff_linearCombination_X_pow_of_ne a hs

Depends on / 依赖: coeff_linearCombination_X_pow_of_eq, coeff_linearCombination_X_pow_of_ne, split_ifs
-/
lemma coeff_linearCombination_X_pow (a : σ ->₀ R) (s : σ ->₀ Nat) (n : Nat) :
    coeff s (((a.linearCombination R X : MvPolynomial σ R)) ^ n) =
      if s.sum (fun _ m => m) = n then s.multinomial * s.prod (fun r m => a r ^ m) else 0 := by
  split_ifs with hs
  · exact coeff_linearCombination_X_pow_of_eq a hs
  · exact coeff_linearCombination_X_pow_of_ne a hs

/--
lemma `coeff_linearCombination_X_pow_of_fintype` / 引理 `coeff_linearCombination_X_pow_of_fintype`

English:
lemma coeff_linearCombination_X_pow_of_fintype
  given: [Fintype σ] (a : σ -> R) (s : σ ->₀ Nat) (n : Nat)
  proof: by
  rw [← ofSupportFinite_coe (f := a) (hf := Set.toFinite _)]; rw [prod_congr (fun r _ => rfl)]; rw [← coeff_linearCombination_X_pow]
  simp [linearCombination_apply, sum_of_support_subset (s := Finset.univ)]

中文:
引理 coeff_linearCombination_X_pow_of_fintype
  条件: [Fintype σ] (a : σ -> R) (s : σ ->₀ 自然数) (n : 自然数)
  证明: by
  rw [← ofSupportFinite_coe (f := a) (hf := Set.toFinite _)]; rw [prod_congr (fun r _ => rfl)]; rw [← coeff_linearCombination_X_pow]
  simp [linearCombination_apply, sum_of_support_subset (s := Finset.univ)]

Depends on / 依赖: Finset, Finset.univ, Set.toFinite, coeff_linearCombination_X_pow, linearCombination_apply, ofSupportFinite_coe, prod_congr, sum_of_support_subset, toFinite
-/
lemma coeff_linearCombination_X_pow_of_fintype [Fintype σ] (a : σ -> R) (s : σ ->₀ Nat) (n : Nat) :
    coeff s (((∑ i, a i • X i : MvPolynomial σ R)) ^ n) =
      if s.sum (fun _ m => m) = n then s.multinomial * s.prod (fun r m => a r ^ m) else 0 := by
  rw [← ofSupportFinite_coe (f := a) (hf := Set.toFinite _)]; rw [prod_congr (fun r _ => rfl)]; rw [← coeff_linearCombination_X_pow]
  simp [linearCombination_apply, sum_of_support_subset (s := Finset.univ)]

/--
lemma `coeff_sum_X_pow_of_fintype` / 引理 `coeff_sum_X_pow_of_fintype`

English:
lemma coeff_sum_X_pow_of_fintype
  given: [Fintype σ] (d : σ ->₀ Nat) (n : Nat)
  proof: by
  have : (∑ i, X i : MvPolynomial σ R) = ∑ i, (1 : σ -> R) i • X i := by simp
  simp [this, coeff_linearCombination_X_pow_of_fintype]

中文:
引理 coeff_sum_X_pow_of_fintype
  条件: [Fintype σ] (d : σ ->₀ 自然数) (n : 自然数)
  证明: by
  have : (∑ i, X i : MvPolynomial σ R) = ∑ i, (1 : σ -> R) i • X i := by simp
  simp [this, coeff_linearCombination_X_pow_of_fintype]

Depends on / 依赖: MvPolynomial, coeff_linearCombination_X_pow_of_fintype
-/
lemma coeff_sum_X_pow_of_fintype [Fintype σ] (d : σ ->₀ Nat) (n : Nat) :
    coeff d (((∑ i, X i : MvPolynomial σ R)) ^ n) =
      if d.sum (fun _ m => m) = n then d.multinomial else 0 := by
  have : (∑ i, X i : MvPolynomial σ R) = ∑ i, (1 : σ -> R) i • X i := by simp
  simp [this, coeff_linearCombination_X_pow_of_fintype]

/--
theorem `coeff_add_pow` / 定理 `coeff_add_pow`

English:
theorem coeff_add_pow
  given: (d : Fin 2 ->₀ Nat) (n : Nat)
  proof: by
  rw [← Fin.sum_univ_two]; rw [coeff_sum_X_pow_of_fintype]
  congr 1
  have : d.sum (fun x m => m) = d 0 + d 1 := by
    simp [Finsupp.sum_of_support_subset d (Finset.subset_univ d.support)]
  simp only [Finset.mem_antidiagonal, this]
  split_ifs with hd
  · rw [multinomial_eq_of_support_subset (

中文:
定理 coeff_add_pow
  条件: (d : Fin 2 ->₀ 自然数) (n : 自然数)
  证明: by
  rw [← Fin.sum_univ_two]; rw [coeff_sum_X_pow_of_fintype]
  congr 1
  have : d.sum (fun x m => m) = d 0 + d 1 := by
    simp [Finsupp.sum_of_support_subset d (Finset.subset_univ d.support)]
  simp only [Finset.mem_antidiagonal, this]
  split_ifs with hd
  · rw [multinomial_eq_of_support_subset (

Depends on / 依赖: Fin.sum_univ_two, Fin.zero_ne_one, Finset, Finset.mem_antidiagonal, Finset.subset_univ, Finset.univ_fin2, Finsupp, Finsupp.sum_of_support_subset, Nat.binomial_eq_choose, binomial_eq_choose, coeff_sum_X_pow_of_fintype, d.sum, d.support, mem_antidiagonal, multinomial_eq_of_support_subset, split_ifs, subset_univ, sum_of_support_subset, sum_univ_two, support
-/
theorem coeff_add_pow (d : Fin 2 ->₀ Nat) (n : Nat) :
    coeff d ((X 0 + X 1 : MvPolynomial (Fin 2) R) ^ n) =
      if (d 0, d 1) in Finset.antidiagonal n then n.choose (d 0) else 0 := by
  rw [← Fin.sum_univ_two]; rw [coeff_sum_X_pow_of_fintype]
  congr 1
  have : d.sum (fun x m => m) = d 0 + d 1 := by
    simp [Finsupp.sum_of_support_subset d (Finset.subset_univ d.support)]
  simp only [Finset.mem_antidiagonal, this]
  split_ifs with hd
  · rw [multinomial_eq_of_support_subset (Finset.subset_univ d.support), Finset.univ_fin2,
      Nat.binomial_eq_choose Fin.zero_ne_one, hd]
  · rfl

/--
theorem `monomial_fin_two` / 定理 `monomial_fin_two`

English:
theorem monomial_fin_two
  given: (d : Fin 2 ->₀ Nat) (a : R)
  proof: by
  rw [monomial_eq]; rw [mul_assoc]; rw [d.prod_fintype _ fun _ => pow_zero _]; rw [Fin.prod_univ_two]

中文:
定理 monomial_fin_two
  条件: (d : Fin 2 ->₀ 自然数) (a : R)
  证明: by
  rw [monomial_eq]; rw [mul_assoc]; rw [d.prod_fintype _ fun _ => pow_zero _]; rw [Fin.prod_univ_two]

Depends on / 依赖: Fin.prod_univ_two, d.prod_fintype, monomial_eq, mul_assoc, pow_zero, prod_fintype, prod_univ_two
-/
theorem monomial_fin_two (d : Fin 2 ->₀ Nat) (a : R) :
    monomial d a = C a * X 0 ^ d 0 * X 1 ^ d 1 := by
  rw [monomial_eq]; rw [mul_assoc]; rw [d.prod_fintype _ fun _ => pow_zero _]; rw [Fin.prod_univ_two]

end MvPolynomial
