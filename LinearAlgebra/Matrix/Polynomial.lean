/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.ComputeDegree

/-!
# Matrices of polynomials and polynomials of matrices

In this file, we prove results about matrices over a polynomial ring.
In particular, we give results about the polynomial given by
`det (t * I + A)`.

## References

  * "The trace Cayley-Hamilton theorem" by Darij Grinberg, Section 5.3

## Tags

matrix determinant, polynomial
-/

public section


open Matrix Polynomial

variable {n α : Type*} [DecidableEq n] [Fintype n] [CommRing α]

open Polynomial Matrix Equiv.Perm

namespace Polynomial

/--
theorem `natDegree_det_X_add_C_le` / 定理 `natDegree_det_X_add_C_le`

English:
theorem natDegree_det_X_add_C_le
  given: (A B : Matrix n n α)
  proof: by
  rw [det_apply]
  refine (natDegree_sum_le _ _).trans ?_
  refine Multiset.max_le_of_forall_le _ _ ?_
  simp only [forall_apply_eq_imp_iff, true_and, Function.comp_apply,
    Multiset.mem_map, exists_imp, Finset.mem_univ_val]
  intro g
  calc
    natDegree (sign g • ∏ i : n, (X • A.map C + B.map

中文:
定理 natDegree_det_X_add_C_le
  条件: (A B : Matrix n n α)
  证明: by
  rw [det_apply]
  refine (natDegree_sum_le _ _).trans ?_
  refine Multiset.max_le_of_forall_le _ _ ?_
  simp only [forall_apply_eq_imp_iff, true_and, Function.comp_apply,
    Multiset.mem_map, exists_imp, Finset.mem_univ_val]
  intro g
  calc
    natDegree (sign g • ∏ i : n, (X • A.map C + B.map

Depends on / 依赖: A.map, B.map, Finset, Finset.mem_univ_val, Function, Function.comp_apply, Int.units_eq_one_or, Matrix, MeasurableSingletonClass, MeasurableSingletonClass.of_separatesPoints, MeasurableSpace, Multiset, Multiset.max_le_of_forall_le, Multiset.mem_map, Units.neg_smul, comp_apply, det_apply, exists_imp, forall_apply_eq_imp_iff, max_le_of_forall_le
-/
theorem natDegree_det_X_add_C_le (A B : Matrix n n α) :
    natDegree (det ((X : α[X]) • A.map C + B.map C : Matrix n n α[X])) <= Fintype.card n := by
  rw [det_apply]
  refine (natDegree_sum_le _ _).trans ?_
  refine Multiset.max_le_of_forall_le _ _ ?_
  simp only [forall_apply_eq_imp_iff, true_and, Function.comp_apply,
    Multiset.mem_map, exists_imp, Finset.mem_univ_val]
  intro g
  calc
    natDegree (sign g • ∏ i : n, (X • A.map C + B.map C : Matrix n n α[X]) (g i) i) <=
        natDegree (∏ i : n, (X • A.map C + B.map C : Matrix n n α[X]) (g i) i) := by
      rcases Int.units_eq_one_or (sign g) with sg | sg
      · rw [sg, one_smul]
      · rw [sg, Units.neg_smul, one_smul, natDegree_neg]
    _ <= ∑ i : n, natDegree (((X : α[X]) • A.map C + B.map C : Matrix n n α[X]) (g i) i) :=
      (natDegree_prod_le (Finset.univ : Finset n) fun i : n =>
        (X • A.map C + B.map C : Matrix n n α[X]) (g i) i)
    _ <= Finset.univ.card • 1 := (Finset.sum_le_card_nsmul _ _ 1 fun (i : n) _ => ?_)
    _ <= Fintype.card n := by simp [mul_one, Finset.card_univ]
  dsimp only [Matrix.add_apply, Matrix.smul_apply, map_apply, smul_eq_mul]
  compute_degree

/--
theorem `coeff_det_X_add_C_zero` / 定理 `coeff_det_X_add_C_zero`

English:
theorem coeff_det_X_add_C_zero
  given: (A B : Matrix n n α)
  proof: by
  rw [det_apply]; rw [finsetSum_coeff]; rw [det_apply]
  refine Finset.sum_congr rfl ?_
  rintro g -
  convert! coeff_smul (R := α) (sign g) _ 0
  rw [coeff_zero_prod]
  refine Finset.prod_congr rfl ?_
  simp

中文:
定理 coeff_det_X_add_C_zero
  条件: (A B : Matrix n n α)
  证明: by
  rw [det_apply]; rw [finsetSum_coeff]; rw [det_apply]
  refine Finset.sum_congr rfl ?_
  rintro g -
  convert! coeff_smul (R := α) (sign g) _ 0
  rw [coeff_zero_prod]
  refine Finset.prod_congr rfl ?_
  simp

Depends on / 依赖: Finset, Finset.prod_congr, Finset.sum_congr, coeff_smul, coeff_zero_prod, convert, det_apply, finsetSum_coeff, prod_congr, sum_congr
-/
theorem coeff_det_X_add_C_zero (A B : Matrix n n α) :
    coeff (det ((X : α[X]) • A.map C + B.map C)) 0 = det B := by
  rw [det_apply]; rw [finsetSum_coeff]; rw [det_apply]
  refine Finset.sum_congr rfl ?_
  rintro g -
  convert! coeff_smul (R := α) (sign g) _ 0
  rw [coeff_zero_prod]
  refine Finset.prod_congr rfl ?_
  simp

/--
theorem `coeff_det_X_add_C_card` / 定理 `coeff_det_X_add_C_card`

English:
theorem coeff_det_X_add_C_card
  given: (A B : Matrix n n α)
  proof: by
  rw [det_apply]; rw [det_apply]; rw [finsetSum_coeff]
  refine Finset.sum_congr rfl ?_
  simp only [Finset.mem_univ, forall_true_left]
  intro g
  convert! coeff_smul (R := α) (sign g) _ _
  rw [← mul_one (Fintype.card n)]
  convert! (coeff_prod_of_natDegree_le (R := α) _ _ _ _).symm
  · simp [c

中文:
定理 coeff_det_X_add_C_card
  条件: (A B : Matrix n n α)
  证明: by
  rw [det_apply]; rw [det_apply]; rw [finsetSum_coeff]
  refine Finset.sum_congr rfl ?_
  simp only [Finset.mem_univ, forall_true_left]
  intro g
  convert! coeff_smul (R := α) (sign g) _ _
  rw [← mul_one (Fintype.card n)]
  convert! (coeff_prod_of_natDegree_le (R := α) _ _ _ _).symm
  · simp [c

Depends on / 依赖: Finset, Finset.mem_univ, Finset.sum_congr, Fintype, Fintype.card, Matrix, Matrix.add_apply, Matrix.smul_apply, add_apply, coeff_C, coeff_prod_of_natDegree_le, coeff_smul, compute_degree, convert, det_apply, finsetSum_coeff, forall_true_left, map_apply, mem_univ, mul_one
-/
theorem coeff_det_X_add_C_card (A B : Matrix n n α) :
    coeff (det ((X : α[X]) • A.map C + B.map C)) (Fintype.card n) = det A := by
  rw [det_apply]; rw [det_apply]; rw [finsetSum_coeff]
  refine Finset.sum_congr rfl ?_
  simp only [Finset.mem_univ, forall_true_left]
  intro g
  convert! coeff_smul (R := α) (sign g) _ _
  rw [← mul_one (Fintype.card n)]
  convert! (coeff_prod_of_natDegree_le (R := α) _ _ _ _).symm
  · simp [coeff_C]
  · rintro p -
    dsimp only [Matrix.add_apply, Matrix.smul_apply, map_apply, smul_eq_mul]
    compute_degree

/--
theorem `leadingCoeff_det_X_one_add_C` / 定理 `leadingCoeff_det_X_one_add_C`

English:
theorem leadingCoeff_det_X_one_add_C
  given: (A : Matrix n n α)
  proof: by
  cases subsingleton_or_nontrivial α
  · simp [eq_iff_true_of_subsingleton]
  rw [← @det_one n]; rw [← coeff_det_X_add_C_card _ A]; rw [leadingCoeff]
  simp only [Matrix.map_one, C_eq_zero, map_one]
  rcases (natDegree_det_X_add_C_le 1 A).eq_or_lt with h | h
  · simp only [map_one, Matrix.map_one

中文:
定理 leadingCoeff_det_X_one_add_C
  条件: (A : Matrix n n α)
  证明: by
  cases subsingleton_or_nontrivial α
  · simp [eq_iff_true_of_subsingleton]
  rw [← @det_one n]; rw [← coeff_det_X_add_C_card _ A]; rw [leadingCoeff]
  simp only [Matrix.map_one, C_eq_zero, map_one]
  rcases (natDegree_det_X_add_C_le 1 A).eq_or_lt with h | h
  · simp only [map_one, Matrix.map_one

Depends on / 依赖: C_eq_zero, Matrix, Matrix.map_one, coeff_det_X_add_C_card, degree, det_one, eq_iff_true_of_subsingleton, eq_or_lt, hypothesis, leadingCoeff, map_one, natDegree_det_X_add_C_le, subsingleton_or_nontrivial
-/
theorem leadingCoeff_det_X_one_add_C (A : Matrix n n α) :
    leadingCoeff (det ((X : α[X]) • (1 : Matrix n n α[X]) + A.map C)) = 1 := by
  cases subsingleton_or_nontrivial α
  · simp [eq_iff_true_of_subsingleton]
  rw [← @det_one n]; rw [← coeff_det_X_add_C_card _ A]; rw [leadingCoeff]
  simp only [Matrix.map_one, C_eq_zero, map_one]
  rcases (natDegree_det_X_add_C_le 1 A).eq_or_lt with h | h
  · simp only [map_one, Matrix.map_one, C_eq_zero] at h
    rw [h]
  · -- contradiction. we have a hypothesis that the degree is less than |n|
    -- but we know that coeff _ n = 1
    have H := coeff_eq_zero_of_natDegree_lt h
    rw [coeff_det_X_add_C_card] at H
    simp at H

end Polynomial
