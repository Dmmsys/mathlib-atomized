/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Euler's homogeneous identity

## Main results

* `IsHomogeneous.sum_X_mul_pderiv`: Euler's identity for homogeneous polynomials:
  for a multivariate homogeneous polynomial,
  the product of each variable with the derivative with respect to that variable
  sums up to the degree times the polynomial.
* `IsWeightedHomogeneous.sum_weight_X_mul_pderiv`: the weighted version of Euler's identity.
-/

public section

namespace MvPolynomial

open Finsupp

variable {R σ M : Type*} [CommSemiring R] {φ : MvPolynomial σ R}

set_option backward.isDefEq.respectTransparency false in
/--
lemma `IsWeightedHomogeneous.pderiv` / 引理 `IsWeightedHomogeneous.pderiv`

English:
lemma IsWeightedHomogeneous.pderiv
  statement: [AddCancelCommMonoid M] {w : σ -> M} {n n' : M} {i : σ}
  proof: by
  rw [← mem_weightedHomogeneousSubmodule]; rw [weightedHomogeneousSubmodule_eq_finsupp_supported]; rw [AddMonoidAlgebra.supported_eq_span_single] at h
  refine Submodule.span_induction ?_ ?_ (fun p q _ _ hp hq => ?_) (fun r p _ h => ?_) h
  · rintro _ ⟨m, hm, rfl⟩
    simp_rw [single_eq_monomial, pderiv_monomial, one_mul]
    by_cases hi : m i = 0
    · rw [hi, Nat.cast_zero, monomial_zero]; apply isWeightedHomogeneous_zero
    convert! isWeightedHomogeneous_monomial ..
    rw [← add_right_cancel_iff (a := w i)]; rw [h']; rw [← hm]; rw [weight_sub_single_add hi]
  · rw [map_zero]; apply isWeightedHomogeneous_zero
  · rw [map_add]; exact hp.add hq
  · rw [(pderiv i).map_smul]; exact (weightedHomogeneousSubmodule ..).smul_mem _ h

中文:
引理 IsWeightedHomogeneous.pderiv
  结论: [加法消去交换幺半群 M] {w : σ -> M} {n n' : M} {i : σ}
  证明: by
  rw [← mem_weightedHomogeneousSubmodule]; rw [weightedHomogeneousSubmodule_eq_finsupp_supported]; rw [AddMonoidAlgebra.supported_eq_span_single] at h
  refine Submodule.span_induction ?_ ?_ (fun p q _ _ hp hq => ?_) (fun r p _ h => ?_) h
  · rintro _ ⟨m, hm, rfl⟩
    simp_rw [single_eq_monomial, pderiv_monomial, one_mul]
    by_cases hi : m i = 0
    · rw [hi, Nat.cast_zero, monomial_zero]; apply isWeightedHomogeneous_zero
    convert! isWeightedHomogeneous_monomial ..
    rw [← add_right_cancel_iff (a := w i)]; rw [h']; rw [← hm]; rw [weight_sub_single_add hi]
  · rw [map_zero]; apply isWeightedHomogeneous_zero
  · rw [map_add]; exact hp.add hq
  · rw [(pderiv i).map_smul]; exact (weightedHomogeneousSubmodule ..).smul_mem _ h
-/
protected lemma IsWeightedHomogeneous.pderiv [AddCancelCommMonoid M] {w : σ -> M} {n n' : M} {i : σ}
    (h : φ.IsWeightedHomogeneous w n) (h' : n' + w i = n) :
    (pderiv i φ).IsWeightedHomogeneous w n' := by
  rw [← mem_weightedHomogeneousSubmodule]; rw [weightedHomogeneousSubmodule_eq_finsupp_supported]; rw [AddMonoidAlgebra.supported_eq_span_single] at h
  refine Submodule.span_induction ?_ ?_ (fun p q _ _ hp hq => ?_) (fun r p _ h => ?_) h
  · rintro _ ⟨m, hm, rfl⟩
    simp_rw [single_eq_monomial, pderiv_monomial, one_mul]
    by_cases hi : m i = 0
    · rw [hi, Nat.cast_zero, monomial_zero]; apply isWeightedHomogeneous_zero
    convert! isWeightedHomogeneous_monomial ..
    rw [← add_right_cancel_iff (a := w i)]; rw [h']; rw [← hm]; rw [weight_sub_single_add hi]
  · rw [map_zero]; apply isWeightedHomogeneous_zero
  · rw [map_add]; exact hp.add hq
  · rw [(pderiv i).map_smul]; exact (weightedHomogeneousSubmodule ..).smul_mem _ h

/--
lemma `IsHomogeneous.pderiv` / 引理 `IsHomogeneous.pderiv`

English:
lemma IsHomogeneous.pderiv
  given: {n : Nat} {i : σ} (h : φ.IsHomogeneous n)
  proof: by
  obtain _ | n := n
  · rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at h
    rw [h]; rw [pderiv_C]; apply isHomogeneous_zero
  · exact IsWeightedHomogeneous.pderiv h rfl

中文:
引理 IsHomogeneous.pderiv
  条件: {n : 自然数} {i : σ} (h : φ.IsHomogeneous n)
  证明: by
  obtain _ | n := n
  · rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at h
    rw [h]; rw [pderiv_C]; apply isHomogeneous_zero
  · exact IsWeightedHomogeneous.pderiv h rfl
-/
protected lemma IsHomogeneous.pderiv {n : Nat} {i : σ} (h : φ.IsHomogeneous n) :
    (pderiv i φ).IsHomogeneous (n - 1) := by
  obtain _ | n := n
  · rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at h
    rw [h]; rw [pderiv_C]; apply isHomogeneous_zero
  · exact IsWeightedHomogeneous.pderiv h rfl

variable [Fintype σ] {n : Nat}

set_option backward.isDefEq.respectTransparency false in
open Finset in
/--
theorem `IsWeightedHomogeneous.sum_weight_X_mul_pderiv` / 定理 `IsWeightedHomogeneous.sum_weight_X_mul_pderiv`

English:
theorem IsWeightedHomogeneous.sum_weight_X_mul_pderiv
  statement: {w : σ -> Nat}
  proof: by
  rw [← mem_weightedHomogeneousSubmodule]; rw [weightedHomogeneousSubmodule_eq_finsupp_supported]; rw [AddMonoidAlgebra.supported_eq_span_single] at h
  refine Submodule.span_induction ?_ ?_ (fun p q _ _ hp hq => ?_) (fun r p _ h => ?_) h
  · rintro _ ⟨m, hm, rfl⟩
    simp_rw [single_eq_monomial, X_mul_pderiv_monomial, smul_smul, ← sum_smul, mul_comm (w _)]
    congr
    rwa [Set.mem_ofPred, weight_apply, sum_fintype] at hm
    intro; apply zero_smul
  · simp
  · simp_rw [map_add, left_distrib, smul_add, sum_add_distrib, hp, hq]
  · simp_rw [(pderiv _).map_smul, nsmul_eq_mul, mul_smul_comm, ← Finset.smul_sum, ← nsmul_eq_mul, h]

中文:
定理 IsWeightedHomogeneous.sum_weight_X_mul_pderiv
  结论: {w : σ -> 自然数}
  证明: by
  rw [← mem_weightedHomogeneousSubmodule]; rw [weightedHomogeneousSubmodule_eq_finsupp_supported]; rw [AddMonoidAlgebra.supported_eq_span_single] at h
  refine Submodule.span_induction ?_ ?_ (fun p q _ _ hp hq => ?_) (fun r p _ h => ?_) h
  · rintro _ ⟨m, hm, rfl⟩
    simp_rw [single_eq_monomial, X_mul_pderiv_monomial, smul_smul, ← sum_smul, mul_comm (w _)]
    congr
    rwa [Set.mem_ofPred, weight_apply, sum_fintype] at hm
    intro; apply zero_smul
  · simp
  · simp_rw [map_add, left_distrib, smul_add, sum_add_distrib, hp, hq]
  · simp_rw [(pderiv _).map_smul, nsmul_eq_mul, mul_smul_comm, ← Finset.smul_sum, ← nsmul_eq_mul, h]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.supported_eq_span_single, Set.mem_ofPred, Submodule, Submodule.span_induction, X_mul_pderiv_monomial, left_distrib, map_add, mem_ofPred, mem_weightedHomogeneousSubmodule, mul_comm, simp_rw, single_eq_monomial, smul_add, smul_smul, span_induction, sum_add_distr, sum_fintype, sum_smul, supported_eq_span_single
-/
theorem IsWeightedHomogeneous.sum_weight_X_mul_pderiv {w : σ -> Nat}
    (h : φ.IsWeightedHomogeneous w n) : ∑ i : σ, w i • (X i * pderiv i φ) = n • φ := by
  rw [← mem_weightedHomogeneousSubmodule]; rw [weightedHomogeneousSubmodule_eq_finsupp_supported]; rw [AddMonoidAlgebra.supported_eq_span_single] at h
  refine Submodule.span_induction ?_ ?_ (fun p q _ _ hp hq => ?_) (fun r p _ h => ?_) h
  · rintro _ ⟨m, hm, rfl⟩
    simp_rw [single_eq_monomial, X_mul_pderiv_monomial, smul_smul, ← sum_smul, mul_comm (w _)]
    congr
    rwa [Set.mem_ofPred, weight_apply, sum_fintype] at hm
    intro; apply zero_smul
  · simp
  · simp_rw [map_add, left_distrib, smul_add, sum_add_distrib, hp, hq]
  · simp_rw [(pderiv _).map_smul, nsmul_eq_mul, mul_smul_comm, ← Finset.smul_sum, ← nsmul_eq_mul, h]

/--
theorem `IsHomogeneous.sum_X_mul_pderiv` / 定理 `IsHomogeneous.sum_X_mul_pderiv`

English:
theorem IsHomogeneous.sum_X_mul_pderiv
  given: (h : φ.IsHomogeneous n)
  proof: by
  simp_rw [← h.sum_weight_X_mul_pderiv, Pi.one_apply, one_smul]

中文:
定理 IsHomogeneous.sum_X_mul_pderiv
  条件: (h : φ.IsHomogeneous n)
  证明: by
  simp_rw [← h.sum_weight_X_mul_pderiv, Pi.one_apply, one_smul]

Depends on / 依赖: Pi.one_apply, h.sum_weight_X_mul_pderiv, one_apply, one_smul, simp_rw, sum_weight_X_mul_pderiv
-/
theorem IsHomogeneous.sum_X_mul_pderiv (h : φ.IsHomogeneous n) :
    ∑ i : σ, X i * pderiv i φ = n • φ := by
  simp_rw [← h.sum_weight_X_mul_pderiv, Pi.one_apply, one_smul]

end MvPolynomial
