/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Canonical tensors in real inner product spaces

Given an `InnerProductSpace ℝ E`, this file defines two canonical tensors.

* `InnerProductSpace.canonicalContravariantTensor E : E ⊗[ℝ] E →ₗ[ℝ] ℝ`. This is the element
  corresponding to the inner product.

* If `E` is finite-dimensional, then `E ⊗[ℝ] E` is canonically isomorphic to its dual. Accordingly,
  there exists an element `InnerProductSpace.canonicalCovariantTensor E : E ⊗[ℝ] E` that
  corresponds to `InnerProductSpace.canonicalContravariantTensor E` under this identification.

The theorem `canonicalCovariantTensor_eq_sum` shows that
`InnerProductSpace.canonicalCovariantTensor E` can be computed from any orthonormal basis `v` as
`∑ i, (v i) ⊗ₜ[ℝ] (v i)`.
-/

@[expose] public section

open InnerProductSpace TensorProduct

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace Real E]

/--
Definition of `InnerProductSpace.canonicalContravariantTensor` / `InnerProductSpace.canonicalContravariantTensor` 的定义

English:
definition InnerProductSpace.canonicalContravariantTensor
  signature: :
  body: lift (innerₗ E)

中文:
定义 内积空间.canonicalContravariantTensor
  签名: :
  定义体: lift (innerₗ E)
-/
noncomputable def InnerProductSpace.canonicalContravariantTensor :
    E otimes[Real] E ->ₗ[Real] Real := lift (innerₗ E)

/--
Definition of `InnerProductSpace.canonicalCovariantTensor` / `InnerProductSpace.canonicalCovariantTensor` 的定义

English:
definition InnerProductSpace.canonicalCovariantTensor
  signature: [FiniteDimensional Real E]
  body: ∑ i, ((stdOrthonormalBasis Real E) i) otimesₜ[Real] ((stdOrthonormalBasis Real E) i)

中文:
定义 内积空间.canonicalCovariantTensor
  签名: [有限维 实数 E]
  定义体: ∑ i, ((stdOrthonormalBasis Real E) i) otimesₜ[Real] ((stdOrthonormalBasis Real E) i)

Depends on / 依赖: stdOrthonormalBasis
-/
noncomputable def InnerProductSpace.canonicalCovariantTensor [FiniteDimensional Real E] :
    E otimes[Real] E := ∑ i, ((stdOrthonormalBasis Real E) i) otimesₜ[Real] ((stdOrthonormalBasis Real E) i)

/--
theorem `InnerProductSpace.canonicalCovariantTensor_eq_sum` / 定理 `InnerProductSpace.canonicalCovariantTensor_eq_sum`

English:
theorem InnerProductSpace.canonicalCovariantTensor_eq_sum
  statement: [FiniteDimensional Real E]
  proof: by
  let w := stdOrthonormalBasis Real E
  calc ∑ m, w m otimesₜ[Real] w m
  _ = ∑ m, ∑ n, ⟪w m, w n⟫_Real • w m otimesₜ[Real] w n := by
    congr 1 with m
    rw [Fintype.sum_eq_single m _]; rw [orthonormal_iff_ite.1 w.orthonormal]
    · simp only [↓reduceIte, one_smul]
    simp only [orthonormal_iff_ite.1 w.orthonormal, ite_smul, one_smul, zero_smul,
      ite_eq_right_iff]
    tauto
  _ = ∑ m, ∑ n, (∑ i, ⟪w m, v i⟫_Real * ⟪v i, w n⟫_Real) • w m otimesₜ[Real] w n := by
    simp_rw [OrthonormalBasis.sum_inner_mul_inner v]
  _ = ∑ m, ∑ n, (∑ i, ⟪w m, v i⟫_Real * ⟪w n, v i⟫_Real) • w m otimesₜ[Real] w n := by
    simp only [real_inner_comm (w _)]
  _ = ∑ i, (∑ m, ⟪w m, v i⟫_Real • w m) otimesₜ[Real] ∑ n, ⟪w n, v i⟫_Real • w n := by
    simp only [sum_tmul, tmul_sum, smul_tmul_smul, Finset.sum_comm (γ := ι), Finset.sum_smul]
    rw [Finset.sum_comm]
  _ = ∑ i, v i otimesₜ[Real] v i := by
    simp only [w.sum_repr' (v _)]

中文:
定理 内积空间.canonicalCovariantTensor_eq_sum
  结论: [有限维 实数 E]
  证明: by
  let w := stdOrthonormalBasis Real E
  calc ∑ m, w m otimesₜ[Real] w m
  _ = ∑ m, ∑ n, ⟪w m, w n⟫_Real • w m otimesₜ[Real] w n := by
    congr 1 with m
    rw [Fintype.sum_eq_single m _]; rw [orthonormal_iff_ite.1 w.orthonormal]
    · simp only [↓reduceIte, one_smul]
    simp only [orthonormal_iff_ite.1 w.orthonormal, ite_smul, one_smul, zero_smul,
      ite_eq_right_iff]
    tauto
  _ = ∑ m, ∑ n, (∑ i, ⟪w m, v i⟫_Real * ⟪v i, w n⟫_Real) • w m otimesₜ[Real] w n := by
    simp_rw [OrthonormalBasis.sum_inner_mul_inner v]
  _ = ∑ m, ∑ n, (∑ i, ⟪w m, v i⟫_Real * ⟪w n, v i⟫_Real) • w m otimesₜ[Real] w n := by
    simp only [real_inner_comm (w _)]
  _ = ∑ i, (∑ m, ⟪w m, v i⟫_Real • w m) otimesₜ[Real] ∑ n, ⟪w n, v i⟫_Real • w n := by
    simp only [sum_tmul, tmul_sum, smul_tmul_smul, Finset.sum_comm (γ := ι), Finset.sum_smul]
    rw [Finset.sum_comm]
  _ = ∑ i, v i otimesₜ[Real] v i := by
    simp only [w.sum_repr' (v _)]

Depends on / 依赖: Fintype, Fintype.sum_eq_single, OrthonormalBasis, OrthonormalBasis.sum_inner_mul_inner, _Real, ite_eq_right_iff, ite_smul, one_smul, orthonormal, orthonormal_iff_ite, reduceIte, simp_rw, stdOrthonormalBasis, sum_eq_single, sum_inner_mul_inner, w.orthonormal, zero_smul
-/
theorem InnerProductSpace.canonicalCovariantTensor_eq_sum [FiniteDimensional Real E]
    {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι Real E) :
    InnerProductSpace.canonicalCovariantTensor E = ∑ i, (v i) otimesₜ[Real] (v i) := by
  let w := stdOrthonormalBasis Real E
  calc ∑ m, w m otimesₜ[Real] w m
  _ = ∑ m, ∑ n, ⟪w m, w n⟫_Real • w m otimesₜ[Real] w n := by
    congr 1 with m
    rw [Fintype.sum_eq_single m _]; rw [orthonormal_iff_ite.1 w.orthonormal]
    · simp only [↓reduceIte, one_smul]
    simp only [orthonormal_iff_ite.1 w.orthonormal, ite_smul, one_smul, zero_smul,
      ite_eq_right_iff]
    tauto
  _ = ∑ m, ∑ n, (∑ i, ⟪w m, v i⟫_Real * ⟪v i, w n⟫_Real) • w m otimesₜ[Real] w n := by
    simp_rw [OrthonormalBasis.sum_inner_mul_inner v]
  _ = ∑ m, ∑ n, (∑ i, ⟪w m, v i⟫_Real * ⟪w n, v i⟫_Real) • w m otimesₜ[Real] w n := by
    simp only [real_inner_comm (w _)]
  _ = ∑ i, (∑ m, ⟪w m, v i⟫_Real • w m) otimesₜ[Real] ∑ n, ⟪w n, v i⟫_Real • w n := by
    simp only [sum_tmul, tmul_sum, smul_tmul_smul, Finset.sum_comm (γ := ι), Finset.sum_smul]
    rw [Finset.sum_comm]
  _ = ∑ i, v i otimesₜ[Real] v i := by
    simp only [w.sum_repr' (v _)]
