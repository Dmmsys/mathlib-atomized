/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Determinant

/-!
# Gershgorin's circle theorem

This file gives the proof of Gershgorin's circle theorem `eigenvalue_mem_ball` on the eigenvalues
of matrices and some applications.

## Reference

* https://en.wikipedia.org/wiki/Gershgorin_circle_theorem
-/

public section

variable {K n : Type*} [NormedField K] [Fintype n] [DecidableEq n] {A : Matrix n n K}

/--
theorem `eigenvalue_mem_ball` / 定理 `eigenvalue_mem_ball`

English:
theorem eigenvalue_mem_ball
  given: {μ : K} (hμ : Module.End.HasEigenvalue (Matrix.toLin' A) μ)
  proof: by
  cases isEmpty_or_nonempty n
  · exfalso
    exact hμ Submodule.eq_bot_of_subsingleton
  · obtain ⟨v, h_eg, h_nz⟩ := hμ.exists_hasEigenvector
    obtain ⟨i, -, h_i⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => ‖v i‖)
    have h_nz : v i != 0 := by
      contrapose h_nz
      ext j

中文:
定理 eigenvalue_mem_ball
  条件: {μ : K} (hμ : Module.End.HasEigenvalue (Matrix.toLin' A) μ)
  证明: by
  cases isEmpty_or_nonempty n
  · exfalso
    exact hμ Submodule.eq_bot_of_subsingleton
  · obtain ⟨v, h_eg, h_nz⟩ := hμ.exists_hasEigenvector
    obtain ⟨i, -, h_i⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => ‖v i‖)
    have h_nz : v i != 0 := by
      contrapose h_nz
      ext j

Depends on / 依赖: Finset, Finset.exists_mem_eq_sup, Finset.le_sup, Finset.mem_univ, Finset.univ_nonempty, Pi.zero_apply, Submodule, Submodule.eq_bot_of_subsingleton, contrapose, eq_bot_of_subsingleton, exists_hasEigenvector, exists_mem_eq_sup, h_eg, h_le, h_nz, isEmpty_or_nonempty, le_sup, mem_univ, norm_le_zero_iff, norm_le_zero_iff.mpr
-/
theorem eigenvalue_mem_ball {μ : K} (hμ : Module.End.HasEigenvalue (Matrix.toLin' A) μ) :
    exists k, μ in Metric.closedBall (A k k) (∑ j in Finset.univ.erase k, ‖A k j‖) := by
  cases isEmpty_or_nonempty n
  · exfalso
    exact hμ Submodule.eq_bot_of_subsingleton
  · obtain ⟨v, h_eg, h_nz⟩ := hμ.exists_hasEigenvector
    obtain ⟨i, -, h_i⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => ‖v i‖)
    have h_nz : v i != 0 := by
      contrapose h_nz
      ext j
      rw [Pi.zero_apply]; rw [← norm_le_zero_iff]
      refine (h_i ▸ Finset.le_sup' (fun i => ‖v i‖) (Finset.mem_univ j)).trans ?_
      exact norm_le_zero_iff.mpr h_nz
    have h_le : forall j, ‖v j * (v i)⁻¹‖ <= 1 := fun j => by
      rw [norm_mul]; rw [norm_inv]; rw [mul_inv_le_iff₀ (norm_pos_iff.mpr h_nz)]; rw [one_mul]
      exact h_i ▸ Finset.le_sup' (fun i => ‖v i‖) (Finset.mem_univ j)
    simp_rw [mem_closedBall_iff_norm']
    refine ⟨i, ?_⟩
    calc
      _ = ‖(A i i * v i - μ * v i) * (v i)⁻¹‖ := by congr; field
      _ = ‖(A i i * v i - ∑ j, A i j * v j) * (v i)⁻¹‖ := by
                rw [show μ * v i = ∑ x : n]; rw [A i x * v x by
                  rw [← dotProduct]; rw [← Matrix.mulVec]
                  exact (congrFun (Module.End.mem_eigenspace_iff.mp h_eg) i).symm]
      _ = ‖(∑ j in Finset.univ.erase i, A i j * v j) * (v i)⁻¹‖ := by
                rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]; rw [← neg_sub]; rw [neg_mul]; rw [norm_neg]
      _ <= ∑ j in Finset.univ.erase i, ‖A i j‖ * ‖v j * (v i)⁻¹‖ := by
                rw [Finset.sum_mul]
                exact (norm_sum_le _ _).trans (le_of_eq (by simp_rw [mul_assoc, norm_mul]))
      _ <= ∑ j in Finset.univ.erase i, ‖A i j‖ :=
                (Finset.sum_le_sum fun j _ => mul_le_of_le_one_right (norm_nonneg _) (h_le j))

/--
theorem `det_ne_zero_of_sum_row_lt_diag` / 定理 `det_ne_zero_of_sum_row_lt_diag`

English:
theorem det_ne_zero_of_sum_row_lt_diag
  given: (h : forall k, ∑ j in Finset.univ.erase k, ‖A k j‖ < ‖A k k‖)
  proof: by
  contrapose! h
  suffices exists k, 0 in Metric.closedBall (A k k) (∑ j in Finset.univ.erase k, ‖A k j‖) by
    exact this.imp (fun a h => by rwa [mem_closedBall_iff_norm', sub_zero] at h)
  refine eigenvalue_mem_ball ?_
  rw [Module.End.hasEigenvalue_iff]; rw [Module.End.eigenspace_zero]; rw [n

中文:
定理 det_ne_zero_of_sum_row_lt_diag
  条件: (h : 对任意 k, ∑ j in Finset.univ.erase k, ‖A k j‖ < ‖A k k‖)
  证明: by
  contrapose! h
  suffices exists k, 0 in Metric.closedBall (A k k) (∑ j in Finset.univ.erase k, ‖A k j‖) by
    exact this.imp (fun a h => by rwa [mem_closedBall_iff_norm', sub_zero] at h)
  refine eigenvalue_mem_ball ?_
  rw [Module.End.hasEigenvalue_iff]; rw [Module.End.eigenspace_zero]; rw [n

Depends on / 依赖: Finset, Finset.univ.erase, LinearMap, LinearMap.bot_lt_ker_of_det_eq_zero, LinearMap.det_toLin, Metric, Metric.closedBall, Module, Module.End.eigenspace_zero, Module.End.hasEigenvalue_iff, bot_lt_ker_of_det_eq_zero, closedBall, contrapose, det_toLin, eigenspace_zero, eigenvalue_mem_ball, hasEigenvalue_iff, mem_closedBall_iff_norm, ne_comm, ne_of_lt
-/
theorem det_ne_zero_of_sum_row_lt_diag (h : forall k, ∑ j in Finset.univ.erase k, ‖A k j‖ < ‖A k k‖) :
    A.det != 0 := by
  contrapose! h
  suffices exists k, 0 in Metric.closedBall (A k k) (∑ j in Finset.univ.erase k, ‖A k j‖) by
    exact this.imp (fun a h => by rwa [mem_closedBall_iff_norm', sub_zero] at h)
  refine eigenvalue_mem_ball ?_
  rw [Module.End.hasEigenvalue_iff]; rw [Module.End.eigenspace_zero]; rw [ne_comm]
  exact ne_of_lt (LinearMap.bot_lt_ker_of_det_eq_zero (by rwa [LinearMap.det_toLin']))

/--
theorem `det_ne_zero_of_sum_col_lt_diag` / 定理 `det_ne_zero_of_sum_col_lt_diag`

English:
theorem det_ne_zero_of_sum_col_lt_diag
  given: (h : forall k, ∑ i in Finset.univ.erase k, ‖A i k‖ < ‖A k k‖)
  proof: by
  rw [← Matrix.det_transpose]
  exact det_ne_zero_of_sum_row_lt_diag (by simp_rw [Matrix.transpose_apply]; exact h)

中文:
定理 det_ne_zero_of_sum_col_lt_diag
  条件: (h : 对任意 k, ∑ i in Finset.univ.erase k, ‖A i k‖ < ‖A k k‖)
  证明: by
  rw [← Matrix.det_transpose]
  exact det_ne_zero_of_sum_row_lt_diag (by simp_rw [Matrix.transpose_apply]; exact h)

Depends on / 依赖: Matrix, Matrix.det_transpose, Matrix.transpose_apply, det_ne_zero_of_sum_row_lt_diag, det_transpose, simp_rw, transpose_apply
-/
theorem det_ne_zero_of_sum_col_lt_diag (h : forall k, ∑ i in Finset.univ.erase k, ‖A i k‖ < ‖A k k‖) :
    A.det != 0 := by
  rw [← Matrix.det_transpose]
  exact det_ne_zero_of_sum_row_lt_diag (by simp_rw [Matrix.transpose_apply]; exact h)
