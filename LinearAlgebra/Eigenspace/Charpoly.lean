/-
Copyright (c) 2025 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/
module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Eigenvalues are the roots of the characteristic polynomial.

## Tags

eigenvalue, characteristic polynomial
-/

public section

namespace Module

namespace End

open LinearMap

variable {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M]
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]

/--
lemma `hasEigenvalue_iff_isRoot_charpoly` / 引理 `hasEigenvalue_iff_isRoot_charpoly`

English:
lemma hasEigenvalue_iff_isRoot_charpoly
  given: (f : End R M) (μ : R)
  proof: by
  rw [hasEigenvalue_iff]; rw [eigenspace_def]; rw [← det_eq_zero_iff_ker_ne_bot]; rw [det_eq_sign_charpoly_coeff]
  simp [Polynomial.coeff_zero_eq_eval_zero, charpoly_sub_smul]

中文:
引理 hasEigenvalue_iff_isRoot_charpoly
  条件: (f : End R M) (μ : R)
  证明: by
  rw [hasEigenvalue_iff]; rw [eigenspace_def]; rw [← det_eq_zero_iff_ker_ne_bot]; rw [det_eq_sign_charpoly_coeff]
  simp [Polynomial.coeff_zero_eq_eval_zero, charpoly_sub_smul]

Depends on / 依赖: Polynomial, Polynomial.coeff_zero_eq_eval_zero, charpoly_sub_smul, coeff_zero_eq_eval_zero, det_eq_sign_charpoly_coeff, det_eq_zero_iff_ker_ne_bot, eigenspace_def, hasEigenvalue_iff
-/
lemma hasEigenvalue_iff_isRoot_charpoly (f : End R M) (μ : R) :
    f.HasEigenvalue μ ↔ f.charpoly.IsRoot μ := by
  rw [hasEigenvalue_iff]; rw [eigenspace_def]; rw [← det_eq_zero_iff_ker_ne_bot]; rw [det_eq_sign_charpoly_coeff]
  simp [Polynomial.coeff_zero_eq_eval_zero, charpoly_sub_smul]

/--
lemma `mem_spectrum_iff_isRoot_charpoly` / 引理 `mem_spectrum_iff_isRoot_charpoly`

English:
lemma mem_spectrum_iff_isRoot_charpoly
  given: (f : End K V) (μ : K)
  proof: by
  rw [← hasEigenvalue_iff_mem_spectrum]; rw [hasEigenvalue_iff_isRoot_charpoly]

中文:
引理 mem_spectrum_iff_isRoot_charpoly
  条件: (f : End K V) (μ : K)
  证明: by
  rw [← hasEigenvalue_iff_mem_spectrum]; rw [hasEigenvalue_iff_isRoot_charpoly]

Depends on / 依赖: hasEigenvalue_iff_isRoot_charpoly, hasEigenvalue_iff_mem_spectrum
-/
lemma mem_spectrum_iff_isRoot_charpoly (f : End K V) (μ : K) :
    μ in spectrum K f ↔ f.charpoly.IsRoot μ := by
  rw [← hasEigenvalue_iff_mem_spectrum]; rw [hasEigenvalue_iff_isRoot_charpoly]

/--
lemma `det_eq_prod_roots_charpoly_of_splits` / 引理 `det_eq_prod_roots_charpoly_of_splits`

English:
lemma det_eq_prod_roots_charpoly_of_splits
  given: {f : End K V} (h : f.charpoly.Splits)
  proof: by
  rw [← det_toMatrix (Module.Free.chooseBasis K V)]; rw [Matrix.det_eq_prod_roots_charpoly_of_splits (by simpa using h)]; rw [charpoly_toMatrix]

中文:
引理 det_eq_prod_roots_charpoly_of_splits
  条件: {f : End K V} (h : f.charpoly.Splits)
  证明: by
  rw [← det_toMatrix (Module.Free.chooseBasis K V)]; rw [Matrix.det_eq_prod_roots_charpoly_of_splits (by simpa using h)]; rw [charpoly_toMatrix]

Depends on / 依赖: Matrix, Matrix.det_eq_prod_roots_charpoly_of_splits, Module, Module.Free.chooseBasis, charpoly_toMatrix, chooseBasis, det_eq_prod_roots_charpoly_of_splits, det_toMatrix
-/
lemma det_eq_prod_roots_charpoly_of_splits {f : End K V} (h : f.charpoly.Splits) :
    f.det = f.charpoly.roots.prod := by
  rw [← det_toMatrix (Module.Free.chooseBasis K V)]; rw [Matrix.det_eq_prod_roots_charpoly_of_splits (by simpa using h)]; rw [charpoly_toMatrix]

/--
lemma `trace_eq_sum_roots_charpoly_of_splits` / 引理 `trace_eq_sum_roots_charpoly_of_splits`

English:
lemma trace_eq_sum_roots_charpoly_of_splits
  given: {f : End K V} (h : f.charpoly.Splits)
  proof: by
  let b := Module.Free.chooseBasis K V
  rw [trace_eq_matrix_trace K (Module.Free.chooseBasis K V)]; rw [Matrix.trace_eq_sum_roots_charpoly_of_splits (by simpa using h)]; rw [charpoly_toMatrix]

中文:
引理 trace_eq_sum_roots_charpoly_of_splits
  条件: {f : End K V} (h : f.charpoly.Splits)
  证明: by
  let b := Module.Free.chooseBasis K V
  rw [trace_eq_matrix_trace K (Module.Free.chooseBasis K V)]; rw [Matrix.trace_eq_sum_roots_charpoly_of_splits (by simpa using h)]; rw [charpoly_toMatrix]

Depends on / 依赖: Matrix, Matrix.trace_eq_sum_roots_charpoly_of_splits, Module, Module.Free.chooseBasis, charpoly_toMatrix, chooseBasis, trace_eq_matrix_trace, trace_eq_sum_roots_charpoly_of_splits
-/
lemma trace_eq_sum_roots_charpoly_of_splits {f : End K V} (h : f.charpoly.Splits) :
    f.trace K V = f.charpoly.roots.sum := by
  let b := Module.Free.chooseBasis K V
  rw [trace_eq_matrix_trace K (Module.Free.chooseBasis K V)]; rw [Matrix.trace_eq_sum_roots_charpoly_of_splits (by simpa using h)]; rw [charpoly_toMatrix]

end End

end Module
