/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-!
# Traces in inner product spaces

This file contains various results about traces of linear operators in inner product spaces.
-/

public section

namespace LinearMap

variable {𝕜 E ι : Type*} [RCLike 𝕜] [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

open scoped InnerProductSpace

/--
lemma `trace_eq_sum_inner` / 引理 `trace_eq_sum_inner`

English:
lemma trace_eq_sum_inner
  given: (T : E ->ₗ[𝕜] E) (b : OrthonormalBasis ι 𝕜 E)
  proof: by
  classical
  rw [LinearMap.trace_eq_matrix_trace 𝕜 b.toBasis T]
  apply Fintype.sum_congr
  intro i
  rw [Matrix.diag_apply]; rw [T.toMatrix_apply]; rw [b.coe_toBasis]; rw [b.coe_toBasis_repr_apply]; rw [b.repr_apply_apply]

中文:
引理 trace_eq_sum_inner
  条件: (T : E ->ₗ[𝕜] E) (b : 正交标准基 ι 𝕜 E)
  证明: by
  classical
  rw [LinearMap.trace_eq_matrix_trace 𝕜 b.toBasis T]
  apply Fintype.sum_congr
  intro i
  rw [Matrix.diag_apply]; rw [T.toMatrix_apply]; rw [b.coe_toBasis]; rw [b.coe_toBasis_repr_apply]; rw [b.repr_apply_apply]

Depends on / 依赖: Fintype, Fintype.sum_congr, LinearMap, LinearMap.trace_eq_matrix_trace, Matrix, Matrix.diag_apply, T.toMatrix_apply, b.coe_toBasis, b.coe_toBasis_repr_apply, b.repr_apply_apply, b.toBasis, classical, coe_toBasis, coe_toBasis_repr_apply, diag_apply, repr_apply_apply, sum_congr, toBasis, toMatrix_apply, trace_eq_matrix_trace
-/
lemma trace_eq_sum_inner (T : E ->ₗ[𝕜] E) (b : OrthonormalBasis ι 𝕜 E) :
    T.trace 𝕜 E = ∑ i, ⟪b i, T (b i)⟫_𝕜 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace 𝕜 b.toBasis T]
  apply Fintype.sum_congr
  intro i
  rw [Matrix.diag_apply]; rw [T.toMatrix_apply]; rw [b.coe_toBasis]; rw [b.coe_toBasis_repr_apply]; rw [b.repr_apply_apply]

variable [FiniteDimensional 𝕜 E]
variable {n : Nat} (hn : Module.finrank 𝕜 E = n)

/--
lemma `IsSymmetric.trace_eq_sum_eigenvalues` / 引理 `IsSymmetric.trace_eq_sum_eigenvalues`

English:
lemma IsSymmetric.trace_eq_sum_eigenvalues
  given: {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric)
  proof: by
  simp [Module.End.trace_eq_sum_roots_charpoly_of_splits hT.splits_charpoly,
    hT.roots_charpoly_eq_eigenvalues hn, List.sum_ofFn]

中文:
引理 IsSymmetric.trace_eq_sum_eigenvalues
  条件: {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric)
  证明: by
  simp [Module.End.trace_eq_sum_roots_charpoly_of_splits hT.splits_charpoly,
    hT.roots_charpoly_eq_eigenvalues hn, List.sum_ofFn]

Depends on / 依赖: List.sum_ofFn, Module, Module.End.trace_eq_sum_roots_charpoly_of_splits, hT.roots_charpoly_eq_eigenvalues, hT.splits_charpoly, roots_charpoly_eq_eigenvalues, splits_charpoly, sum_ofFn, trace_eq_sum_roots_charpoly_of_splits
-/
lemma IsSymmetric.trace_eq_sum_eigenvalues {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) :
    T.trace 𝕜 E = ∑ i, hT.eigenvalues hn i := by
  simp [Module.End.trace_eq_sum_roots_charpoly_of_splits hT.splits_charpoly,
    hT.roots_charpoly_eq_eigenvalues hn, List.sum_ofFn]

/--
lemma `IsSymmetric.re_trace_eq_sum_eigenvalues` / 引理 `IsSymmetric.re_trace_eq_sum_eigenvalues`

English:
lemma IsSymmetric.re_trace_eq_sum_eigenvalues
  given: {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric)
  proof: by
  rw [hT.trace_eq_sum_eigenvalues]
  exact RCLike.ofReal_re_ax _

中文:
引理 IsSymmetric.re_trace_eq_sum_eigenvalues
  条件: {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric)
  证明: by
  rw [hT.trace_eq_sum_eigenvalues]
  exact RCLike.ofReal_re_ax _

Depends on / 依赖: RCLike, RCLike.ofReal_re_ax, hT.trace_eq_sum_eigenvalues, ofReal_re_ax, trace_eq_sum_eigenvalues
-/
lemma IsSymmetric.re_trace_eq_sum_eigenvalues {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) :
    RCLike.re (T.trace 𝕜 E) = ∑ i, hT.eigenvalues hn i := by
  rw [hT.trace_eq_sum_eigenvalues]
  exact RCLike.ofReal_re_ax _

open InnerProductSpace in
/--
lemma `_root_.InnerProductSpace.trace_rankOne` / 引理 `_root_.InnerProductSpace.trace_rankOne`

English:
lemma _root_.InnerProductSpace.trace_rankOne
  given: (x y : E)
  proof: by
  rw [rankOne_def']; rw [ContinuousLinearMap.toLinearMap_comp]; rw [trace_comp_comm']; rw [← ContinuousLinearMap.toLinearMap_comp]; rw [ContinuousLinearMap.comp_toSpanSingleton]
  simp [trace_eq_sum_inner _ (OrthonormalBasis.singleton Unit 𝕜)]

中文:
引理 _root_.内积空间.trace_rankOne
  条件: (x y : E)
  证明: by
  rw [rankOne_def']; rw [ContinuousLinearMap.toLinearMap_comp]; rw [trace_comp_comm']; rw [← ContinuousLinearMap.toLinearMap_comp]; rw [ContinuousLinearMap.comp_toSpanSingleton]
  simp [trace_eq_sum_inner _ (OrthonormalBasis.singleton Unit 𝕜)]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_toSpanSingleton, ContinuousLinearMap.toLinearMap_comp, OrthonormalBasis, OrthonormalBasis.singleton, comp_toSpanSingleton, rankOne_def, singleton, toLinearMap_comp, trace_comp_comm, trace_eq_sum_inner
-/
lemma _root_.InnerProductSpace.trace_rankOne (x y : E) :
    (rankOne 𝕜 x y).trace 𝕜 E = inner 𝕜 y x := by
  rw [rankOne_def']; rw [ContinuousLinearMap.toLinearMap_comp]; rw [trace_comp_comm']; rw [← ContinuousLinearMap.toLinearMap_comp]; rw [ContinuousLinearMap.comp_toSpanSingleton]
  simp [trace_eq_sum_inner _ (OrthonormalBasis.singleton Unit 𝕜)]

end LinearMap
