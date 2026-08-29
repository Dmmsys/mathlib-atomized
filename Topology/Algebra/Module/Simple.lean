/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# The kernel of a linear function is closed or dense

In this file we prove (`LinearMap.isClosed_or_dense_ker`) that the kernel of a linear function
`f : M →ₗ[R] N` is either closed or dense in `M` provided that `N` is a simple module over `R`. This
applies, e.g., to the case when `R = N` is a division ring.
-/

public section


universe u v w

variable {R : Type u} {M : Type v} {N : Type w} [Ring R] [TopologicalSpace R] [TopologicalSpace M]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [ContinuousSMul R M] [Module R N] [ContinuousAdd M]
  [IsSimpleModule R N]

/--
theorem `LinearMap.isClosed_or_dense_ker` / 定理 `LinearMap.isClosed_or_dense_ker`

English:
theorem LinearMap.isClosed_or_dense_ker
  given: (l : M ->ₗ[R] N)
  proof: by
  rcases l.surjective_or_eq_zero with (hl | rfl)
  · exact (LinearMap.ker l).isClosed_or_dense_of_isCoatom (LinearMap.isCoatom_ker_of_surjective hl)
  · rw [LinearMap.ker_zero]
    left
    exact isClosed_univ

中文:
定理 线性映射.isClosed_or_dense_ker
  条件: (l : M ->ₗ[R] N)
  证明: by
  rcases l.surjective_or_eq_zero with (hl | rfl)
  · exact (LinearMap.ker l).isClosed_or_dense_of_isCoatom (LinearMap.isCoatom_ker_of_surjective hl)
  · rw [LinearMap.ker_zero]
    left
    exact isClosed_univ

Depends on / 依赖: LinearMap, LinearMap.isCoatom_ker_of_surjective, LinearMap.ker, LinearMap.ker_zero, isClosed_or_dense_of_isCoatom, isClosed_univ, isCoatom_ker_of_surjective, ker_zero, l.surjective_or_eq_zero, surjective_or_eq_zero
-/
theorem LinearMap.isClosed_or_dense_ker (l : M ->ₗ[R] N) :
    IsClosed (LinearMap.ker l : Set M) ∨ Dense (LinearMap.ker l : Set M) := by
  rcases l.surjective_or_eq_zero with (hl | rfl)
  · exact (LinearMap.ker l).isClosed_or_dense_of_isCoatom (LinearMap.isCoatom_ker_of_surjective hl)
  · rw [LinearMap.ker_zero]
    left
    exact isClosed_univ
