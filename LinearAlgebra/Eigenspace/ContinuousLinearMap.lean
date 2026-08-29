/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Eigenspaces of continuous linear maps

This file provides some basic properties of eigenspaces of continuous linear maps.

These results are in a separate file to avoid heavy topology imports.
-/

public section

namespace ContinuousLinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [T0Space M]
  [ContinuousConstSMul R M] [IsTopologicalAddGroup M] (f : M ->L[R] M) (μ : R) (n : Nat)

open Module End

/--
Instance `isClosed_genEigenspace` / 实例 `isClosed_genEigenspace`

English:
instance isClosed_genEigenspace
  signature: : IsClosed (genEigenspace (f : End R M) μ n : Set M)
  body: by
  simpa [genEigenspace_nat] using isClosed_ker ↑((f - μ • 1) ^ n)

中文:
实例 isClosed_genEigenspace
  签名: : IsClosed (genEigenspace (f : End R M) μ n : Set M)
  定义体: by
  simpa [genEigenspace_nat] using isClosed_ker ↑((f - μ • 1) ^ n)

Depends on / 依赖: genEigenspace_nat, isClosed_ker
-/
instance isClosed_genEigenspace : IsClosed (genEigenspace (f : End R M) μ n : Set M) := by
  simpa [genEigenspace_nat] using isClosed_ker ↑((f - μ • 1) ^ n)

/--
Instance `isClosed_eigenspace` / 实例 `isClosed_eigenspace`

English:
instance isClosed_eigenspace
  signature: : IsClosed (eigenspace (f : End R M) μ : Set M)
  body: isClosed_genEigenspace f μ 1

中文:
实例 isClosed_eigenspace
  签名: : IsClosed (eigenspace (f : End R M) μ : Set M)
  定义体: isClosed_genEigenspace f μ 1

Depends on / 依赖: isClosed_genEigenspace
-/
instance isClosed_eigenspace : IsClosed (eigenspace (f : End R M) μ : Set M) :=
  isClosed_genEigenspace f μ 1

end ContinuousLinearMap
