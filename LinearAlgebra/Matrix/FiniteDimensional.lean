/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# The finite-dimensional space of matrices

This file shows that `m` by `n` matrices form a finite-dimensional space.
Note that this is proven more generally elsewhere over modules as `Module.Finite.matrix`; this file
exists only to provide an entry in the instance list for `FiniteDimensional`.

## Main definitions

* `Matrix.finiteDimensional`: matrices form a finite-dimensional vector space over a field `K`
* `LinearMap.finiteDimensional`

## Tags

matrix, finite dimensional, findim, finrank

-/

public section


universe u v

namespace Matrix

section FiniteDimensional

variable {m n : Type*} {R : Type v} [Field R]

/--
Instance `finiteDimensional` / 实例 `finiteDimensional`

English:
instance finiteDimensional
  signature: [Finite m] [Finite n]
  body: Module.Finite.matrix

中文:
实例 finiteDimensional
  签名: [有限 m] [有限 n]
  定义体: Module.Finite.matrix

Depends on / 依赖: Finite, Module, Module.Finite.matrix, matrix
-/
instance finiteDimensional [Finite m] [Finite n] : FiniteDimensional R (Matrix m n R) :=
  Module.Finite.matrix

end FiniteDimensional

end Matrix

namespace LinearMap

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/--
Instance `finiteDimensional` / 实例 `finiteDimensional`

English:
instance finiteDimensional
  signature: : FiniteDimensional K (V ->ₗ[K] W)
  body: Module.Finite.linearMap _ _ _ _

中文:
实例 finiteDimensional
  签名: : 有限维 K (V ->ₗ[K] W)
  定义体: Module.Finite.linearMap _ _ _ _

Depends on / 依赖: Finite, Module, Module.Finite.linearMap, linearMap
-/
instance finiteDimensional : FiniteDimensional K (V ->ₗ[K] W) :=
  Module.Finite.linearMap _ _ _ _

variable {A : Type*} [Ring A] [Algebra K A] [Module A V] [IsScalarTower K A V] [Module A W]
  [IsScalarTower K A W]

/--
Instance `finiteDimensional'` / 实例 `finiteDimensional'`

English:
instance finiteDimensional'
  signature: : FiniteDimensional K (V ->ₗ[A] W)
  body: FiniteDimensional.of_injective (restrictScalarsₗ K A V W K) (restrictScalars_injective _)

中文:
实例 finiteDimensional'
  签名: : 有限维 K (V ->ₗ[A] W)
  定义体: FiniteDimensional.of_injective (restrictScalarsₗ K A V W K) (restrictScalars_injective _)

Depends on / 依赖: FiniteDimensional, FiniteDimensional.of_injective, of_injective, restrictScalars_injective
-/
instance finiteDimensional' : FiniteDimensional K (V ->ₗ[A] W) :=
  FiniteDimensional.of_injective (restrictScalarsₗ K A V W K) (restrictScalars_injective _)

end LinearMap
