/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Building continuous bilinear maps in finite dimensions over complete fields

Given a complete nontrivially normed field `𝕜` and finite dimensional T₂ topological vector spaces
over `𝕜`, this file builds a continuous bilinear map from any bilinear function.

This applies in particular to evaluation of linear maps between such spaces.

Working with topological vector spaces instead of normed spaces is important for applications in the
differential geometry part of Mathlib where we don’t want to fix a norm on tangent spaces for
instance.

-/

@[expose] public section

variable
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E] [T2Space E]
    {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [FiniteDimensional 𝕜 F] [T2Space F]
    {G : Type*} [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousSMul 𝕜 G]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `LinearMap.toContinuousBilinearMap` / `LinearMap.toContinuousBilinearMap` 的定义

English:
definition LinearMap.toContinuousBilinearMap
  signature: (f : E ->ₗ[𝕜] F ->ₗ[𝕜] G)
  body: IsLinearMap.mk' (fun x : E => f x |>.toContinuousLinearMap)
.toContinuousLinearMap (by constructor <;> (intros; simp))

@[simp]

中文:
定义 LinearMap.toContinuousBilinearMap
  签名: (f : E ->ₗ[𝕜] F ->ₗ[𝕜] G)
  定义体: IsLinearMap.mk' (fun x : E => f x |>.toContinuousLinearMap)
.toContinuousLinearMap (by constructor <;> (intros; simp))

@[simp]

Depends on / 依赖: IsLinearMap, IsLinearMap.mk, intros, toContinuousLinearMap
-/
def LinearMap.toContinuousBilinearMap (f : E ->ₗ[𝕜] F ->ₗ[𝕜] G) : E ->L[𝕜] F ->L[𝕜] G :=
  IsLinearMap.mk' (fun x : E => f x |>.toContinuousLinearMap)
.toContinuousLinearMap (by constructor <;> (intros; simp))

@[simp]
/--
lemma `LinearMap.toContinuousBilinearMap_apply` / 引理 `LinearMap.toContinuousBilinearMap_apply`

English:
lemma LinearMap.toContinuousBilinearMap_apply
  given: (f : E ->ₗ[𝕜] F ->ₗ[𝕜] G) (x : E) (y : F)
  proof: rfl

中文:
引理 LinearMap.toContinuousBilinearMap_apply
  条件: (f : E ->ₗ[𝕜] F ->ₗ[𝕜] G) (x : E) (y : F)
  证明: rfl
-/
lemma LinearMap.toContinuousBilinearMap_apply (f : E ->ₗ[𝕜] F ->ₗ[𝕜] G) (x : E) (y : F) :
  f.toContinuousBilinearMap x y = f x y := rfl

/--
Definition of `IsBilinearMap.toContinuousBilinearMap` / `IsBilinearMap.toContinuousBilinearMap` 的定义

English:
definition IsBilinearMap.toContinuousBilinearMap
  body: h.toLinearMap.toContinuousBilinearMap

@[simp]

中文:
定义 IsBilinearMap.toContinuousBilinearMap
  定义体: h.toLinearMap.toContinuousBilinearMap

@[simp]

Depends on / 依赖: h.toLinearMap.toContinuousBilinearMap, toContinuousBilinearMap, toLinearMap
-/
def IsBilinearMap.toContinuousBilinearMap
    {f : E -> F -> G} (h : IsBilinearMap 𝕜 f) : E ->L[𝕜] F ->L[𝕜] G :=
  h.toLinearMap.toContinuousBilinearMap

@[simp]
/--
lemma `IsBilinearMap.toContinuousBilinearMap_apply` / 引理 `IsBilinearMap.toContinuousBilinearMap_apply`

English:
lemma IsBilinearMap.toContinuousBilinearMap_apply
  statement: {f : E -> F -> G} (h : IsBilinearMap 𝕜 f)
  proof: rfl

中文:
引理 IsBilinearMap.toContinuousBilinearMap_apply
  结论: {f : E -> F -> G} (h : IsBilinearMap 𝕜 f)
  证明: rfl
-/
lemma IsBilinearMap.toContinuousBilinearMap_apply {f : E -> F -> G} (h : IsBilinearMap 𝕜 f)
    (x : E) (y : F) :
  h.toContinuousBilinearMap x y = f x y := rfl

variable (𝕜 E F) in
/--
Definition of `ContinuousLinearMap.evalL` / `ContinuousLinearMap.evalL` 的定义

English:
definition ContinuousLinearMap.evalL
  signature: : E ->L[𝕜] (E ->L[𝕜] F) ->L[𝕜] F
  body: .toContinuousBilinearMap .flip LinearMap.toContinuousLinearMap.symm.toLinearMap

@[simp]

中文:
定义 ContinuousLinearMap.evalL
  签名: : E ->L[𝕜] (E ->L[𝕜] F) ->L[𝕜] F
  定义体: .toContinuousBilinearMap .flip LinearMap.toContinuousLinearMap.symm.toLinearMap

@[simp]

Depends on / 依赖: LinearMap, LinearMap.toContinuousLinearMap.symm.toLinearMap, toContinuousBilinearMap, toContinuousLinearMap, toLinearMap
-/
def ContinuousLinearMap.evalL : E ->L[𝕜] (E ->L[𝕜] F) ->L[𝕜] F :=
.toContinuousBilinearMap .flip LinearMap.toContinuousLinearMap.symm.toLinearMap

@[simp]
/--
lemma `ContinuousLinearMap.evalL_apply` / 引理 `ContinuousLinearMap.evalL_apply`

English:
lemma ContinuousLinearMap.evalL_apply
  given: (x : E) (φ : E ->L[𝕜] F)
  statement: φ.evalL 𝕜 E F x = φ x
  proof: rfl

中文:
引理 ContinuousLinearMap.evalL_apply
  条件: (x : E) (φ : E ->L[𝕜] F)
  结论: φ.evalL 𝕜 E F x = φ x
  证明: rfl
-/
lemma ContinuousLinearMap.evalL_apply (x : E) (φ : E ->L[𝕜] F) : φ.evalL 𝕜 E F x = φ x := rfl
