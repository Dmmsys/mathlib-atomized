/-
Copyright (c) 2025 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin, Thomas Zhu
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Integrating compactly supported continuous functions

This file contains definitions and lemmas related to integrals of compactly supported continuous
functions.
-/

@[expose] public section

open scoped ENNReal NNReal
open CompactlySupported MeasureTheory

variable {X : Type*}

namespace CompactlySupportedContinuousMap
variable [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/--
lemma `integrable` / 引理 `integrable`

English:
lemma integrable
  statement: {E : Type*} [NormedAddCommGroup E] (f : C_c(X, E))
  proof: f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport

中文:
引理 integrable
  结论: {E : 类型} [NormedAddCommGroup E] (f : C_c(X, E))
  证明: f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport

Depends on / 依赖: continuous, f.continuous.integrable_of_hasCompactSupport, f.hasCompactSupport, hasCompactSupport, integrable_of_hasCompactSupport
-/
lemma integrable {E : Type*} [NormedAddCommGroup E] (f : C_c(X, E))
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] :
    Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport

variable [T2Space X] [LocallyCompactSpace X] (Λ : C_c(X, Real) ->ₚ[Real] Real)

/-- Integral as a positive linear functional on `C_c(X, ℝ)`. -/
@[simps!]
/--
Definition of `integralPositiveLinearMap` / `integralPositiveLinearMap` 的定义

English:
definition integralPositiveLinearMap
  signature: (μ : Measure X)
  body: PositiveLinearMap.mk₀
    { toFun f := ∫ x, f x ∂μ,
      map_add' f g := integral_add' f.integrable g.integrable
      map_smul' c f := integral_smul c f }
    fun _ => integral_nonneg

中文:
定义 integralPositiveLinearMap
  签名: (μ : Measure X)
  定义体: PositiveLinearMap.mk₀
    { toFun f := ∫ x, f x ∂μ,
      map_add' f g := integral_add' f.integrable g.integrable
      map_smul' c f := integral_smul c f }
    fun _ => integral_nonneg

Depends on / 依赖: PositiveLinearMap, PositiveLinearMap.mk, f.integrable, g.integrable, integrable, integral_add, integral_nonneg, integral_smul, map_add, map_smul
-/
noncomputable def integralPositiveLinearMap (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] : C_c(X, Real) ->ₚ[Real] Real :=
  PositiveLinearMap.mk₀
    { toFun f := ∫ x, f x ∂μ,
      map_add' f g := integral_add' f.integrable g.integrable
      map_smul' c f := integral_smul c f }
    fun _ => integral_nonneg

/-- Integration as a positive linear functional on `C_c(X, ℝ≥0)`. -/
-- Note: the default generated `simps` lemma uses `Subtype.val` instead of `NNReal.toReal`.
@[simps! apply]
/--
Definition of `integralLinearMap` / `integralLinearMap` 的定义

English:
definition integralLinearMap
  signature: (μ : Measure X)
  body: CompactlySupportedContinuousMap.toNNRealLinear (integralPositiveLinearMap μ)

中文:
定义 integralLinearMap
  签名: (μ : Measure X)
  定义体: CompactlySupportedContinuousMap.toNNRealLinear (integralPositiveLinearMap μ)

Depends on / 依赖: CompactlySupportedContinuousMap, CompactlySupportedContinuousMap.toNNRealLinear, integralPositiveLinearMap, toNNRealLinear
-/
noncomputable def integralLinearMap (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] :
    C_c(X, Real>=0) ->ₗ[Real>=0] Real>=0 :=
  CompactlySupportedContinuousMap.toNNRealLinear (integralPositiveLinearMap μ)

end CompactlySupportedContinuousMap
