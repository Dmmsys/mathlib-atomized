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

/-
**CompactlySupportedContinuousMap.integrable** 是 Mathlib 中的一个引理，位于命名空间 `Compactl
ySupportedContinuousMap`。
形式化陈述：integrable {E : Type*} [NormedAddCommGroup E] (f : C_c(X, E)) {μ : Measure
 X} [IsFiniteMeasureOnCompacts μ] : Integrable f μ
参数：f : C_c(X, E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.integrable_of_hasCompactSupport`：Continuous.integrable_of_has
CompactSupport (hf : Continuous f) (hcf : HasCompactSupport f) : Integrable f μ
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `CompactlySupportedContinuousMap.hasCompactSupport`：∀ {α : Type u_2} {β :
 Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [inst_2 : Z
ero β]   (f : CompactlySupportedContinu…
-/
lemma integrable {E : Type*} [NormedAddCommGroup E] (f : C_c(X, E))
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] :
    Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport

variable [T2Space X] [LocallyCompactSpace X] (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ)

/-- Integral as a positive linear functional on `C_c(X, ℝ)`. -/
@[simps!]
/-
**CompactlySupportedContinuousMap.integralPositiveLinearMap** 是 Mathlib 中的一个定义，位
于命名空间 `CompactlySupportedContinuousMap`。
形式化陈述：integralPositiveLinearMap (μ : Measure X) [IsFiniteMeasureOnCompacts μ] : 
C_c(X, Real) ->ₚ[Real] Real
参数：μ : Measure X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ

--- 原说明 ---
Integral as a positive linear functional on `C_c(X, ℝ)`.
-/
noncomputable def integralPositiveLinearMap (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun f := ∫ x, f x ∂μ,
      map_add' f g := integral_add' f.integrable g.integrable
      map_smul' c f := integral_smul c f }
    fun _ ↦ integral_nonneg

/-- Integration as a positive linear functional on `C_c(X, ℝ≥0)`. -/
-- Note: the default generated `simps` lemma uses `Subtype.val` instead of `NNReal.toReal`.
@[simps! apply]
/-
**CompactlySupportedContinuousMap.integralLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `C
ompactlySupportedContinuousMap`。
形式化陈述：integralLinearMap (μ : Measure X) [IsFiniteMeasureOnCompacts μ] : C_c(X, R
eal>=0) ->ₗ[Real>=0] Real>=0
参数：μ : Measure X。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def integralLinearMap (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] :
    C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0 :=
  CompactlySupportedContinuousMap.toNNRealLinear (integralPositiveLinearMap μ)

end CompactlySupportedContinuousMap

