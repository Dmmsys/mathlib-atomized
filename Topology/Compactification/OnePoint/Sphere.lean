/-
Copyright (c) 2025 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Oliver Nash
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!

# One-point compactification of Euclidean space is homeomorphic to the sphere.

-/

@[expose] public section

open Function Metric Module Set Submodule

noncomputable section

/-- A homeomorphism from the one-point compactification of a hyperplane in Euclidean space to the
sphere. -/
/-
**onePointHyperplaneHomeoUnitSphere** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：onePointHyperplaneHomeoUnitSphere {E : Type*} [NormedAddCommGroup E] [Inne
rProductSpace Real E] [FiniteDimensional Real E] {v : E} (hv : ‖v‖ = 1) : OnePoi
nt (Real ∙ v)ᗮ ≃ₜ sphere (0 : E) 1
参数：hv : ‖v‖ = 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homeomorphism from the one-point compactification of a hyperplane in Euclidean
 space to the
sphere.
-/
def onePointHyperplaneHomeoUnitSphere
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {v : E} (hv : ‖v‖ = 1) :
    OnePoint (ℝ ∙ v)ᗮ ≃ₜ sphere (0 : E) 1 :=
  OnePoint.equivOfIsEmbeddingOfRangeEq _ _
    (isOpenEmbedding_stereographic_symm hv).toIsEmbedding (range_stereographic_symm hv)

/-- A homeomorphism from the one-point compactification of a finite-dimensional real vector space to
the sphere. -/
/-
**onePointEquivSphereOfFinrankEq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：onePointEquivSphereOfFinrankEq {ι V : Type*} [Fintype ι] [AddCommGroup V] 
[Module Real V] [FiniteDimensional Real V] [TopologicalSpace V] [IsTopologicalAd
dGroup V] [ContinuousSMul Real V] [T2Space V] (h : finrank Real V + 1 = Fintype.
card ι) : OnePoint V ≃ₜ sphere (0 : EuclideanSpace Real ι) 1
参数：h : finrank Real V + 1 = Fintype.card ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
A homeomorphism from the one-point compactification of a finite-dimensional real
 vector space to
the sphere.
-/
def onePointEquivSphereOfFinrankEq {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    (h : finrank ℝ V + 1 = Fintype.card ι) :
    OnePoint V ≃ₜ sphere (0 : EuclideanSpace ℝ ι) 1 := by
  classical
  have : Nonempty ι := Fintype.card_pos_iff.mp <| by lia
  let v : EuclideanSpace ℝ ι := .single (Classical.arbitrary ι) 1
  have hv : ‖v‖ = 1 := by simp [v]
  have hv₀ : v ≠ 0 := fun contra ↦ by simp [contra] at hv
  have : Fact (finrank ℝ (EuclideanSpace ℝ ι) = finrank ℝ V + 1) := ⟨by simp [h]⟩
  have hV : finrank ℝ V = finrank ℝ (ℝ ∙ v)ᗮ := (finrank_orthogonal_span_singleton hv₀).symm
  letI e : V ≃ₜ (ℝ ∙ v)ᗮ := (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq hV).some
  exact e.onePointCongr.trans <| onePointHyperplaneHomeoUnitSphere hv
