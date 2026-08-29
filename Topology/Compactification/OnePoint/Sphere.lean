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

/--
Definition of `onePointHyperplaneHomeoUnitSphere` / `onePointHyperplaneHomeoUnitSphere` 的定义

English:
definition onePointHyperplaneHomeoUnitSphere
  body: OnePoint.equivOfIsEmbeddingOfRangeEq _ _
    (isOpenEmbedding_stereographic_symm hv).toIsEmbedding (range_stereographic_symm hv)

中文:
定义 onePointHyperplaneHomeoUnitSphere
  定义体: OnePoint.equivOfIsEmbeddingOfRangeEq _ _
    (isOpenEmbedding_stereographic_symm hv).toIsEmbedding (range_stereographic_symm hv)

Depends on / 依赖: OnePoint, OnePoint.equivOfIsEmbeddingOfRangeEq, equivOfIsEmbeddingOfRangeEq, isOpenEmbedding_stereographic_symm, range_stereographic_symm, toIsEmbedding
-/
def onePointHyperplaneHomeoUnitSphere
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
    {v : E} (hv : ‖v‖ = 1) :
    OnePoint (Real ∙ v)ᗮ ≃ₜ sphere (0 : E) 1 :=
  OnePoint.equivOfIsEmbeddingOfRangeEq _ _
    (isOpenEmbedding_stereographic_symm hv).toIsEmbedding (range_stereographic_symm hv)

/--
Definition of `onePointEquivSphereOfFinrankEq` / `onePointEquivSphereOfFinrankEq` 的定义

English:
definition onePointEquivSphereOfFinrankEq
  signature: {ι V : Type*} [Fintype ι]
  body: by
  classical
have : Nonempty ι := Fintype.card_pos_iff.mp by lia
  let v : EuclideanSpace Real ι := .single (Classical.arbitrary ι) 1
  have hv : ‖v‖ = 1 := by simp [v]
  have hv₀ : v != 0 := fun contra => by simp [contra] at hv
  have : Fact (finrank Real (EuclideanSpace Real ι) = finrank Real V + 1) := ⟨by simp [h]⟩
  have hV : finrank Real V = finrank Real (Real ∙ v)ᗮ := (finrank_orthogonal_span_singleton hv₀).symm
  letI e : V ≃ₜ (Real ∙ v)ᗮ := (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq hV).some
exact e.onePointCongr.trans onePointHyperplaneHomeoUnitSphere hv

中文:
定义 onePointEquivSphereOfFinrankEq
  签名: {ι V : 类型} [有限类型 ι]
  定义体: by
  classical
have : Nonempty ι := Fintype.card_pos_iff.mp by lia
  let v : EuclideanSpace Real ι := .single (Classical.arbitrary ι) 1
  have hv : ‖v‖ = 1 := by simp [v]
  have hv₀ : v != 0 := fun contra => by simp [contra] at hv
  have : Fact (finrank Real (EuclideanSpace Real ι) = finrank Real V + 1) := ⟨by simp [h]⟩
  have hV : finrank Real V = finrank Real (Real ∙ v)ᗮ := (finrank_orthogonal_span_singleton hv₀).symm
  letI e : V ≃ₜ (Real ∙ v)ᗮ := (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq hV).some
exact e.onePointCongr.trans onePointHyperplaneHomeoUnitSphere hv

Depends on / 依赖: Classical, Classical.arbitrary, EuclideanSpace, FiniteDimensional, FiniteDimensional.nonempty_continuousLinearEquiv_of_finran, Fintype, Fintype.card_pos_iff.mp, Nonempty, arbitrary, card_pos_iff, classical, contra, finrank, finrank_orthogonal_span_singleton, nonempty_continuousLinearEquiv_of_finran, single
-/
def onePointEquivSphereOfFinrankEq {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul Real V] [T2Space V]
    (h : finrank Real V + 1 = Fintype.card ι) :
    OnePoint V ≃ₜ sphere (0 : EuclideanSpace Real ι) 1 := by
  classical
have : Nonempty ι := Fintype.card_pos_iff.mp by lia
  let v : EuclideanSpace Real ι := .single (Classical.arbitrary ι) 1
  have hv : ‖v‖ = 1 := by simp [v]
  have hv₀ : v != 0 := fun contra => by simp [contra] at hv
  have : Fact (finrank Real (EuclideanSpace Real ι) = finrank Real V + 1) := ⟨by simp [h]⟩
  have hV : finrank Real V = finrank Real (Real ∙ v)ᗮ := (finrank_orthogonal_span_singleton hv₀).symm
  letI e : V ≃ₜ (Real ∙ v)ᗮ := (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq hV).some
exact e.onePointCongr.trans onePointHyperplaneHomeoUnitSphere hv
