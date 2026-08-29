/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.LocallyConvex.StrongTopology

/-!
# The topology of pointwise convergence is locally convex

We prove that the topology of pointwise convergence is induced by a family of seminorms and
that it is locally convex in the topological sense

* `PointwiseConvergenceCLM.seminorm`: the seminorms on `E →SLₚₜ[σ] F` given by `A ↦ ‖A x‖` for fixed
  `x : E`.
* `PointwiseConvergenceCLM.withSeminorm`: the topology is induced by the seminorms.
* `PointwiseConvergenceCLM.instLocallyConvexSpace`: `E →SLₚₜ[σ] F` is locally convex.

-/

@[expose] public section

variable {α R 𝕜₁ 𝕜₂ 𝕜₃ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃]
  {σ : 𝕜₁ ->+* 𝕜₂} {τ : 𝕜₃ ->+* 𝕜₂} {D E F G : Type*}
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E]

namespace PointwiseConvergenceCLM

section NormedSpace

variable [NormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/--
Definition of `seminorm` / `seminorm` 的定义

English:
definition seminorm
  signature: (x : E)
  body: ‖A x‖
  map_zero' := by simp
  add_le' A B := by simpa only using! norm_add_le _ _
  neg' A := by simp
  smul' r A := by simp [norm_smul]

中文:
定义 seminorm
  签名: (x : E)
  定义体: ‖A x‖
  map_zero' := by simp
  add_le' A B := by simpa only using! norm_add_le _ _
  neg' A := by simp
  smul' r A := by simp [norm_smul]
-/
protected def seminorm (x : E) : Seminorm 𝕜₂ (E ->SLₚₜ[σ] F) where
  toFun A := ‖A x‖
  map_zero' := by simp
  add_le' A B := by simpa only using! norm_add_le _ _
  neg' A := by simp
  smul' r A := by simp [norm_smul]

variable (σ E F) in
/--
Definition of `seminormFamily` / `seminormFamily` 的定义

English:
abbreviation seminormFamily
  signature: : SeminormFamily 𝕜₂ (E ->SLₚₜ[σ] F) E
  body: PointwiseConvergenceCLM.seminorm

中文:
缩写 seminormFamily
  签名: : SeminormFamily 𝕜₂ (E ->SLₚₜ[σ] F) E
  定义体: PointwiseConvergenceCLM.seminorm
-/
protected abbrev seminormFamily : SeminormFamily 𝕜₂ (E ->SLₚₜ[σ] F) E :=
  PointwiseConvergenceCLM.seminorm

variable (σ E F) in
/--
Definition of `inducingFn` / `inducingFn` 的定义

English:
definition inducingFn
  signature: : (E ->SLₚₜ[σ] F) ->ₗ[𝕜₂] (E -> F) where
  body: f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 inducingFn
  签名: : (E ->SLₚₜ[σ] F) ->ₗ[𝕜₂] (E -> F) where
  定义体: f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
-/
def inducingFn : (E ->SLₚₜ[σ] F) ->ₗ[𝕜₂] (E -> F) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (σ E F) in
/--
theorem `isInducing_inducingFn` / 定理 `isInducing_inducingFn`

English:
theorem isInducing_inducingFn
  statement: Topology.IsInducing (inducingFn σ E F)
  proof: (PointwiseConvergenceCLM.isEmbedding_coeFn σ E F).isInducing

中文:
定理 isInducing_inducingFn
  结论: 拓扑.是Inducing (inducingFn σ E F)
  证明: (PointwiseConvergenceCLM.isEmbedding_coeFn σ E F).isInducing

Depends on / 依赖: PointwiseConvergenceCLM, PointwiseConvergenceCLM.isEmbedding_coeFn, isEmbedding_coeFn, isInducing
-/
theorem isInducing_inducingFn : Topology.IsInducing (inducingFn σ E F) :=
  (PointwiseConvergenceCLM.isEmbedding_coeFn σ E F).isInducing

/--
lemma `withSeminorms` / 引理 `withSeminorms`

English:
lemma withSeminorms
  statement: WithSeminorms (PointwiseConvergenceCLM.seminormFamily σ E F)
  proof: let e : E ≃ (Σ _ : E, Fin 1) := .symm .sigmaUnique _ _
(isInducing_inducingFn σ E F).withSeminorms withSeminorms_pi (fun _ => norm_withSeminorms 𝕜₂ F)
.congr_equiv e

中文:
引理 withSeminorms
  结论: WithSeminorms (PointwiseConvergenceCLM.seminormFamily σ E F)
  证明: let e : E ≃ (Σ _ : E, Fin 1) := .symm .sigmaUnique _ _
(isInducing_inducingFn σ E F).withSeminorms withSeminorms_pi (fun _ => norm_withSeminorms 𝕜₂ F)
.congr_equiv e

Depends on / 依赖: congr_equiv, isInducing_inducingFn, norm_withSeminorms, sigmaUnique, withSeminorms, withSeminorms_pi
-/
lemma withSeminorms : WithSeminorms (PointwiseConvergenceCLM.seminormFamily σ E F) :=
let e : E ≃ (Σ _ : E, Fin 1) := .symm .sigmaUnique _ _
(isInducing_inducingFn σ E F).withSeminorms withSeminorms_pi (fun _ => norm_withSeminorms 𝕜₂ F)
.congr_equiv e

section Tendsto

open Filter
open scoped Topology

/--
theorem `tendsto_nhds` / 定理 `tendsto_nhds`

English:
theorem tendsto_nhds
  given: {f : Filter α} (u : α -> E ->SLₚₜ[σ] F) (y₀ : E ->SLₚₜ[σ] F)
  proof: PointwiseConvergenceCLM.withSeminorms.tendsto_nhds _ _

中文:
定理 tendsto_nhds
  条件: {f : 滤子 α} (u : α -> E ->SLₚₜ[σ] F) (y₀ : E ->SLₚₜ[σ] F)
  证明: PointwiseConvergenceCLM.withSeminorms.tendsto_nhds _ _

Depends on / 依赖: PointwiseConvergenceCLM, PointwiseConvergenceCLM.withSeminorms.tendsto_nhds, tendsto_nhds, withSeminorms
-/
theorem tendsto_nhds {f : Filter α} (u : α -> E ->SLₚₜ[σ] F) (y₀ : E ->SLₚₜ[σ] F) :
    Tendsto u f (𝓝 y₀) ↔ forall (x : E) (ε : Real), 0 < ε -> forallᶠ (k : α) in f, ‖u k x - y₀ x‖ < ε :=
  PointwiseConvergenceCLM.withSeminorms.tendsto_nhds _ _

/--
theorem `tendsto_nhds_atTop` / 定理 `tendsto_nhds_atTop`

English:
theorem tendsto_nhds_atTop
  statement: [SemilatticeSup α] [Nonempty α] (u : α -> E ->SLₚₜ[σ] F)
  proof: PointwiseConvergenceCLM.withSeminorms.tendsto_nhds_atTop _ _

中文:
定理 tendsto_nhds_atTop
  结论: [SemilatticeSup α] [非空 α] (u : α -> E ->SLₚₜ[σ] F)
  证明: PointwiseConvergenceCLM.withSeminorms.tendsto_nhds_atTop _ _

Depends on / 依赖: PointwiseConvergenceCLM, PointwiseConvergenceCLM.withSeminorms.tendsto_nhds_atTop, tendsto_nhds_atTop, withSeminorms
-/
theorem tendsto_nhds_atTop [SemilatticeSup α] [Nonempty α] (u : α -> E ->SLₚₜ[σ] F)
    (y₀ : E ->SLₚₜ[σ] F) :
    Tendsto u atTop (𝓝 y₀) ↔
      forall (x : E) (ε : Real), 0 < ε -> exists (k₀ : α), forall (k : α), k₀ <= k -> ‖u k x - y₀ x‖ < ε :=
  PointwiseConvergenceCLM.withSeminorms.tendsto_nhds_atTop _ _

end Tendsto

section ContinuousLinearMap

variable [AddCommGroup D] [TopologicalSpace D] [Module 𝕜₃ D]
  [NormedAddCommGroup G] [NormedSpace 𝕜₂ G]

open NNReal ContinuousLinearMap

variable (F G) in
/--
Definition of `mkCLM` / `mkCLM` 的定义

English:
definition mkCLM
  signature: (A : (E ->SL[σ] F) ->ₗ[𝕜₂] D ->SL[τ] G) (hbound : forall (f : D), exists (s : Finset E) (C : Real>=0),
  body: (toUniformConvergenceCLM _ _ _).toLinearMap.comp
    (A.comp (toUniformConvergenceCLM _ _ _).symm.toLinearMap)
  cont := by
    apply PointwiseConvergenceCLM.withSeminorms.continuous_of_isBounded
      PointwiseConvergenceCLM.withSeminorms A
    intro f
    obtain ⟨s, C, h⟩ := hbound f
    use s, C


中文:
定义 mkCLM
  签名: (A : (E ->SL[σ] F) ->ₗ[𝕜₂] D ->SL[τ] G) (hbound : 对任意 (f : D), 存在 (s : 有限集 E) (C : 实数>=0),
  定义体: (toUniformConvergenceCLM _ _ _).toLinearMap.comp
    (A.comp (toUniformConvergenceCLM _ _ _).symm.toLinearMap)
  cont := by
    apply PointwiseConvergenceCLM.withSeminorms.continuous_of_isBounded
      PointwiseConvergenceCLM.withSeminorms A
    intro f
    obtain ⟨s, C, h⟩ := hbound f
    use s, C


Depends on / 依赖: toLinearMap, toLinearMap.comp, toUniformConvergenceCLM
-/
def mkCLM (A : (E ->SL[σ] F) ->ₗ[𝕜₂] D ->SL[τ] G) (hbound : forall (f : D), exists (s : Finset E) (C : Real>=0),
  forall (B : E ->SL[σ] F), exists (g : E) (_hb : g in s), ‖(A B) f‖ <= C • ‖B g‖) :
    (E ->SLₚₜ[σ] F) ->L[𝕜₂] D ->SLₚₜ[τ] G where
  __ := (toUniformConvergenceCLM _ _ _).toLinearMap.comp
    (A.comp (toUniformConvergenceCLM _ _ _).symm.toLinearMap)
  cont := by
    apply PointwiseConvergenceCLM.withSeminorms.continuous_of_isBounded
      PointwiseConvergenceCLM.withSeminorms A
    intro f
    obtain ⟨s, C, h⟩ := hbound f
    use s, C
    rw [← Seminorm.finset_sup_smul]
    intro B
    obtain ⟨g, h₁, h₂⟩ := h ((toUniformConvergenceCLM _ _ _).symm B)
    refine le_trans ?_ (Seminorm.le_finset_sup_apply h₁)
    exact h₂

end ContinuousLinearMap

end NormedSpace

section IsTopologicalAddGroup

variable [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [Module 𝕜₂ F]
  [Semiring R] [PartialOrder R]
  [Module R F] [ContinuousConstSMul R F] [LocallyConvexSpace R F] [SMulCommClass 𝕜₂ R F]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LocallyConvexSpace R (E ->SLₚₜ[σ] F)
  body: UniformConvergenceCLM.locallyConvexSpace R {(s : Set E) | Set.Finite s} ⟨∅, Set.finite_empty⟩
    (directedOn_of_sup_mem fun _ _ => Set.Finite.union)

中文:
实例 :
  签名: LocallyConvex空间 R (E ->SLₚₜ[σ] F)
  定义体: UniformConvergenceCLM.locallyConvexSpace R {(s : Set E) | Set.Finite s} ⟨∅, Set.finite_empty⟩
    (directedOn_of_sup_mem fun _ _ => Set.Finite.union)

Depends on / 依赖: Finite, Set.Finite, Set.Finite.union, Set.finite_empty, UniformConvergenceCLM, UniformConvergenceCLM.locallyConvexSpace, directedOn_of_sup_mem, finite_empty, locallyConvexSpace
-/
instance : LocallyConvexSpace R (E ->SLₚₜ[σ] F) :=
  UniformConvergenceCLM.locallyConvexSpace R {(s : Set E) | Set.Finite s} ⟨∅, Set.finite_empty⟩
    (directedOn_of_sup_mem fun _ _ => Set.Finite.union)

end IsTopologicalAddGroup

end PointwiseConvergenceCLM
