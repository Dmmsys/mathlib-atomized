/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Topology.Algebra.SeparationQuotient.Basic
public import Mathlib.Topology.Maps.OpenQuotient

/-!
# Algebraic operations on `SeparationQuotient`

In this file we construct a section of the quotient map `E → SeparationQuotient E` as a continuous
linear map `SeparationQuotient E →L[K] E`.
-/

@[expose] public section

open Topology

namespace SeparationQuotient
section VectorSpace

variable (K E : Type*) [DivisionRing K] [AddCommGroup E] [Module K E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul K E]

/--
theorem `exists_out_continuousLinearMap` / 定理 `exists_out_continuousLinearMap`

English:
theorem exists_out_continuousLinearMap
  proof: by
  rcases (mkCLM K E).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr surjective_mk) with ⟨f, hf⟩
  replace hf : mk ∘ f = id := congr_arg DFunLike.coe hf
  exact ⟨⟨f, isInducing_mk.continuous_iff.2 (by continuity)⟩, DFunLike.ext' hf⟩

中文:
定理 存在_out_continuousLinearMap
  证明: by
  rcases (mkCLM K E).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr surjective_mk) with ⟨f, hf⟩
  replace hf : mk ∘ f = id := congr_arg DFunLike.coe hf
  exact ⟨⟨f, isInducing_mk.continuous_iff.2 (by continuity)⟩, DFunLike.ext' hf⟩

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.ext, LinearMap, LinearMap.range_eq_top.mpr, congr_arg, continuity, continuous_iff, exists_rightInverse_of_surjective, isInducing_mk, isInducing_mk.continuous_iff, range_eq_top, replace, surjective_mk, toLinearMap, toLinearMap.exists_rightInverse_of_surjective
-/
theorem exists_out_continuousLinearMap :
    exists f : SeparationQuotient E ->L[K] E, mkCLM K E ∘L f = .id K (SeparationQuotient E) := by
  rcases (mkCLM K E).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr surjective_mk) with ⟨f, hf⟩
  replace hf : mk ∘ f = id := congr_arg DFunLike.coe hf
  exact ⟨⟨f, isInducing_mk.continuous_iff.2 (by continuity)⟩, DFunLike.ext' hf⟩

/--
Definition of `outCLM` / `outCLM` 的定义

English:
definition outCLM
  signature: : SeparationQuotient E ->L[K] E
  body: (exists_out_continuousLinearMap K E).choose

@[simp]

中文:
定义 outCLM
  签名: : SeparationQuotient E ->L[K] E
  定义体: (exists_out_continuousLinearMap K E).choose

@[simp]

Depends on / 依赖: exists_out_continuousLinearMap
-/
noncomputable def outCLM : SeparationQuotient E ->L[K] E :=
  (exists_out_continuousLinearMap K E).choose

@[simp]
/--
theorem `mkCLM_comp_outCLM` / 定理 `mkCLM_comp_outCLM`

English:
theorem mkCLM_comp_outCLM
  statement: mkCLM K E ∘L outCLM K E = .id K (SeparationQuotient E)
  proof: (exists_out_continuousLinearMap K E).choose_spec

中文:
定理 mkCLM_comp_outCLM
  结论: mkCLM K E ∘L outCLM K E = .id K (SeparationQuotient E)
  证明: (exists_out_continuousLinearMap K E).choose_spec

Depends on / 依赖: choose_spec, exists_out_continuousLinearMap
-/
theorem mkCLM_comp_outCLM : mkCLM K E ∘L outCLM K E = .id K (SeparationQuotient E) :=
  (exists_out_continuousLinearMap K E).choose_spec

variable {E} in
@[simp]
/--
theorem `mk_outCLM` / 定理 `mk_outCLM`

English:
theorem mk_outCLM
  given: (x : SeparationQuotient E)
  statement: mk (outCLM K E x) = x
  proof: DFunLike.congr_fun (mkCLM_comp_outCLM K E) x

@[simp]

中文:
定理 mk_outCLM
  条件: (x : SeparationQuotient E)
  结论: mk (outCLM K E x) = x
  证明: DFunLike.congr_fun (mkCLM_comp_outCLM K E) x

@[simp]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, mkCLM_comp_outCLM
-/
theorem mk_outCLM (x : SeparationQuotient E) : mk (outCLM K E x) = x :=
  DFunLike.congr_fun (mkCLM_comp_outCLM K E) x

@[simp]
/--
theorem `mk_comp_outCLM` / 定理 `mk_comp_outCLM`

English:
theorem mk_comp_outCLM
  statement: mk ∘ outCLM K E = id
  proof: funext (mk_outCLM K)

中文:
定理 mk_comp_outCLM
  结论: mk ∘ outCLM K E = id
  证明: funext (mk_outCLM K)

Depends on / 依赖: mk_outCLM
-/
theorem mk_comp_outCLM : mk ∘ outCLM K E = id := funext (mk_outCLM K)

variable {K} in
/--
theorem `postcomp_mkCLM_surjective` / 定理 `postcomp_mkCLM_surjective`

English:
theorem postcomp_mkCLM_surjective
  statement: {L : Type*} [Semiring L] (σ : L ->+* K)
  proof: by
  intro f
  use (outCLM K E).comp f
  rw [← ContinuousLinearMap.comp_assoc]; rw [mkCLM_comp_outCLM]; rw [ContinuousLinearMap.id_comp]

中文:
定理 postcomp_mkCLM_surjective
  结论: {L : 类型} [半环 L] (σ : L ->+* K)
  证明: by
  intro f
  use (outCLM K E).comp f
  rw [← ContinuousLinearMap.comp_assoc]; rw [mkCLM_comp_outCLM]; rw [ContinuousLinearMap.id_comp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_assoc, ContinuousLinearMap.id_comp, comp_assoc, id_comp, mkCLM_comp_outCLM, outCLM
-/
theorem postcomp_mkCLM_surjective {L : Type*} [Semiring L] (σ : L ->+* K)
    (F : Type*) [AddCommMonoid F] [Module L F] [TopologicalSpace F] :
    Function.Surjective ((mkCLM K E).comp : (F ->SL[σ] E) -> (F ->SL[σ] SeparationQuotient E)) := by
  intro f
  use (outCLM K E).comp f
  rw [← ContinuousLinearMap.comp_assoc]; rw [mkCLM_comp_outCLM]; rw [ContinuousLinearMap.id_comp]

/--
theorem `isEmbedding_outCLM` / 定理 `isEmbedding_outCLM`

English:
theorem isEmbedding_outCLM
  statement: IsEmbedding (outCLM K E)
  proof: Function.LeftInverse.isEmbedding (mk_outCLM K) continuous_mk (map_continuous _)

中文:
定理 isEmbedding_outCLM
  结论: 是嵌入 (outCLM K E)
  证明: Function.LeftInverse.isEmbedding (mk_outCLM K) continuous_mk (map_continuous _)

Depends on / 依赖: Function, Function.LeftInverse.isEmbedding, LeftInverse, continuous_mk, isEmbedding, map_continuous, mk_outCLM
-/
theorem isEmbedding_outCLM : IsEmbedding (outCLM K E) :=
  Function.LeftInverse.isEmbedding (mk_outCLM K) continuous_mk (map_continuous _)

/--
theorem `outCLM_injective` / 定理 `outCLM_injective`

English:
theorem outCLM_injective
  statement: Function.Injective (outCLM K E)
  proof: (isEmbedding_outCLM K E).injective

中文:
定理 outCLM_injective
  结论: 函数.单射 (outCLM K E)
  证明: (isEmbedding_outCLM K E).injective

Depends on / 依赖: injective, isEmbedding_outCLM
-/
theorem outCLM_injective : Function.Injective (outCLM K E) :=
  (isEmbedding_outCLM K E).injective

end VectorSpace

section VectorSpaceUniform

variable (K E : Type*) [DivisionRing K] [AddCommGroup E] [Module K E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousConstSMul K E]

@[fun_prop]
/--
theorem `outCLM_isUniformInducing` / 定理 `outCLM_isUniformInducing`

English:
theorem outCLM_isUniformInducing
  statement: IsUniformInducing (outCLM K E)
  proof: by
  rw [← isUniformInducing_mk.of_comp_iff]; rw [mk_comp_outCLM]
  exact .id

@[fun_prop]

中文:
定理 outCLM_isUniformInducing
  结论: 是UniformInducing (outCLM K E)
  证明: by
  rw [← isUniformInducing_mk.of_comp_iff]; rw [mk_comp_outCLM]
  exact .id

@[fun_prop]

Depends on / 依赖: isUniformInducing_mk, isUniformInducing_mk.of_comp_iff, mk_comp_outCLM, of_comp_iff
-/
theorem outCLM_isUniformInducing : IsUniformInducing (outCLM K E) := by
  rw [← isUniformInducing_mk.of_comp_iff]; rw [mk_comp_outCLM]
  exact .id

@[fun_prop]
/--
theorem `outCLM_isUniformEmbedding` / 定理 `outCLM_isUniformEmbedding`

English:
theorem outCLM_isUniformEmbedding
  statement: IsUniformEmbedding (outCLM K E) where
  proof: outCLM_injective K E
  toIsUniformInducing := outCLM_isUniformInducing K E

@[fun_prop]

中文:
定理 outCLM_isUniformEmbedding
  结论: 是一致嵌入 (outCLM K E) where
  证明: outCLM_injective K E
  toIsUniformInducing := outCLM_isUniformInducing K E

@[fun_prop]

Depends on / 依赖: outCLM_injective
-/
theorem outCLM_isUniformEmbedding : IsUniformEmbedding (outCLM K E) where
  injective := outCLM_injective K E
  toIsUniformInducing := outCLM_isUniformInducing K E

@[fun_prop]
/--
theorem `outCLM_uniformContinuous` / 定理 `outCLM_uniformContinuous`

English:
theorem outCLM_uniformContinuous
  statement: UniformContinuous (outCLM K E)
  proof: (outCLM_isUniformInducing K E).uniformContinuous

中文:
定理 outCLM_uniformContinuous
  结论: 一致连续 (outCLM K E)
  证明: (outCLM_isUniformInducing K E).uniformContinuous

Depends on / 依赖: outCLM_isUniformInducing, uniformContinuous
-/
theorem outCLM_uniformContinuous : UniformContinuous (outCLM K E) :=
  (outCLM_isUniformInducing K E).uniformContinuous

end VectorSpaceUniform
end SeparationQuotient
