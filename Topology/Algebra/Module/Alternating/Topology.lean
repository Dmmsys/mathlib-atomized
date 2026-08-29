/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Algebra.Module.Multilinear.Topology
public import Mathlib.Topology.Algebra.Module.Alternating.Basic

/-!
# Topology on continuous alternating maps

In this file we define `UniformSpace` and `TopologicalSpace` structures
on the space of continuous alternating maps between topological vector spaces.

The structures are induced by those on `ContinuousMultilinearMap`s,
and most of the lemmas follow from the corresponding lemmas about `ContinuousMultilinearMap`s.
-/

@[expose] public section

open Bornology Function Set Topology
open scoped UniformConvergence Filter

namespace ContinuousAlternatingMap

variable {𝕜 E F ι : Type*} [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [AddCommGroup F] [Module 𝕜 F]

section IsClosedRange

variable [TopologicalSpace F] [IsTopologicalAddGroup F]

/--
Instance `instTopologicalSpace` / 实例 `instTopologicalSpace`

English:
instance instTopologicalSpace
  signature: : TopologicalSpace (E [⋀^ι]->L[𝕜] F)
  body: .induced toContinuousMultilinearMap inferInstance

中文:
实例 instTopologicalSpace
  签名: : TopologicalSpace (E [⋀^ι]->L[𝕜] F)
  定义体: .induced toContinuousMultilinearMap inferInstance

Depends on / 依赖: induced, toContinuousMultilinearMap
-/
instance instTopologicalSpace : TopologicalSpace (E [⋀^ι]->L[𝕜] F) :=
  .induced toContinuousMultilinearMap inferInstance

/--
lemma `isClosed_range_toContinuousMultilinearMap` / 引理 `isClosed_range_toContinuousMultilinearMap`

English:
lemma isClosed_range_toContinuousMultilinearMap
  given: [ContinuousSMul 𝕜 E] [T2Space F]
  proof: by
  simp only [range_toContinuousMultilinearMap, ofPred_forall]
  repeat refine isClosed_iInter fun _ => ?_
  exact isClosed_singleton.preimage (continuous_eval_const _)

中文:
引理 isClosed_range_toContinuousMultilinearMap
  条件: [ContinuousSMul 𝕜 E] [T2Space F]
  证明: by
  simp only [range_toContinuousMultilinearMap, ofPred_forall]
  repeat refine isClosed_iInter fun _ => ?_
  exact isClosed_singleton.preimage (continuous_eval_const _)

Depends on / 依赖: continuous_eval_const, isClosed_iInter, isClosed_singleton, isClosed_singleton.preimage, ofPred_forall, preimage, range_toContinuousMultilinearMap, repeat
-/
lemma isClosed_range_toContinuousMultilinearMap [ContinuousSMul 𝕜 E] [T2Space F] :
    IsClosed (Set.range (toContinuousMultilinearMap : (E [⋀^ι]->L[𝕜] F) ->
      ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F)) := by
  simp only [range_toContinuousMultilinearMap, ofPred_forall]
  repeat refine isClosed_iInter fun _ => ?_
  exact isClosed_singleton.preimage (continuous_eval_const _)

end IsClosedRange

section IsUniformAddGroup

variable [UniformSpace F] [IsUniformAddGroup F]

/--
Instance `instUniformSpace` / 实例 `instUniformSpace`

English:
instance instUniformSpace
  signature: : UniformSpace (E [⋀^ι]->L[𝕜] F)
  body: .comap toContinuousMultilinearMap inferInstance

中文:
实例 instUniformSpace
  签名: : UniformSpace (E [⋀^ι]->L[𝕜] F)
  定义体: .comap toContinuousMultilinearMap inferInstance

Depends on / 依赖: toContinuousMultilinearMap
-/
instance instUniformSpace : UniformSpace (E [⋀^ι]->L[𝕜] F) :=
  .comap toContinuousMultilinearMap inferInstance

/--
lemma `isUniformEmbedding_toContinuousMultilinearMap` / 引理 `isUniformEmbedding_toContinuousMultilinearMap`

English:
lemma isUniformEmbedding_toContinuousMultilinearMap
  proof: toContinuousMultilinearMap_injective
  comap_uniformity := rfl

中文:
引理 isUniformEmbedding_toContinuousMultilinearMap
  证明: toContinuousMultilinearMap_injective
  comap_uniformity := rfl

Depends on / 依赖: toContinuousMultilinearMap_injective
-/
lemma isUniformEmbedding_toContinuousMultilinearMap :
    IsUniformEmbedding (toContinuousMultilinearMap : (E [⋀^ι]->L[𝕜] F) -> _) where
  injective := toContinuousMultilinearMap_injective
  comap_uniformity := rfl

/--
lemma `uniformContinuous_toContinuousMultilinearMap` / 引理 `uniformContinuous_toContinuousMultilinearMap`

English:
lemma uniformContinuous_toContinuousMultilinearMap
  proof: isUniformEmbedding_toContinuousMultilinearMap.uniformContinuous

中文:
引理 uniformContinuous_toContinuousMultilinearMap
  证明: isUniformEmbedding_toContinuousMultilinearMap.uniformContinuous

Depends on / 依赖: isUniformEmbedding_toContinuousMultilinearMap, isUniformEmbedding_toContinuousMultilinearMap.uniformContinuous, uniformContinuous
-/
lemma uniformContinuous_toContinuousMultilinearMap :
    UniformContinuous (toContinuousMultilinearMap : (E [⋀^ι]->L[𝕜] F) -> _) :=
  isUniformEmbedding_toContinuousMultilinearMap.uniformContinuous

/--
theorem `uniformContinuous_coe_fun` / 定理 `uniformContinuous_coe_fun`

English:
theorem uniformContinuous_coe_fun
  given: [ContinuousSMul 𝕜 E]
  proof: ContinuousMultilinearMap.uniformContinuous_coe_fun.comp
    uniformContinuous_toContinuousMultilinearMap

中文:
定理 uniformContinuous_coe_fun
  条件: [ContinuousSMul 𝕜 E]
  证明: ContinuousMultilinearMap.uniformContinuous_coe_fun.comp
    uniformContinuous_toContinuousMultilinearMap

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.uniformContinuous_coe_fun.comp, uniformContinuous_coe_fun, uniformContinuous_toContinuousMultilinearMap
-/
theorem uniformContinuous_coe_fun [ContinuousSMul 𝕜 E] :
    UniformContinuous (DFunLike.coe : (E [⋀^ι]->L[𝕜] F) -> (ι -> E) -> F) :=
  ContinuousMultilinearMap.uniformContinuous_coe_fun.comp
    uniformContinuous_toContinuousMultilinearMap

/--
theorem `uniformContinuous_eval_const` / 定理 `uniformContinuous_eval_const`

English:
theorem uniformContinuous_eval_const
  given: [ContinuousSMul 𝕜 E] (x : ι -> E)
  proof: uniformContinuous_pi.1 uniformContinuous_coe_fun x

中文:
定理 uniformContinuous_eval_const
  条件: [ContinuousSMul 𝕜 E] (x : ι -> E)
  证明: uniformContinuous_pi.1 uniformContinuous_coe_fun x

Depends on / 依赖: uniformContinuous_coe_fun, uniformContinuous_pi
-/
theorem uniformContinuous_eval_const [ContinuousSMul 𝕜 E] (x : ι -> E) :
    UniformContinuous fun f : E [⋀^ι]->L[𝕜] F => f x :=
  uniformContinuous_pi.1 uniformContinuous_coe_fun x

/--
Instance `instIsUniformAddGroup` / 实例 `instIsUniformAddGroup`

English:
instance instIsUniformAddGroup
  signature: : IsUniformAddGroup (E [⋀^ι]->L[𝕜] F)
  body: isUniformEmbedding_toContinuousMultilinearMap.isUniformAddGroup
    (toContinuousMultilinearMapLinear (R := Nat))

中文:
实例 instIsUniformAddGroup
  签名: : IsUniformAddGroup (E [⋀^ι]->L[𝕜] F)
  定义体: isUniformEmbedding_toContinuousMultilinearMap.isUniformAddGroup
    (toContinuousMultilinearMapLinear (R := Nat))

Depends on / 依赖: isUniformAddGroup, isUniformEmbedding_toContinuousMultilinearMap, isUniformEmbedding_toContinuousMultilinearMap.isUniformAddGroup, toContinuousMultilinearMapLinear
-/
instance instIsUniformAddGroup : IsUniformAddGroup (E [⋀^ι]->L[𝕜] F) :=
  isUniformEmbedding_toContinuousMultilinearMap.isUniformAddGroup
    (toContinuousMultilinearMapLinear (R := Nat))

/--
Instance `instUniformContinuousConstSMul` / 实例 `instUniformContinuousConstSMul`

English:
instance instUniformContinuousConstSMul
  signature: {M : Type*}
  body: isUniformEmbedding_toContinuousMultilinearMap.uniformContinuousConstSMul fun _ _ => rfl

中文:
实例 instUniformContinuousConstSMul
  签名: {M : 类型}
  定义体: isUniformEmbedding_toContinuousMultilinearMap.uniformContinuousConstSMul fun _ _ => rfl

Depends on / 依赖: isUniformEmbedding_toContinuousMultilinearMap, isUniformEmbedding_toContinuousMultilinearMap.uniformContinuousConstSMul, uniformContinuousConstSMul
-/
instance instUniformContinuousConstSMul {M : Type*}
    [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜 M F] [ContinuousConstSMul M F] :
    UniformContinuousConstSMul M (E [⋀^ι]->L[𝕜] F) :=
  isUniformEmbedding_toContinuousMultilinearMap.uniformContinuousConstSMul fun _ _ => rfl

/--
theorem `isUniformInducing_postcomp` / 定理 `isUniformInducing_postcomp`

English:
theorem isUniformInducing_postcomp
  statement: {G : Type*} [AddCommGroup G] [UniformSpace G]
  proof: by
  rw [← isUniformEmbedding_toContinuousMultilinearMap.1.of_comp_iff]
  exact (ContinuousMultilinearMap.isUniformInducing_postcomp g hg).comp
    isUniformEmbedding_toContinuousMultilinearMap.1

中文:
定理 isUniformInducing_postcomp
  结论: {G : 类型} [AddCommGroup G] [UniformSpace G]
  证明: by
  rw [← isUniformEmbedding_toContinuousMultilinearMap.1.of_comp_iff]
  exact (ContinuousMultilinearMap.isUniformInducing_postcomp g hg).comp
    isUniformEmbedding_toContinuousMultilinearMap.1

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.isUniformInducing_postcomp, isUniformEmbedding_toContinuousMultilinearMap, isUniformInducing_postcomp, of_comp_iff
-/
theorem isUniformInducing_postcomp {G : Type*} [AddCommGroup G] [UniformSpace G]
    [IsUniformAddGroup G] [Module 𝕜 G] (g : F ->L[𝕜] G) (hg : IsUniformInducing g) :
    IsUniformInducing (g.compContinuousAlternatingMap : (E [⋀^ι]->L[𝕜] F) -> (E [⋀^ι]->L[𝕜] G)) := by
  rw [← isUniformEmbedding_toContinuousMultilinearMap.1.of_comp_iff]
  exact (ContinuousMultilinearMap.isUniformInducing_postcomp g hg).comp
    isUniformEmbedding_toContinuousMultilinearMap.1

section CompleteSpace

variable [ContinuousSMul 𝕜 E] [ContinuousConstSMul 𝕜 F] [CompleteSpace F]

open UniformOnFun in
/--
theorem `completeSpace` / 定理 `completeSpace`

English:
theorem completeSpace
  given: (h : IsCoherentWith {s : Set (ι -> E) | IsVonNBounded 𝕜 s})
  proof: by
  wlog hF : T2Space F generalizing F
  · rw [(isUniformInducing_postcomp (SeparationQuotient.mkCLM _ _)
      SeparationQuotient.isUniformInducing_mk).completeSpace_congr]
    · exact this inferInstance
    · intro f
      use (SeparationQuotient.outCLM _ _).compContinuousAlternatingMap f
      e

中文:
定理 completeSpace
  条件: (h : IsCoherentWith {s : Set (ι -> E) | IsVonNBounded 𝕜 s})
  证明: by
  wlog hF : T2Space F generalizing F
  · rw [(isUniformInducing_postcomp (SeparationQuotient.mkCLM _ _)
      SeparationQuotient.isUniformInducing_mk).completeSpace_congr]
    · exact this inferInstance
    · intro f
      use (SeparationQuotient.outCLM _ _).compContinuousAlternatingMap f
      e

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.completeSpace, SeparationQuotient, SeparationQuotient.isUniformInducing_mk, SeparationQuotient.mkCLM, SeparationQuotient.outCLM, T2Space, compContinuousAlternatingMap, completeSpace, completeSpace_congr, completeSpace_iff_isComplete_range, generalizing, isClosed_range_toContinuousMultilinearMap, isClosed_range_toContinuousMultilinearMap.isComplete, isComplete, isUniformEmbedding_toContinuousMultilinearMap, isUniformEmbedding_toContinuousMultilinearMap.isUniformInducing, isUniformInducing, isUniformInducing_mk, isUniformInducing_postcomp
-/
theorem completeSpace (h : IsCoherentWith {s : Set (ι -> E) | IsVonNBounded 𝕜 s}) :
    CompleteSpace (E [⋀^ι]->L[𝕜] F) := by
  wlog hF : T2Space F generalizing F
  · rw [(isUniformInducing_postcomp (SeparationQuotient.mkCLM _ _)
      SeparationQuotient.isUniformInducing_mk).completeSpace_congr]
    · exact this inferInstance
    · intro f
      use (SeparationQuotient.outCLM _ _).compContinuousAlternatingMap f
      ext
      simp
  have := ContinuousMultilinearMap.completeSpace (F := F) h
  rw [completeSpace_iff_isComplete_range
    isUniformEmbedding_toContinuousMultilinearMap.isUniformInducing]
  apply isClosed_range_toContinuousMultilinearMap.isComplete

/--
Instance `instCompleteSpace` / 实例 `instCompleteSpace`

English:
instance instCompleteSpace
  signature: [IsTopologicalAddGroup E] [SequentialSpace (ι -> E)]
  body: completeSpace .of_seq fun _u x hux => (hux.isVonNBounded_range 𝕜).insert x

中文:
实例 instCompleteSpace
  签名: [IsTopologicalAddGroup E] [SequentialSpace (ι -> E)]
  定义体: completeSpace .of_seq fun _u x hux => (hux.isVonNBounded_range 𝕜).insert x

Depends on / 依赖: completeSpace, hux.isVonNBounded_range, insert, isVonNBounded_range, of_seq
-/
instance instCompleteSpace [IsTopologicalAddGroup E] [SequentialSpace (ι -> E)] :
    CompleteSpace (E [⋀^ι]->L[𝕜] F) :=
completeSpace .of_seq fun _u x hux => (hux.isVonNBounded_range 𝕜).insert x

end CompleteSpace

section RestrictScalars

variable (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
  [Module 𝕜' E] [IsScalarTower 𝕜' 𝕜 E] [Module 𝕜' F] [IsScalarTower 𝕜' 𝕜 F] [ContinuousSMul 𝕜 E]

/--
theorem `isUniformEmbedding_restrictScalars` / 定理 `isUniformEmbedding_restrictScalars`

English:
theorem isUniformEmbedding_restrictScalars
  proof: by
  rw [← isUniformEmbedding_toContinuousMultilinearMap.of_comp_iff]
  exact (ContinuousMultilinearMap.isUniformEmbedding_restrictScalars 𝕜').comp
    isUniformEmbedding_toContinuousMultilinearMap

中文:
定理 isUniformEmbedding_restrictScalars
  证明: by
  rw [← isUniformEmbedding_toContinuousMultilinearMap.of_comp_iff]
  exact (ContinuousMultilinearMap.isUniformEmbedding_restrictScalars 𝕜').comp
    isUniformEmbedding_toContinuousMultilinearMap

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.isUniformEmbedding_restrictScalars, isUniformEmbedding_restrictScalars, isUniformEmbedding_toContinuousMultilinearMap, isUniformEmbedding_toContinuousMultilinearMap.of_comp_iff, of_comp_iff
-/
theorem isUniformEmbedding_restrictScalars :
    IsUniformEmbedding (restrictScalars 𝕜' : E [⋀^ι]->L[𝕜] F -> E [⋀^ι]->L[𝕜'] F) := by
  rw [← isUniformEmbedding_toContinuousMultilinearMap.of_comp_iff]
  exact (ContinuousMultilinearMap.isUniformEmbedding_restrictScalars 𝕜').comp
    isUniformEmbedding_toContinuousMultilinearMap

/--
theorem `uniformContinuous_restrictScalars` / 定理 `uniformContinuous_restrictScalars`

English:
theorem uniformContinuous_restrictScalars
  proof: (isUniformEmbedding_restrictScalars 𝕜').uniformContinuous

中文:
定理 uniformContinuous_restrictScalars
  证明: (isUniformEmbedding_restrictScalars 𝕜').uniformContinuous

Depends on / 依赖: isUniformEmbedding_restrictScalars, uniformContinuous
-/
theorem uniformContinuous_restrictScalars :
    UniformContinuous (restrictScalars 𝕜' : E [⋀^ι]->L[𝕜] F -> E [⋀^ι]->L[𝕜'] F) :=
  (isUniformEmbedding_restrictScalars 𝕜').uniformContinuous

end RestrictScalars

end IsUniformAddGroup

variable [TopologicalSpace F] [IsTopologicalAddGroup F]

/--
lemma `isEmbedding_toContinuousMultilinearMap` / 引理 `isEmbedding_toContinuousMultilinearMap`

English:
lemma isEmbedding_toContinuousMultilinearMap
  proof: letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  isUniformEmbedding_toContinuousMultilinearMap.isEmbedding

中文:
引理 isEmbedding_toContinuousMultilinearMap
  证明: letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  isUniformEmbedding_toContinuousMultilinearMap.isEmbedding

Depends on / 依赖: IsTopologicalAddGroup, IsTopologicalAddGroup.rightUniformSpace, isEmbedding, isUniformAddGroup_of_addCommGroup, isUniformEmbedding_toContinuousMultilinearMap, isUniformEmbedding_toContinuousMultilinearMap.isEmbedding, rightUniformSpace
-/
lemma isEmbedding_toContinuousMultilinearMap :
    IsEmbedding (toContinuousMultilinearMap : (E [⋀^ι]->L[𝕜] F -> _)) :=
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  isUniformEmbedding_toContinuousMultilinearMap.isEmbedding

/--
Instance `instIsTopologicalAddGroup` / 实例 `instIsTopologicalAddGroup`

English:
instance instIsTopologicalAddGroup
  signature: : IsTopologicalAddGroup (E [⋀^ι]->L[𝕜] F)
  body: isEmbedding_toContinuousMultilinearMap.topologicalAddGroup
    (toContinuousMultilinearMapLinear (R := Nat))

@[continuity, fun_prop]

中文:
实例 instIsTopologicalAddGroup
  签名: : IsTopologicalAddGroup (E [⋀^ι]->L[𝕜] F)
  定义体: isEmbedding_toContinuousMultilinearMap.topologicalAddGroup
    (toContinuousMultilinearMapLinear (R := Nat))

@[continuity, fun_prop]

Depends on / 依赖: isEmbedding_toContinuousMultilinearMap, isEmbedding_toContinuousMultilinearMap.topologicalAddGroup, toContinuousMultilinearMapLinear, topologicalAddGroup
-/
instance instIsTopologicalAddGroup : IsTopologicalAddGroup (E [⋀^ι]->L[𝕜] F) :=
  isEmbedding_toContinuousMultilinearMap.topologicalAddGroup
    (toContinuousMultilinearMapLinear (R := Nat))

@[continuity, fun_prop]
/--
lemma `continuous_toContinuousMultilinearMap` / 引理 `continuous_toContinuousMultilinearMap`

English:
lemma continuous_toContinuousMultilinearMap
  proof: isEmbedding_toContinuousMultilinearMap.continuous

中文:
引理 continuous_toContinuousMultilinearMap
  证明: isEmbedding_toContinuousMultilinearMap.continuous

Depends on / 依赖: continuous, isEmbedding_toContinuousMultilinearMap, isEmbedding_toContinuousMultilinearMap.continuous
-/
lemma continuous_toContinuousMultilinearMap :
    Continuous (toContinuousMultilinearMap : (E [⋀^ι]->L[𝕜] F -> _)) :=
  isEmbedding_toContinuousMultilinearMap.continuous

/--
Instance `instContinuousConstSMul` / 实例 `instContinuousConstSMul`

English:
instance instContinuousConstSMul
  body: isEmbedding_toContinuousMultilinearMap.continuousConstSMul id rfl

中文:
实例 instContinuousConstSMul
  定义体: isEmbedding_toContinuousMultilinearMap.continuousConstSMul id rfl

Depends on / 依赖: continuousConstSMul, isEmbedding_toContinuousMultilinearMap, isEmbedding_toContinuousMultilinearMap.continuousConstSMul
-/
instance instContinuousConstSMul
    {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜 M F] [ContinuousConstSMul M F] :
    ContinuousConstSMul M (E [⋀^ι]->L[𝕜] F) :=
  isEmbedding_toContinuousMultilinearMap.continuousConstSMul id rfl

/--
Instance `instContinuousSMul` / 实例 `instContinuousSMul`

English:
instance instContinuousSMul
  signature: [ContinuousSMul 𝕜 F]
  body: isEmbedding_toContinuousMultilinearMap.continuousSMul continuous_id rfl

中文:
实例 instContinuousSMul
  签名: [ContinuousSMul 𝕜 F]
  定义体: isEmbedding_toContinuousMultilinearMap.continuousSMul continuous_id rfl

Depends on / 依赖: continuousSMul, continuous_id, isEmbedding_toContinuousMultilinearMap, isEmbedding_toContinuousMultilinearMap.continuousSMul
-/
instance instContinuousSMul [ContinuousSMul 𝕜 F] : ContinuousSMul 𝕜 (E [⋀^ι]->L[𝕜] F) :=
  isEmbedding_toContinuousMultilinearMap.continuousSMul continuous_id rfl

/--
theorem `hasBasis_nhds_zero_of_basis` / 定理 `hasBasis_nhds_zero_of_basis`

English:
theorem hasBasis_nhds_zero_of_basis
  statement: {ι' : Type*} {p : ι' -> Prop} {b : ι' -> Set F}
  proof: by
  rw [nhds_induced]
  exact (ContinuousMultilinearMap.hasBasis_nhds_zero_of_basis h).comap _

中文:
定理 hasBasis_nhds_zero_of_basis
  结论: {ι' : 类型} {p : ι' -> 命题} {b : ι' -> Set F}
  证明: by
  rw [nhds_induced]
  exact (ContinuousMultilinearMap.hasBasis_nhds_zero_of_basis h).comap _

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.hasBasis_nhds_zero_of_basis, hasBasis_nhds_zero_of_basis, nhds_induced
-/
theorem hasBasis_nhds_zero_of_basis {ι' : Type*} {p : ι' -> Prop} {b : ι' -> Set F}
    (h : (𝓝 (0 : F)).HasBasis p b) :
    (𝓝 (0 : E [⋀^ι]->L[𝕜] F)).HasBasis
      (fun Si : Set (ι -> E) × ι' => IsVonNBounded 𝕜 Si.1 ∧ p Si.2)
      fun Si => { f | MapsTo f Si.1 (b Si.2) } := by
  rw [nhds_induced]
  exact (ContinuousMultilinearMap.hasBasis_nhds_zero_of_basis h).comap _

/--
theorem `hasBasis_nhds_zero` / 定理 `hasBasis_nhds_zero`

English:
theorem hasBasis_nhds_zero
  proof: hasBasis_nhds_zero_of_basis (Filter.basis_sets _)

中文:
定理 hasBasis_nhds_zero
  证明: hasBasis_nhds_zero_of_basis (Filter.basis_sets _)

Depends on / 依赖: Filter, Filter.basis_sets, basis_sets, hasBasis_nhds_zero_of_basis
-/
theorem hasBasis_nhds_zero :
    (𝓝 (0 : E [⋀^ι]->L[𝕜] F)).HasBasis
      (fun SV : Set (ι -> E) × Set F => IsVonNBounded 𝕜 SV.1 ∧ SV.2 in 𝓝 0)
      fun SV => { f | MapsTo f SV.1 SV.2 } :=
  hasBasis_nhds_zero_of_basis (Filter.basis_sets _)

/-- The inclusion of *alternating* continuous multilinear maps into continuous multilinear maps
as a continuous linear map. -/
@[simps! -fullyApplied]
/--
Definition of `toContinuousMultilinearMapCLM` / `toContinuousMultilinearMapCLM` 的定义

English:
definition toContinuousMultilinearMapCLM
  body: ⟨toContinuousMultilinearMapLinear, continuous_induced_dom⟩

中文:
定义 toContinuousMultilinearMapCLM
  定义体: ⟨toContinuousMultilinearMapLinear, continuous_induced_dom⟩

Depends on / 依赖: continuous_induced_dom, toContinuousMultilinearMapLinear
-/
def toContinuousMultilinearMapCLM
    (R : Type*) [Semiring R] [Module R F] [ContinuousConstSMul R F] [SMulCommClass 𝕜 R F] :
    E [⋀^ι]->L[𝕜] F ->L[R] ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F :=
  ⟨toContinuousMultilinearMapLinear, continuous_induced_dom⟩

section ContinuousSMul

variable [ContinuousSMul 𝕜 E]

/--
lemma `isClosedEmbedding_toContinuousMultilinearMap` / 引理 `isClosedEmbedding_toContinuousMultilinearMap`

English:
lemma isClosedEmbedding_toContinuousMultilinearMap
  given: [T2Space F]
  proof: ⟨isEmbedding_toContinuousMultilinearMap, isClosed_range_toContinuousMultilinearMap⟩

中文:
引理 isClosedEmbedding_toContinuousMultilinearMap
  条件: [T2Space F]
  证明: ⟨isEmbedding_toContinuousMultilinearMap, isClosed_range_toContinuousMultilinearMap⟩

Depends on / 依赖: isClosed_range_toContinuousMultilinearMap, isEmbedding_toContinuousMultilinearMap
-/
lemma isClosedEmbedding_toContinuousMultilinearMap [T2Space F] :
    IsClosedEmbedding (toContinuousMultilinearMap :
      (E [⋀^ι]->L[𝕜] F) -> ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) :=
  ⟨isEmbedding_toContinuousMultilinearMap, isClosed_range_toContinuousMultilinearMap⟩

/--
Instance `instContinuousEvalConst` / 实例 `instContinuousEvalConst`

English:
instance instContinuousEvalConst
  signature: : ContinuousEvalConst (E [⋀^ι]->L[𝕜] F) (ι -> E) F
  body: .of_continuous_forget continuous_toContinuousMultilinearMap

中文:
实例 instContinuousEvalConst
  签名: : ContinuousEvalConst (E [⋀^ι]->L[𝕜] F) (ι -> E) F
  定义体: .of_continuous_forget continuous_toContinuousMultilinearMap

Depends on / 依赖: continuous_toContinuousMultilinearMap, of_continuous_forget
-/
instance instContinuousEvalConst : ContinuousEvalConst (E [⋀^ι]->L[𝕜] F) (ι -> E) F :=
  .of_continuous_forget continuous_toContinuousMultilinearMap

/--
Instance `instT2Space` / 实例 `instT2Space`

English:
instance instT2Space
  signature: [T2Space F]
  body: .of_injective_continuous DFunLike.coe_injective continuous_coeFun

中文:
实例 instT2Space
  签名: [T2Space F]
  定义体: .of_injective_continuous DFunLike.coe_injective continuous_coeFun

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective, continuous_coeFun, of_injective_continuous
-/
instance instT2Space [T2Space F] : T2Space (E [⋀^ι]->L[𝕜] F) :=
  .of_injective_continuous DFunLike.coe_injective continuous_coeFun

/--
Instance `instT3Space` / 实例 `instT3Space`

English:
instance instT3Space
  signature: [T2Space F]
  body: inferInstance

中文:
实例 instT3Space
  签名: [T2Space F]
  定义体: inferInstance
-/
instance instT3Space [T2Space F] : T3Space (E [⋀^ι]->L[𝕜] F) :=
  inferInstance

section RestrictScalars

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
  [Module 𝕜' E] [IsScalarTower 𝕜' 𝕜 E] [Module 𝕜' F] [IsScalarTower 𝕜' 𝕜 F]

/--
theorem `isEmbedding_restrictScalars` / 定理 `isEmbedding_restrictScalars`

English:
theorem isEmbedding_restrictScalars
  proof: letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  (isUniformEmbedding_restrictScalars _).isEmbedding

@[continuity, fun_prop]

中文:
定理 isEmbedding_restrictScalars
  证明: letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  (isUniformEmbedding_restrictScalars _).isEmbedding

@[continuity, fun_prop]

Depends on / 依赖: IsTopologicalAddGroup, IsTopologicalAddGroup.rightUniformSpace, IsUniformAddGroup, UniformSpace, isEmbedding, isUniformAddGroup_of_addCommGroup, isUniformEmbedding_restrictScalars, rightUniformSpace
-/
theorem isEmbedding_restrictScalars :
    IsEmbedding (restrictScalars 𝕜' : E [⋀^ι]->L[𝕜] F -> E [⋀^ι]->L[𝕜'] F) :=
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  (isUniformEmbedding_restrictScalars _).isEmbedding

@[continuity, fun_prop]
/--
theorem `continuous_restrictScalars` / 定理 `continuous_restrictScalars`

English:
theorem continuous_restrictScalars
  proof: isEmbedding_restrictScalars.continuous

中文:
定理 continuous_restrictScalars
  证明: isEmbedding_restrictScalars.continuous

Depends on / 依赖: continuous, isEmbedding_restrictScalars, isEmbedding_restrictScalars.continuous
-/
theorem continuous_restrictScalars :
    Continuous (restrictScalars 𝕜' : E [⋀^ι]->L[𝕜] F -> E [⋀^ι]->L[𝕜'] F) :=
  isEmbedding_restrictScalars.continuous

variable (𝕜') in
/-- `ContinuousAlternatingMap.restrictScalars` as a `ContinuousLinearMap`. -/
@[simps -fullyApplied apply]
/--
Definition of `restrictScalarsCLM` / `restrictScalarsCLM` 的定义

English:
definition restrictScalarsCLM
  signature: [ContinuousConstSMul 𝕜' F]
  body: restrictScalars 𝕜'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 restrictScalarsCLM
  签名: [ContinuousConstSMul 𝕜' F]
  定义体: restrictScalars 𝕜'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: restrictScalars
-/
def restrictScalarsCLM [ContinuousConstSMul 𝕜' F] :
    E [⋀^ι]->L[𝕜] F ->L[𝕜'] E [⋀^ι]->L[𝕜'] F where
  toFun := restrictScalars 𝕜'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end RestrictScalars

end ContinuousSMul

section ContinuousConstSMul

variable {G : Type*} [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [ContinuousConstSMul 𝕜 F]

/--
Definition of `liftCLM` / `liftCLM` 的定义

English:
definition liftCLM
  signature: (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F)
  body: ⟨f x, hf x⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  cont := continuous_induced_rng.mpr (map_continuous f)

@[simp]

中文:
定义 liftCLM
  签名: (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F)
  定义体: ⟨f x, hf x⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  cont := continuous_induced_rng.mpr (map_continuous f)

@[simp]
-/
def liftCLM (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F)
    (hf : forall x v i j, v i = v j -> i != j -> f x v = 0) : G ->L[𝕜] (E [⋀^ι]->L[𝕜] F) where
  toFun x := ⟨f x, hf x⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  cont := continuous_induced_rng.mpr (map_continuous f)

@[simp]
/--
lemma `liftCLM_apply` / 引理 `liftCLM_apply`

English:
lemma liftCLM_apply
  statement: (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F)
  proof: rfl

中文:
引理 liftCLM_apply
  结论: (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F)
  证明: rfl
-/
lemma liftCLM_apply (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F)
    (hf : forall x v i j, v i = v j -> i != j -> f x v = 0) (x : G) (v : ι -> E) :
    liftCLM f hf x v = f x v :=
  rfl

section CompContinuousLinearMap

variable {E' : Type*} [AddCommGroup E'] [Module 𝕜 E'] [TopologicalSpace E']

/-- Composition of a continuous alternating map and a continuous linear map
as a bundled continuous linear map.

Note that for general topological vector spaces,
this function does not need to be continuous in `f`. -/
@[simps! apply]
/--
Definition of `compContinuousLinearMapCLM` / `compContinuousLinearMapCLM` 的定义

English:
definition compContinuousLinearMapCLM
  signature: (f : E ->L[𝕜] E')
  body: compContinuousLinearMapₗ f
  cont := by
    rw [isEmbedding_toContinuousMultilinearMap.continuous_iff]
    exact (map_continuous <| ContinuousMultilinearMap.compContinuousLinearMapL fun _ => f).comp
      continuous_toContinuousMultilinearMap

中文:
定义 compContinuousLinearMapCLM
  签名: (f : E ->L[𝕜] E')
  定义体: compContinuousLinearMapₗ f
  cont := by
    rw [isEmbedding_toContinuousMultilinearMap.continuous_iff]
    exact (map_continuous <| ContinuousMultilinearMap.compContinuousLinearMapL fun _ => f).comp
      continuous_toContinuousMultilinearMap
-/
def compContinuousLinearMapCLM (f : E ->L[𝕜] E') : (E' [⋀^ι]->L[𝕜] F) ->L[𝕜] (E [⋀^ι]->L[𝕜] F) where
  toLinearMap := compContinuousLinearMapₗ f
  cont := by
    rw [isEmbedding_toContinuousMultilinearMap.continuous_iff]
    exact (map_continuous <| ContinuousMultilinearMap.compContinuousLinearMapL fun _ => f).comp
      continuous_toContinuousMultilinearMap

end CompContinuousLinearMap

variable [ContinuousSMul 𝕜 E]
variable (𝕜 E F)

/--
Definition of `apply` / `apply` 的定义

English:
definition apply
  signature: (m : ι -> E)
  body: c m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 apply
  签名: (m : ι -> E)
  定义体: c m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
-/
def apply (m : ι -> E) : E [⋀^ι]->L[𝕜] F ->L[𝕜] F where
  toFun c := c m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {𝕜 E F}

@[simp]
/--
lemma `apply_apply` / 引理 `apply_apply`

English:
lemma apply_apply
  given: {m : ι -> E} {c : E [⋀^ι]->L[𝕜] F}
  statement: apply 𝕜 E F m c = c m
  proof: rfl

中文:
引理 apply_apply
  条件: {m : ι -> E} {c : E [⋀^ι]->L[𝕜] F}
  结论: apply 𝕜 E F m c = c m
  证明: rfl
-/
lemma apply_apply {m : ι -> E} {c : E [⋀^ι]->L[𝕜] F} : apply 𝕜 E F m c = c m := rfl

end ContinuousConstSMul

variable [ContinuousSMul 𝕜 E] {α : Type*} {p : α -> E [⋀^ι]->L[𝕜] F}

/--
theorem `hasSum_eval` / 定理 `hasSum_eval`

English:
theorem hasSum_eval
  given: {q : E [⋀^ι]->L[𝕜] F} (h : HasSum p q) (m : ι -> E)
  proof: h.map (applyAddHom m) (continuous_eval_const m)

中文:
定理 hasSum_eval
  条件: {q : E [⋀^ι]->L[𝕜] F} (h : HasSum p q) (m : ι -> E)
  证明: h.map (applyAddHom m) (continuous_eval_const m)

Depends on / 依赖: applyAddHom, continuous_eval_const, h.map
-/
theorem hasSum_eval {q : E [⋀^ι]->L[𝕜] F} (h : HasSum p q) (m : ι -> E) :
    HasSum (fun a => p a m) (q m) :=
  h.map (applyAddHom m) (continuous_eval_const m)

/--
theorem `tsum_eval` / 定理 `tsum_eval`

English:
theorem tsum_eval
  given: [T2Space F] (hp : Summable p) (m : ι -> E)
  statement: (∑' a, p a) m = ∑' a, p a m
  proof: (hasSum_eval hp.hasSum m).tsum_eq.symm

中文:
定理 tsum_eval
  条件: [T2Space F] (hp : Summable p) (m : ι -> E)
  结论: (∑' a, p a) m = ∑' a, p a m
  证明: (hasSum_eval hp.hasSum m).tsum_eq.symm

Depends on / 依赖: hasSum, hasSum_eval, hp.hasSum, tsum_eq, tsum_eq.symm
-/
theorem tsum_eval [T2Space F] (hp : Summable p) (m : ι -> E) : (∑' a, p a) m = ∑' a, p a m :=
  (hasSum_eval hp.hasSum m).tsum_eq.symm

end ContinuousAlternatingMap

namespace ContinuousLinearMap
variable (𝕜 E F G ι : Type*) [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousSMul 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul 𝕜 F]
  [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousConstSMul 𝕜 G]

/-- `ContinuousLinearMap.compContinuousAlternatingMap` as a bundled continuous bilinear map.

Given a continuous linear map `g : F →L[𝕜] G` and a continuous alternating map `f : E [⋀^ι]→L[𝕜] F`,
it returns the continuous alternating map `g ∘ f`.
This function is continuous in `f` (for each `g`)
and in `g` (as a function taking values in continuous linear maps).
Note that for a general topological vector space,
the map is not guaranteed to be continuous in `(g, f)`.
-/
@[simps! apply_apply]
/--
Definition of `compContinuousAlternatingMapCLM` / `compContinuousAlternatingMapCLM` 的定义

English:
definition compContinuousAlternatingMapCLM
  signature: :
  body: { toLinearMap := compContinuousAlternatingMapₗ _ _ _ _ g
      cont := by
        rw [ContinuousAlternatingMap.isEmbedding_toContinuousMultilinearMap.continuous_iff]
        exact (map_continuous <| compContinuousMultilinearMapL 𝕜 (fun _ : ι => E) F G g).comp
          ContinuousAlternatingMap.conti

中文:
定义 compContinuousAlternatingMapCLM
  签名: :
  定义体: { toLinearMap := compContinuousAlternatingMapₗ _ _ _ _ g
      cont := by
        rw [ContinuousAlternatingMap.isEmbedding_toContinuousMultilinearMap.continuous_iff]
        exact (map_continuous <| compContinuousMultilinearMapL 𝕜 (fun _ : ι => E) F G g).comp
          ContinuousAlternatingMap.conti

Depends on / 依赖: Contin, ContinuousAlternatingMap, ContinuousAlternatingMap.continuous_toContinuousMultilinearMap, ContinuousAlternatingMap.isEmbedding_toContinuousMultilinearMap.continuous_iff, ContinuousAlternatingMap.toContinuousMultilinearMapCLM, ContinuousLinearMap, ContinuousLinearMap.isEmbedding_postcomp, compContinuousMultilinearMapL, continuous_iff, continuous_toContinuousMultilinearMap, isEmbedding_postcomp, isEmbedding_toContinuousMultilinearMap, map_add, map_continuous, map_smul, toContinuousMultilinearMapCLM, toLinearMap
-/
def compContinuousAlternatingMapCLM :
    (F ->L[𝕜] G) ->L[𝕜] (E [⋀^ι]->L[𝕜] F) ->L[𝕜] (E [⋀^ι]->L[𝕜] G) where
  toFun g :=
    { toLinearMap := compContinuousAlternatingMapₗ _ _ _ _ g
      cont := by
        rw [ContinuousAlternatingMap.isEmbedding_toContinuousMultilinearMap.continuous_iff]
        exact (map_continuous <| compContinuousMultilinearMapL 𝕜 (fun _ : ι => E) F G g).comp
          ContinuousAlternatingMap.continuous_toContinuousMultilinearMap }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  cont := by
    rw [ContinuousLinearMap.isEmbedding_postcomp
      (ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜)
.continuous_iff] ContinuousAlternatingMap.isEmbedding_toContinuousMultilinearMap
exact map_continuous
      (precomp (ContinuousMultilinearMap 𝕜 (fun _ : ι => E) G)
        ((ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜 : (E [⋀^ι]->L[𝕜] F) ->L[𝕜] _))) ∘L
        (compContinuousMultilinearMapL 𝕜 (fun _ : ι => E) F G)

end ContinuousLinearMap

namespace ContinuousLinearEquiv
variable {𝕜 E E' F G ι : Type*} [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup E'] [Module 𝕜 E'] [TopologicalSpace E']
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul 𝕜 F]
  [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousConstSMul 𝕜 G]

/-- `ContinuousLinearMap.compContinuousAlternatingMap` as a bundled continuous linear equiv.

Given a continuous linear equivalence `g : F ≃L[𝕜] G`,
this function returns the equivalence between continuous alternating maps with codomain `F`
and continuous alternating maps with codomain `G`
that acts by composing these maps with `g`.
-/
@[simps +simpRhs apply]
/--
Definition of `continuousAlternatingMapCongrRight` / `continuousAlternatingMapCongrRight` 的定义

English:
definition continuousAlternatingMapCongrRight
  signature: (g : F ≃L[𝕜] G)
  body: g.continuousAlternatingMapCongrRightEquiv
  __ := ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 E F G ι g.toContinuousLinearMap
continuous_toFun := map_continuous
    ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 E F G ι g.toContinuousLinearMap
continuous_invFun := map_continuous
   

中文:
定义 continuousAlternatingMapCongrRight
  签名: (g : F ≃L[𝕜] G)
  定义体: g.continuousAlternatingMapCongrRightEquiv
  __ := ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 E F G ι g.toContinuousLinearMap
continuous_toFun := map_continuous
    ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 E F G ι g.toContinuousLinearMap
continuous_invFun := map_continuous
   

Depends on / 依赖: continuousAlternatingMapCongrRightEquiv, g.continuousAlternatingMapCongrRightEquiv
-/
def continuousAlternatingMapCongrRight (g : F ≃L[𝕜] G) :
    (E [⋀^ι]->L[𝕜] F) ≃L[𝕜] (E [⋀^ι]->L[𝕜] G) where
  __ := g.continuousAlternatingMapCongrRightEquiv
  __ := ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 E F G ι g.toContinuousLinearMap
continuous_toFun := map_continuous
    ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 E F G ι g.toContinuousLinearMap
continuous_invFun := map_continuous
    ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 E G F ι g.symm.toContinuousLinearMap

@[simp]
/--
theorem `_root_.ContinuousLinearEquiv.continuousAlternatingMapCongrRight_symm` / 定理 `_root_.ContinuousLinearEquiv.continuousAlternatingMapCongrRight_symm`

English:
theorem _root_.ContinuousLinearEquiv.continuousAlternatingMapCongrRight_symm
  given: (g : F ≃L[𝕜] G)
  proof: rfl

中文:
定理 _root_.ContinuousLinearEquiv.continuousAlternatingMapCongrRight_symm
  条件: (g : F ≃L[𝕜] G)
  证明: rfl
-/
theorem _root_.ContinuousLinearEquiv.continuousAlternatingMapCongrRight_symm (g : F ≃L[𝕜] G) :
    (g.continuousAlternatingMapCongrRight (ι := ι) (E := E)).symm =
      g.symm.continuousAlternatingMapCongrRight :=
  rfl

/-- Given a continuous linear isomorphism between the domains,
generate a continuous linear isomorphism between the spaces of continuous alternating maps.

This is `ContinuousAlternatingMap.compContinuousLinearMap` as an equivalence,
and is the continuous version of `AlternatingMap.domLCongr`. -/
@[simps apply]
/--
Definition of `continuousAlternatingMapCongrLeft` / `continuousAlternatingMapCongrLeft` 的定义

English:
definition continuousAlternatingMapCongrLeft
  signature: (f : E ≃L[𝕜] E')
  body: f.continuousAlternatingMapCongrLeftEquiv
  __ := ContinuousAlternatingMap.compContinuousLinearMapCLM (f.symm : E' ->L[𝕜] E)
  toFun g := g.compContinuousLinearMap (f.symm : E' ->L[𝕜] E)
  continuous_invFun :=
    (ContinuousAlternatingMap.compContinuousLinearMapCLM (f : E ->L[𝕜] E')).cont
  continuo

中文:
定义 continuousAlternatingMapCongrLeft
  签名: (f : E ≃L[𝕜] E')
  定义体: f.continuousAlternatingMapCongrLeftEquiv
  __ := ContinuousAlternatingMap.compContinuousLinearMapCLM (f.symm : E' ->L[𝕜] E)
  toFun g := g.compContinuousLinearMap (f.symm : E' ->L[𝕜] E)
  continuous_invFun :=
    (ContinuousAlternatingMap.compContinuousLinearMapCLM (f : E ->L[𝕜] E')).cont
  continuo

Depends on / 依赖: continuousAlternatingMapCongrLeftEquiv, f.continuousAlternatingMapCongrLeftEquiv
-/
def continuousAlternatingMapCongrLeft (f : E ≃L[𝕜] E') :
    E [⋀^ι]->L[𝕜] F ≃L[𝕜] (E' [⋀^ι]->L[𝕜] F) where
  __ := f.continuousAlternatingMapCongrLeftEquiv
  __ := ContinuousAlternatingMap.compContinuousLinearMapCLM (f.symm : E' ->L[𝕜] E)
  toFun g := g.compContinuousLinearMap (f.symm : E' ->L[𝕜] E)
  continuous_invFun :=
    (ContinuousAlternatingMap.compContinuousLinearMapCLM (f : E ->L[𝕜] E')).cont
  continuous_toFun :=
    (ContinuousAlternatingMap.compContinuousLinearMapCLM (f.symm : E' ->L[𝕜] E)).cont

/-- Continuous linear equivalences between the domains and the codomains
generate a continuous linear equivalence between the spaces of continuous alternating maps. -/
@[simps! apply]
/--
Definition of `continuousAlternatingMapCongr` / `continuousAlternatingMapCongr` 的定义

English:
definition continuousAlternatingMapCongr
  signature: (e : E ≃L[𝕜] E') (e' : F ≃L[𝕜] G)
  body: e.continuousAlternatingMapCongrLeft.trans e'.continuousAlternatingMapCongrRight

中文:
定义 continuousAlternatingMapCongr
  签名: (e : E ≃L[𝕜] E') (e' : F ≃L[𝕜] G)
  定义体: e.continuousAlternatingMapCongrLeft.trans e'.continuousAlternatingMapCongrRight

Depends on / 依赖: continuousAlternatingMapCongrLeft, continuousAlternatingMapCongrRight, e.continuousAlternatingMapCongrLeft.trans
-/
def continuousAlternatingMapCongr (e : E ≃L[𝕜] E') (e' : F ≃L[𝕜] G) :
    (E [⋀^ι]->L[𝕜] F) ≃L[𝕜] (E' [⋀^ι]->L[𝕜] G) :=
e.continuousAlternatingMapCongrLeft.trans e'.continuousAlternatingMapCongrRight

/--
lemma `coe_continuousAlternatingMapCongr` / 引理 `coe_continuousAlternatingMapCongr`

English:
lemma coe_continuousAlternatingMapCongr
  given: (e : E ≃L[𝕜] E') (e' : F ≃L[𝕜] G)
  proof: rfl

中文:
引理 coe_continuousAlternatingMapCongr
  条件: (e : E ≃L[𝕜] E') (e' : F ≃L[𝕜] G)
  证明: rfl
-/
lemma coe_continuousAlternatingMapCongr (e : E ≃L[𝕜] E') (e' : F ≃L[𝕜] G) :
    (e.continuousAlternatingMapCongr e' (ι := ι) : (E [⋀^ι]->L[𝕜] F) ->L[𝕜] (E' [⋀^ι]->L[𝕜] G)) =
      ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 E' F G ι (e' : F ->L[𝕜] G) ∘L
        ContinuousAlternatingMap.compContinuousLinearMapCLM e.symm :=
  rfl

end ContinuousLinearEquiv
