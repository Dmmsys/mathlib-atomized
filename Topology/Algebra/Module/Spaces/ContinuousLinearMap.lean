/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Yury Kudryashov
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
public import Mathlib.Topology.Algebra.Module.Spaces.UniformConvergenceCLM

/-!
# Topology of bounded convergence on the space of continuous linear map

In this file, we endow `E →L[𝕜] F` with the "topology of bounded convergence",
or "topology of uniform convergence on bounded sets". This is declared as an instance.

A key feature of the topology of bounded convergence is that, in the normed setting, it coincides
with the operator norm topology.

Note that, more generally, we defined the "topology of `𝔖`-convergence" for any
`𝔖 : Set (Set E)` in `Mathlib.Topology.Algebra.Module.Spaces.UniformConvergenceCLM`.

Here is a list of type aliases for `E →L[𝕜] F` endowed with various topologies :
* `ContinuousLinearMap`: topology of bounded convergence
* `UniformConvergenceCLM`: topology of `𝔖`-convergence, for a general `𝔖 : Set (Set E)`
* `CompactConvergenceCLM`: topology of compact convergence
* `PointwiseConvergenceCLM`: topology of pointwise convergence, also called "weak-\* topology"
  or "strong-operator topology" depending on the context
* `ContinuousLinearMapWOT`: topology of weak pointwise convergence, also called "weak-operator
  topology"

## Main definitions

* `ContinuousLinearMap.topologicalSpace` is the topology of bounded convergence. This is
  declared as an instance.

## Main statements

* `ContinuousLinearMap.topologicalAddGroup` and
  `ContinuousLinearMap.continuousSMul` register these facts as instances for the special
  case of bounded convergence.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

uniform convergence, bounded convergence
-/

@[expose] public section

open Bornology Filter Function Set Topology
open scoped UniformConvergence Uniformity

namespace ContinuousLinearMap

section BoundedConvergence

/-! ### Topology of bounded convergence -/

variable {𝕜₁ 𝕜₂ 𝕜₃ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃] {σ : 𝕜₁ ->+* 𝕜₂}
  {τ : 𝕜₂ ->+* 𝕜₃} {ρ : 𝕜₁ ->+* 𝕜₃} [RingHomCompTriple σ τ ρ] {E F G : Type*} [AddCommGroup E]
  [Module 𝕜₁ E] [AddCommGroup F] [Module 𝕜₂ F]
  [AddCommGroup G] [Module 𝕜₃ G] [TopologicalSpace E]

/--
Instance `topologicalSpace` / 实例 `topologicalSpace`

English:
instance topologicalSpace
  signature: [TopologicalSpace F] [IsTopologicalAddGroup F]
  body: fast_instance% UniformConvergenceCLM.instTopologicalSpace σ F { S | IsVonNBounded 𝕜₁ S }

中文:
实例 topologicalSpace
  签名: [拓扑空间 F] [是拓扑加群 F]
  定义体: fast_instance% UniformConvergenceCLM.instTopologicalSpace σ F { S | IsVonNBounded 𝕜₁ S }

Depends on / 依赖: IsVonNBounded, UniformConvergenceCLM, UniformConvergenceCLM.instTopologicalSpace, fast_instance, instTopologicalSpace
-/
instance topologicalSpace [TopologicalSpace F] [IsTopologicalAddGroup F] :
    TopologicalSpace (E ->SL[σ] F) :=
  fast_instance% UniformConvergenceCLM.instTopologicalSpace σ F { S | IsVonNBounded 𝕜₁ S }

/--
Instance `topologicalAddGroup` / 实例 `topologicalAddGroup`

English:
instance topologicalAddGroup
  signature: [TopologicalSpace F] [IsTopologicalAddGroup F]
  body: UniformConvergenceCLM.instIsTopologicalAddGroup σ F _

中文:
实例 topologicalAddGroup
  签名: [拓扑空间 F] [是拓扑加群 F]
  定义体: UniformConvergenceCLM.instIsTopologicalAddGroup σ F _

Depends on / 依赖: UniformConvergenceCLM, UniformConvergenceCLM.instIsTopologicalAddGroup, instIsTopologicalAddGroup
-/
instance topologicalAddGroup [TopologicalSpace F] [IsTopologicalAddGroup F] :
    IsTopologicalAddGroup (E ->SL[σ] F) :=
  UniformConvergenceCLM.instIsTopologicalAddGroup σ F _

/--
Instance `continuousSMul` / 实例 `continuousSMul`

English:
instance continuousSMul
  signature: [RingHomSurjective σ] [RingHomIsometric σ] [TopologicalSpace F]
  body: UniformConvergenceCLM.continuousSMul σ F { S | IsVonNBounded 𝕜₁ S } fun _ hs => hs

中文:
实例 continuousSMul
  签名: [RingHomSurjective σ] [RingHomIsometric σ] [拓扑空间 F]
  定义体: UniformConvergenceCLM.continuousSMul σ F { S | IsVonNBounded 𝕜₁ S } fun _ hs => hs

Depends on / 依赖: IsVonNBounded, UniformConvergenceCLM, UniformConvergenceCLM.continuousSMul, continuousSMul
-/
instance continuousSMul [RingHomSurjective σ] [RingHomIsometric σ] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul 𝕜₂ F] : ContinuousSMul 𝕜₂ (E ->SL[σ] F) :=
  UniformConvergenceCLM.continuousSMul σ F { S | IsVonNBounded 𝕜₁ S } fun _ hs => hs

/--
Instance `uniformSpace` / 实例 `uniformSpace`

English:
instance uniformSpace
  signature: [UniformSpace F] [IsUniformAddGroup F]
  body: fast_instance% UniformConvergenceCLM.instUniformSpace σ F { S | IsVonNBounded 𝕜₁ S }

中文:
实例 uniformSpace
  签名: [一致空间 F] [是UniformAdd群 F]
  定义体: fast_instance% UniformConvergenceCLM.instUniformSpace σ F { S | IsVonNBounded 𝕜₁ S }

Depends on / 依赖: IsVonNBounded, UniformConvergenceCLM, UniformConvergenceCLM.instUniformSpace, fast_instance, instUniformSpace
-/
instance uniformSpace [UniformSpace F] [IsUniformAddGroup F] : UniformSpace (E ->SL[σ] F) :=
  fast_instance% UniformConvergenceCLM.instUniformSpace σ F { S | IsVonNBounded 𝕜₁ S }

/--
Instance `isUniformAddGroup` / 实例 `isUniformAddGroup`

English:
instance isUniformAddGroup
  signature: [UniformSpace F] [IsUniformAddGroup F]
  body: UniformConvergenceCLM.instIsUniformAddGroup σ F _

中文:
实例 isUniformAddGroup
  签名: [一致空间 F] [是UniformAdd群 F]
  定义体: UniformConvergenceCLM.instIsUniformAddGroup σ F _

Depends on / 依赖: UniformConvergenceCLM, UniformConvergenceCLM.instIsUniformAddGroup, instIsUniformAddGroup
-/
instance isUniformAddGroup [UniformSpace F] [IsUniformAddGroup F] :
    IsUniformAddGroup (E ->SL[σ] F) :=
  UniformConvergenceCLM.instIsUniformAddGroup σ F _

/--
Instance `instContinuousEvalConst` / 实例 `instContinuousEvalConst`

English:
instance instContinuousEvalConst
  signature: [TopologicalSpace F] [IsTopologicalAddGroup F]
  body: UniformConvergenceCLM.continuousEvalConst σ F _ Bornology.sUnion_isVonNBounded_eq_univ

中文:
实例 instContinuousEvalConst
  签名: [拓扑空间 F] [是拓扑加群 F]
  定义体: UniformConvergenceCLM.continuousEvalConst σ F _ Bornology.sUnion_isVonNBounded_eq_univ

Depends on / 依赖: Bornology, Bornology.sUnion_isVonNBounded_eq_univ, UniformConvergenceCLM, UniformConvergenceCLM.continuousEvalConst, continuousEvalConst, sUnion_isVonNBounded_eq_univ
-/
instance instContinuousEvalConst [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜₁ E] : ContinuousEvalConst (E ->SL[σ] F) E F :=
  UniformConvergenceCLM.continuousEvalConst σ F _ Bornology.sUnion_isVonNBounded_eq_univ

/--
Instance `instT2Space` / 实例 `instT2Space`

English:
instance instT2Space
  signature: [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜₁ E]
  body: UniformConvergenceCLM.t2Space σ F _ Bornology.sUnion_isVonNBounded_eq_univ

中文:
实例 instT2Space
  签名: [拓扑空间 F] [是拓扑加群 F] [连续标量乘法 𝕜₁ E]
  定义体: UniformConvergenceCLM.t2Space σ F _ Bornology.sUnion_isVonNBounded_eq_univ

Depends on / 依赖: Bornology, Bornology.sUnion_isVonNBounded_eq_univ, UniformConvergenceCLM, UniformConvergenceCLM.t2Space, sUnion_isVonNBounded_eq_univ, t2Space
-/
instance instT2Space [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜₁ E]
    [T2Space F] : T2Space (E ->SL[σ] F) :=
  UniformConvergenceCLM.t2Space σ F _ Bornology.sUnion_isVonNBounded_eq_univ

/--
theorem `hasBasis_nhds_zero_of_basis` / 定理 `hasBasis_nhds_zero_of_basis`

English:
theorem hasBasis_nhds_zero_of_basis
  statement: [TopologicalSpace F] [IsTopologicalAddGroup F]
  proof: UniformConvergenceCLM.hasBasis_nhds_zero_of_basis σ F { S | IsVonNBounded 𝕜₁ S }
    ⟨∅, isVonNBounded_empty 𝕜₁ E⟩
    (directedOn_of_sup_mem fun _ _ => IsVonNBounded.union) h

中文:
定理 hasBasis_nhds_zero_of_basis
  结论: [拓扑空间 F] [是拓扑加群 F]
  证明: UniformConvergenceCLM.hasBasis_nhds_zero_of_basis σ F { S | IsVonNBounded 𝕜₁ S }
    ⟨∅, isVonNBounded_empty 𝕜₁ E⟩
    (directedOn_of_sup_mem fun _ _ => IsVonNBounded.union) h
-/
protected theorem hasBasis_nhds_zero_of_basis [TopologicalSpace F] [IsTopologicalAddGroup F]
    {ι : Type*} {p : ι -> Prop} {b : ι -> Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    (𝓝 (0 : E ->SL[σ] F)).HasBasis (fun Si : Set E × ι => IsVonNBounded 𝕜₁ Si.1 ∧ p Si.2)
      fun Si => { f : E ->SL[σ] F | forall x in Si.1, f x in b Si.2 } :=
  UniformConvergenceCLM.hasBasis_nhds_zero_of_basis σ F { S | IsVonNBounded 𝕜₁ S }
    ⟨∅, isVonNBounded_empty 𝕜₁ E⟩
    (directedOn_of_sup_mem fun _ _ => IsVonNBounded.union) h

/--
theorem `hasBasis_nhds_zero` / 定理 `hasBasis_nhds_zero`

English:
theorem hasBasis_nhds_zero
  given: [TopologicalSpace F] [IsTopologicalAddGroup F]
  proof: ContinuousLinearMap.hasBasis_nhds_zero_of_basis (𝓝 0).basis_sets

中文:
定理 hasBasis_nhds_zero
  条件: [拓扑空间 F] [是拓扑加群 F]
  证明: ContinuousLinearMap.hasBasis_nhds_zero_of_basis (𝓝 0).basis_sets
-/
protected theorem hasBasis_nhds_zero [TopologicalSpace F] [IsTopologicalAddGroup F] :
    (𝓝 (0 : E ->SL[σ] F)).HasBasis
      (fun SV : Set E × Set F => IsVonNBounded 𝕜₁ SV.1 ∧ SV.2 in (𝓝 0 : Filter F))
      fun SV => { f : E ->SL[σ] F | forall x in SV.1, f x in SV.2 } :=
  ContinuousLinearMap.hasBasis_nhds_zero_of_basis (𝓝 0).basis_sets

/--
theorem `isUniformEmbedding_toUniformOnFun` / 定理 `isUniformEmbedding_toUniformOnFun`

English:
theorem isUniformEmbedding_toUniformOnFun
  given: [UniformSpace F] [IsUniformAddGroup F]
  proof: UniformConvergenceCLM.isUniformEmbedding_coeFn ..

中文:
定理 isUniformEmbedding_toUniformOnFun
  条件: [一致空间 F] [是UniformAdd群 F]
  证明: UniformConvergenceCLM.isUniformEmbedding_coeFn ..

Depends on / 依赖: UniformConvergenceCLM, UniformConvergenceCLM.isUniformEmbedding_coeFn, isUniformEmbedding_coeFn
-/
theorem isUniformEmbedding_toUniformOnFun [UniformSpace F] [IsUniformAddGroup F] :
    IsUniformEmbedding
      fun f : E ->SL[σ] F => UniformOnFun.ofFun {s | Bornology.IsVonNBounded 𝕜₁ s} f :=
  UniformConvergenceCLM.isUniformEmbedding_coeFn ..

/--
Instance `uniformContinuousConstSMul` / 实例 `uniformContinuousConstSMul`

English:
instance uniformContinuousConstSMul
  body: UniformConvergenceCLM.instUniformContinuousConstSMul σ F _ _

中文:
实例 uniformContinuousConstSMul
  定义体: UniformConvergenceCLM.instUniformContinuousConstSMul σ F _ _

Depends on / 依赖: UniformConvergenceCLM, UniformConvergenceCLM.instUniformContinuousConstSMul, instUniformContinuousConstSMul
-/
instance uniformContinuousConstSMul
    {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
    [UniformSpace F] [IsUniformAddGroup F] [UniformContinuousConstSMul M F] :
    UniformContinuousConstSMul M (E ->SL[σ] F) :=
  UniformConvergenceCLM.instUniformContinuousConstSMul σ F _ _

/--
Instance `continuousConstSMul` / 实例 `continuousConstSMul`

English:
instance continuousConstSMul
  signature: {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
  body: UniformConvergenceCLM.instContinuousConstSMul σ F _ _

中文:
实例 continuousConstSMul
  签名: {M : 类型} [幺半群 M] [分配乘法作用 M F] [标量交换类 𝕜₂ M F]
  定义体: UniformConvergenceCLM.instContinuousConstSMul σ F _ _

Depends on / 依赖: UniformConvergenceCLM, UniformConvergenceCLM.instContinuousConstSMul, instContinuousConstSMul
-/
instance continuousConstSMul {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul M F] :
    ContinuousConstSMul M (E ->SL[σ] F) :=
  UniformConvergenceCLM.instContinuousConstSMul σ F _ _

/--
theorem `nhds_zero_eq_of_basis` / 定理 `nhds_zero_eq_of_basis`

English:
theorem nhds_zero_eq_of_basis
  statement: [TopologicalSpace F] [IsTopologicalAddGroup F]
  proof: UniformConvergenceCLM.nhds_zero_eq_of_basis _ _ _ h

中文:
定理 nhds_zero_eq_of_basis
  结论: [拓扑空间 F] [是拓扑加群 F]
  证明: UniformConvergenceCLM.nhds_zero_eq_of_basis _ _ _ h
-/
protected theorem nhds_zero_eq_of_basis [TopologicalSpace F] [IsTopologicalAddGroup F]
    {ι : Type*} {p : ι -> Prop} {b : ι -> Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    𝓝 (0 : E ->SL[σ] F) =
      ⨅ (s : Set E) (_ : IsVonNBounded 𝕜₁ s) (i : ι) (_ : p i),
        𝓟 {f : E ->SL[σ] F | MapsTo f s (b i)} :=
  UniformConvergenceCLM.nhds_zero_eq_of_basis _ _ _ h

/--
theorem `nhds_zero_eq` / 定理 `nhds_zero_eq`

English:
theorem nhds_zero_eq
  given: [TopologicalSpace F] [IsTopologicalAddGroup F]
  proof: UniformConvergenceCLM.nhds_zero_eq ..

中文:
定理 nhds_zero_eq
  条件: [拓扑空间 F] [是拓扑加群 F]
  证明: UniformConvergenceCLM.nhds_zero_eq ..
-/
protected theorem nhds_zero_eq [TopologicalSpace F] [IsTopologicalAddGroup F] :
    𝓝 (0 : E ->SL[σ] F) =
      ⨅ (s : Set E) (_ : IsVonNBounded 𝕜₁ s) (U : Set F) (_ : U in 𝓝 0),
        𝓟 {f : E ->SL[σ] F | MapsTo f s U} :=
  UniformConvergenceCLM.nhds_zero_eq ..

/--
theorem `eventually_nhds_zero_mapsTo` / 定理 `eventually_nhds_zero_mapsTo`

English:
theorem eventually_nhds_zero_mapsTo
  statement: [TopologicalSpace F] [IsTopologicalAddGroup F]
  proof: UniformConvergenceCLM.eventually_nhds_zero_mapsTo _ hs hu

中文:
定理 eventually_nhds_zero_mapsTo
  结论: [拓扑空间 F] [是拓扑加群 F]
  证明: UniformConvergenceCLM.eventually_nhds_zero_mapsTo _ hs hu

Depends on / 依赖: UniformConvergenceCLM, UniformConvergenceCLM.eventually_nhds_zero_mapsTo, eventually_nhds_zero_mapsTo
-/
theorem eventually_nhds_zero_mapsTo [TopologicalSpace F] [IsTopologicalAddGroup F]
    {s : Set E} (hs : IsVonNBounded 𝕜₁ s) {U : Set F} (hu : U in 𝓝 0) :
    forallᶠ f : E ->SL[σ] F in 𝓝 0, MapsTo f s U :=
  UniformConvergenceCLM.eventually_nhds_zero_mapsTo _ hs hu

/--
theorem `isVonNBounded_image2_apply` / 定理 `isVonNBounded_image2_apply`

English:
theorem isVonNBounded_image2_apply
  statement: {R : Type*} [SeminormedRing R]
  proof: UniformConvergenceCLM.isVonNBounded_image2_apply hS hs

中文:
定理 isVonNBounded_image2_apply
  结论: {R : 类型} [Seminormed环 R]
  证明: UniformConvergenceCLM.isVonNBounded_image2_apply hS hs

Depends on / 依赖: UniformConvergenceCLM, UniformConvergenceCLM.isVonNBounded_image2_apply, isVonNBounded_image2_apply
-/
theorem isVonNBounded_image2_apply {R : Type*} [SeminormedRing R]
    [TopologicalSpace F] [IsTopologicalAddGroup F]
    [DistribMulAction R F] [ContinuousConstSMul R F] [SMulCommClass 𝕜₂ R F]
    {S : Set (E ->SL[σ] F)} (hS : IsVonNBounded R S) {s : Set E} (hs : IsVonNBounded 𝕜₁ s) :
    IsVonNBounded R (Set.image2 (fun f x => f x) S s) :=
  UniformConvergenceCLM.isVonNBounded_image2_apply hS hs

/--
theorem `isVonNBounded_iff` / 定理 `isVonNBounded_iff`

English:
theorem isVonNBounded_iff
  statement: {R : Type*} [NormedDivisionRing R]
  proof: UniformConvergenceCLM.isVonNBounded_iff

中文:
定理 isVonNBounded_iff
  结论: {R : 类型} [NormedDivision环 R]
  证明: UniformConvergenceCLM.isVonNBounded_iff

Depends on / 依赖: UniformConvergenceCLM, UniformConvergenceCLM.isVonNBounded_iff, isVonNBounded_iff
-/
theorem isVonNBounded_iff {R : Type*} [NormedDivisionRing R]
    [TopologicalSpace F] [IsTopologicalAddGroup F]
    [Module R F] [ContinuousConstSMul R F] [SMulCommClass 𝕜₂ R F]
    {S : Set (E ->SL[σ] F)} :
    IsVonNBounded R S ↔
      forall s, IsVonNBounded 𝕜₁ s -> IsVonNBounded R (Set.image2 (fun f x => f x) S s) :=
  UniformConvergenceCLM.isVonNBounded_iff

/--
theorem `completeSpace` / 定理 `completeSpace`

English:
theorem completeSpace
  statement: [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜₂ F] [CompleteSpace F]
  proof: UniformConvergenceCLM.completeSpace _ _ h sUnion_isVonNBounded_eq_univ

中文:
定理 completeSpace
  结论: [一致空间 F] [是UniformAdd群 F] [连续标量乘法 𝕜₂ F] [完备空间 F]
  证明: UniformConvergenceCLM.completeSpace _ _ h sUnion_isVonNBounded_eq_univ

Depends on / 依赖: UniformConvergenceCLM, UniformConvergenceCLM.completeSpace, completeSpace, sUnion_isVonNBounded_eq_univ
-/
theorem completeSpace [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜₂ F] [CompleteSpace F]
    [ContinuousSMul 𝕜₁ E] (h : IsCoherentWith {s : Set E | IsVonNBounded 𝕜₁ s}) :
    CompleteSpace (E ->SL[σ] F) :=
  UniformConvergenceCLM.completeSpace _ _ h sUnion_isVonNBounded_eq_univ

/--
Instance `instCompleteSpace` / 实例 `instCompleteSpace`

English:
instance instCompleteSpace
  signature: [IsTopologicalAddGroup E] [ContinuousSMul 𝕜₁ E] [SequentialSpace E]
  body: completeSpace .of_seq fun _ _ h => (h.isVonNBounded_range 𝕜₁).insert _

中文:
实例 instCompleteSpace
  签名: [是拓扑加群 E] [连续标量乘法 𝕜₁ E] [Sequential空间 E]
  定义体: completeSpace .of_seq fun _ _ h => (h.isVonNBounded_range 𝕜₁).insert _

Depends on / 依赖: completeSpace, h.isVonNBounded_range, insert, isVonNBounded_range, of_seq
-/
instance instCompleteSpace [IsTopologicalAddGroup E] [ContinuousSMul 𝕜₁ E] [SequentialSpace E]
    [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜₂ F] [CompleteSpace F] :
    CompleteSpace (E ->SL[σ] F) :=
completeSpace .of_seq fun _ _ h => (h.isVonNBounded_range 𝕜₁).insert _

/--
theorem `isUniformInducing_postcomp` / 定理 `isUniformInducing_postcomp`

English:
theorem isUniformInducing_postcomp
  statement: [UniformSpace F] [IsUniformAddGroup F]
  proof: UniformConvergenceCLM.isUniformInducing_postcomp _ f hf _

中文:
定理 isUniformInducing_postcomp
  结论: [一致空间 F] [是UniformAdd群 F]
  证明: UniformConvergenceCLM.isUniformInducing_postcomp _ f hf _

Depends on / 依赖: UniformConvergenceCLM, UniformConvergenceCLM.isUniformInducing_postcomp, isUniformInducing_postcomp
-/
theorem isUniformInducing_postcomp [UniformSpace F] [IsUniformAddGroup F]
    [UniformSpace G] [IsUniformAddGroup G] (f : F ->SL[τ] G) (hf : IsUniformInducing f) :
    IsUniformInducing (f.comp : (E ->SL[σ] F) -> (E ->SL[ρ] G)) :=
  UniformConvergenceCLM.isUniformInducing_postcomp _ f hf _

/--
theorem `isUniformEmbedding_postcomp` / 定理 `isUniformEmbedding_postcomp`

English:
theorem isUniformEmbedding_postcomp
  statement: [UniformSpace F] [IsUniformAddGroup F]
  proof: UniformConvergenceCLM.isUniformEmbedding_postcomp _ f hf _

中文:
定理 isUniformEmbedding_postcomp
  结论: [一致空间 F] [是UniformAdd群 F]
  证明: UniformConvergenceCLM.isUniformEmbedding_postcomp _ f hf _

Depends on / 依赖: UniformConvergenceCLM, UniformConvergenceCLM.isUniformEmbedding_postcomp, isUniformEmbedding_postcomp
-/
theorem isUniformEmbedding_postcomp [UniformSpace F] [IsUniformAddGroup F]
    [UniformSpace G] [IsUniformAddGroup G] (f : F ->SL[τ] G) (hf : IsUniformEmbedding f) :
    IsUniformEmbedding (f.comp : (E ->SL[σ] F) -> (E ->SL[ρ] G)) :=
  UniformConvergenceCLM.isUniformEmbedding_postcomp _ f hf _

variable [TopologicalSpace F] [TopologicalSpace G] (𝔖 : Set (Set E)) (𝔗 : Set (Set F))

/--
theorem `isInducing_postcomp` / 定理 `isInducing_postcomp`

English:
theorem isInducing_postcomp
  statement: [IsTopologicalAddGroup F] [IsTopologicalAddGroup G]
  proof: letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  haveI : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  (isUniformInducing_postcomp 

中文:
定理 isInducing_postcomp
  结论: [是拓扑加群 F] [是拓扑加群 G]
  证明: letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  haveI : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  (isUniformInducing_postcomp 

Depends on / 依赖: AddMonoidHom, AddMonoidHom.isUniformInducing_of_isInducing, IsTopologicalAddGroup, IsTopologicalAddGroup.rightUniformSpace, IsUniformAddGroup, UniformSpace, isInducing, isUniformAddGroup_of_addCommGroup, isUniformInducing_of_isInducing, isUniformInducing_postcomp, rightUniformSpace
-/
theorem isInducing_postcomp [IsTopologicalAddGroup F] [IsTopologicalAddGroup G]
    (f : F ->SL[τ] G) (hf : IsInducing f) :
    IsInducing (f.comp : (E ->SL[σ] F) -> (E ->SL[ρ] G)) :=
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  haveI : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  (isUniformInducing_postcomp f <| AddMonoidHom.isUniformInducing_of_isInducing hf).isInducing

/--
theorem `isEmbedding_postcomp` / 定理 `isEmbedding_postcomp`

English:
theorem isEmbedding_postcomp
  statement: [IsTopologicalAddGroup F] [IsTopologicalAddGroup G]
  proof: .mk (isInducing_postcomp f hf.isInducing) fun _ _ => f.cancel_left hf.injective

中文:
定理 isEmbedding_postcomp
  结论: [是拓扑加群 F] [是拓扑加群 G]
  证明: .mk (isInducing_postcomp f hf.isInducing) fun _ _ => f.cancel_left hf.injective

Depends on / 依赖: cancel_left, f.cancel_left, hf.injective, hf.isInducing, injective, isInducing, isInducing_postcomp
-/
theorem isEmbedding_postcomp [IsTopologicalAddGroup F] [IsTopologicalAddGroup G]
    (f : F ->SL[τ] G) (hf : IsEmbedding f) :
    IsEmbedding (f.comp : (E ->SL[σ] F) -> (E ->SL[ρ] G)) :=
  .mk (isInducing_postcomp f hf.isInducing) fun _ _ => f.cancel_left hf.injective

variable (G) in
/-- Pre-composition by a *fixed* continuous linear map as a continuous linear map.

Note that in non-normed space it is not always true that composition is continuous
in both variables, so we have to fix one of them. -/
@[simps! apply]
/--
Definition of `precomp` / `precomp` 的定义

English:
definition precomp
  signature: [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G] [RingHomSurjective σ]
  body: f.comp L
  __ := precompUniformConvergenceCLM G { S | IsVonNBounded 𝕜₁ S } { S | IsVonNBounded 𝕜₂ S } L
    (fun _ hS => hS.image L)

中文:
定义 precomp
  签名: [是拓扑加群 G] [连续常数标量乘法 𝕜₃ G] [RingHomSurjective σ]
  定义体: f.comp L
  __ := precompUniformConvergenceCLM G { S | IsVonNBounded 𝕜₁ S } { S | IsVonNBounded 𝕜₂ S } L
    (fun _ hS => hS.image L)

Depends on / 依赖: f.comp
-/
def precomp [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G] [RingHomSurjective σ]
    [RingHomIsometric σ] (L : E ->SL[σ] F) : (F ->SL[τ] G) ->L[𝕜₃] E ->SL[ρ] G where
  toFun f := f.comp L
  __ := precompUniformConvergenceCLM G { S | IsVonNBounded 𝕜₁ S } { S | IsVonNBounded 𝕜₂ S } L
    (fun _ hS => hS.image L)

variable (E) in
/-- Post-composition by a *fixed* continuous linear map as a continuous linear map.

Note that in non-normed space it is not always true that composition is continuous
in both variables, so we have to fix one of them. -/
@[simps! apply]
/--
Definition of `postcomp` / `postcomp` 的定义

English:
definition postcomp
  signature: [IsTopologicalAddGroup F] [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]
  body: L.comp f
  __ := postcompUniformConvergenceCLM { S | IsVonNBounded 𝕜₁ S } L

中文:
定义 postcomp
  签名: [是拓扑加群 F] [是拓扑加群 G] [连续常数标量乘法 𝕜₃ G]
  定义体: L.comp f
  __ := postcompUniformConvergenceCLM { S | IsVonNBounded 𝕜₁ S } L

Depends on / 依赖: L.comp
-/
def postcomp [IsTopologicalAddGroup F] [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]
    [ContinuousConstSMul 𝕜₂ F] (L : F ->SL[τ] G) : (E ->SL[σ] F) ->SL[τ] E ->SL[ρ] G where
  toFun f := L.comp f
  __ := postcompUniformConvergenceCLM { S | IsVonNBounded 𝕜₁ S } L

variable (σ F) in
/--
lemma `toUniformConvergenceCLM_continuous` / 引理 `toUniformConvergenceCLM_continuous`

English:
lemma toUniformConvergenceCLM_continuous
  statement: [IsTopologicalAddGroup F]
  proof: continuous_id_of_le UniformConvergenceCLM.topologicalSpace_mono _ _ h

中文:
引理 toUniformConvergenceCLM_continuous
  结论: [是拓扑加群 F]
  证明: continuous_id_of_le UniformConvergenceCLM.topologicalSpace_mono _ _ h

Depends on / 依赖: UniformConvergenceCLM, UniformConvergenceCLM.topologicalSpace_mono, continuous_id_of_le, topologicalSpace_mono
-/
lemma toUniformConvergenceCLM_continuous [IsTopologicalAddGroup F]
    [ContinuousConstSMul 𝕜₂ F]
    (𝔖 : Set (Set E)) (h : 𝔖 subseteq {S | IsVonNBounded 𝕜₁ S}) :
    Continuous (ContinuousLinearMap.toUniformConvergenceCLM σ F 𝔖) :=
continuous_id_of_le UniformConvergenceCLM.topologicalSpace_mono _ _ h

/--
theorem `continuous_of_continuous_uncurry` / 定理 `continuous_of_continuous_uncurry`

English:
theorem continuous_of_continuous_uncurry
  proof: UniformConvergenceCLM.continuous_of_continuous_uncurry (fun _ => id) B hB

中文:
定理 continuous_of_continuous_uncurry
  证明: UniformConvergenceCLM.continuous_of_continuous_uncurry (fun _ => id) B hB

Depends on / 依赖: UniformConvergenceCLM, UniformConvergenceCLM.continuous_of_continuous_uncurry, continuous_of_continuous_uncurry
-/
theorem continuous_of_continuous_uncurry
    {𝕜₁ : Type*} [NontriviallyNormedField 𝕜₁] {σ : 𝕜₁ ->+* 𝕜₂} [Module 𝕜₁ E]
    {τ : 𝕜₃ ->+* 𝕜₂} [RingHomSurjective τ]
    [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]
    [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F]
    (B : G ->ₛₗ[τ] (E ->SL[σ] F))
    (hB : Continuous (fun p : G × E => B p.1 p.2)) :
    Continuous B :=
  UniformConvergenceCLM.continuous_of_continuous_uncurry (fun _ => id) B hB

end BoundedConvergence

section Pi

variable (𝕜 : Type*) [NormedField 𝕜] (E : Type*) {ι : Type*} (F : ι -> Type*)
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [forall i, AddCommGroup (F i)] [forall i, Module 𝕜 (F i)] [forall i, TopologicalSpace (F i)]
  [forall i, IsTopologicalAddGroup (F i)] [forall i, ContinuousConstSMul 𝕜 (F i)]

/-- `ContinuousLinearMap.pi`, upgraded to a continuous linear equivalence between
`Π i, E →L[𝕜] F i` and `E →L[𝕜] Π i, F i`. -/
@[simps]
/--
Definition of `piEquivL` / `piEquivL` 的定义

English:
definition piEquivL
  signature: :
  body: ContinuousLinearMap.pi F
  invFun f i := (ContinuousLinearMap.proj i).comp f
  __ := UniformConvergenceCLM.piEquivL _ _ _

中文:
定义 piEquivL
  签名: :
  定义体: ContinuousLinearMap.pi F
  invFun f i := (ContinuousLinearMap.proj i).comp f
  __ := UniformConvergenceCLM.piEquivL _ _ _

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.pi
-/
def piEquivL :
    (Π i, E ->L[𝕜] F i) ≃L[𝕜] (E ->L[𝕜] Π i, F i) where
  toFun F := ContinuousLinearMap.pi F
  invFun f i := (ContinuousLinearMap.proj i).comp f
  __ := UniformConvergenceCLM.piEquivL _ _ _

end Pi

section BilinearMaps
variable {R 𝕜 𝕜₂ 𝕜₃ : Type*}
variable {E F G : Type*}

/-!
We prove some computation rules for continuous (semi-)bilinear maps in their first argument.
If `f` is a continuous bilinear map, to use the corresponding rules for the second argument, use
`(f _).map_add` and similar.
-/

section AddCommMonoid
variable
  [Semiring R] [NormedField 𝕜₂] [NormedField 𝕜₃]
  [AddCommMonoid E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜₂ F] [TopologicalSpace F]
  [AddCommGroup G] [Module 𝕜₃ G]
  [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]
  {σ₁₃ : R ->+* 𝕜₃} {σ₂₃ : 𝕜₂ ->+* 𝕜₃}

/--
theorem `map_add₂` / 定理 `map_add₂`

English:
theorem map_add₂
  given: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (x x' : E) (y : F)
  proof: by rw [f.map_add, add_apply]

中文:
定理 map_add₂
  条件: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (x x' : E) (y : F)
  证明: by rw [f.map_add, add_apply]

Depends on / 依赖: add_apply, f.map_add, map_add
-/
theorem map_add₂ (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (x x' : E) (y : F) :
    f (x + x') y = f x y + f x' y := by rw [f.map_add, add_apply]

/--
theorem `map_zero₂` / 定理 `map_zero₂`

English:
theorem map_zero₂
  given: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (y : F)
  statement: f 0 y = 0
  proof: by
  rw [f.map_zero]; rw [zero_apply]

中文:
定理 map_zero₂
  条件: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (y : F)
  结论: f 0 y = 0
  证明: by
  rw [f.map_zero]; rw [zero_apply]

Depends on / 依赖: f.map_zero, map_zero, zero_apply
-/
theorem map_zero₂ (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (y : F) : f 0 y = 0 := by
  rw [f.map_zero]; rw [zero_apply]

/--
theorem `map_smulₛₗ₂` / 定理 `map_smulₛₗ₂`

English:
theorem map_smulₛₗ₂
  given: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (c : R) (x : E) (y : F)
  proof: by rw [f.map_smulₛₗ, smul_apply]

中文:
定理 map_smulₛₗ₂
  条件: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (c : R) (x : E) (y : F)
  证明: by rw [f.map_smulₛₗ, smul_apply]

Depends on / 依赖: f.map_smul, smul_apply
-/
theorem map_smulₛₗ₂ (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (c : R) (x : E) (y : F) :
    f (c • x) y = σ₁₃ c • f x y := by rw [f.map_smulₛₗ, smul_apply]

/-- Send a continuous sesquilinear map to an abstract sesquilinear map (forgetting continuity). -/
@[simps -isSimp apply]
/--
Definition of `toLinearMap₁₂` / `toLinearMap₁₂` 的定义

English:
definition toLinearMap₁₂
  signature: : (E ->SL[σ₁₃] F ->SL[σ₂₃] G) ->ₗ[𝕜₃] E ->ₛₗ[σ₁₃] F ->ₛₗ[σ₂₃] G where
  body: (coeLMₛₗ σ₂₃).comp L.toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 toLinearMap₁₂
  签名: : (E ->SL[σ₁₃] F ->SL[σ₂₃] G) ->ₗ[𝕜₃] E ->ₛₗ[σ₁₃] F ->ₛₗ[σ₂₃] G where
  定义体: (coeLMₛₗ σ₂₃).comp L.toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: L.toLinearMap, toLinearMap
-/
def toLinearMap₁₂ : (E ->SL[σ₁₃] F ->SL[σ₂₃] G) ->ₗ[𝕜₃] E ->ₛₗ[σ₁₃] F ->ₛₗ[σ₂₃] G where
  toFun L := (coeLMₛₗ σ₂₃).comp L.toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
lemma `toLinearMap₁₂_apply_apply_apply` / 引理 `toLinearMap₁₂_apply_apply_apply`

English:
lemma toLinearMap₁₂_apply_apply_apply
  given: (L : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (v : E) (w : F)
  proof: rfl

中文:
引理 toLinearMap₁₂_apply_apply_apply
  条件: (L : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (v : E) (w : F)
  证明: rfl
-/
@[simp] lemma toLinearMap₁₂_apply_apply_apply (L : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (v : E) (w : F) :
    L.toLinearMap₁₂ v w = L v w := rfl

/--
lemma `toLinearMap₁₂_injective` / 引理 `toLinearMap₁₂_injective`

English:
lemma toLinearMap₁₂_injective
  proof: by
  simp [Function.Injective, LinearMap.ext_iff, ← ContinuousLinearMap.ext_iff]

中文:
引理 toLinearMap₁₂_injective
  证明: by
  simp [Function.Injective, LinearMap.ext_iff, ← ContinuousLinearMap.ext_iff]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext_iff, Function, Function.Injective, Injective, LinearMap, LinearMap.ext_iff, ext_iff
-/
lemma toLinearMap₁₂_injective :
    (toLinearMap₁₂ (E := E) (F := F) (G := G) (σ₁₃ := σ₁₃) (σ₂₃ := σ₂₃) : _ -> _).Injective := by
  simp [Function.Injective, LinearMap.ext_iff, ← ContinuousLinearMap.ext_iff]

/--
lemma `toLinearMap₁₂_inj` / 引理 `toLinearMap₁₂_inj`

English:
lemma toLinearMap₁₂_inj
  given: (L₁ L₂ : E ->SL[σ₁₃] F ->SL[σ₂₃] G)
  proof: toLinearMap₁₂_injective.eq_iff

中文:
引理 toLinearMap₁₂_inj
  条件: (L₁ L₂ : E ->SL[σ₁₃] F ->SL[σ₂₃] G)
  证明: toLinearMap₁₂_injective.eq_iff

Depends on / 依赖: _injective.eq_iff, eq_iff
-/
lemma toLinearMap₁₂_inj (L₁ L₂ : E ->SL[σ₁₃] F ->SL[σ₂₃] G) :
    L₁.toLinearMap₁₂ = L₂.toLinearMap₁₂ ↔ L₁ = L₂ :=
  toLinearMap₁₂_injective.eq_iff

end AddCommMonoid

section Nonsemilinear
variable
  [NormedField 𝕜₂] [NormedField 𝕜₃]
  [AddCommMonoid E] [Module 𝕜₃ E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜₂ F] [TopologicalSpace F]
  [AddCommGroup G] [Module 𝕜₃ G]
  [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]
  {σ₂₃ : 𝕜₂ ->+* 𝕜₃}

/--
theorem `map_smul₂` / 定理 `map_smul₂`

English:
theorem map_smul₂
  given: (f : E ->L[𝕜₃] F ->SL[σ₂₃] G) (c : 𝕜₃) (x : E) (y : F)
  proof: by
  rw [f.map_smul]; rw [smul_apply]

中文:
定理 map_smul₂
  条件: (f : E ->L[𝕜₃] F ->SL[σ₂₃] G) (c : 𝕜₃) (x : E) (y : F)
  证明: by
  rw [f.map_smul]; rw [smul_apply]

Depends on / 依赖: f.map_smul, map_smul, smul_apply
-/
theorem map_smul₂ (f : E ->L[𝕜₃] F ->SL[σ₂₃] G) (c : 𝕜₃) (x : E) (y : F) :
    f (c • x) y = c • f x y := by
  rw [f.map_smul]; rw [smul_apply]

end Nonsemilinear

section AddCommGroup
variable
  [Semiring R] [NormedField 𝕜₂] [NormedField 𝕜₃]
  [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜₂ F] [TopologicalSpace F]
  [AddCommGroup G] [Module 𝕜₃ G]
  [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]
  {σ₁₃ : R ->+* 𝕜₃} {σ₂₃ : 𝕜₂ ->+* 𝕜₃}

/--
theorem `map_sub₂` / 定理 `map_sub₂`

English:
theorem map_sub₂
  given: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (x x' : E) (y : F)
  proof: by rw [map_sub, sub_apply]

中文:
定理 map_sub₂
  条件: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (x x' : E) (y : F)
  证明: by rw [map_sub, sub_apply]

Depends on / 依赖: map_sub, sub_apply
-/
theorem map_sub₂ (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (x x' : E) (y : F) :
    f (x - x') y = f x y - f x' y := by rw [map_sub, sub_apply]

/--
theorem `map_neg₂` / 定理 `map_neg₂`

English:
theorem map_neg₂
  given: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (x : E) (y : F)
  statement: f (-x) y = -f x y
  proof: by
  rw [map_neg]; rw [neg_apply]

中文:
定理 map_neg₂
  条件: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (x : E) (y : F)
  结论: f (-x) y = -f x y
  证明: by
  rw [map_neg]; rw [neg_apply]

Depends on / 依赖: map_neg, neg_apply
-/
theorem map_neg₂ (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (x : E) (y : F) : f (-x) y = -f x y := by
  rw [map_neg]; rw [neg_apply]

end AddCommGroup

section BilinForm
variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

/--
Definition of `toBilinForm` / `toBilinForm` 的定义

English:
definition toBilinForm
  signature: (L : E ->L[𝕜] E ->L[𝕜] 𝕜)
  body: L.toLinearMap₁₂

中文:
定义 toBilinForm
  签名: (L : E ->L[𝕜] E ->L[𝕜] 𝕜)
  定义体: L.toLinearMap₁₂

Depends on / 依赖: L.toLinearMap
-/
def toBilinForm (L : E ->L[𝕜] E ->L[𝕜] 𝕜) : LinearMap.BilinForm 𝕜 E := L.toLinearMap₁₂

/--
lemma `toBilinForm_apply` / 引理 `toBilinForm_apply`

English:
lemma toBilinForm_apply
  given: (L : E ->L[𝕜] E ->L[𝕜] 𝕜) (v : E) (w : E)
  proof: rfl

中文:
引理 toBilinForm_apply
  条件: (L : E ->L[𝕜] E ->L[𝕜] 𝕜) (v : E) (w : E)
  证明: rfl
-/
@[simp] lemma toBilinForm_apply (L : E ->L[𝕜] E ->L[𝕜] 𝕜) (v : E) (w : E) :
    L.toBilinForm v w = L v w := rfl

/--
lemma `toBilinForm_injective` / 引理 `toBilinForm_injective`

English:
lemma toBilinForm_injective
  statement: (toBilinForm (𝕜 := 𝕜) (E := E)).Injective
  proof: toLinearMap₁₂_injective

中文:
引理 toBilinForm_injective
  结论: (toBilinForm (𝕜 := 𝕜) (E := E)).单射
  证明: toLinearMap₁₂_injective

Depends on / 依赖: Injective
-/
lemma toBilinForm_injective : (toBilinForm (𝕜 := 𝕜) (E := E)).Injective :=
  toLinearMap₁₂_injective

/--
lemma `toBilinForm_inj` / 引理 `toBilinForm_inj`

English:
lemma toBilinForm_inj
  given: (L₁ L₂ : E ->L[𝕜] E ->L[𝕜] 𝕜)
  proof: toBilinForm_injective.eq_iff

中文:
引理 toBilinForm_inj
  条件: (L₁ L₂ : E ->L[𝕜] E ->L[𝕜] 𝕜)
  证明: toBilinForm_injective.eq_iff

Depends on / 依赖: eq_iff, toBilinForm_injective, toBilinForm_injective.eq_iff
-/
lemma toBilinForm_inj (L₁ L₂ : E ->L[𝕜] E ->L[𝕜] 𝕜) :
    L₁.toBilinForm = L₂.toBilinForm ↔ L₁ = L₂ :=
  toBilinForm_injective.eq_iff

end BilinForm

end BilinearMaps

section RestrictScalars

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
  {F : Type*} [AddCommGroup F]

section UniformSpace

variable [UniformSpace F] [IsUniformAddGroup F] [Module 𝕜 F]
  (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
  [Module 𝕜' E] [IsScalarTower 𝕜' 𝕜 E] [Module 𝕜' F] [IsScalarTower 𝕜' 𝕜 F]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isUniformEmbedding_restrictScalars` / 定理 `isUniformEmbedding_restrictScalars`

English:
theorem isUniformEmbedding_restrictScalars
  proof: by
  rw [← isUniformEmbedding_toUniformOnFun.of_comp_iff]
  convert! isUniformEmbedding_toUniformOnFun using 4 with s
  exact ⟨fun h => h.extend_scalars _, fun h => h.restrict_scalars _⟩

中文:
定理 isUniformEmbedding_restrictScalars
  证明: by
  rw [← isUniformEmbedding_toUniformOnFun.of_comp_iff]
  convert! isUniformEmbedding_toUniformOnFun using 4 with s
  exact ⟨fun h => h.extend_scalars _, fun h => h.restrict_scalars _⟩

Depends on / 依赖: convert, extend_scalars, h.extend_scalars, h.restrict_scalars, isUniformEmbedding_toUniformOnFun, isUniformEmbedding_toUniformOnFun.of_comp_iff, of_comp_iff, restrict_scalars
-/
theorem isUniformEmbedding_restrictScalars :
    IsUniformEmbedding (restrictScalars 𝕜' : (E ->L[𝕜] F) -> (E ->L[𝕜'] F)) := by
  rw [← isUniformEmbedding_toUniformOnFun.of_comp_iff]
  convert! isUniformEmbedding_toUniformOnFun using 4 with s
  exact ⟨fun h => h.extend_scalars _, fun h => h.restrict_scalars _⟩

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
    UniformContinuous (restrictScalars 𝕜' : (E ->L[𝕜] F) -> (E ->L[𝕜'] F)) :=
  (isUniformEmbedding_restrictScalars 𝕜').uniformContinuous

end UniformSpace

variable [TopologicalSpace F] [IsTopologicalAddGroup F] [Module 𝕜 F]
  (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
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
    IsEmbedding (restrictScalars 𝕜' : (E ->L[𝕜] F) -> (E ->L[𝕜'] F)) :=
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  (isUniformEmbedding_restrictScalars _).isEmbedding

@[continuity, fun_prop]
/--
theorem `continuous_restrictScalars` / 定理 `continuous_restrictScalars`

English:
theorem continuous_restrictScalars
  proof: (isEmbedding_restrictScalars _).continuous

中文:
定理 continuous_restrictScalars
  证明: (isEmbedding_restrictScalars _).continuous

Depends on / 依赖: continuous, isEmbedding_restrictScalars
-/
theorem continuous_restrictScalars :
    Continuous (restrictScalars 𝕜' : (E ->L[𝕜] F) -> (E ->L[𝕜'] F)) :=
  (isEmbedding_restrictScalars _).continuous

variable (𝕜 E F)
variable (𝕜'' : Type*) [Ring 𝕜'']
  [Module 𝕜'' F] [ContinuousConstSMul 𝕜'' F] [SMulCommClass 𝕜 𝕜'' F] [SMulCommClass 𝕜' 𝕜'' F]

/--
Definition of `restrictScalarsL` / `restrictScalarsL` 的定义

English:
definition restrictScalarsL
  signature: : (E ->L[𝕜] F) ->L[𝕜''] E ->L[𝕜'] F
  body: .mk restrictScalarsₗ 𝕜 E F 𝕜' 𝕜''

中文:
定义 restrictScalarsL
  签名: : (E ->L[𝕜] F) ->L[𝕜''] E ->L[𝕜'] F
  定义体: .mk restrictScalarsₗ 𝕜 E F 𝕜' 𝕜''
-/
def restrictScalarsL : (E ->L[𝕜] F) ->L[𝕜''] E ->L[𝕜'] F :=
.mk restrictScalarsₗ 𝕜 E F 𝕜' 𝕜''

variable {𝕜 E F 𝕜' 𝕜''}

@[simp]
/--
theorem `coe_restrictScalarsL` / 定理 `coe_restrictScalarsL`

English:
theorem coe_restrictScalarsL
  statement: (restrictScalarsL 𝕜 E F 𝕜' 𝕜'' : (E ->L[𝕜] F) ->ₗ[𝕜''] E ->L[𝕜'] F) =
  proof: rfl

@[simp]

中文:
定理 coe_restrictScalarsL
  结论: (restrictScalarsL 𝕜 E F 𝕜' 𝕜'' : (E ->L[𝕜] F) ->ₗ[𝕜''] E ->L[𝕜'] F) =
  证明: rfl

@[simp]
-/
theorem coe_restrictScalarsL : (restrictScalarsL 𝕜 E F 𝕜' 𝕜'' : (E ->L[𝕜] F) ->ₗ[𝕜''] E ->L[𝕜'] F) =
    restrictScalarsₗ 𝕜 E F 𝕜' 𝕜'' :=
  rfl

@[simp]
/--
theorem `coe_restrict_scalarsL'` / 定理 `coe_restrict_scalarsL'`

English:
theorem coe_restrict_scalarsL'
  statement: ⇑(restrictScalarsL 𝕜 E F 𝕜' 𝕜'') = restrictScalars 𝕜'
  proof: rfl

中文:
定理 coe_restrict_scalarsL'
  结论: ⇑(restrictScalarsL 𝕜 E F 𝕜' 𝕜'') = restrictScalars 𝕜'
  证明: rfl
-/
theorem coe_restrict_scalarsL' : ⇑(restrictScalarsL 𝕜 E F 𝕜' 𝕜'') = restrictScalars 𝕜' :=
  rfl

end RestrictScalars

section Prod

variable {𝕜 E F G : Type*} (S : Type*) [NormedField 𝕜] [Semiring S]
  [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
  [AddCommGroup G] [Module 𝕜 G]
  [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜 G]
  [Module S G] [SMulCommClass 𝕜 S G] [ContinuousConstSMul S G]

/-- `ContinuousLinearMap.coprod` as a `ContinuousLinearEquiv`. -/
@[simps!]
/--
Definition of `coprodEquivL` / `coprodEquivL` 的定义

English:
definition coprodEquivL
  signature: : ((E ->L[𝕜] G) × (F ->L[𝕜] G)) ≃L[S] (E × F ->L[𝕜] G) where
  body: coprodEquiv
  continuous_toFun :=
    (((fst 𝕜 E F).precomp G).coprod ((snd 𝕜 E F).precomp G)).continuous
  continuous_invFun :=
    (((inl 𝕜 E F).precomp G).prod ((inr 𝕜 E F).precomp G)).continuous

中文:
定义 coprodEquivL
  签名: : ((E ->L[𝕜] G) × (F ->L[𝕜] G)) ≃L[S] (E × F ->L[𝕜] G) where
  定义体: coprodEquiv
  continuous_toFun :=
    (((fst 𝕜 E F).precomp G).coprod ((snd 𝕜 E F).precomp G)).continuous
  continuous_invFun :=
    (((inl 𝕜 E F).precomp G).prod ((inr 𝕜 E F).precomp G)).continuous

Depends on / 依赖: coprodEquiv
-/
def coprodEquivL : ((E ->L[𝕜] G) × (F ->L[𝕜] G)) ≃L[S] (E × F ->L[𝕜] G) where
  __ := coprodEquiv
  continuous_toFun :=
    (((fst 𝕜 E F).precomp G).coprod ((snd 𝕜 E F).precomp G)).continuous
  continuous_invFun :=
    (((inl 𝕜 E F).precomp G).prod ((inr 𝕜 E F).precomp G)).continuous

variable [Module S F] [SMulCommClass 𝕜 S F] [ContinuousConstSMul S F]

/-- `ContinuousLinearMap.prod` as a `ContinuousLinearEquiv`. -/
@[simps! apply]
/--
Definition of `prodL` / `prodL` 的定义

English:
definition prodL
  signature: : ((E ->L[𝕜] F) × (E ->L[𝕜] G)) ≃L[S] (E ->L[𝕜] F × G) where
  body: prodₗ S
  continuous_toFun := by
    change Continuous fun x => .id 𝕜 _ ∘L prodₗ S x
    simp_rw [← coprod_inl_inr]
    exact (((inl 𝕜 F G).postcomp E).coprod ((inr 𝕜 F G).postcomp E)).continuous
  continuous_invFun :=
    (((fst 𝕜 F G).postcomp E).prod ((snd 𝕜 F G).postcomp E)).continuous

中文:
定义 prodL
  签名: : ((E ->L[𝕜] F) × (E ->L[𝕜] G)) ≃L[S] (E ->L[𝕜] F × G) where
  定义体: prodₗ S
  continuous_toFun := by
    change Continuous fun x => .id 𝕜 _ ∘L prodₗ S x
    simp_rw [← coprod_inl_inr]
    exact (((inl 𝕜 F G).postcomp E).coprod ((inr 𝕜 F G).postcomp E)).continuous
  continuous_invFun :=
    (((fst 𝕜 F G).postcomp E).prod ((snd 𝕜 F G).postcomp E)).continuous
-/
def prodL : ((E ->L[𝕜] F) × (E ->L[𝕜] G)) ≃L[S] (E ->L[𝕜] F × G) where
  __ := prodₗ S
  continuous_toFun := by
    change Continuous fun x => .id 𝕜 _ ∘L prodₗ S x
    simp_rw [← coprod_inl_inr]
    exact (((inl 𝕜 F G).postcomp E).coprod ((inr 𝕜 F G).postcomp E)).continuous
  continuous_invFun :=
    (((fst 𝕜 F G).postcomp E).prod ((snd 𝕜 F G).postcomp E)).continuous

end Prod

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-- `ContinuousLinearMap.toSpanSingleton` as a continuous linear equivalence. -/
@[simps!]
/--
Definition of `toSpanSingletonCLE` / `toSpanSingletonCLE` 的定义

English:
definition toSpanSingletonCLE
  signature: : E ≃L[𝕜] (𝕜 ->L[𝕜] E) where
  body: toSpanSingletonLE ..
continuous_toFun := continuous_of_continuous_uncurry _
    continuous_snd.smul continuous_fst
  continuous_invFun := continuous_eval_const 1

中文:
定义 toSpanSingletonCLE
  签名: : E ≃L[𝕜] (𝕜 ->L[𝕜] E) where
  定义体: toSpanSingletonLE ..
continuous_toFun := continuous_of_continuous_uncurry _
    continuous_snd.smul continuous_fst
  continuous_invFun := continuous_eval_const 1

Depends on / 依赖: toSpanSingletonLE
-/
def toSpanSingletonCLE : E ≃L[𝕜] (𝕜 ->L[𝕜] E) where
  toLinearEquiv := toSpanSingletonLE ..
continuous_toFun := continuous_of_continuous_uncurry _
    continuous_snd.smul continuous_fst
  continuous_invFun := continuous_eval_const 1

end ContinuousLinearMap

open ContinuousLinearMap

namespace ContinuousLinearEquiv

/-! ### Continuous linear equivalences -/

section Semilinear

variable {𝕜 : Type*} {𝕜₂ : Type*} {𝕜₃ : Type*} {𝕜₄ : Type*} {E : Type*} {F : Type*}
  {G : Type*} {H : Type*} [AddCommGroup E] [AddCommGroup F] [AddCommGroup G] [AddCommGroup H]
  [NormedField 𝕜] [NormedField 𝕜₂] [NormedField 𝕜₃] [NormedField 𝕜₄]
  [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜₃ G] [Module 𝕜₄ H]
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalAddGroup G] [IsTopologicalAddGroup H] [ContinuousConstSMul 𝕜₃ G]
  [ContinuousConstSMul 𝕜₄ H] {σ₁₂ : 𝕜 ->+* 𝕜₂} {σ₂₁ : 𝕜₂ ->+* 𝕜} {σ₂₃ : 𝕜₂ ->+* 𝕜₃} {σ₁₃ : 𝕜 ->+* 𝕜₃}
  {σ₃₄ : 𝕜₃ ->+* 𝕜₄} {σ₄₃ : 𝕜₄ ->+* 𝕜₃} {σ₂₄ : 𝕜₂ ->+* 𝕜₄} {σ₁₄ : 𝕜 ->+* 𝕜₄} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂] [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄]
  [RingHomCompTriple σ₂₁ σ₁₄ σ₂₄] [RingHomCompTriple σ₂₄ σ₄₃ σ₂₃] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
  [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄]
  [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₁]

/-- A pair of continuous (semi)linear equivalences generates a (semi)linear equivalence between the
spaces of continuous (semi)linear maps. -/
@[simps apply symm_apply toLinearEquiv_apply toLinearEquiv_symm_apply]
/--
Definition of `arrowCongrSL` / `arrowCongrSL` 的定义

English:
definition arrowCongrSL
  signature: (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G)
  body: { e₁₂.arrowCongrEquivₛₗ e₄₃ with
    -- given explicitly to help `simps`
    toFun := fun L => (e₄₃ : H ->SL[σ₄₃] G).comp (L.comp (e₁₂.symm : F ->SL[σ₂₁] E))
    -- given explicitly to help `simps`
    invFun := fun L => (e₄₃.symm : G ->SL[σ₃₄] H).comp (L.comp (e₁₂ : E ->SL[σ₁₂] F))
    continuous_t

中文:
定义 arrowCongrSL
  签名: (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G)
  定义体: { e₁₂.arrowCongrEquivₛₗ e₄₃ with
    -- given explicitly to help `simps`
    toFun := fun L => (e₄₃ : H ->SL[σ₄₃] G).comp (L.comp (e₁₂.symm : F ->SL[σ₂₁] E))
    -- given explicitly to help `simps`
    invFun := fun L => (e₄₃.symm : G ->SL[σ₃₄] H).comp (L.comp (e₁₂ : E ->SL[σ₁₂] F))
    continuous_t
-/
def arrowCongrSL (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G) :
    (E ->SL[σ₁₄] H) ≃SL[σ₄₃] F ->SL[σ₂₃] G :=
{ e₁₂.arrowCongrEquivₛₗ e₄₃ with
    -- given explicitly to help `simps`
    toFun := fun L => (e₄₃ : H ->SL[σ₄₃] G).comp (L.comp (e₁₂.symm : F ->SL[σ₂₁] E))
    -- given explicitly to help `simps`
    invFun := fun L => (e₄₃.symm : G ->SL[σ₃₄] H).comp (L.comp (e₁₂ : E ->SL[σ₁₂] F))
    continuous_toFun := ((postcomp F e₄₃.toContinuousLinearMap).comp
      (precomp H e₁₂.symm.toContinuousLinearMap)).continuous
    continuous_invFun := ((precomp H e₁₂.toContinuousLinearMap).comp
      (postcomp F e₄₃.symm.toContinuousLinearMap)).continuous }

end Semilinear

section Linear

variable {𝕜 : Type*} {E : Type*} {F : Type*} {G : Type*} {H : Type*} [AddCommGroup E]
  [AddCommGroup F] [AddCommGroup G] [AddCommGroup H] [NormedField 𝕜] [Module 𝕜 E]
  [Module 𝕜 F] [Module 𝕜 G] [Module 𝕜 H] [TopologicalSpace E] [TopologicalSpace F]
  [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalAddGroup G] [IsTopologicalAddGroup H]
  [ContinuousConstSMul 𝕜 G] [ContinuousConstSMul 𝕜 H]

/--
Definition of `arrowCongr` / `arrowCongr` 的定义

English:
definition arrowCongr
  signature: (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G)
  body: e₁.arrowCongrSL e₂

中文:
定义 arrowCongr
  签名: (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G)
  定义体: e₁.arrowCongrSL e₂

Depends on / 依赖: arrowCongrSL
-/
def arrowCongr (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) : (E ->L[𝕜] H) ≃L[𝕜] F ->L[𝕜] G :=
  e₁.arrowCongrSL e₂

/--
lemma `arrowCongr_apply` / 引理 `arrowCongr_apply`

English:
lemma arrowCongr_apply
  given: (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) (f : E ->L[𝕜] H) (x : F)
  proof: rfl

中文:
引理 arrowCongr_apply
  条件: (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) (f : E ->L[𝕜] H) (x : F)
  证明: rfl
-/
@[simp] lemma arrowCongr_apply (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) (f : E ->L[𝕜] H) (x : F) :
    e₁.arrowCongr e₂ f x = e₂ (f (e₁.symm x)) := rfl

/--
lemma `arrowCongr_symm` / 引理 `arrowCongr_symm`

English:
lemma arrowCongr_symm
  given: (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G)
  proof: rfl

中文:
引理 arrowCongr_symm
  条件: (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G)
  证明: rfl
-/
@[simp] lemma arrowCongr_symm (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) :
    (e₁.arrowCongr e₂).symm = e₁.symm.arrowCongr e₂.symm := rfl

/--
Definition of `conjContinuousAlgEquiv` / `conjContinuousAlgEquiv` 的定义

English:
definition conjContinuousAlgEquiv
  signature: (e : G ≃L[𝕜] H)
  body: { e.arrowCongr e with
    map_mul' _ _ := by ext; simp
    commutes' _ := by ext; simp }

中文:
定义 conjContinuousAlgEquiv
  签名: (e : G ≃L[𝕜] H)
  定义体: { e.arrowCongr e with
    map_mul' _ _ := by ext; simp
    commutes' _ := by ext; simp }

Depends on / 依赖: arrowCongr, commutes, e.arrowCongr, map_mul
-/
def conjContinuousAlgEquiv (e : G ≃L[𝕜] H) : (G ->L[𝕜] G) ≃A[𝕜] (H ->L[𝕜] H) :=
  { e.arrowCongr e with
    map_mul' _ _ := by ext; simp
    commutes' _ := by ext; simp }

/--
theorem `conjContinuousAlgEquiv_apply_apply` / 定理 `conjContinuousAlgEquiv_apply_apply`

English:
theorem conjContinuousAlgEquiv_apply_apply
  given: (e : G ≃L[𝕜] H) (f : G ->L[𝕜] G) (x : H)
  proof: rfl

中文:
定理 conjContinuousAlgEquiv_apply_apply
  条件: (e : G ≃L[𝕜] H) (f : G ->L[𝕜] G) (x : H)
  证明: rfl
-/
@[simp] theorem conjContinuousAlgEquiv_apply_apply (e : G ≃L[𝕜] H) (f : G ->L[𝕜] G) (x : H) :
    e.conjContinuousAlgEquiv f x = e (f (e.symm x)) := rfl

/--
theorem `symm_conjContinuousAlgEquiv_apply_apply` / 定理 `symm_conjContinuousAlgEquiv_apply_apply`

English:
theorem symm_conjContinuousAlgEquiv_apply_apply
  given: (e : G ≃L[𝕜] H) (f : H ->L[𝕜] H) (x : G)
  proof: rfl

中文:
定理 symm_conjContinuousAlgEquiv_apply_apply
  条件: (e : G ≃L[𝕜] H) (f : H ->L[𝕜] H) (x : G)
  证明: rfl
-/
theorem symm_conjContinuousAlgEquiv_apply_apply (e : G ≃L[𝕜] H) (f : H ->L[𝕜] H) (x : G) :
    e.conjContinuousAlgEquiv.symm f x = e.symm (f (e x)) := rfl

/--
theorem `conjContinuousAlgEquiv_apply` / 定理 `conjContinuousAlgEquiv_apply`

English:
theorem conjContinuousAlgEquiv_apply
  given: (e : G ≃L[𝕜] H) (f : G ->L[𝕜] G)
  proof: rfl

中文:
定理 conjContinuousAlgEquiv_apply
  条件: (e : G ≃L[𝕜] H) (f : G ->L[𝕜] G)
  证明: rfl
-/
theorem conjContinuousAlgEquiv_apply (e : G ≃L[𝕜] H) (f : G ->L[𝕜] G) :
    e.conjContinuousAlgEquiv f = e ∘L f ∘L e.symm := rfl

/--
theorem `symm_conjContinuousAlgEquiv` / 定理 `symm_conjContinuousAlgEquiv`

English:
theorem symm_conjContinuousAlgEquiv
  given: (e : G ≃L[𝕜] H)
  proof: rfl

中文:
定理 symm_conjContinuousAlgEquiv
  条件: (e : G ≃L[𝕜] H)
  证明: rfl
-/
@[simp] theorem symm_conjContinuousAlgEquiv (e : G ≃L[𝕜] H) :
    e.conjContinuousAlgEquiv.symm = e.symm.conjContinuousAlgEquiv := rfl

/--
theorem `conjContinuousAlgEquiv_refl` / 定理 `conjContinuousAlgEquiv_refl`

English:
theorem conjContinuousAlgEquiv_refl
  statement: conjContinuousAlgEquiv (.refl 𝕜 G) = .refl 𝕜 _
  proof: rfl

中文:
定理 conjContinuousAlgEquiv_refl
  结论: conjContinuousAlgEquiv (.refl 𝕜 G) = .refl 𝕜 _
  证明: rfl
-/
@[simp] theorem conjContinuousAlgEquiv_refl : conjContinuousAlgEquiv (.refl 𝕜 G) = .refl 𝕜 _ := rfl

/--
theorem `conjContinuousAlgEquiv_trans` / 定理 `conjContinuousAlgEquiv_trans`

English:
theorem conjContinuousAlgEquiv_trans
  statement: [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
  proof: rfl

中文:
定理 conjContinuousAlgEquiv_trans
  结论: [是拓扑加群 E] [连续常数标量乘法 𝕜 E]
  证明: rfl
-/
theorem conjContinuousAlgEquiv_trans [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
    (e : E ≃L[𝕜] G) (f : G ≃L[𝕜] H) :
    (e.trans f).conjContinuousAlgEquiv = e.conjContinuousAlgEquiv.trans f.conjContinuousAlgEquiv :=
  rfl

end Linear

end ContinuousLinearEquiv
