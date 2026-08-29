/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Multilinear.Bounded
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.UniformConvergence
public import Mathlib.Topology.Algebra.SeparationQuotient.Section
public import Mathlib.Topology.Hom.ContinuousEvalConst
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Topology on continuous multilinear maps

In this file we define `TopologicalSpace` and `UniformSpace` structures
on `ContinuousMultilinearMap 𝕜 E F`,
where `E i` is a family of vector spaces over `𝕜` with topologies
and `F` is a topological vector space.
-/

@[expose] public section

open Bornology Function Set Topology
open scoped UniformConvergence Filter

namespace ContinuousMultilinearMap

variable {𝕜 ι : Type*} {E : ι -> Type*} {F : Type*}
  [NormedField 𝕜]
  [forall i, TopologicalSpace (E i)] [forall i, AddCommGroup (E i)] [forall i, Module 𝕜 (E i)]
  [AddCommGroup F] [Module 𝕜 F]

/--
Definition of `toUniformOnFun` / `toUniformOnFun` 的定义

English:
definition toUniformOnFun
  signature: [TopologicalSpace F] (f : ContinuousMultilinearMap 𝕜 E F)
  body: UniformOnFun.ofFun _ f

中文:
定义 toUniformOnFun
  签名: [拓扑空间 F] (f : 连续多重线性映射 𝕜 E F)
  定义体: UniformOnFun.ofFun _ f

Depends on / 依赖: UniformOnFun, UniformOnFun.ofFun
-/
def toUniformOnFun [TopologicalSpace F] (f : ContinuousMultilinearMap 𝕜 E F) :
    (Π i, E i) ->ᵤ[{s | IsVonNBounded 𝕜 s}] F :=
  UniformOnFun.ofFun _ f

open UniformOnFun in
/--
lemma `range_toUniformOnFun` / 引理 `range_toUniformOnFun`

English:
lemma range_toUniformOnFun
  given: [DecidableEq ι] [TopologicalSpace F]
  proof: by
  ext f
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.cont, f.map_update_add, f.map_update_smul⟩
  · rintro ⟨hcont, hadd, hsmul⟩
    exact ⟨⟨⟨f, by intro; convert! hadd, by intro; convert! hsmul⟩, hcont⟩, rfl⟩

@[simp]

中文:
引理 range_toUniformOnFun
  条件: [DecidableEq ι] [拓扑空间 F]
  证明: by
  ext f
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.cont, f.map_update_add, f.map_update_smul⟩
  · rintro ⟨hcont, hadd, hsmul⟩
    exact ⟨⟨⟨f, by intro; convert! hadd, by intro; convert! hsmul⟩, hcont⟩, rfl⟩

@[simp]

Depends on / 依赖: convert, f.cont, f.map_update_add, f.map_update_smul, map_update_add, map_update_smul
-/
lemma range_toUniformOnFun [DecidableEq ι] [TopologicalSpace F] :
    range toUniformOnFun =
      {f : (Π i, E i) ->ᵤ[{s | IsVonNBounded 𝕜 s}] F |
        Continuous (toFun _ f) ∧
        (forall (m : Π i, E i) i x y,
          toFun _ f (update m i (x + y)) = toFun _ f (update m i x) + toFun _ f (update m i y)) ∧
        (forall (m : Π i, E i) i (c : 𝕜) x,
          toFun _ f (update m i (c • x)) = c • toFun _ f (update m i x))} := by
  ext f
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.cont, f.map_update_add, f.map_update_smul⟩
  · rintro ⟨hcont, hadd, hsmul⟩
    exact ⟨⟨⟨f, by intro; convert! hadd, by intro; convert! hsmul⟩, hcont⟩, rfl⟩

@[simp]
/--
lemma `toUniformOnFun_toFun` / 引理 `toUniformOnFun_toFun`

English:
lemma toUniformOnFun_toFun
  given: [TopologicalSpace F] (f : ContinuousMultilinearMap 𝕜 E F)
  proof: rfl

中文:
引理 toUniformOnFun_toFun
  条件: [拓扑空间 F] (f : 连续多重线性映射 𝕜 E F)
  证明: rfl
-/
lemma toUniformOnFun_toFun [TopologicalSpace F] (f : ContinuousMultilinearMap 𝕜 E F) :
    UniformOnFun.toFun _ f.toUniformOnFun = f :=
  rfl

/--
Instance `instTopologicalSpace` / 实例 `instTopologicalSpace`

English:
instance instTopologicalSpace
  signature: [TopologicalSpace F] [IsTopologicalAddGroup F]
  body: .induced toUniformOnFun
    @UniformOnFun.topologicalSpace _ _ (IsTopologicalAddGroup.rightUniformSpace F) _

中文:
实例 instTopologicalSpace
  签名: [拓扑空间 F] [是拓扑加群 F]
  定义体: .induced toUniformOnFun
    @UniformOnFun.topologicalSpace _ _ (IsTopologicalAddGroup.rightUniformSpace F) _

Depends on / 依赖: IsTopologicalAddGroup, IsTopologicalAddGroup.rightUniformSpace, UniformOnFun, UniformOnFun.topologicalSpace, induced, rightUniformSpace, toUniformOnFun, topologicalSpace
-/
instance instTopologicalSpace [TopologicalSpace F] [IsTopologicalAddGroup F] :
    TopologicalSpace (ContinuousMultilinearMap 𝕜 E F) :=
.induced toUniformOnFun
    @UniformOnFun.topologicalSpace _ _ (IsTopologicalAddGroup.rightUniformSpace F) _

/--
Instance `instUniformSpace` / 实例 `instUniformSpace`

English:
instance instUniformSpace
  signature: [UniformSpace F] [IsUniformAddGroup F]
  body: .replaceTopology (.comap toUniformOnFun <| UniformOnFun.uniformSpace _ _ _) by
    rw [instTopologicalSpace]; rw [IsUniformAddGroup.rightUniformSpace_eq]; rfl

中文:
实例 instUniformSpace
  签名: [一致空间 F] [是UniformAdd群 F]
  定义体: .replaceTopology (.comap toUniformOnFun <| UniformOnFun.uniformSpace _ _ _) by
    rw [instTopologicalSpace]; rw [IsUniformAddGroup.rightUniformSpace_eq]; rfl

Depends on / 依赖: IsUniformAddGroup, IsUniformAddGroup.rightUniformSpace_eq, UniformOnFun, UniformOnFun.uniformSpace, instTopologicalSpace, replaceTopology, rightUniformSpace_eq, toUniformOnFun, uniformSpace
-/
instance instUniformSpace [UniformSpace F] [IsUniformAddGroup F] :
    UniformSpace (ContinuousMultilinearMap 𝕜 E F) :=
.replaceTopology (.comap toUniformOnFun <| UniformOnFun.uniformSpace _ _ _) by
    rw [instTopologicalSpace]; rw [IsUniformAddGroup.rightUniformSpace_eq]; rfl

section IsUniformAddGroup

variable [UniformSpace F] [IsUniformAddGroup F]

/--
lemma `isUniformInducing_toUniformOnFun` / 引理 `isUniformInducing_toUniformOnFun`

English:
lemma isUniformInducing_toUniformOnFun
  proof: ⟨rfl⟩

中文:
引理 isUniformInducing_toUniformOnFun
  证明: ⟨rfl⟩
-/
lemma isUniformInducing_toUniformOnFun :
    IsUniformInducing (toUniformOnFun :
      ContinuousMultilinearMap 𝕜 E F -> ((Π i, E i) ->ᵤ[{s | IsVonNBounded 𝕜 s}] F)) := ⟨rfl⟩

/--
lemma `isUniformEmbedding_toUniformOnFun` / 引理 `isUniformEmbedding_toUniformOnFun`

English:
lemma isUniformEmbedding_toUniformOnFun
  proof: ⟨isUniformInducing_toUniformOnFun, DFunLike.coe_injective⟩

中文:
引理 isUniformEmbedding_toUniformOnFun
  证明: ⟨isUniformInducing_toUniformOnFun, DFunLike.coe_injective⟩

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective, isUniformInducing_toUniformOnFun
-/
lemma isUniformEmbedding_toUniformOnFun :
    IsUniformEmbedding (toUniformOnFun : ContinuousMultilinearMap 𝕜 E F -> _) :=
  ⟨isUniformInducing_toUniformOnFun, DFunLike.coe_injective⟩

/--
lemma `isEmbedding_toUniformOnFun` / 引理 `isEmbedding_toUniformOnFun`

English:
lemma isEmbedding_toUniformOnFun
  proof: isUniformEmbedding_toUniformOnFun.isEmbedding

@[fun_prop]

中文:
引理 isEmbedding_toUniformOnFun
  证明: isUniformEmbedding_toUniformOnFun.isEmbedding

@[fun_prop]

Depends on / 依赖: isEmbedding, isUniformEmbedding_toUniformOnFun, isUniformEmbedding_toUniformOnFun.isEmbedding
-/
lemma isEmbedding_toUniformOnFun :
    IsEmbedding (toUniformOnFun : ContinuousMultilinearMap 𝕜 E F ->
      ((Π i, E i) ->ᵤ[{s | IsVonNBounded 𝕜 s}] F)) :=
  isUniformEmbedding_toUniformOnFun.isEmbedding

@[fun_prop]
/--
theorem `uniformContinuous_coe_fun` / 定理 `uniformContinuous_coe_fun`

English:
theorem uniformContinuous_coe_fun
  given: [forall i, ContinuousSMul 𝕜 (E i)]
  proof: (UniformOnFun.uniformContinuous_toFun sUnion_isVonNBounded_eq_univ).comp
    isUniformEmbedding_toUniformOnFun.uniformContinuous

@[fun_prop]

中文:
定理 uniformContinuous_coe_fun
  条件: [对任意 i, 连续标量乘法 𝕜 (E i)]
  证明: (UniformOnFun.uniformContinuous_toFun sUnion_isVonNBounded_eq_univ).comp
    isUniformEmbedding_toUniformOnFun.uniformContinuous

@[fun_prop]

Depends on / 依赖: UniformOnFun, UniformOnFun.uniformContinuous_toFun, isUniformEmbedding_toUniformOnFun, isUniformEmbedding_toUniformOnFun.uniformContinuous, sUnion_isVonNBounded_eq_univ, uniformContinuous, uniformContinuous_toFun
-/
theorem uniformContinuous_coe_fun [forall i, ContinuousSMul 𝕜 (E i)] :
    UniformContinuous (DFunLike.coe : ContinuousMultilinearMap 𝕜 E F -> (Π i, E i) -> F) :=
  (UniformOnFun.uniformContinuous_toFun sUnion_isVonNBounded_eq_univ).comp
    isUniformEmbedding_toUniformOnFun.uniformContinuous

@[fun_prop]
/--
theorem `uniformContinuous_eval_const` / 定理 `uniformContinuous_eval_const`

English:
theorem uniformContinuous_eval_const
  given: [forall i, ContinuousSMul 𝕜 (E i)] (x : Π i, E i)
  proof: uniformContinuous_pi.1 uniformContinuous_coe_fun x

中文:
定理 uniformContinuous_eval_const
  条件: [对任意 i, 连续标量乘法 𝕜 (E i)] (x : Π i, E i)
  证明: uniformContinuous_pi.1 uniformContinuous_coe_fun x

Depends on / 依赖: uniformContinuous_coe_fun, uniformContinuous_pi
-/
theorem uniformContinuous_eval_const [forall i, ContinuousSMul 𝕜 (E i)] (x : Π i, E i) :
    UniformContinuous fun f : ContinuousMultilinearMap 𝕜 E F => f x :=
  uniformContinuous_pi.1 uniformContinuous_coe_fun x

/--
Instance `instIsUniformAddGroup` / 实例 `instIsUniformAddGroup`

English:
instance instIsUniformAddGroup
  signature: : IsUniformAddGroup (ContinuousMultilinearMap 𝕜 E F)
  body: let φ : ContinuousMultilinearMap 𝕜 E F ->+ (Π i, E i) ->ᵤ[{s | IsVonNBounded 𝕜 s}] F :=
    { toFun := toUniformOnFun, map_add' := fun _ _ => rfl, map_zero' := rfl }
  isUniformEmbedding_toUniformOnFun.isUniformAddGroup φ

中文:
实例 instIsUniformAddGroup
  签名: : 是UniformAdd群 (连续多重线性映射 𝕜 E F)
  定义体: let φ : ContinuousMultilinearMap 𝕜 E F ->+ (Π i, E i) ->ᵤ[{s | IsVonNBounded 𝕜 s}] F :=
    { toFun := toUniformOnFun, map_add' := fun _ _ => rfl, map_zero' := rfl }
  isUniformEmbedding_toUniformOnFun.isUniformAddGroup φ

Depends on / 依赖: ContinuousMultilinearMap, IsVonNBounded, isUniformAddGroup, isUniformEmbedding_toUniformOnFun, isUniformEmbedding_toUniformOnFun.isUniformAddGroup, map_add, map_zero, toUniformOnFun
-/
instance instIsUniformAddGroup : IsUniformAddGroup (ContinuousMultilinearMap 𝕜 E F) :=
  let φ : ContinuousMultilinearMap 𝕜 E F ->+ (Π i, E i) ->ᵤ[{s | IsVonNBounded 𝕜 s}] F :=
    { toFun := toUniformOnFun, map_add' := fun _ _ => rfl, map_zero' := rfl }
  isUniformEmbedding_toUniformOnFun.isUniformAddGroup φ

/--
Instance `instUniformContinuousConstSMul` / 实例 `instUniformContinuousConstSMul`

English:
instance instUniformContinuousConstSMul
  signature: {M : Type*}
  body: haveI := uniformContinuousConstSMul_of_continuousConstSMul M F
  isUniformEmbedding_toUniformOnFun.uniformContinuousConstSMul fun _ _ => rfl

@[fun_prop]

中文:
实例 instUniformContinuousConstSMul
  签名: {M : 类型}
  定义体: haveI := uniformContinuousConstSMul_of_continuousConstSMul M F
  isUniformEmbedding_toUniformOnFun.uniformContinuousConstSMul fun _ _ => rfl

@[fun_prop]

Depends on / 依赖: isUniformEmbedding_toUniformOnFun, isUniformEmbedding_toUniformOnFun.uniformContinuousConstSMul, uniformContinuousConstSMul, uniformContinuousConstSMul_of_continuousConstSMul
-/
instance instUniformContinuousConstSMul {M : Type*}
    [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜 M F] [ContinuousConstSMul M F] :
    UniformContinuousConstSMul M (ContinuousMultilinearMap 𝕜 E F) :=
  haveI := uniformContinuousConstSMul_of_continuousConstSMul M F
  isUniformEmbedding_toUniformOnFun.uniformContinuousConstSMul fun _ _ => rfl

@[fun_prop]
/--
theorem `isUniformInducing_postcomp` / 定理 `isUniformInducing_postcomp`

English:
theorem isUniformInducing_postcomp
  proof: by
  rw [← isUniformInducing_toUniformOnFun.of_comp_iff]
  exact (UniformOnFun.postcomp_isUniformInducing hg).comp isUniformInducing_toUniformOnFun

中文:
定理 isUniformInducing_postcomp
  证明: by
  rw [← isUniformInducing_toUniformOnFun.of_comp_iff]
  exact (UniformOnFun.postcomp_isUniformInducing hg).comp isUniformInducing_toUniformOnFun

Depends on / 依赖: UniformOnFun, UniformOnFun.postcomp_isUniformInducing, isUniformInducing_toUniformOnFun, isUniformInducing_toUniformOnFun.of_comp_iff, of_comp_iff, postcomp_isUniformInducing
-/
theorem isUniformInducing_postcomp
    {G : Type*} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] [Module 𝕜 G]
    (g : F ->L[𝕜] G) (hg : IsUniformInducing g) :
    IsUniformInducing (g.compContinuousMultilinearMap :
      ContinuousMultilinearMap 𝕜 E F -> ContinuousMultilinearMap 𝕜 E G) := by
  rw [← isUniformInducing_toUniformOnFun.of_comp_iff]
  exact (UniformOnFun.postcomp_isUniformInducing hg).comp isUniformInducing_toUniformOnFun

section CompleteSpace

variable [forall i, ContinuousSMul 𝕜 (E i)] [ContinuousConstSMul 𝕜 F] [CompleteSpace F]

open UniformOnFun in
/--
theorem `completeSpace` / 定理 `completeSpace`

English:
theorem completeSpace
  given: (h : IsCoherentWith {s : Set (Π i, E i) | IsVonNBounded 𝕜 s})
  proof: by
  classical
  wlog hF : T2Space F generalizing F
  · rw [(isUniformInducing_postcomp (SeparationQuotient.mkCLM _ _)
      SeparationQuotient.isUniformInducing_mk).completeSpace_congr]
    · exact this inferInstance
    · intro f
      use (SeparationQuotient.outCLM _ _).compContinuousMultilinearMap f
      simp [DFunLike.ext_iff]
  have H : forall {m : Π i, E i},
      Continuous fun f : (Π i, E i) ->ᵤ[{s | IsVonNBounded 𝕜 s}] F => toFun _ f m :=
    (uniformContinuous_eval (sUnion_isVonNBounded_eq_univ) _).continuous
  rw [completeSpace_iff_isComplete_range isUniformInducing_toUniformOnFun]; rw [range_toUniformOnFun]
  simp only [ofPred_and, ofPred_forall]
  apply_rules [IsClosed.isComplete, IsClosed.inter]
  · exact UniformOnFun.isClosed_setOfPred_continuous h
  · exact isClosed_iInter fun m => isClosed_iInter fun i =>
      isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq H (H.add H)
  · exact isClosed_iInter fun m => isClosed_iInter fun i =>
      isClosed_iInter fun c => isClosed_iInter fun x => isClosed_eq H (H.const_smul _)

中文:
定理 completeSpace
  条件: (h : 是余herentWith {s : 集合 (Π i, E i) | IsVonNBounded 𝕜 s})
  证明: by
  classical
  wlog hF : T2Space F generalizing F
  · rw [(isUniformInducing_postcomp (SeparationQuotient.mkCLM _ _)
      SeparationQuotient.isUniformInducing_mk).completeSpace_congr]
    · exact this inferInstance
    · intro f
      use (SeparationQuotient.outCLM _ _).compContinuousMultilinearMap f
      simp [DFunLike.ext_iff]
  have H : forall {m : Π i, E i},
      Continuous fun f : (Π i, E i) ->ᵤ[{s | IsVonNBounded 𝕜 s}] F => toFun _ f m :=
    (uniformContinuous_eval (sUnion_isVonNBounded_eq_univ) _).continuous
  rw [completeSpace_iff_isComplete_range isUniformInducing_toUniformOnFun]; rw [range_toUniformOnFun]
  simp only [ofPred_and, ofPred_forall]
  apply_rules [IsClosed.isComplete, IsClosed.inter]
  · exact UniformOnFun.isClosed_setOfPred_continuous h
  · exact isClosed_iInter fun m => isClosed_iInter fun i =>
      isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq H (H.add H)
  · exact isClosed_iInter fun m => isClosed_iInter fun i =>
      isClosed_iInter fun c => isClosed_iInter fun x => isClosed_eq H (H.const_smul _)

Depends on / 依赖: Continuous, DFunLike, DFunLike.ext_iff, IsVonNBounded, SeparationQuotient, SeparationQuotient.isUniformInducing_mk, SeparationQuotient.mkCLM, SeparationQuotient.outCLM, T2Space, classical, compContinuousMultilinearMap, completeSpace, completeSpace_congr, continuous, ext_iff, generalizing, isUniformInducing_mk, isUniformInducing_postcomp, outCLM, sUnion_isVonNBounded_eq_univ
-/
theorem completeSpace (h : IsCoherentWith {s : Set (Π i, E i) | IsVonNBounded 𝕜 s}) :
    CompleteSpace (ContinuousMultilinearMap 𝕜 E F) := by
  classical
  wlog hF : T2Space F generalizing F
  · rw [(isUniformInducing_postcomp (SeparationQuotient.mkCLM _ _)
      SeparationQuotient.isUniformInducing_mk).completeSpace_congr]
    · exact this inferInstance
    · intro f
      use (SeparationQuotient.outCLM _ _).compContinuousMultilinearMap f
      simp [DFunLike.ext_iff]
  have H : forall {m : Π i, E i},
      Continuous fun f : (Π i, E i) ->ᵤ[{s | IsVonNBounded 𝕜 s}] F => toFun _ f m :=
    (uniformContinuous_eval (sUnion_isVonNBounded_eq_univ) _).continuous
  rw [completeSpace_iff_isComplete_range isUniformInducing_toUniformOnFun]; rw [range_toUniformOnFun]
  simp only [ofPred_and, ofPred_forall]
  apply_rules [IsClosed.isComplete, IsClosed.inter]
  · exact UniformOnFun.isClosed_setOfPred_continuous h
  · exact isClosed_iInter fun m => isClosed_iInter fun i =>
      isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq H (H.add H)
  · exact isClosed_iInter fun m => isClosed_iInter fun i =>
      isClosed_iInter fun c => isClosed_iInter fun x => isClosed_eq H (H.const_smul _)

/--
Instance `instCompleteSpace` / 实例 `instCompleteSpace`

English:
instance instCompleteSpace
  signature: [forall i, IsTopologicalAddGroup (E i)] [SequentialSpace (Π i, E i)]
  body: completeSpace .of_seq fun _u x hux => (hux.isVonNBounded_range 𝕜).insert x

中文:
实例 instCompleteSpace
  签名: [对任意 i, 是拓扑加群 (E i)] [Sequential空间 (Π i, E i)]
  定义体: completeSpace .of_seq fun _u x hux => (hux.isVonNBounded_range 𝕜).insert x

Depends on / 依赖: completeSpace, hux.isVonNBounded_range, insert, isVonNBounded_range, of_seq
-/
instance instCompleteSpace [forall i, IsTopologicalAddGroup (E i)] [SequentialSpace (Π i, E i)] :
    CompleteSpace (ContinuousMultilinearMap 𝕜 E F) :=
completeSpace .of_seq fun _u x hux => (hux.isVonNBounded_range 𝕜).insert x

end CompleteSpace

section RestrictScalars

variable (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
  [forall i, Module 𝕜' (E i)] [forall i, IsScalarTower 𝕜' 𝕜 (E i)] [Module 𝕜' F] [IsScalarTower 𝕜' 𝕜 F]
  [forall i, ContinuousSMul 𝕜 (E i)]

set_option backward.isDefEq.respectTransparency false in
@[fun_prop]
/--
theorem `isUniformEmbedding_restrictScalars` / 定理 `isUniformEmbedding_restrictScalars`

English:
theorem isUniformEmbedding_restrictScalars
  proof: by
  let : NontriviallyNormedField 𝕜 :=
    ⟨let ⟨x, hx⟩ := @NontriviallyNormedField.non_trivial 𝕜' _; ⟨algebraMap 𝕜' 𝕜 x, by simpa⟩⟩
  rw [← isUniformEmbedding_toUniformOnFun.of_comp_iff]
  convert! isUniformEmbedding_toUniformOnFun using 4 with s
  exact ⟨fun h => h.extend_scalars _, fun h => h.restrict_scalars _⟩

@[fun_prop]

中文:
定理 isUniformEmbedding_restrictScalars
  证明: by
  let : NontriviallyNormedField 𝕜 :=
    ⟨let ⟨x, hx⟩ := @NontriviallyNormedField.non_trivial 𝕜' _; ⟨algebraMap 𝕜' 𝕜 x, by simpa⟩⟩
  rw [← isUniformEmbedding_toUniformOnFun.of_comp_iff]
  convert! isUniformEmbedding_toUniformOnFun using 4 with s
  exact ⟨fun h => h.extend_scalars _, fun h => h.restrict_scalars _⟩

@[fun_prop]

Depends on / 依赖: NontriviallyNormedField, NontriviallyNormedField.non_trivial, algebraMap, convert, extend_scalars, h.extend_scalars, h.restrict_scalars, isUniformEmbedding_toUniformOnFun, isUniformEmbedding_toUniformOnFun.of_comp_iff, non_trivial, of_comp_iff, restrict_scalars
-/
theorem isUniformEmbedding_restrictScalars :
    IsUniformEmbedding
      (restrictScalars 𝕜' : ContinuousMultilinearMap 𝕜 E F -> ContinuousMultilinearMap 𝕜' E F) := by
  let : NontriviallyNormedField 𝕜 :=
    ⟨let ⟨x, hx⟩ := @NontriviallyNormedField.non_trivial 𝕜' _; ⟨algebraMap 𝕜' 𝕜 x, by simpa⟩⟩
  rw [← isUniformEmbedding_toUniformOnFun.of_comp_iff]
  convert! isUniformEmbedding_toUniformOnFun using 4 with s
  exact ⟨fun h => h.extend_scalars _, fun h => h.restrict_scalars _⟩

@[fun_prop]
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
    UniformContinuous
      (restrictScalars 𝕜' : ContinuousMultilinearMap 𝕜 E F -> ContinuousMultilinearMap 𝕜' E F) :=
  (isUniformEmbedding_restrictScalars 𝕜').uniformContinuous

end RestrictScalars

end IsUniformAddGroup

variable [TopologicalSpace F] [IsTopologicalAddGroup F]

/--
Instance `instIsTopologicalAddGroup` / 实例 `instIsTopologicalAddGroup`

English:
instance instIsTopologicalAddGroup
  signature: : IsTopologicalAddGroup (ContinuousMultilinearMap 𝕜 E F)
  body: letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  inferInstance

中文:
实例 instIsTopologicalAddGroup
  签名: : 是拓扑加群 (连续多重线性映射 𝕜 E F)
  定义体: letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  inferInstance

Depends on / 依赖: IsTopologicalAddGroup, IsTopologicalAddGroup.rightUniformSpace, isUniformAddGroup_of_addCommGroup, rightUniformSpace
-/
instance instIsTopologicalAddGroup : IsTopologicalAddGroup (ContinuousMultilinearMap 𝕜 E F) :=
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  inferInstance

/--
Instance `instContinuousConstSMul` / 实例 `instContinuousConstSMul`

English:
instance instContinuousConstSMul
  body: by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  infer_instance

中文:
实例 instContinuousConstSMul
  定义体: by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  infer_instance

Depends on / 依赖: IsTopologicalAddGroup, IsTopologicalAddGroup.rightUniformSpace, infer_instance, isUniformAddGroup_of_addCommGroup, rightUniformSpace
-/
instance instContinuousConstSMul
    {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜 M F] [ContinuousConstSMul M F] :
    ContinuousConstSMul M (ContinuousMultilinearMap 𝕜 E F) := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  infer_instance

/--
Instance `instContinuousSMul` / 实例 `instContinuousSMul`

English:
instance instContinuousSMul
  signature: [ContinuousSMul 𝕜 F]
  body: letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  let φ : ContinuousMultilinearMap 𝕜 E F ->ₗ[𝕜] (Π i, E i) -> F :=
    { toFun := (↑), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  UniformOnFun.continuousSMul_induced_of_image_bounded _ _ _ _ φ
    isEmbedding_toUniformOnFun.isInducing fun _ _ hu => hu.image_multilinear _

中文:
实例 instContinuousSMul
  签名: [连续标量乘法 𝕜 F]
  定义体: letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  let φ : ContinuousMultilinearMap 𝕜 E F ->ₗ[𝕜] (Π i, E i) -> F :=
    { toFun := (↑), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  UniformOnFun.continuousSMul_induced_of_image_bounded _ _ _ _ φ
    isEmbedding_toUniformOnFun.isInducing fun _ _ hu => hu.image_multilinear _

Depends on / 依赖: ContinuousMultilinearMap, IsTopologicalAddGroup, IsTopologicalAddGroup.rightUniformSpace, UniformOnFun, UniformOnFun.continuousSMul_induced_of_image_bounded, continuousSMul_induced_of_image_bounded, hu.image_multilinear, image_multilinear, isEmbedding_toUniformOnFun, isEmbedding_toUniformOnFun.isInducing, isInducing, isUniformAddGroup_of_addCommGroup, map_add, map_smul, rightUniformSpace
-/
instance instContinuousSMul [ContinuousSMul 𝕜 F] :
    ContinuousSMul 𝕜 (ContinuousMultilinearMap 𝕜 E F) :=
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  let φ : ContinuousMultilinearMap 𝕜 E F ->ₗ[𝕜] (Π i, E i) -> F :=
    { toFun := (↑), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  UniformOnFun.continuousSMul_induced_of_image_bounded _ _ _ _ φ
    isEmbedding_toUniformOnFun.isInducing fun _ _ hu => hu.image_multilinear _

/--
theorem `hasBasis_nhds_zero_of_basis` / 定理 `hasBasis_nhds_zero_of_basis`

English:
theorem hasBasis_nhds_zero_of_basis
  statement: {ι : Type*} {p : ι -> Prop} {b : ι -> Set F}
  proof: by
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  have : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  rw [nhds_induced]
  refine (UniformOnFun.hasBasis_nhds_zero_of_basis _ ?_ ?_ h).comap DFunLike.coe
  · exact ⟨∅, isVonNBounded_empty _ _⟩
  · exact directedOn_of_sup_mem fun _ _ => Bornology.IsVonNBounded.union

中文:
定理 hasBasis_nhds_zero_of_basis
  结论: {ι : 类型} {p : ι -> 命题} {b : ι -> 集合 F}
  证明: by
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  have : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  rw [nhds_induced]
  refine (UniformOnFun.hasBasis_nhds_zero_of_basis _ ?_ ?_ h).comap DFunLike.coe
  · exact ⟨∅, isVonNBounded_empty _ _⟩
  · exact directedOn_of_sup_mem fun _ _ => Bornology.IsVonNBounded.union

Depends on / 依赖: Bornology, Bornology.IsVonNBounded.union, DFunLike, DFunLike.coe, IsTopologicalAddGroup, IsTopologicalAddGroup.rightUniformSpace, IsUniformAddGroup, IsVonNBounded, UniformOnFun, UniformOnFun.hasBasis_nhds_zero_of_basis, UniformSpace, directedOn_of_sup_mem, hasBasis_nhds_zero_of_basis, isUniformAddGroup_of_addCommGroup, isVonNBounded_empty, nhds_induced, rightUniformSpace
-/
theorem hasBasis_nhds_zero_of_basis {ι : Type*} {p : ι -> Prop} {b : ι -> Set F}
    (h : (𝓝 (0 : F)).HasBasis p b) :
    (𝓝 (0 : ContinuousMultilinearMap 𝕜 E F)).HasBasis
      (fun Si : Set (Π i, E i) × ι => IsVonNBounded 𝕜 Si.1 ∧ p Si.2)
      fun Si => { f | MapsTo f Si.1 (b Si.2) } := by
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  have : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  rw [nhds_induced]
  refine (UniformOnFun.hasBasis_nhds_zero_of_basis _ ?_ ?_ h).comap DFunLike.coe
  · exact ⟨∅, isVonNBounded_empty _ _⟩
  · exact directedOn_of_sup_mem fun _ _ => Bornology.IsVonNBounded.union

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
    (𝓝 (0 : ContinuousMultilinearMap 𝕜 E F)).HasBasis
      (fun SV : Set (Π i, E i) × Set F => IsVonNBounded 𝕜 SV.1 ∧ SV.2 in 𝓝 0) fun SV =>
      { f | MapsTo f SV.1 SV.2 } :=
  hasBasis_nhds_zero_of_basis (Filter.basis_sets _)

/--
theorem `eventually_nhds_zero_mapsTo` / 定理 `eventually_nhds_zero_mapsTo`

English:
theorem eventually_nhds_zero_mapsTo
  statement: {s : Set (forall i, E i)} (hs : IsVonNBounded 𝕜 s)
  proof: hasBasis_nhds_zero.mem_of_mem (i := (s, U)) ⟨hs, hu⟩

中文:
定理 eventually_nhds_zero_mapsTo
  结论: {s : 集合 (对任意 i, E i)} (hs : IsVonNBounded 𝕜 s)
  证明: hasBasis_nhds_zero.mem_of_mem (i := (s, U)) ⟨hs, hu⟩

Depends on / 依赖: hasBasis_nhds_zero, hasBasis_nhds_zero.mem_of_mem, mem_of_mem
-/
theorem eventually_nhds_zero_mapsTo {s : Set (forall i, E i)} (hs : IsVonNBounded 𝕜 s)
    {U : Set F} (hu : U in 𝓝 0) :
    forallᶠ f : ContinuousMultilinearMap 𝕜 E F in 𝓝 0, MapsTo f s U :=
  hasBasis_nhds_zero.mem_of_mem (i := (s, U)) ⟨hs, hu⟩

/--
theorem `isVonNBounded_image2_apply` / 定理 `isVonNBounded_image2_apply`

English:
theorem isVonNBounded_image2_apply
  statement: [ContinuousConstSMul 𝕜 F]
  proof: by
  intro U hU
  filter_upwards [hS (eventually_nhds_zero_mapsTo hs hU)] with c hc
  rw [image2_subset_iff]
  intro f hf x hx
  rcases hc hf with ⟨g, hg, rfl⟩
  exact smul_mem_smul_set (hg hx)

中文:
定理 isVonNBounded_image2_apply
  结论: [连续常数标量乘法 𝕜 F]
  证明: by
  intro U hU
  filter_upwards [hS (eventually_nhds_zero_mapsTo hs hU)] with c hc
  rw [image2_subset_iff]
  intro f hf x hx
  rcases hc hf with ⟨g, hg, rfl⟩
  exact smul_mem_smul_set (hg hx)

Depends on / 依赖: eventually_nhds_zero_mapsTo, filter_upwards, image2_subset_iff, smul_mem_smul_set
-/
theorem isVonNBounded_image2_apply [ContinuousConstSMul 𝕜 F]
    {S : Set (ContinuousMultilinearMap 𝕜 E F)} (hS : IsVonNBounded 𝕜 S)
    {s : Set (forall i, E i)} (hs : IsVonNBounded 𝕜 s) :
    IsVonNBounded 𝕜 (Set.image2 (fun f x => f x) S s) := by
  intro U hU
  filter_upwards [hS (eventually_nhds_zero_mapsTo hs hU)] with c hc
  rw [image2_subset_iff]
  intro f hf x hx
  rcases hc hf with ⟨g, hg, rfl⟩
  exact smul_mem_smul_set (hg hx)

section CompContinuousLinearMap
variable {E₁ : ι -> Type*} [forall i, TopologicalSpace (E₁ i)] [ContinuousConstSMul 𝕜 F]
  [forall i, AddCommGroup (E₁ i)] [forall i, Module 𝕜 (E₁ i)]

/-- `ContinuousMultilinearMap.compContinuousLinearMap` as a bundled continuous linear map.
Given a family of continuous linear maps `f : Π i, E i →L[𝕜] E₁ i`,
this function returns a continuous linear maps between the spaces of continuous multilinear maps
on `Π i, E₁ i` and on `Π i, E i`.
The map sends `g` to the map given by `v ↦ g (fun i ↦ f i (v i))`.

Actually, the map is multilinear in `f`,
see `ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear`.

For a version fixing `g` and varying `f`, see `compContinuousLinearMapLRight`. -/
@[simps! apply]
/--
Definition of `compContinuousLinearMapL` / `compContinuousLinearMapL` 的定义

English:
definition compContinuousLinearMapL
  signature: (f : forall i, E i ->L[𝕜] E₁ i)
  body: letI aux : ContinuousMultilinearMap 𝕜 E₁ F ->ₗ[𝕜] ContinuousMultilinearMap 𝕜 E F :=
    { toFun g := g.compContinuousLinearMap f
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
  { toLinearMap := aux
    cont := by
      apply continuous_of_tendsto_nhds_zero aux
      rw [hasBasis_nhds_zero.tendsto_iff hasBasis_nhds_zero]
      rintro ⟨U, V⟩ ⟨hU, hV⟩
      set φ : (forall i, E i) ->L[𝕜] (forall i, E₁ i) := .piMap f
      exact ⟨(φ '' U, V), ⟨hU.image φ, hV⟩, fun g hg => hg.comp (mapsTo_image _ _)⟩ }

@[fun_prop]

中文:
定义 compContinuousLinearMapL
  签名: (f : 对任意 i, E i ->L[𝕜] E₁ i)
  定义体: letI aux : ContinuousMultilinearMap 𝕜 E₁ F ->ₗ[𝕜] ContinuousMultilinearMap 𝕜 E F :=
    { toFun g := g.compContinuousLinearMap f
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
  { toLinearMap := aux
    cont := by
      apply continuous_of_tendsto_nhds_zero aux
      rw [hasBasis_nhds_zero.tendsto_iff hasBasis_nhds_zero]
      rintro ⟨U, V⟩ ⟨hU, hV⟩
      set φ : (forall i, E i) ->L[𝕜] (forall i, E₁ i) := .piMap f
      exact ⟨(φ '' U, V), ⟨hU.image φ, hV⟩, fun g hg => hg.comp (mapsTo_image _ _)⟩ }

@[fun_prop]

Depends on / 依赖: ContinuousMultilinearMap, compContinuousLinearMap, continuous_of_tendsto_nhds_zero, g.compContinuousLinearMap, hU.image, hasBasis_nhds_zero, hasBasis_nhds_zero.tendsto_iff, hg.comp, map_add, map_smul, mapsTo_image, tendsto_iff, toLinearMap
-/
def compContinuousLinearMapL (f : forall i, E i ->L[𝕜] E₁ i) :
    ContinuousMultilinearMap 𝕜 E₁ F ->L[𝕜] ContinuousMultilinearMap 𝕜 E F :=
  letI aux : ContinuousMultilinearMap 𝕜 E₁ F ->ₗ[𝕜] ContinuousMultilinearMap 𝕜 E F :=
    { toFun g := g.compContinuousLinearMap f
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
  { toLinearMap := aux
    cont := by
      apply continuous_of_tendsto_nhds_zero aux
      rw [hasBasis_nhds_zero.tendsto_iff hasBasis_nhds_zero]
      rintro ⟨U, V⟩ ⟨hU, hV⟩
      set φ : (forall i, E i) ->L[𝕜] (forall i, E₁ i) := .piMap f
      exact ⟨(φ '' U, V), ⟨hU.image φ, hV⟩, fun g hg => hg.comp (mapsTo_image _ _)⟩ }

@[fun_prop]
/--
theorem `continuous_precomp` / 定理 `continuous_precomp`

English:
theorem continuous_precomp
  given: (f : forall i, E i ->L[𝕜] E₁ i)
  proof: map_continuous (compContinuousLinearMapL f)

中文:
定理 continuous_precomp
  条件: (f : 对任意 i, E i ->L[𝕜] E₁ i)
  证明: map_continuous (compContinuousLinearMapL f)

Depends on / 依赖: compContinuousLinearMapL, map_continuous
-/
theorem continuous_precomp (f : forall i, E i ->L[𝕜] E₁ i) :
    Continuous fun g : ContinuousMultilinearMap 𝕜 E₁ F => g.compContinuousLinearMap f :=
  map_continuous (compContinuousLinearMapL f)

end CompContinuousLinearMap

variable [forall i, ContinuousSMul 𝕜 (E i)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousEvalConst (ContinuousMultilinearMap 𝕜 E F) (Π i, E i) F
  body: let _ := IsTopologicalAddGroup.rightUniformSpace F
    have _ := isUniformAddGroup_of_addCommGroup (G := F)
    (uniformContinuous_eval_const x).continuous

中文:
实例 :
  签名: 余ntinuousEvalConst (连续多重线性映射 𝕜 E F) (Π i, E i) F
  定义体: let _ := IsTopologicalAddGroup.rightUniformSpace F
    have _ := isUniformAddGroup_of_addCommGroup (G := F)
    (uniformContinuous_eval_const x).continuous

Depends on / 依赖: IsTopologicalAddGroup, IsTopologicalAddGroup.rightUniformSpace, continuous, isUniformAddGroup_of_addCommGroup, rightUniformSpace, uniformContinuous_eval_const
-/
instance : ContinuousEvalConst (ContinuousMultilinearMap 𝕜 E F) (Π i, E i) F where
  continuous_eval_const x :=
    let _ := IsTopologicalAddGroup.rightUniformSpace F
    have _ := isUniformAddGroup_of_addCommGroup (G := F)
    (uniformContinuous_eval_const x).continuous

/--
Instance `instT2Space` / 实例 `instT2Space`

English:
instance instT2Space
  signature: [T2Space F]
  body: .of_injective_continuous DFunLike.coe_injective continuous_coeFun

中文:
实例 instT2Space
  签名: [T2空间 F]
  定义体: .of_injective_continuous DFunLike.coe_injective continuous_coeFun

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective, continuous_coeFun, of_injective_continuous
-/
instance instT2Space [T2Space F] : T2Space (ContinuousMultilinearMap 𝕜 E F) :=
  .of_injective_continuous DFunLike.coe_injective continuous_coeFun

/--
Instance `instT3Space` / 实例 `instT3Space`

English:
instance instT3Space
  signature: [T2Space F]
  body: inferInstance

中文:
实例 instT3Space
  签名: [T2空间 F]
  定义体: inferInstance
-/
instance instT3Space [T2Space F] : T3Space (ContinuousMultilinearMap 𝕜 E F) :=
  inferInstance

section RestrictScalars

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
  [forall i, Module 𝕜' (E i)] [forall i, IsScalarTower 𝕜' 𝕜 (E i)] [Module 𝕜' F] [IsScalarTower 𝕜' 𝕜 F]

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
    IsEmbedding
      (restrictScalars 𝕜' : ContinuousMultilinearMap 𝕜 E F -> ContinuousMultilinearMap 𝕜' E F) :=
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
    Continuous
      (restrictScalars 𝕜' : ContinuousMultilinearMap 𝕜 E F -> ContinuousMultilinearMap 𝕜' E F) :=
  isEmbedding_restrictScalars.continuous

variable (𝕜') in
/-- `ContinuousMultilinearMap.restrictScalars` as a `ContinuousLinearMap`. -/
@[simps -fullyApplied apply]
/--
Definition of `restrictScalarsLinear` / `restrictScalarsLinear` 的定义

English:
definition restrictScalarsLinear
  signature: [ContinuousConstSMul 𝕜' F]
  body: restrictScalars 𝕜'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 restrictScalarsLinear
  签名: [连续常数标量乘法 𝕜' F]
  定义体: restrictScalars 𝕜'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: restrictScalars
-/
def restrictScalarsLinear [ContinuousConstSMul 𝕜' F] :
    ContinuousMultilinearMap 𝕜 E F ->L[𝕜'] ContinuousMultilinearMap 𝕜' E F where
  toFun := restrictScalars 𝕜'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end RestrictScalars

variable (𝕜 E F)

/--
Definition of `apply` / `apply` 的定义

English:
definition apply
  signature: [ContinuousConstSMul 𝕜 F] (m : Π i, E i)
  body: c m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 apply
  签名: [连续常数标量乘法 𝕜 F] (m : Π i, E i)
  定义体: c m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
-/
def apply [ContinuousConstSMul 𝕜 F] (m : Π i, E i) : ContinuousMultilinearMap 𝕜 E F ->L[𝕜] F where
  toFun c := c m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {𝕜 E F}

@[simp]
/--
lemma `apply_apply` / 引理 `apply_apply`

English:
lemma apply_apply
  given: [ContinuousConstSMul 𝕜 F] {m : Π i, E i} {c : ContinuousMultilinearMap 𝕜 E F}
  proof: rfl

中文:
引理 apply_apply
  条件: [连续常数标量乘法 𝕜 F] {m : Π i, E i} {c : 连续多重线性映射 𝕜 E F}
  证明: rfl
-/
lemma apply_apply [ContinuousConstSMul 𝕜 F] {m : Π i, E i} {c : ContinuousMultilinearMap 𝕜 E F} :
    apply 𝕜 E F m c = c m := rfl

/--
theorem `hasSum_eval` / 定理 `hasSum_eval`

English:
theorem hasSum_eval
  statement: {α : Type*} {p : α -> ContinuousMultilinearMap 𝕜 E F}
  proof: h.map (applyAddHom m) (continuous_eval_const m)

中文:
定理 hasSum_eval
  结论: {α : 类型} {p : α -> 连续多重线性映射 𝕜 E F}
  证明: h.map (applyAddHom m) (continuous_eval_const m)

Depends on / 依赖: applyAddHom, continuous_eval_const, h.map
-/
theorem hasSum_eval {α : Type*} {p : α -> ContinuousMultilinearMap 𝕜 E F}
    {q : ContinuousMultilinearMap 𝕜 E F} (h : HasSum p q) (m : Π i, E i) :
    HasSum (fun a => p a m) (q m) :=
  h.map (applyAddHom m) (continuous_eval_const m)

/--
theorem `tsum_eval` / 定理 `tsum_eval`

English:
theorem tsum_eval
  statement: [T2Space F] {α : Type*} {p : α -> ContinuousMultilinearMap 𝕜 E F} (hp : Summable p)
  proof: (hasSum_eval hp.hasSum m).tsum_eq.symm

中文:
定理 tsum_eval
  结论: [T2空间 F] {α : 类型} {p : α -> 连续多重线性映射 𝕜 E F} (hp : Summable p)
  证明: (hasSum_eval hp.hasSum m).tsum_eq.symm

Depends on / 依赖: hasSum, hasSum_eval, hp.hasSum, tsum_eq, tsum_eq.symm
-/
theorem tsum_eval [T2Space F] {α : Type*} {p : α -> ContinuousMultilinearMap 𝕜 E F} (hp : Summable p)
    (m : Π i, E i) : (∑' a, p a) m = ∑' a, p a m :=
  (hasSum_eval hp.hasSum m).tsum_eq.symm

end ContinuousMultilinearMap

namespace ContinuousLinearMap

variable {𝕜 ι : Type*} {E : ι -> Type*} {F G : Type*} [NormedField 𝕜] [forall i, TopologicalSpace (E i)]
  [forall i, AddCommGroup (E i)] [forall i, Module 𝕜 (E i)]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul 𝕜 F]
  [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousConstSMul 𝕜 G]

variable (𝕜 E F G) in
/--
Definition of `compContinuousMultilinearMapL` / `compContinuousMultilinearMapL` 的定义

English:
definition compContinuousMultilinearMapL
  signature: :
  body: letI aux : (F ->L[𝕜] G) ->ₗ[𝕜]
      ContinuousMultilinearMap 𝕜 E F ->L[𝕜] ContinuousMultilinearMap 𝕜 E G :=
    { toFun g :=
        letI aux₁ : ContinuousMultilinearMap 𝕜 E F ->ₗ[𝕜] ContinuousMultilinearMap 𝕜 E G :=
          { toFun := g.compContinuousMultilinearMap
            map_add' _ _ := by ext; simp
            map_smul' _ _ := by ext; simp }
        { toLinearMap := aux₁
          cont := by
            apply continuous_of_tendsto_nhds_zero aux₁
            rw [ContinuousMultilinearMap.hasBasis_nhds_zero.tendsto_iff
              ContinuousMultilinearMap.hasBasis_nhds_zero]
            rintro ⟨U, V⟩ ⟨hU, hV⟩
            refine ⟨(U, g ⁻¹' V), ⟨hU, ?_⟩, ?_⟩
· exact (map_continuous g).tendsto 0 by simpa
            · exact fun f hf => hf
        }
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
  { toLinearMap := aux
    cont := by
      apply continuous_of_tendsto_nhds_zero aux
      rw [ContinuousLinearMap.hasBasis_nhds_zero.tendsto_iff <|
ContinuousLinearMap.hasBasis_nhds_zero_of_basis
        ContinuousMultilinearMap.hasBasis_nhds_zero]
      rintro ⟨U, V, W⟩ ⟨hU, hV, hW⟩
      refine ⟨(.image2 (fun f v => f v) U V, W), ⟨?_, hW⟩, ?_⟩
      · exact ContinuousMultilinearMap.isVonNBounded_image2_apply hU hV
· exact fun g hg f hf m hm => hg _ mem_image2_of_mem hf hm }

@[simp]

中文:
定义 compContinuousMultilinearMapL
  签名: :
  定义体: letI aux : (F ->L[𝕜] G) ->ₗ[𝕜]
      ContinuousMultilinearMap 𝕜 E F ->L[𝕜] ContinuousMultilinearMap 𝕜 E G :=
    { toFun g :=
        letI aux₁ : ContinuousMultilinearMap 𝕜 E F ->ₗ[𝕜] ContinuousMultilinearMap 𝕜 E G :=
          { toFun := g.compContinuousMultilinearMap
            map_add' _ _ := by ext; simp
            map_smul' _ _ := by ext; simp }
        { toLinearMap := aux₁
          cont := by
            apply continuous_of_tendsto_nhds_zero aux₁
            rw [ContinuousMultilinearMap.hasBasis_nhds_zero.tendsto_iff
              ContinuousMultilinearMap.hasBasis_nhds_zero]
            rintro ⟨U, V⟩ ⟨hU, hV⟩
            refine ⟨(U, g ⁻¹' V), ⟨hU, ?_⟩, ?_⟩
· exact (map_continuous g).tendsto 0 by simpa
            · exact fun f hf => hf
        }
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
  { toLinearMap := aux
    cont := by
      apply continuous_of_tendsto_nhds_zero aux
      rw [ContinuousLinearMap.hasBasis_nhds_zero.tendsto_iff <|
ContinuousLinearMap.hasBasis_nhds_zero_of_basis
        ContinuousMultilinearMap.hasBasis_nhds_zero]
      rintro ⟨U, V, W⟩ ⟨hU, hV, hW⟩
      refine ⟨(.image2 (fun f v => f v) U V, W), ⟨?_, hW⟩, ?_⟩
      · exact ContinuousMultilinearMap.isVonNBounded_image2_apply hU hV
· exact fun g hg f hf m hm => hg _ mem_image2_of_mem hf hm }

@[simp]

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.hasBasis_nhds_zero, ContinuousMultilinearMap.hasBasis_nhds_zero.tendsto_iff, compContinuousMultilinearMap, continuous_of_tendsto_nhds_zero, g.compContinuousMultilinearMap, hasBasis_nhds_zero, map_add, map_smul, tendsto_iff, toLinearMap
-/
def compContinuousMultilinearMapL :
    (F ->L[𝕜] G) ->L[𝕜] ContinuousMultilinearMap 𝕜 E F ->L[𝕜] ContinuousMultilinearMap 𝕜 E G :=
  letI aux : (F ->L[𝕜] G) ->ₗ[𝕜]
      ContinuousMultilinearMap 𝕜 E F ->L[𝕜] ContinuousMultilinearMap 𝕜 E G :=
    { toFun g :=
        letI aux₁ : ContinuousMultilinearMap 𝕜 E F ->ₗ[𝕜] ContinuousMultilinearMap 𝕜 E G :=
          { toFun := g.compContinuousMultilinearMap
            map_add' _ _ := by ext; simp
            map_smul' _ _ := by ext; simp }
        { toLinearMap := aux₁
          cont := by
            apply continuous_of_tendsto_nhds_zero aux₁
            rw [ContinuousMultilinearMap.hasBasis_nhds_zero.tendsto_iff
              ContinuousMultilinearMap.hasBasis_nhds_zero]
            rintro ⟨U, V⟩ ⟨hU, hV⟩
            refine ⟨(U, g ⁻¹' V), ⟨hU, ?_⟩, ?_⟩
· exact (map_continuous g).tendsto 0 by simpa
            · exact fun f hf => hf
        }
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
  { toLinearMap := aux
    cont := by
      apply continuous_of_tendsto_nhds_zero aux
      rw [ContinuousLinearMap.hasBasis_nhds_zero.tendsto_iff <|
ContinuousLinearMap.hasBasis_nhds_zero_of_basis
        ContinuousMultilinearMap.hasBasis_nhds_zero]
      rintro ⟨U, V, W⟩ ⟨hU, hV, hW⟩
      refine ⟨(.image2 (fun f v => f v) U V, W), ⟨?_, hW⟩, ?_⟩
      · exact ContinuousMultilinearMap.isVonNBounded_image2_apply hU hV
· exact fun g hg f hf m hm => hg _ mem_image2_of_mem hf hm }

@[simp]
/--
theorem `compContinuousMultilinearMapL_apply` / 定理 `compContinuousMultilinearMapL_apply`

English:
theorem compContinuousMultilinearMapL_apply
  given: (g : F ->L[𝕜] G) (f : ContinuousMultilinearMap 𝕜 E F)
  proof: rfl

@[fun_prop]

中文:
定理 compContinuousMultilinearMapL_apply
  条件: (g : F ->L[𝕜] G) (f : 连续多重线性映射 𝕜 E F)
  证明: rfl

@[fun_prop]
-/
theorem compContinuousMultilinearMapL_apply (g : F ->L[𝕜] G) (f : ContinuousMultilinearMap 𝕜 E F) :
    compContinuousMultilinearMapL 𝕜 E F G g f = g.compContinuousMultilinearMap f :=
  rfl

@[fun_prop]
/--
theorem `_root_.ContinuousLinearMap.continuous_postcomp_continuousMultilinearMap` / 定理 `_root_.ContinuousLinearMap.continuous_postcomp_continuousMultilinearMap`

English:
theorem _root_.ContinuousLinearMap.continuous_postcomp_continuousMultilinearMap
  given: (g : F ->L[𝕜] G)
  proof: map_continuous (compContinuousMultilinearMapL 𝕜 E F G g)

中文:
定理 _root_.连续线性映射.continuous_postcomp_continuousMultilinearMap
  条件: (g : F ->L[𝕜] G)
  证明: map_continuous (compContinuousMultilinearMapL 𝕜 E F G g)
-/
theorem _root_.ContinuousLinearMap.continuous_postcomp_continuousMultilinearMap (g : F ->L[𝕜] G) :
    Continuous (g.compContinuousMultilinearMap (M₁ := E)) :=
  map_continuous (compContinuousMultilinearMapL 𝕜 E F G g)

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable {𝕜 ι : Type*} {E E₁ : ι -> Type*} {F G : Type*} [NormedField 𝕜]
  [forall i, TopologicalSpace (E i)] [forall i, AddCommGroup (E i)] [forall i, Module 𝕜 (E i)]
  [forall i, TopologicalSpace (E₁ i)] [forall i, AddCommGroup (E₁ i)] [forall i, Module 𝕜 (E₁ i)]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul 𝕜 F]
  [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousConstSMul 𝕜 G]

variable (F) in
/--
Definition of `continuousMultilinearMapCongrLeft` / `continuousMultilinearMapCongrLeft` 的定义

English:
definition continuousMultilinearMapCongrLeft
  signature: (f : forall i, E i ≃L[𝕜] E₁ i)
  body: ContinuousMultilinearMap.compContinuousLinearMapL fun i => ↑(f i)
  invFun := ContinuousMultilinearMap.compContinuousLinearMapL fun i => ↑(f i).symm
  left_inv g := by ext; simp
  right_inv g := by ext; simp

@[simp]

中文:
定义 continuousMultilinearMapCongrLeft
  签名: (f : 对任意 i, E i ≃L[𝕜] E₁ i)
  定义体: ContinuousMultilinearMap.compContinuousLinearMapL fun i => ↑(f i)
  invFun := ContinuousMultilinearMap.compContinuousLinearMapL fun i => ↑(f i).symm
  left_inv g := by ext; simp
  right_inv g := by ext; simp

@[simp]

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.compContinuousLinearMapL, compContinuousLinearMapL
-/
def continuousMultilinearMapCongrLeft (f : forall i, E i ≃L[𝕜] E₁ i) :
    ContinuousMultilinearMap 𝕜 E₁ F ≃L[𝕜] ContinuousMultilinearMap 𝕜 E F where
  __ := ContinuousMultilinearMap.compContinuousLinearMapL fun i => ↑(f i)
  invFun := ContinuousMultilinearMap.compContinuousLinearMapL fun i => ↑(f i).symm
  left_inv g := by ext; simp
  right_inv g := by ext; simp

@[simp]
/--
theorem `continuousMultilinearMapCongrLeft_symm` / 定理 `continuousMultilinearMapCongrLeft_symm`

English:
theorem continuousMultilinearMapCongrLeft_symm
  proof: rfl

@[simp]

中文:
定理 continuousMultilinearMapCongrLeft_symm
  证明: rfl

@[simp]
-/
theorem continuousMultilinearMapCongrLeft_symm
    (f : forall i, E i ≃L[𝕜] E₁ i) :
    (ContinuousLinearEquiv.continuousMultilinearMapCongrLeft F f).symm =
      .continuousMultilinearMapCongrLeft F fun i : ι => (f i).symm :=
  rfl

@[simp]
/--
theorem `continuousMultilinearMapCongrLeft_apply` / 定理 `continuousMultilinearMapCongrLeft_apply`

English:
theorem continuousMultilinearMapCongrLeft_apply
  proof: rfl

中文:
定理 continuousMultilinearMapCongrLeft_apply
  证明: rfl
-/
theorem continuousMultilinearMapCongrLeft_apply
    (g : ContinuousMultilinearMap 𝕜 E₁ F) (f : forall i, E i ≃L[𝕜] E₁ i) :
    ContinuousLinearEquiv.continuousMultilinearMapCongrLeft F f g =
      g.compContinuousLinearMap fun i => (f i : E i ->L[𝕜] E₁ i) :=
  rfl

variable (E) in
/--
Definition of `continuousMultilinearMapCongrRight` / `continuousMultilinearMapCongrRight` 的定义

English:
definition continuousMultilinearMapCongrRight
  signature: (g : F ≃L[𝕜] G)
  body: ContinuousLinearMap.compContinuousMultilinearMapL _ _ _ _ g
  invFun := ContinuousLinearMap.compContinuousMultilinearMapL _ _ _ _ g.symm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

@[simp]

中文:
定义 continuousMultilinearMapCongrRight
  签名: (g : F ≃L[𝕜] G)
  定义体: ContinuousLinearMap.compContinuousMultilinearMapL _ _ _ _ g
  invFun := ContinuousLinearMap.compContinuousMultilinearMapL _ _ _ _ g.symm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.compContinuousMultilinearMapL, compContinuousMultilinearMapL
-/
def continuousMultilinearMapCongrRight (g : F ≃L[𝕜] G) :
    ContinuousMultilinearMap 𝕜 E F ≃L[𝕜] ContinuousMultilinearMap 𝕜 E G where
  __ := ContinuousLinearMap.compContinuousMultilinearMapL _ _ _ _ g
  invFun := ContinuousLinearMap.compContinuousMultilinearMapL _ _ _ _ g.symm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

@[simp]
/--
theorem `continuousMultilinearMapCongrRight_symm` / 定理 `continuousMultilinearMapCongrRight_symm`

English:
theorem continuousMultilinearMapCongrRight_symm
  given: (g : F ≃L[𝕜] G)
  proof: rfl

@[simp]

中文:
定理 continuousMultilinearMapCongrRight_symm
  条件: (g : F ≃L[𝕜] G)
  证明: rfl

@[simp]
-/
theorem continuousMultilinearMapCongrRight_symm (g : F ≃L[𝕜] G) :
    (g.continuousMultilinearMapCongrRight E).symm = g.symm.continuousMultilinearMapCongrRight E :=
  rfl

@[simp]
/--
theorem `continuousMultilinearMapCongrRight_apply` / 定理 `continuousMultilinearMapCongrRight_apply`

English:
theorem continuousMultilinearMapCongrRight_apply
  statement: (g : F ≃L[𝕜] G)
  proof: rfl

中文:
定理 continuousMultilinearMapCongrRight_apply
  结论: (g : F ≃L[𝕜] G)
  证明: rfl
-/
theorem continuousMultilinearMapCongrRight_apply (g : F ≃L[𝕜] G)
    (f : ContinuousMultilinearMap 𝕜 E F) :
    g.continuousMultilinearMapCongrRight E f = (g : F ->L[𝕜] G).compContinuousMultilinearMap f :=
  rfl

end ContinuousLinearEquiv
