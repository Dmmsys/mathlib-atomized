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

/-! ### Topology of bounded convergence  -/

variable {𝕜₁ 𝕜₂ 𝕜₃ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃] {σ : 𝕜₁ →+* 𝕜₂}
  {τ : 𝕜₂ →+* 𝕜₃} {ρ : 𝕜₁ →+* 𝕜₃} [RingHomCompTriple σ τ ρ] {E F G : Type*} [AddCommGroup E]
  [Module 𝕜₁ E] [AddCommGroup F] [Module 𝕜₂ F]
  [AddCommGroup G] [Module 𝕜₃ G] [TopologicalSpace E]

/-- The topology of bounded convergence on `E →L[𝕜] F`. This coincides with the topology induced by
the operator norm when `E` and `F` are normed spaces. -/
/-
**ContinuousLinearMap.topologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：topologicalSpace [TopologicalSpace F] [IsTopologicalAddGroup F] : Topologi
calSpace (E ->SL[σ] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topology of bounded convergence on `E →L[𝕜] F`. This coincides with the topo
logy induced by
the operator norm when `E` and `F` are normed spaces.
-/
instance topologicalSpace [TopologicalSpace F] [IsTopologicalAddGroup F] :
    TopologicalSpace (E →SL[σ] F) :=
  fast_instance% UniformConvergenceCLM.instTopologicalSpace σ F { S | IsVonNBounded 𝕜₁ S }
/-
**ContinuousLinearMap.topologicalAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：topologicalAddGroup [TopologicalSpace F] [IsTopologicalAddGroup F] : IsTop
ologicalAddGroup (E ->SL[σ] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance topologicalAddGroup [TopologicalSpace F] [IsTopologicalAddGroup F] :
    IsTopologicalAddGroup (E →SL[σ] F) :=
  UniformConvergenceCLM.instIsTopologicalAddGroup σ F _
/-
**ContinuousLinearMap.continuousSMul** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：continuousSMul [RingHomSurjective σ] [RingHomIsometric σ] [TopologicalSpac
e F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜₂ F] : ContinuousSMul 𝕜₂ (E ->SL
[σ] F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.continuousSMul`：continuousSMul [RingHomSurjective 
σ] [RingHomIsometric σ] [TopologicalSpace F] [IsTopologicalAddGroup F] [Continuo
usSMul 𝕜₂ F] (𝔖 : Set (Set…
-/
instance continuousSMul [RingHomSurjective σ] [RingHomIsometric σ] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul 𝕜₂ F] : ContinuousSMul 𝕜₂ (E →SL[σ] F) :=
  UniformConvergenceCLM.continuousSMul σ F { S | IsVonNBounded 𝕜₁ S } fun _ hs => hs
/-
**ContinuousLinearMap.uniformSpace** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：uniformSpace [UniformSpace F] [IsUniformAddGroup F] : UniformSpace (E ->SL
[σ] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniformSpace [UniformSpace F] [IsUniformAddGroup F] : UniformSpace (E →SL[σ] F) :=
  fast_instance% UniformConvergenceCLM.instUniformSpace σ F { S | IsVonNBounded 𝕜₁ S }
/-
**ContinuousLinearMap.isUniformAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：isUniformAddGroup [UniformSpace F] [IsUniformAddGroup F] : IsUniformAddGro
up (E ->SL[σ] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isUniformAddGroup [UniformSpace F] [IsUniformAddGroup F] :
    IsUniformAddGroup (E →SL[σ] F) :=
  UniformConvergenceCLM.instIsUniformAddGroup σ F _
/-
**ContinuousLinearMap.instContinuousEvalConst** 是 Mathlib 中的一个实例，位于命名空间 `Continu
ousLinearMap`。
形式化陈述：instContinuousEvalConst [TopologicalSpace F] [IsTopologicalAddGroup F] [Co
ntinuousSMul 𝕜₁ E] : ContinuousEvalConst (E ->SL[σ] F) E F
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.continuousEvalConst`：continuousEvalConst [Topologi
calSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E)) (h𝔖 : ⋃₀ 𝔖 = Set.univ) :
 ContinuousEvalConst (E ->SLᵤ[σ…
· 使用定理 `Bornology.sUnion_isVonNBounded_eq_univ`：sUnion_isVonNBounded_eq_univ : ⋃
₀ Set.ofPred (IsVonNBounded 𝕜) = (Set.univ : Set E)
-/
instance instContinuousEvalConst [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜₁ E] : ContinuousEvalConst (E →SL[σ] F) E F :=
  UniformConvergenceCLM.continuousEvalConst σ F _ Bornology.sUnion_isVonNBounded_eq_univ
/-
**ContinuousLinearMap.instT2Space** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：instT2Space [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul
 𝕜₁ E] [T2Space F] : T2Space (E ->SL[σ] F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.t2Space`：t2Space [TopologicalSpace F] [IsTopologic
alAddGroup F] [T2Space F] (𝔖 : Set (Set E)) (h𝔖 : ⋃₀ 𝔖 = univ) : T2Space (E ->SL
ᵤ[σ, 𝔖] F)
· 使用定理 `Bornology.sUnion_isVonNBounded_eq_univ`：sUnion_isVonNBounded_eq_univ : ⋃
₀ Set.ofPred (IsVonNBounded 𝕜) = (Set.univ : Set E)
-/
instance instT2Space [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜₁ E]
    [T2Space F] : T2Space (E →SL[σ] F) :=
  UniformConvergenceCLM.t2Space σ F _ Bornology.sUnion_isVonNBounded_eq_univ
/-
**ContinuousLinearMap.hasBasis_nhds_zero_of_basis** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousLinearMap`。
形式化陈述：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} [inst : NormedField 𝕜₁] [inst_1 : Normed
Field 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_4}   {F : Type u_5} [inst_2 : AddCommGroup
 E] [inst_3 : _root_.Module 𝕜₁ E] [inst_4 : AddCommGroup F]   [inst_5 : _root_.M
odule 𝕜₂ F] [inst_6 : TopologicalSpace E] [inst_7 : TopologicalSpace F]   [inst_
8 : IsTopologicalAddGroup F] {ι : Type u_7} {p : ι → Prop} {b : ι → Set F},   (n
hds 0).HasBasis p b →     (nhds 0).HasBasis (fun Si => Bornology.IsVonNBounded 𝕜
₁ Si.1 ∧ p Si.2) fun Si => {f | ∀ x ∈ Si.1, f x ∈ b Si.2}
参数：nhds 0；nhds 0；fun Si => Bornology.IsVonNBounded 𝕜₁ Si.1 ∧ p Si.2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.hasBasis_nhds_zero_of_basis`：hasBasis_nhds_zero_of
_basis [TopologicalSpace F] [IsTopologicalAddGroup F] {ι : Type*} (𝔖 : Set (Set 
E)) (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedO…
· 使用定理 `Bornology.isVonNBounded_empty`：isVonNBounded_empty : IsVonNBounded 𝕜 (∅ 
: Set E)
· 使用定理 `directedOn_of_sup_mem`：directedOn_of_sup_mem [SemilatticeSup α] {S : Set
 α} (H : forall ⦃i j⦄, i in S -> j in S -> i ⊔ j in S) : DirectedOn (· <= ·) S
· 使用定理 `Bornology.IsVonNBounded.union`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : S
eminormedRing 𝕜] [inst_1 : SMul 𝕜 E] [inst_2 : Zero E]   [inst_3 : TopologicalSp
ace E] {s₁ s₂ : Set…
-/
protected theorem hasBasis_nhds_zero_of_basis [TopologicalSpace F] [IsTopologicalAddGroup F]
    {ι : Type*} {p : ι → Prop} {b : ι → Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    (𝓝 (0 : E →SL[σ] F)).HasBasis (fun Si : Set E × ι => IsVonNBounded 𝕜₁ Si.1 ∧ p Si.2)
      fun Si => { f : E →SL[σ] F | ∀ x ∈ Si.1, f x ∈ b Si.2 } :=
  UniformConvergenceCLM.hasBasis_nhds_zero_of_basis σ F { S | IsVonNBounded 𝕜₁ S }
    ⟨∅, isVonNBounded_empty 𝕜₁ E⟩
    (directedOn_of_sup_mem fun _ _ => IsVonNBounded.union) h
/-
**ContinuousLinearMap.hasBasis_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} [inst : NormedField 𝕜₁] [inst_1 : Normed
Field 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_4}   {F : Type u_5} [inst_2 : AddCommGroup
 E] [inst_3 : _root_.Module 𝕜₁ E] [inst_4 : AddCommGroup F]   [inst_5 : _root_.M
odule 𝕜₂ F] [inst_6 : TopologicalSpace E] [inst_7 : TopologicalSpace F]   [inst_
8 : IsTopologicalAddGroup F],   (nhds 0).HasBasis (fun SV => Bornology.IsVonNBou
nded 𝕜₁ SV.1 ∧ SV.2 ∈ nhds 0) fun SV => {f | ∀ x ∈ SV.1, f x ∈ SV.2}
参数：nhds 0；fun SV => Bornology.IsVonNBounded 𝕜₁ SV.1 ∧ SV.2 ∈ nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.hasBasis_nhds_zero_of_basis`：∀ {𝕜₁ : Type u_1} {𝕜₂ :
 Type u_2} [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E 
: Type u_4}   {F : Type u_5} [inst_2 …
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
protected theorem hasBasis_nhds_zero [TopologicalSpace F] [IsTopologicalAddGroup F] :
    (𝓝 (0 : E →SL[σ] F)).HasBasis
      (fun SV : Set E × Set F => IsVonNBounded 𝕜₁ SV.1 ∧ SV.2 ∈ (𝓝 0 : Filter F))
      fun SV => { f : E →SL[σ] F | ∀ x ∈ SV.1, f x ∈ SV.2 } :=
  ContinuousLinearMap.hasBasis_nhds_zero_of_basis (𝓝 0).basis_sets
/-
**ContinuousLinearMap.isUniformEmbedding_toUniformOnFun** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousLinearMap`。
形式化陈述：isUniformEmbedding_toUniformOnFun [UniformSpace F] [IsUniformAddGroup F] :
 IsUniformEmbedding fun f : E ->SL[σ] F => UniformOnFun.ofFun {s | Bornology.IsV
onNBounded 𝕜₁ s} f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.isUniformEmbedding_coeFn`：isUniformEmbedding_coeFn
 [UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) : IsUniformEmbedding (
α
-/
theorem isUniformEmbedding_toUniformOnFun [UniformSpace F] [IsUniformAddGroup F] :
    IsUniformEmbedding
      fun f : E →SL[σ] F ↦ UniformOnFun.ofFun {s | Bornology.IsVonNBounded 𝕜₁ s} f :=
  UniformConvergenceCLM.isUniformEmbedding_coeFn ..
/-
**ContinuousLinearMap.uniformContinuousConstSMul** 是 Mathlib 中的一个实例，位于命名空间 `Cont
inuousLinearMap`。
形式化陈述：uniformContinuousConstSMul {M : Type*} [Monoid M] [DistribMulAction M F] [
SMulCommClass 𝕜₂ M F] [UniformSpace F] [IsUniformAddGroup F] [UniformContinuousC
onstSMul M F] : UniformContinuousConstSMul M (E ->SL[σ] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniformContinuousConstSMul
    {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
    [UniformSpace F] [IsUniformAddGroup F] [UniformContinuousConstSMul M F] :
    UniformContinuousConstSMul M (E →SL[σ] F) :=
  UniformConvergenceCLM.instUniformContinuousConstSMul σ F _ _
/-
**ContinuousLinearMap.continuousConstSMul** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：continuousConstSMul {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCom
mClass 𝕜₂ M F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSM
ul M F] : ContinuousConstSMul M (E ->SL[σ] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance continuousConstSMul {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul M F] :
    ContinuousConstSMul M (E →SL[σ] F) :=
  UniformConvergenceCLM.instContinuousConstSMul σ F _ _
/-
**ContinuousLinearMap.nhds_zero_eq_of_basis** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} [inst : NormedField 𝕜₁] [inst_1 : Normed
Field 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_4}   {F : Type u_5} [inst_2 : AddCommGroup
 E] [inst_3 : _root_.Module 𝕜₁ E] [inst_4 : AddCommGroup F]   [inst_5 : _root_.M
odule 𝕜₂ F] [inst_6 : TopologicalSpace E] [inst_7 : TopologicalSpace F]   [inst_
8 : IsTopologicalAddGroup F] {ι : Type u_7} {p : ι → Prop} {b : ι → Set F},   (n
hds 0).HasBasis p b →     nhds 0 = ⨅ s, ⨅ (_ : Bornology.IsVonNBounded 𝕜₁ s), ⨅ 
i, ⨅ (_ : p i), Filter.principal {f | Set.MapsTo (⇑f) s (b i)}
参数：nhds 0；_ : Bornology.IsVonNBounded 𝕜₁ s；_ : p i；⇑f；b i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.nhds_zero_eq_of_basis`：nhds_zero_eq_of_basis [Topo
logicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E)) {ι : Type*} {p : ι -
> Prop} {b : ι -> Set F} (h : (𝓝 …
-/
protected theorem nhds_zero_eq_of_basis [TopologicalSpace F] [IsTopologicalAddGroup F]
    {ι : Type*} {p : ι → Prop} {b : ι → Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    𝓝 (0 : E →SL[σ] F) =
      ⨅ (s : Set E) (_ : IsVonNBounded 𝕜₁ s) (i : ι) (_ : p i),
        𝓟 {f : E →SL[σ] F | MapsTo f s (b i)} :=
  UniformConvergenceCLM.nhds_zero_eq_of_basis _ _ _ h
/-
**ContinuousLinearMap.nhds_zero_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} [inst : NormedField 𝕜₁] [inst_1 : Normed
Field 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_4}   {F : Type u_5} [inst_2 : AddCommGroup
 E] [inst_3 : _root_.Module 𝕜₁ E] [inst_4 : AddCommGroup F]   [inst_5 : _root_.M
odule 𝕜₂ F] [inst_6 : TopologicalSpace E] [inst_7 : TopologicalSpace F]   [inst_
8 : IsTopologicalAddGroup F],   nhds 0 = ⨅ s, ⨅ (_ : Bornology.IsVonNBounded 𝕜₁ 
s), ⨅ U ∈ nhds 0, Filter.principal {f | Set.MapsTo (⇑f) s U}
参数：_ : Bornology.IsVonNBounded 𝕜₁ s；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.nhds_zero_eq`：nhds_zero_eq [TopologicalSpace F] [I
sTopologicalAddGroup F] (𝔖 : Set (Set E)) : 𝓝 (0 : E ->SLᵤ[σ, 𝔖] F) = ⨅ s in 𝔖, 
⨅ t in 𝓝 (0 : F), 𝓟 {f :…
-/
protected theorem nhds_zero_eq [TopologicalSpace F] [IsTopologicalAddGroup F] :
    𝓝 (0 : E →SL[σ] F) =
      ⨅ (s : Set E) (_ : IsVonNBounded 𝕜₁ s) (U : Set F) (_ : U ∈ 𝓝 0),
        𝓟 {f : E →SL[σ] F | MapsTo f s U} :=
  UniformConvergenceCLM.nhds_zero_eq ..

/-- If `s` is a von Neumann bounded set and `U` is a neighbourhood of zero,
then sufficiently small continuous linear maps map `s` to `U`. -/
/-
**ContinuousLinearMap.eventually_nhds_zero_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousLinearMap`。
形式化陈述：eventually_nhds_zero_mapsTo [TopologicalSpace F] [IsTopologicalAddGroup F]
 {s : Set E} (hs : IsVonNBounded 𝕜₁ s) {U : Set F} (hu : U in 𝓝 0) : forallᶠ f :
 E ->SL[σ] F in 𝓝 0, MapsTo f s U
参数：hs : IsVonNBounded 𝕜₁ s；hu : U in 𝓝 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.eventually_nhds_zero_mapsTo`：eventually_nhds_zero_
mapsTo [TopologicalSpace F] [IsTopologicalAddGroup F] {𝔖 : Set (Set E)} {s : Set
 E} (hs : s in 𝔖) {U : Set F} (hu : U i…

--- 原说明 ---
If `s` is a von Neumann bounded set and `U` is a neighbourhood of zero,
then sufficiently small continuous linear maps map `s` to `U`.
-/
theorem eventually_nhds_zero_mapsTo [TopologicalSpace F] [IsTopologicalAddGroup F]
    {s : Set E} (hs : IsVonNBounded 𝕜₁ s) {U : Set F} (hu : U ∈ 𝓝 0) :
    ∀ᶠ f : E →SL[σ] F in 𝓝 0, MapsTo f s U :=
  UniformConvergenceCLM.eventually_nhds_zero_mapsTo _ hs hu

/-- If `S` is a von Neumann bounded set of continuous linear maps `f : E →SL[σ] F`
and `s` is a von Neumann bounded set in the domain,
then the set `{f x | (f ∈ S) (x ∈ s)}` is von Neumann bounded.

See also `isVonNBounded_iff` for an `Iff` version with stronger typeclass assumptions. -/
/-
**ContinuousLinearMap.isVonNBounded_image2_apply** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousLinearMap`。
形式化陈述：isVonNBounded_image2_apply {R : Type*} [SeminormedRing R] [TopologicalSpac
e F] [IsTopologicalAddGroup F] [DistribMulAction R F] [ContinuousConstSMul R F] 
[SMulCommClass 𝕜₂ R F] {S : Set (E ->SL[σ] F)} (hS : IsVonNBounded R S) {s : Set
 E} (hs : IsVonNBounded 𝕜₁ s) : IsVonNBounded R (Set.image2 (fun f x => f x) S s
)
参数：E ->SL[σ] F；hS : IsVonNBounded R S；hs : IsVonNBounded 𝕜₁ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.isVonNBounded_image2_apply`：isVonNBounded_image2_a
pply {R : Type*} [SeminormedRing R] [TopologicalSpace F] [IsTopologicalAddGroup 
F] [DistribMulAction R F] [ContinuousC…

--- 原说明 ---
If `S` is a von Neumann bounded set of continuous linear maps `f : E →SL[σ] F`
and `s` is a von Neumann bounded set in the domain,
then the set `{f x | (f ∈ S) (x ∈ s)}` is von Neumann bounded.

See also `isVonNBounded_iff` for an `Iff` version with stronger typeclass assump
tions.
-/
theorem isVonNBounded_image2_apply {R : Type*} [SeminormedRing R]
    [TopologicalSpace F] [IsTopologicalAddGroup F]
    [DistribMulAction R F] [ContinuousConstSMul R F] [SMulCommClass 𝕜₂ R F]
    {S : Set (E →SL[σ] F)} (hS : IsVonNBounded R S) {s : Set E} (hs : IsVonNBounded 𝕜₁ s) :
    IsVonNBounded R (Set.image2 (fun f x ↦ f x) S s) :=
  UniformConvergenceCLM.isVonNBounded_image2_apply hS hs

/-- A set `S` of continuous linear maps is von Neumann bounded
iff for any von Neumann bounded set `s`,
the set `{f x | (f ∈ S) (x ∈ s)}` is von Neumann bounded.

For the forward implication with weaker typeclass assumptions, see `isVonNBounded_image2_apply`. -/
/-
**ContinuousLinearMap.isVonNBounded_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：isVonNBounded_iff {R : Type*} [NormedDivisionRing R] [TopologicalSpace F] 
[IsTopologicalAddGroup F] [Module R F] [ContinuousConstSMul R F] [SMulCommClass 
𝕜₂ R F] {S : Set (E ->SL[σ] F)} : IsVonNBounded R S ↔ forall s, IsVonNBounded 𝕜₁
 s -> IsVonNBounded R (Set.image2 (fun f x => f x) S s)
参数：E ->SL[σ] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.isVonNBounded_iff`：isVonNBounded_iff {R : Type*} [
NormedDivisionRing R] [TopologicalSpace F] [IsTopologicalAddGroup F] [Module R F
] [ContinuousConstSMul R F] […

--- 原说明 ---
A set `S` of continuous linear maps is von Neumann bounded
iff for any von Neumann bounded set `s`,
the set `{f x | (f ∈ S) (x ∈ s)}` is von Neumann bounded.

For the forward implication with weaker typeclass assumptions, see `isVonNBounde
d_image2_apply`.
-/
theorem isVonNBounded_iff {R : Type*} [NormedDivisionRing R]
    [TopologicalSpace F] [IsTopologicalAddGroup F]
    [Module R F] [ContinuousConstSMul R F] [SMulCommClass 𝕜₂ R F]
    {S : Set (E →SL[σ] F)} :
    IsVonNBounded R S ↔
      ∀ s, IsVonNBounded 𝕜₁ s → IsVonNBounded R (Set.image2 (fun f x ↦ f x) S s) :=
  UniformConvergenceCLM.isVonNBounded_iff
/-
**ContinuousLinearMap.completeSpace** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：completeSpace [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜₂ F]
 [CompleteSpace F] [ContinuousSMul 𝕜₁ E] (h : IsCoherentWith {s : Set E | IsVonN
Bounded 𝕜₁ s}) : CompleteSpace (E ->SL[σ] F)
参数：h : IsCoherentWith {s : Set E | IsVonNBounded 𝕜₁ s}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.completeSpace`：completeSpace [UniformSpace F] [IsU
niformAddGroup F] [ContinuousSMul 𝕜₂ F] [CompleteSpace F] {𝔖 : Set (Set E)} (h𝔖 
: IsCoherentWith 𝔖) (h𝔖U …
· 使用定理 `Bornology.sUnion_isVonNBounded_eq_univ`：sUnion_isVonNBounded_eq_univ : ⋃
₀ Set.ofPred (IsVonNBounded 𝕜) = (Set.univ : Set E)
-/
theorem completeSpace [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜₂ F] [CompleteSpace F]
    [ContinuousSMul 𝕜₁ E] (h : IsCoherentWith {s : Set E | IsVonNBounded 𝕜₁ s}) :
    CompleteSpace (E →SL[σ] F) :=
  UniformConvergenceCLM.completeSpace _ _ h sUnion_isVonNBounded_eq_univ
/-
**ContinuousLinearMap.instCompleteSpace** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：instCompleteSpace [IsTopologicalAddGroup E] [ContinuousSMul 𝕜₁ E] [Sequent
ialSpace E] [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜₂ F] [Comple
teSpace F] : CompleteSpace (E ->SL[σ] F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.completeSpace`：completeSpace [UniformSpace F] [IsUni
formAddGroup F] [ContinuousSMul 𝕜₂ F] [CompleteSpace F] [ContinuousSMul 𝕜₁ E] (h
 : IsCoherentWith {s : …
· 使用引理 `Topology.IsCoherentWith.of_seq`：of_seq [SequentialSpace X] (h : forall ⦃
u : Nat -> X⦄ ⦃x : X⦄, Tendsto u atTop (𝓝 x) -> insert x (range u) in S) : IsCoh
erentWith S
· 使用定理 `Bornology.IsVonNBounded.insert`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : 
NormedField 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   [inst_3 
: TopologicalSpace E…
· 使用定理 `Filter.Tendsto.isVonNBounded_range`：Filter.Tendsto.isVonNBounded_range [
NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopological
AddGroup E] [ContinuousS…
-/
instance instCompleteSpace [IsTopologicalAddGroup E] [ContinuousSMul 𝕜₁ E] [SequentialSpace E]
    [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜₂ F] [CompleteSpace F] :
    CompleteSpace (E →SL[σ] F) :=
  completeSpace <| .of_seq fun _ _ h ↦ (h.isVonNBounded_range 𝕜₁).insert _
/-
**ContinuousLinearMap.isUniformInducing_postcomp** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousLinearMap`。
形式化陈述：isUniformInducing_postcomp [UniformSpace F] [IsUniformAddGroup F] [Uniform
Space G] [IsUniformAddGroup G] (f : F ->SL[τ] G) (hf : IsUniformInducing f) : Is
UniformInducing (f.comp : (E ->SL[σ] F) -> (E ->SL[ρ] G))
参数：f : F ->SL[τ] G；hf : IsUniformInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.isUniformInducing_postcomp`：isUniformInducing_post
comp [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] {𝕜₃ : Type*} [Norme
dField 𝕜₃] [Module 𝕜₃ G] {τ : 𝕜₂ ->+* …
-/
theorem isUniformInducing_postcomp [UniformSpace F] [IsUniformAddGroup F]
    [UniformSpace G] [IsUniformAddGroup G] (f : F →SL[τ] G) (hf : IsUniformInducing f) :
    IsUniformInducing (f.comp : (E →SL[σ] F) → (E →SL[ρ] G)) :=
  UniformConvergenceCLM.isUniformInducing_postcomp _ f hf _
/-
**ContinuousLinearMap.isUniformEmbedding_postcomp** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousLinearMap`。
形式化陈述：isUniformEmbedding_postcomp [UniformSpace F] [IsUniformAddGroup F] [Unifor
mSpace G] [IsUniformAddGroup G] (f : F ->SL[τ] G) (hf : IsUniformEmbedding f) : 
IsUniformEmbedding (f.comp : (E ->SL[σ] F) -> (E ->SL[ρ] G))
参数：f : F ->SL[τ] G；hf : IsUniformEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.isUniformEmbedding_postcomp`：isUniformEmbedding_po
stcomp [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] {𝕜₃ : Type*} [Nor
medField 𝕜₃] [Module 𝕜₃ G] {τ : 𝕜₂ ->+*…
-/
theorem isUniformEmbedding_postcomp [UniformSpace F] [IsUniformAddGroup F]
    [UniformSpace G] [IsUniformAddGroup G] (f : F →SL[τ] G) (hf : IsUniformEmbedding f) :
    IsUniformEmbedding (f.comp : (E →SL[σ] F) → (E →SL[ρ] G)) :=
  UniformConvergenceCLM.isUniformEmbedding_postcomp _ f hf _

variable [TopologicalSpace F] [TopologicalSpace G] (𝔖 : Set (Set E)) (𝔗 : Set (Set F))
/-
**ContinuousLinearMap.isInducing_postcomp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：isInducing_postcomp [IsTopologicalAddGroup F] [IsTopologicalAddGroup G] (f
 : F ->SL[τ] G) (hf : IsInducing f) : IsInducing (f.comp : (E ->SL[σ] F) -> (E -
>SL[ρ] G))
参数：f : F ->SL[τ] G；hf : IsInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.isInducing`：IsUniformInducing.isInducing {f : α -> β} 
(h : IsUniformInducing f) : IsInducing f
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `ContinuousLinearMap.isUniformInducing_postcomp`：isUniformInducing_postco
mp [UniformSpace F] [IsUniformAddGroup F] [UniformSpace G] [IsUniformAddGroup G]
 (f : F ->SL[τ] G) (hf : IsUniformIn…
· 使用定理 `AddMonoidHom.isUniformInducing_of_isInducing`：∀ {α : Type u_1} {β : Type
 u_2} [inst : UniformSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α] {Hom :
 Type u_3}   [inst_3 : UniformSpac…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem isInducing_postcomp [IsTopologicalAddGroup F] [IsTopologicalAddGroup G]
    (f : F →SL[τ] G) (hf : IsInducing f) :
    IsInducing (f.comp : (E →SL[σ] F) → (E →SL[ρ] G)) :=
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  haveI : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  (isUniformInducing_postcomp f <| AddMonoidHom.isUniformInducing_of_isInducing hf).isInducing
/-
**ContinuousLinearMap.isEmbedding_postcomp** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearMap`。
形式化陈述：isEmbedding_postcomp [IsTopologicalAddGroup F] [IsTopologicalAddGroup G] (
f : F ->SL[τ] G) (hf : IsEmbedding f) : IsEmbedding (f.comp : (E ->SL[σ] F) -> (
E ->SL[ρ] G))
参数：f : F ->SL[τ] G；hf : IsEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.isInducing_postcomp`：isInducing_postcomp [IsTopologi
calAddGroup F] [IsTopologicalAddGroup G] (f : F ->SL[τ] G) (hf : IsInducing f) :
 IsInducing (f.comp : (E ->SL…
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用定理 `ContinuousLinearMap.cancel_left`：cancel_left {g : M₂ ->SL[σ₂₃] M₃} {f₁ f
₂ : M₁ ->SL[σ₁₂] M₂} (hg : Function.Injective g) (h : g ∘SL f₁ = g ∘SL f₂) : f₁ 
= f₂
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
-/
theorem isEmbedding_postcomp [IsTopologicalAddGroup F] [IsTopologicalAddGroup G]
    (f : F →SL[τ] G) (hf : IsEmbedding f) :
    IsEmbedding (f.comp : (E →SL[σ] F) → (E →SL[ρ] G)) :=
  .mk (isInducing_postcomp f hf.isInducing) fun _ _ ↦ f.cancel_left hf.injective

variable (G) in
/-- Pre-composition by a *fixed* continuous linear map as a continuous linear map.

Note that in non-normed space it is not always true that composition is continuous
in both variables, so we have to fix one of them. -/
@[simps! apply]
/-
**ContinuousLinearMap.precomp** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：precomp [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G] [RingHomSurje
ctive σ] [RingHomIsometric σ] (L : E ->SL[σ] F) : (F ->SL[τ] G) ->L[𝕜₃] E ->SL[ρ
] G where toFun f
参数：L : E ->SL[σ] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pre-composition by a *fixed* continuous linear map as a continuous linear map.

Note that in non-normed space it is not always true that composition is continuo
us
in both variables, so we have to fix one of them.
-/
def precomp [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G] [RingHomSurjective σ]
    [RingHomIsometric σ] (L : E →SL[σ] F) : (F →SL[τ] G) →L[𝕜₃] E →SL[ρ] G where
  toFun f := f.comp L
  __ := precompUniformConvergenceCLM G { S | IsVonNBounded 𝕜₁ S } { S | IsVonNBounded 𝕜₂ S } L
    (fun _ hS ↦ hS.image L)

variable (E) in
/-- Post-composition by a *fixed* continuous linear map as a continuous linear map.

Note that in non-normed space it is not always true that composition is continuous
in both variables, so we have to fix one of them. -/
@[simps! apply]
/-
**ContinuousLinearMap.postcomp** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：postcomp [IsTopologicalAddGroup F] [IsTopologicalAddGroup G] [ContinuousCo
nstSMul 𝕜₃ G] [ContinuousConstSMul 𝕜₂ F] (L : F ->SL[τ] G) : (E ->SL[σ] F) ->SL[
τ] E ->SL[ρ] G where toFun f
参数：L : F ->SL[τ] G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Post-composition by a *fixed* continuous linear map as a continuous linear map.

Note that in non-normed space it is not always true that composition is continuo
us
in both variables, so we have to fix one of them.
-/
def postcomp [IsTopologicalAddGroup F] [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]
    [ContinuousConstSMul 𝕜₂ F] (L : F →SL[τ] G) : (E →SL[σ] F) →SL[τ] E →SL[ρ] G where
  toFun f := L.comp f
  __ := postcompUniformConvergenceCLM { S | IsVonNBounded 𝕜₁ S } L

variable (σ F) in
/-
**ContinuousLinearMap.toUniformConvergenceCLM_continuous** 是 Mathlib 中的一个引理，位于命名
空间 `ContinuousLinearMap`。
形式化陈述：toUniformConvergenceCLM_continuous [IsTopologicalAddGroup F] [ContinuousCo
nstSMul 𝕜₂ F] (𝔖 : Set (Set E)) (h : 𝔖 subseteq {S | IsVonNBounded 𝕜₁ S}) : Cont
inuous (ContinuousLinearMap.toUniformConvergenceCLM σ F 𝔖)
参数：𝔖 : Set (Set E)；h : 𝔖 subseteq {S | IsVonNBounded 𝕜₁ S}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_id_of_le`：continuous_id_of_le {t t' : TopologicalSpace α} (h 
: t <= t') : Continuous[t, t'] id
· 使用定理 `UniformConvergenceCLM.topologicalSpace_mono`：topologicalSpace_mono [Topo
logicalSpace F] [IsTopologicalAddGroup F] (h : 𝔖₂ subseteq 𝔖₁) : instTopological
Space σ F 𝔖₁ <= instTopologicalSp…
-/
lemma toUniformConvergenceCLM_continuous [IsTopologicalAddGroup F]
    [ContinuousConstSMul 𝕜₂ F]
    (𝔖 : Set (Set E)) (h : 𝔖 ⊆ {S | IsVonNBounded 𝕜₁ S}) :
    Continuous (ContinuousLinearMap.toUniformConvergenceCLM σ F 𝔖) :=
  continuous_id_of_le <| UniformConvergenceCLM.topologicalSpace_mono _ _ h

/-- A bilinear map `B : E × F → G` which is (jointly) continuous is **hypocontinuous**:
in curried form, it defines a continuous linear map `E →L[𝕜] F →L[𝕜] G`.

In the normed setting, the converse is true, see `ContinuousLinearMap.continuous₂`.
In general, however, hypocontinuity is a strictly weaker condition than joint continuity. -/
/-
**ContinuousLinearMap.continuous_of_continuous_uncurry** 是 Mathlib 中的一个定理，位于命名空间
 `ContinuousLinearMap`。
形式化陈述：continuous_of_continuous_uncurry {𝕜₁ : Type*} [NontriviallyNormedField 𝕜₁]
 {σ : 𝕜₁ ->+* 𝕜₂} [Module 𝕜₁ E] {τ : 𝕜₃ ->+* 𝕜₂} [RingHomSurjective τ] [IsTopolo
gicalAddGroup G] [ContinuousConstSMul 𝕜₃ G] [IsTopologicalAddGroup F] [Continuou
sConstSMul 𝕜₂ F] (B : G ->ₛₗ[τ] (E ->SL[σ] F)) (hB : Continuous (fun p : G × E =
> B p.1 p.2)) : Continuous B
参数：B : G ->ₛₗ[τ] (E ->SL[σ] F)；hB : Continuous (fun p : G × E => B p.1 p.2)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformConvergenceCLM.continuous_of_continuous_uncurry`：∀ {𝕜₂ : Type u_2
} [inst : NormedField 𝕜₂] {E : Type u_3} {F : Type u_4} {G : Type u_5} [inst_1 :
 AddCommGroup E]   [inst_2 : TopologicalSpac…

--- 原说明 ---
A bilinear map `B : E × F → G` which is (jointly) continuous is **hypocontinuous
**:
in curried form, it defines a continuous linear map `E →L[𝕜] F →L[𝕜] G`.

In the normed setting, the converse is true, see `ContinuousLinearMap.continuous
₂`.
In general, however, hypocontinuity is a strictly weaker condition than joint co
ntinuity.
-/
theorem continuous_of_continuous_uncurry
    {𝕜₁ : Type*} [NontriviallyNormedField 𝕜₁] {σ : 𝕜₁ →+* 𝕜₂} [Module 𝕜₁ E]
    {τ : 𝕜₃ →+* 𝕜₂} [RingHomSurjective τ]
    [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]
    [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F]
    (B : G →ₛₗ[τ] (E →SL[σ] F))
    (hB : Continuous (fun p : G × E ↦ B p.1 p.2)) :
    Continuous B :=
  UniformConvergenceCLM.continuous_of_continuous_uncurry (fun _ ↦ id) B hB

end BoundedConvergence

section Pi

variable (𝕜 : Type*) [NormedField 𝕜] (E : Type*) {ι : Type*} (F : ι → Type*)
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [∀ i, AddCommGroup (F i)] [∀ i, Module 𝕜 (F i)] [∀ i, TopologicalSpace (F i)]
  [∀ i, IsTopologicalAddGroup (F i)] [∀ i, ContinuousConstSMul 𝕜 (F i)]

/-- `ContinuousLinearMap.pi`, upgraded to a continuous linear equivalence between
`Π i, E →L[𝕜] F i` and `E →L[𝕜] Π i, F i`. -/
@[simps]
/-
**ContinuousLinearMap.piEquivL** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：piEquivL : (Π i, E ->L[𝕜] F i) ≃L[𝕜] (E ->L[𝕜] Π i, F i) where toFun F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousLinearMap.pi`, upgraded to a continuous linear equivalence between
`Π i, E →L[𝕜] F i` and `E →L[𝕜] Π i, F i`.
-/
def piEquivL :
    (Π i, E →L[𝕜] F i) ≃L[𝕜] (E →L[𝕜] Π i, F i) where
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
  {σ₁₃ : R →+* 𝕜₃} {σ₂₃ : 𝕜₂ →+* 𝕜₃}

/-
**ContinuousLinearMap.map_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Semiring R₁] [inst_1 : Semiring 
R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 : TopologicalSpace M₁] [inst_3 :
 AddCommMonoid M₁] {M₂ : Type u_6} [inst_4 : TopologicalSpace M₂]   [inst_5 : Ad
dCommMonoid M₂] [inst_6 : _root_.Module R₁ M₁] [inst_7 : _root_.Module R₂ M₂] (f
 : M₁ →SL[σ₁₂] M₂)   (x y : M₁), f (x + y) = f x + f y
参数：f : M₁ →SL[σ₁₂] M₂；x y : M₁；x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem map_add₂ (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x x' : E) (y : F) :
    f (x + x') y = f x y + f x' y := by rw [f.map_add, add_apply]
/-
**ContinuousLinearMap.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Semiring R₁] [inst_1 : Semiring 
R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 : TopologicalSpace M₁] [inst_3 :
 AddCommMonoid M₁] {M₂ : Type u_6} [inst_4 : TopologicalSpace M₂]   [inst_5 : Ad
dCommMonoid M₂] [inst_6 : _root_.Module R₁ M₁] [inst_7 : _root_.Module R₂ M₂] (f
 : M₁ →SL[σ₁₂] M₂),   f 0 = 0
参数：f : M₁ →SL[σ₁₂] M₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem map_zero₂ (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (y : F) : f 0 y = 0 := by
  rw [f.map_zero, zero_apply]
/-
**ContinuousLinearMap.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ {R₁ : Type u_1} [inst : Semiring R₁] {M₁ : Type u_4} [inst_1 : Topologic
alSpace M₁] [inst_2 : AddCommMonoid M₁]   {M₂ : Type u_6} [inst_3 : TopologicalS
pace M₂] [inst_4 : AddCommMonoid M₂] [inst_5 : _root_.Module R₁ M₁]   [inst_6 : 
_root_.Module R₁ M₂] (f : M₁ →L[R₁] M₂) (c : R₁) (x : M₁), f (c • x) = c • f x
参数：f : M₁ →L[R₁] M₂；c : R₁；x : M₁；c • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_smulₛₗ₂ (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (c : R) (x : E) (y : F) :
    f (c • x) y = σ₁₃ c • f x y := by rw [f.map_smulₛₗ, smul_apply]

/-- Send a continuous sesquilinear map to an abstract sesquilinear map (forgetting continuity). -/
@[simps -isSimp apply]
/-
**ContinuousLinearMap.toLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     [inst : Semiring R] →       [inst_
1 : Semiring S] →         {σ : R →+* S} →           {M : Type u_3} →            
 [inst_2 : TopologicalSpace M] →               [inst_3 : AddCommMonoid M] →     
            {M₂ : Type u_4} →                   [inst_4 : TopologicalSpace M₂] →
                     [inst_5 : AddCommMonoid M₂] →                       [inst_6
 : _root_.Module R M] → [inst_7 : _root_.Module S M₂] → (M →SL[σ] M₂) → M →ₛₗ[σ]
 M₂
参数：M →SL[σ] M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Send a continuous sesquilinear map to an abstract sesquilinear map (forgetting c
ontinuity).
-/
def toLinearMap₁₂ : (E →SL[σ₁₃] F →SL[σ₂₃] G) →ₗ[𝕜₃] E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G where
  toFun L := (coeLMₛₗ σ₂₃).comp L.toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-
**ContinuousLinearMap.toLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     [inst : Semiring R] →       [inst_
1 : Semiring S] →         {σ : R →+* S} →           {M : Type u_3} →            
 [inst_2 : TopologicalSpace M] →               [inst_3 : AddCommMonoid M] →     
            {M₂ : Type u_4} →                   [inst_4 : TopologicalSpace M₂] →
                     [inst_5 : AddCommMonoid M₂] →                       [inst_6
 : _root_.Module R M] → [inst_7 : _root_.Module S M₂] → (M →SL[σ] M₂) → M →ₛₗ[σ]
 M₂
参数：M →SL[σ] M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearMap₁₂_apply_apply_apply (L : E →SL[σ₁₃] F →SL[σ₂₃] G) (v : E) (w : F) :
    L.toLinearMap₁₂ v w = L v w := rfl
/-
**ContinuousLinearMap.toLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     [inst : Semiring R] →       [inst_
1 : Semiring S] →         {σ : R →+* S} →           {M : Type u_3} →            
 [inst_2 : TopologicalSpace M] →               [inst_3 : AddCommMonoid M] →     
            {M₂ : Type u_4} →                   [inst_4 : TopologicalSpace M₂] →
                     [inst_5 : AddCommMonoid M₂] →                       [inst_6
 : _root_.Module R M] → [inst_7 : _root_.Module S M₂] → (M →SL[σ] M₂) → M →ₛₗ[σ]
 M₂
参数：M →SL[σ] M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap₁₂_injective :
    (toLinearMap₁₂ (E := E) (F := F) (G := G) (σ₁₃ := σ₁₃) (σ₂₃ := σ₂₃) : _ → _).Injective := by
  simp [Function.Injective, LinearMap.ext_iff, ← ContinuousLinearMap.ext_iff]
/-
**ContinuousLinearMap.toLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     [inst : Semiring R] →       [inst_
1 : Semiring S] →         {σ : R →+* S} →           {M : Type u_3} →            
 [inst_2 : TopologicalSpace M] →               [inst_3 : AddCommMonoid M] →     
            {M₂ : Type u_4} →                   [inst_4 : TopologicalSpace M₂] →
                     [inst_5 : AddCommMonoid M₂] →                       [inst_6
 : _root_.Module R M] → [inst_7 : _root_.Module S M₂] → (M →SL[σ] M₂) → M →ₛₗ[σ]
 M₂
参数：M →SL[σ] M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap₁₂_inj (L₁ L₂ : E →SL[σ₁₃] F →SL[σ₂₃] G) :
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
  {σ₂₃ : 𝕜₂ →+* 𝕜₃}

/-
**ContinuousLinearMap.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ {R₁ : Type u_1} [inst : Semiring R₁] {M₁ : Type u_4} [inst_1 : Topologic
alSpace M₁] [inst_2 : AddCommMonoid M₁]   {M₂ : Type u_6} [inst_3 : TopologicalS
pace M₂] [inst_4 : AddCommMonoid M₂] [inst_5 : _root_.Module R₁ M₁]   [inst_6 : 
_root_.Module R₁ M₂] (f : M₁ →L[R₁] M₂) (c : R₁) (x : M₁), f (c • x) = c • f x
参数：f : M₁ →L[R₁] M₂；c : R₁；x : M₁；c • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_smul₂ (f : E →L[𝕜₃] F →SL[σ₂₃] G) (c : 𝕜₃) (x : E) (y : F) :
    f (c • x) y = c • f x y := by
  rw [f.map_smul, smul_apply]

end Nonsemilinear

section AddCommGroup
variable
  [Semiring R] [NormedField 𝕜₂] [NormedField 𝕜₃]
  [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜₂ F] [TopologicalSpace F]
  [AddCommGroup G] [Module 𝕜₃ G]
  [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]
  {σ₁₃ : R →+* 𝕜₃} {σ₂₃ : 𝕜₂ →+* 𝕜₃}

/-
**ContinuousLinearMap.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {R₂ : Type u_2} [inst_1 : Ring R₂] {M : T
ype u_4} [inst_2 : TopologicalSpace M]   [inst_3 : AddCommGroup M] {M₂ : Type u_
5} [inst_4 : TopologicalSpace M₂] [inst_5 : AddCommGroup M₂]   [inst_6 : _root_.
Module R M] [inst_7 : _root_.Module R₂ M₂] {σ₁₂ : R →+* R₂} (f : M →SL[σ₁₂] M₂) 
(x y : M),   f (x - y) = f x - f y
参数：f : M →SL[σ₁₂] M₂；x y : M；x - y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem map_sub₂ (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x x' : E) (y : F) :
    f (x - x') y = f x y - f x' y := by rw [map_sub, sub_apply]
/-
**ContinuousLinearMap.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {R₂ : Type u_2} [inst_1 : Ring R₂] {M : T
ype u_4} [inst_2 : TopologicalSpace M]   [inst_3 : AddCommGroup M] {M₂ : Type u_
5} [inst_4 : TopologicalSpace M₂] [inst_5 : AddCommGroup M₂]   [inst_6 : _root_.
Module R M] [inst_7 : _root_.Module R₂ M₂] {σ₁₂ : R →+* R₂} (f : M →SL[σ₁₂] M₂) 
(x : M),   f (-x) = -f x
参数：f : M →SL[σ₁₂] M₂；x : M；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem map_neg₂ (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x : E) (y : F) : f (-x) y = -f x y := by
  rw [map_neg, neg_apply]

end AddCommGroup

section BilinForm
variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

/-- Send a continuous bilinear form to an abstract bilinear form (forgetting continuity). -/
/-
**ContinuousLinearMap.toBilinForm** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：toBilinForm (L : E ->L[𝕜] E ->L[𝕜] 𝕜) : LinearMap.BilinForm 𝕜 E
参数：L : E ->L[𝕜] E ->L[𝕜] 𝕜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Send a continuous bilinear form to an abstract bilinear form (forgetting continu
ity).
-/
def toBilinForm (L : E →L[𝕜] E →L[𝕜] 𝕜) : LinearMap.BilinForm 𝕜 E := L.toLinearMap₁₂
/-
**ContinuousLinearMap.toBilinForm_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：∀ {𝕜 : Type u_2} {E : Type u_5} [inst : NormedField 𝕜] [inst_1 : AddCommGr
oup E] [inst_2 : _root_.Module 𝕜 E]   [inst_3 : TopologicalSpace E] (L : E →L[𝕜]
 E →L[𝕜] 𝕜) (v w : E), (L.toBilinForm v) w = (L v) w
参数：L : E →L[𝕜] E →L[𝕜] 𝕜；v w : E；L.toBilinForm v；L v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
-/
@[simp] lemma toBilinForm_apply (L : E →L[𝕜] E →L[𝕜] 𝕜) (v : E) (w : E) :
    L.toBilinForm v w = L v w := rfl
/-
**ContinuousLinearMap.toBilinForm_injective** 是 Mathlib 中的一个引理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：toBilinForm_injective : (toBilinForm (𝕜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMap.toLinearMap₁₂_injective`：toLinearMap₁₂_injective : (
toLinearMap₁₂ (E
-/
lemma toBilinForm_injective : (toBilinForm (𝕜 := 𝕜) (E := E)).Injective :=
  toLinearMap₁₂_injective
/-
**ContinuousLinearMap.toBilinForm_inj** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：toBilinForm_inj (L₁ L₂ : E ->L[𝕜] E ->L[𝕜] 𝕜) : L₁.toBilinForm = L₂.toBili
nForm ↔ L₁ = L₂
参数：L₁ L₂ : E ->L[𝕜] E ->L[𝕜] 𝕜。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `ContinuousLinearMap.toBilinForm_injective`：toBilinForm_injective : (toBi
linForm (𝕜
-/
lemma toBilinForm_inj (L₁ L₂ : E →L[𝕜] E →L[𝕜] 𝕜) :
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
/-
**ContinuousLinearMap.isUniformEmbedding_restrictScalars** 是 Mathlib 中的一个定理，位于命名
空间 `ContinuousLinearMap`。
形式化陈述：isUniformEmbedding_restrictScalars : IsUniformEmbedding (restrictScalars 𝕜
' : (E ->L[𝕜] F) -> (E ->L[𝕜'] F))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUniformEmbedding.of_comp_iff`：IsUniformEmbedding.of_comp_iff {g : β ->
 γ} (hg : IsUniformEmbedding g) {f : α -> β} : IsUniformEmbedding (g ∘ f) ↔ IsUn
iformEmbedding f
· 使用定理 `ContinuousLinearMap.isUniformEmbedding_toUniformOnFun`：isUniformEmbeddin
g_toUniformOnFun [UniformSpace F] [IsUniformAddGroup F] : IsUniformEmbedding fun
 f : E ->SL[σ] F => UniformOnFun.ofFun {s |…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Bornology.IsVonNBounded.extend_scalars`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_6} [inst_1 : AddCommGroup E]   [inst_2 : _root_.
Module 𝕜 E] (𝕝 : Type u_7) […
· 使用定理 `Bornology.IsVonNBounded.restrict_scalars`：∀ (𝕜 : Type u_1) {𝕜' : Type u_
2} {E : Type u_3} [inst : NormedField 𝕜] [inst_1 : NormedRing 𝕜']   [inst_2 : No
rmedAlgebra 𝕜 𝕜'] [inst_3 : Ze…
-/
theorem isUniformEmbedding_restrictScalars :
    IsUniformEmbedding (restrictScalars 𝕜' : (E →L[𝕜] F) → (E →L[𝕜'] F)) := by
  rw [← isUniformEmbedding_toUniformOnFun.of_comp_iff]
  convert! isUniformEmbedding_toUniformOnFun using 4 with s
  exact ⟨fun h ↦ h.extend_scalars _, fun h ↦ h.restrict_scalars _⟩
/-
**ContinuousLinearMap.uniformContinuous_restrictScalars** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousLinearMap`。
形式化陈述：uniformContinuous_restrictScalars : UniformContinuous (restrictScalars 𝕜' 
: (E ->L[𝕜] F) -> (E ->L[𝕜'] F))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用定理 `ContinuousLinearMap.isUniformEmbedding_restrictScalars`：isUniformEmbeddi
ng_restrictScalars : IsUniformEmbedding (restrictScalars 𝕜' : (E ->L[𝕜] F) -> (E
 ->L[𝕜'] F))
-/
theorem uniformContinuous_restrictScalars :
    UniformContinuous (restrictScalars 𝕜' : (E →L[𝕜] F) → (E →L[𝕜'] F)) :=
  (isUniformEmbedding_restrictScalars 𝕜').uniformContinuous

end UniformSpace

variable [TopologicalSpace F] [IsTopologicalAddGroup F] [Module 𝕜 F]
  (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
  [Module 𝕜' E] [IsScalarTower 𝕜' 𝕜 E] [Module 𝕜' F] [IsScalarTower 𝕜' 𝕜 F]

/-
**ContinuousLinearMap.isEmbedding_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousLinearMap`。
形式化陈述：isEmbedding_restrictScalars : IsEmbedding (restrictScalars 𝕜' : (E ->L[𝕜] 
F) -> (E ->L[𝕜'] F))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.isEmbedding`：∀ {α : Type u} {β : Type v} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Topo
logy.IsEmbedding f
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `ContinuousLinearMap.isUniformEmbedding_restrictScalars`：isUniformEmbeddi
ng_restrictScalars : IsUniformEmbedding (restrictScalars 𝕜' : (E ->L[𝕜] F) -> (E
 ->L[𝕜'] F))
-/
theorem isEmbedding_restrictScalars :
    IsEmbedding (restrictScalars 𝕜' : (E →L[𝕜] F) → (E →L[𝕜'] F)) :=
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  (isUniformEmbedding_restrictScalars _).isEmbedding

@[continuity, fun_prop]
/-
**ContinuousLinearMap.continuous_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousLinearMap`。
形式化陈述：continuous_restrictScalars : Continuous (restrictScalars 𝕜' : (E ->L[𝕜] F)
 -> (E ->L[𝕜'] F))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `ContinuousLinearMap.isEmbedding_restrictScalars`：isEmbedding_restrictSca
lars : IsEmbedding (restrictScalars 𝕜' : (E ->L[𝕜] F) -> (E ->L[𝕜'] F))
-/
theorem continuous_restrictScalars :
    Continuous (restrictScalars 𝕜' : (E →L[𝕜] F) → (E →L[𝕜'] F)) :=
  (isEmbedding_restrictScalars _).continuous

variable (𝕜 E F)
variable (𝕜'' : Type*) [Ring 𝕜'']
  [Module 𝕜'' F] [ContinuousConstSMul 𝕜'' F] [SMulCommClass 𝕜 𝕜'' F] [SMulCommClass 𝕜' 𝕜'' F]

/-- `ContinuousLinearMap.restrictScalars` as a `ContinuousLinearMap`. -/
/-
**ContinuousLinearMap.restrictScalarsL** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：restrictScalarsL : (E ->L[𝕜] F) ->L[𝕜''] E ->L[𝕜'] F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousLinearMap.restrictScalars` as a `ContinuousLinearMap`.
-/
def restrictScalarsL : (E →L[𝕜] F) →L[𝕜''] E →L[𝕜'] F :=
  .mk <| restrictScalarsₗ 𝕜 E F 𝕜' 𝕜''

variable {𝕜 E F 𝕜' 𝕜''}

@[simp]
/-
**ContinuousLinearMap.coe_restrictScalarsL** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearMap`。
形式化陈述：coe_restrictScalarsL : (restrictScalarsL 𝕜 E F 𝕜' 𝕜'' : (E ->L[𝕜] F) ->ₗ[𝕜
''] E ->L[𝕜'] F) = restrictScalarsₗ 𝕜 E F 𝕜' 𝕜''
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem coe_restrictScalarsL : (restrictScalarsL 𝕜 E F 𝕜' 𝕜'' : (E →L[𝕜] F) →ₗ[𝕜''] E →L[𝕜'] F) =
    restrictScalarsₗ 𝕜 E F 𝕜' 𝕜'' :=
  rfl

@[simp]
/-
**ContinuousLinearMap.coe_restrict_scalarsL'** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：coe_restrict_scalarsL' : ⇑(restrictScalarsL 𝕜 E F 𝕜' 𝕜'') = restrictScalar
s 𝕜'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
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
/-
**ContinuousLinearMap.coprodEquivL** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：coprodEquivL : ((E ->L[𝕜] G) × (F ->L[𝕜] G)) ≃L[S] (E × F ->L[𝕜] G) where 
__
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousLinearMap.coprod` as a `ContinuousLinearEquiv`.
-/
def coprodEquivL : ((E →L[𝕜] G) × (F →L[𝕜] G)) ≃L[S] (E × F →L[𝕜] G) where
  __ := coprodEquiv
  continuous_toFun :=
    (((fst 𝕜 E F).precomp G).coprod ((snd 𝕜 E F).precomp G)).continuous
  continuous_invFun :=
    (((inl 𝕜 E F).precomp G).prod ((inr 𝕜 E F).precomp G)).continuous

variable [Module S F] [SMulCommClass 𝕜 S F] [ContinuousConstSMul S F]

/-- `ContinuousLinearMap.prod` as a `ContinuousLinearEquiv`. -/
@[simps! apply]
/-
**ContinuousLinearMap.prodL** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：prodL : ((E ->L[𝕜] F) × (E ->L[𝕜] G)) ≃L[S] (E ->L[𝕜] F × G) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousLinearMap.prod` as a `ContinuousLinearEquiv`.
-/
def prodL : ((E →L[𝕜] F) × (E →L[𝕜] G)) ≃L[S] (E →L[𝕜] F × G) where
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
/-
**ContinuousLinearMap.toSpanSingletonCLE** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：toSpanSingletonCLE : E ≃L[𝕜] (𝕜 ->L[𝕜] E) where toLinearEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousLinearMap.toSpanSingleton` as a continuous linear equivalence.
-/
def toSpanSingletonCLE : E ≃L[𝕜] (𝕜 →L[𝕜] E) where
  toLinearEquiv := toSpanSingletonLE ..
  continuous_toFun := continuous_of_continuous_uncurry _ <|
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
  [ContinuousConstSMul 𝕜₄ H] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
  {σ₃₄ : 𝕜₃ →+* 𝕜₄} {σ₄₃ : 𝕜₄ →+* 𝕜₃} {σ₂₄ : 𝕜₂ →+* 𝕜₄} {σ₁₄ : 𝕜 →+* 𝕜₄} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂] [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄]
  [RingHomCompTriple σ₂₁ σ₁₄ σ₂₄] [RingHomCompTriple σ₂₄ σ₄₃ σ₂₃] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
  [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄]
  [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₁]

/-- A pair of continuous (semi)linear equivalences generates a (semi)linear equivalence between the
spaces of continuous (semi)linear maps. -/
@[simps apply symm_apply toLinearEquiv_apply toLinearEquiv_symm_apply]
/-
**ContinuousLinearEquiv.arrowCongrSL** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinear
Equiv`。
形式化陈述：arrowCongrSL (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G) : (E ->SL[σ₁₄] H) ≃
SL[σ₄₃] F ->SL[σ₂₃] G
参数：e₁₂ : E ≃SL[σ₁₂] F；e₄₃ : H ≃SL[σ₄₃] G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pair of continuous (semi)linear equivalences generates a (semi)linear equivale
nce between the
spaces of continuous (semi)linear maps.
-/
def arrowCongrSL (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G) :
    (E →SL[σ₁₄] H) ≃SL[σ₄₃] F →SL[σ₂₃] G :=
{ e₁₂.arrowCongrEquivₛₗ e₄₃ with
    -- given explicitly to help `simps`
    toFun := fun L => (e₄₃ : H →SL[σ₄₃] G).comp (L.comp (e₁₂.symm : F →SL[σ₂₁] E))
    -- given explicitly to help `simps`
    invFun := fun L => (e₄₃.symm : G →SL[σ₃₄] H).comp (L.comp (e₁₂ : E →SL[σ₁₂] F))
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

/-- A pair of continuous linear equivalences generates a continuous linear equivalence between
the spaces of continuous linear maps. -/
/-
**ContinuousLinearEquiv.arrowCongr** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearEq
uiv`。
形式化陈述：arrowCongr (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) : (E ->L[𝕜] H) ≃L[𝕜] F ->L[𝕜]
 G
参数：e₁ : E ≃L[𝕜] F；e₂ : H ≃L[𝕜] G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pair of continuous linear equivalences generates a continuous linear equivalen
ce between
the spaces of continuous linear maps.
-/
def arrowCongr (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) : (E →L[𝕜] H) ≃L[𝕜] F →L[𝕜] G :=
  e₁.arrowCongrSL e₂
/-
**ContinuousLinearEquiv.arrowCongr_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} {H : Type u_
5} [inst : AddCommGroup E]   [inst_1 : AddCommGroup F] [inst_2 : AddCommGroup G]
 [inst_3 : AddCommGroup H] [inst_4 : NormedField 𝕜]   [inst_5 : _root_.Module 𝕜 
E] [inst_6 : _root_.Module 𝕜 F] [inst_7 : _root_.Module 𝕜 G] [inst_8 : _root_.Mo
dule 𝕜 H]   [inst_9 : TopologicalSpace E] [inst_10 : TopologicalSpace F] [inst_1
1 : TopologicalSpace G]   [inst_12 : TopologicalSpace H] [inst_13 : IsTopologica
lAddGroup G] [inst_14 : IsTopologicalAddGroup H]   [inst_15 : ContinuousConstSMu
l 𝕜 G] [inst_16 : ContinuousConstSMul 𝕜 H] (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G)   (
f : E →L[𝕜] H) (x : F), ((e₁.arrowCongr e₂) f) x = e₂ (f (e₁.symm x))
参数：e₁ : E ≃L[𝕜] F；e₂ : H ≃L[𝕜] G；f : E →L[𝕜] H；x : F；(e₁.arrowCongr e₂) f；f (e₁.
symm x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
@[simp] lemma arrowCongr_apply (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) (f : E →L[𝕜] H) (x : F) :
    e₁.arrowCongr e₂ f x = e₂ (f (e₁.symm x)) := rfl
/-
**ContinuousLinearEquiv.arrowCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} {H : Type u_
5} [inst : AddCommGroup E]   [inst_1 : AddCommGroup F] [inst_2 : AddCommGroup G]
 [inst_3 : AddCommGroup H] [inst_4 : NormedField 𝕜]   [inst_5 : _root_.Module 𝕜 
E] [inst_6 : _root_.Module 𝕜 F] [inst_7 : _root_.Module 𝕜 G] [inst_8 : _root_.Mo
dule 𝕜 H]   [inst_9 : TopologicalSpace E] [inst_10 : TopologicalSpace F] [inst_1
1 : TopologicalSpace G]   [inst_12 : TopologicalSpace H] [inst_13 : IsTopologica
lAddGroup G] [inst_14 : IsTopologicalAddGroup H]   [inst_15 : ContinuousConstSMu
l 𝕜 G] [inst_16 : ContinuousConstSMul 𝕜 H] (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G),   
(e₁.arrowCongr e₂).symm = e₁.symm.arrowCongr e₂.symm
参数：e₁ : E ≃L[𝕜] F；e₂ : H ≃L[𝕜] G；e₁.arrowCongr e₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
@[simp] lemma arrowCongr_symm (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) :
    (e₁.arrowCongr e₂).symm = e₁.symm.arrowCongr e₂.symm := rfl

/-- A continuous linear equivalence of two spaces induces a continuous equivalence of algebras of
their endomorphisms. -/
/-
**ContinuousLinearEquiv.conjContinuousAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Contin
uousLinearEquiv`。
形式化陈述：conjContinuousAlgEquiv (e : G ≃L[𝕜] H) : (G ->L[𝕜] G) ≃A[𝕜] (H ->L[𝕜] H)
参数：e : G ≃L[𝕜] H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous linear equivalence of two spaces induces a continuous equivalence o
f algebras of
their endomorphisms.
-/
def conjContinuousAlgEquiv (e : G ≃L[𝕜] H) : (G →L[𝕜] G) ≃A[𝕜] (H →L[𝕜] H) :=
  { e.arrowCongr e with
    map_mul' _ _ := by ext; simp
    commutes' _ := by ext; simp }
/-
**ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply** 是 Mathlib 中的一个定理，位于
命名空间 `ContinuousLinearEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} {G : Type u_4} {H : Type u_5} [inst : AddCommGroup G] [in
st_1 : AddCommGroup H]   [inst_2 : NormedField 𝕜] [inst_3 : _root_.Module 𝕜 G] [
inst_4 : _root_.Module 𝕜 H] [inst_5 : TopologicalSpace G]   [inst_6 : Topologica
lSpace H] [inst_7 : IsTopologicalAddGroup G] [inst_8 : IsTopologicalAddGroup H] 
  [inst_9 : ContinuousConstSMul 𝕜 G] [inst_10 : ContinuousConstSMul 𝕜 H] (e : G 
≃L[𝕜] H) (f : G →L[𝕜] G) (x : H),   (e.conjContinuousAlgEquiv f) x = e (f (e.sym
m x))
参数：e : G ≃L[𝕜] H；f : G →L[𝕜] G；x : H；e.conjContinuousAlgEquiv f；f (e.symm x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
@[simp] theorem conjContinuousAlgEquiv_apply_apply (e : G ≃L[𝕜] H) (f : G →L[𝕜] G) (x : H) :
    e.conjContinuousAlgEquiv f x = e (f (e.symm x)) := rfl
/-
**ContinuousLinearEquiv.symm_conjContinuousAlgEquiv_apply_apply** 是 Mathlib 中的一个
定理，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：symm_conjContinuousAlgEquiv_apply_apply (e : G ≃L[𝕜] H) (f : H ->L[𝕜] H) (
x : G) : e.conjContinuousAlgEquiv.symm f x = e.symm (f (e x))
参数：e : G ≃L[𝕜] H；f : H ->L[𝕜] H；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem symm_conjContinuousAlgEquiv_apply_apply (e : G ≃L[𝕜] H) (f : H →L[𝕜] H) (x : G) :
    e.conjContinuousAlgEquiv.symm f x = e.symm (f (e x)) := rfl
/-
**ContinuousLinearEquiv.conjContinuousAlgEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousLinearEquiv`。
形式化陈述：conjContinuousAlgEquiv_apply (e : G ≃L[𝕜] H) (f : G ->L[𝕜] G) : e.conjCont
inuousAlgEquiv f = e ∘L f ∘L e.symm
参数：e : G ≃L[𝕜] H；f : G ->L[𝕜] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem conjContinuousAlgEquiv_apply (e : G ≃L[𝕜] H) (f : G →L[𝕜] G) :
    e.conjContinuousAlgEquiv f = e ∘L f ∘L e.symm := rfl
/-
**ContinuousLinearEquiv.symm_conjContinuousAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousLinearEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} {G : Type u_4} {H : Type u_5} [inst : AddCommGroup G] [in
st_1 : AddCommGroup H]   [inst_2 : NormedField 𝕜] [inst_3 : _root_.Module 𝕜 G] [
inst_4 : _root_.Module 𝕜 H] [inst_5 : TopologicalSpace G]   [inst_6 : Topologica
lSpace H] [inst_7 : IsTopologicalAddGroup G] [inst_8 : IsTopologicalAddGroup H] 
  [inst_9 : ContinuousConstSMul 𝕜 G] [inst_10 : ContinuousConstSMul 𝕜 H] (e : G 
≃L[𝕜] H),   e.conjContinuousAlgEquiv.symm = e.symm.conjContinuousAlgEquiv
参数：e : G ≃L[𝕜] H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
@[simp] theorem symm_conjContinuousAlgEquiv (e : G ≃L[𝕜] H) :
    e.conjContinuousAlgEquiv.symm = e.symm.conjContinuousAlgEquiv := rfl
/-
**ContinuousLinearEquiv.conjContinuousAlgEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousLinearEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} {G : Type u_4} [inst : AddCommGroup G] [inst_1 : NormedFi
eld 𝕜] [inst_2 : _root_.Module 𝕜 G]   [inst_3 : TopologicalSpace G] [inst_4 : Is
TopologicalAddGroup G] [inst_5 : ContinuousConstSMul 𝕜 G],   (ContinuousLinearEq
uiv.refl 𝕜 G).conjContinuousAlgEquiv = ContinuousAlgEquiv.refl 𝕜 (G →L[𝕜] G)
参数：ContinuousLinearEquiv.refl 𝕜 G；G →L[𝕜] G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
@[simp] theorem conjContinuousAlgEquiv_refl : conjContinuousAlgEquiv (.refl 𝕜 G) = .refl 𝕜 _ := rfl
/-
**ContinuousLinearEquiv.conjContinuousAlgEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousLinearEquiv`。
形式化陈述：conjContinuousAlgEquiv_trans [IsTopologicalAddGroup E] [ContinuousConstSMu
l 𝕜 E] (e : E ≃L[𝕜] G) (f : G ≃L[𝕜] H) : (e.trans f).conjContinuousAlgEquiv = e.
conjContinuousAlgEquiv.trans f.conjContinuousAlgEquiv
参数：e : E ≃L[𝕜] G；f : G ≃L[𝕜] H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem conjContinuousAlgEquiv_trans [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
    (e : E ≃L[𝕜] G) (f : G ≃L[𝕜] H) :
    (e.trans f).conjContinuousAlgEquiv = e.conjContinuousAlgEquiv.trans f.conjContinuousAlgEquiv :=
  rfl

end Linear

end ContinuousLinearEquiv

