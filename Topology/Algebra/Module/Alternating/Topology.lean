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

/-
**ContinuousAlternatingMap.instTopologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 `Conti
nuousAlternatingMap`。
形式化陈述：instTopologicalSpace : TopologicalSpace (E [⋀^ι]->L[𝕜] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instTopologicalSpace : TopologicalSpace (E [⋀^ι]→L[𝕜] F) :=
  .induced toContinuousMultilinearMap inferInstance
/-
**ContinuousAlternatingMap.isClosed_range_toContinuousMultilinearMap** 是 Mathlib
 中的一个引理，位于命名空间 `ContinuousAlternatingMap`。
形式化陈述：isClosed_range_toContinuousMultilinearMap [ContinuousSMul 𝕜 E] [T2Space F]
 : IsClosed (Set.range (toContinuousMultilinearMap : (E [⋀^ι]->L[𝕜] F) -> Contin
uousMultilinearMap 𝕜 (fun _ : ι => E) F))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousAlternatingMap.range_toContinuousMultilinearMap`：range_toConti
nuousMultilinearMap : Set.range (toContinuousMultilinearMap : M [⋀^ι]->L[R] N ->
 ContinuousMultilinearMap R (fun _ : ι => M) N)…
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `ContinuousEvalConst.continuous_eval_const`：∀ {F : Type u_1} {α : outPara
m (Type u_2)} {X : outParam (Type u_3)} {inst : FunLike F α X}   {inst_1 : Topol
ogicalSpace F} {inst_2 : Topolo…
· 使用定理 `ContinuousMultilinearMap.instContinuousEvalConstForall`：∀ {𝕜 : Type u_1}
 {ι : Type u_2} {E : ι → Type u_3} {F : Type u_4} [inst : NormedField 𝕜]   [inst
_1 : (i : ι) → TopologicalSpace (E i)] [inst…
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
-/
lemma isClosed_range_toContinuousMultilinearMap [ContinuousSMul 𝕜 E] [T2Space F] :
    IsClosed (Set.range (toContinuousMultilinearMap : (E [⋀^ι]→L[𝕜] F) →
      ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F)) := by
  simp only [range_toContinuousMultilinearMap, ofPred_forall]
  repeat refine isClosed_iInter fun _ ↦ ?_
  exact isClosed_singleton.preimage (continuous_eval_const _)

end IsClosedRange

section IsUniformAddGroup

variable [UniformSpace F] [IsUniformAddGroup F]

/-
**ContinuousAlternatingMap.instUniformSpace** 是 Mathlib 中的一个实例，位于命名空间 `Continuou
sAlternatingMap`。
形式化陈述：instUniformSpace : UniformSpace (E [⋀^ι]->L[𝕜] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instUniformSpace : UniformSpace (E [⋀^ι]→L[𝕜] F) :=
  .comap toContinuousMultilinearMap inferInstance
/-
**ContinuousAlternatingMap.isUniformEmbedding_toContinuousMultilinearMap** 是 Mat
hlib 中的一个引理，位于命名空间 `ContinuousAlternatingMap`。
形式化陈述：isUniformEmbedding_toContinuousMultilinearMap : IsUniformEmbedding (toCont
inuousMultilinearMap : (E [⋀^ι]->L[𝕜] F) -> _) where injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlternatingMap.toContinuousMultilinearMap_injective`：∀ {R : Ty
pe u_1} {M : Type u_2} {N : Type u_4} {ι : Type u_6} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] …
-/
lemma isUniformEmbedding_toContinuousMultilinearMap :
    IsUniformEmbedding (toContinuousMultilinearMap : (E [⋀^ι]→L[𝕜] F) → _) where
  injective := toContinuousMultilinearMap_injective
  comap_uniformity := rfl
/-
**ContinuousAlternatingMap.uniformContinuous_toContinuousMultilinearMap** 是 Math
lib 中的一个引理，位于命名空间 `ContinuousAlternatingMap`。
形式化陈述：uniformContinuous_toContinuousMultilinearMap : UniformContinuous (toContin
uousMultilinearMap : (E [⋀^ι]->L[𝕜] F) -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用引理 `ContinuousAlternatingMap.isUniformEmbedding_toContinuousMultilinearMap`：
isUniformEmbedding_toContinuousMultilinearMap : IsUniformEmbedding (toContinuous
MultilinearMap : (E [⋀^ι]->L[𝕜] F) -> _) where injective
-/
lemma uniformContinuous_toContinuousMultilinearMap :
    UniformContinuous (toContinuousMultilinearMap : (E [⋀^ι]→L[𝕜] F) → _) :=
  isUniformEmbedding_toContinuousMultilinearMap.uniformContinuous
/-
**ContinuousAlternatingMap.uniformContinuous_coe_fun** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousAlternatingMap`。
形式化陈述：uniformContinuous_coe_fun [ContinuousSMul 𝕜 E] : UniformContinuous (DFunLi
ke.coe : (E [⋀^ι]->L[𝕜] F) -> (ι -> E) -> F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `ContinuousMultilinearMap.uniformContinuous_coe_fun`：uniformContinuous_co
e_fun [forall i, ContinuousSMul 𝕜 (E i)] : UniformContinuous (DFunLike.coe : Con
tinuousMultilinearMap 𝕜 E F -> (Π i, E i…
· 使用引理 `ContinuousAlternatingMap.uniformContinuous_toContinuousMultilinearMap`：u
niformContinuous_toContinuousMultilinearMap : UniformContinuous (toContinuousMul
tilinearMap : (E [⋀^ι]->L[𝕜] F) -> _)
-/
theorem uniformContinuous_coe_fun [ContinuousSMul 𝕜 E] :
    UniformContinuous (DFunLike.coe : (E [⋀^ι]→L[𝕜] F) → (ι → E) → F) :=
  ContinuousMultilinearMap.uniformContinuous_coe_fun.comp
    uniformContinuous_toContinuousMultilinearMap
/-
**ContinuousAlternatingMap.uniformContinuous_eval_const** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousAlternatingMap`。
形式化陈述：uniformContinuous_eval_const [ContinuousSMul 𝕜 E] (x : ι -> E) : UniformCo
ntinuous fun f : E [⋀^ι]->L[𝕜] F => f x
参数：x : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `uniformContinuous_pi`：uniformContinuous_pi {β : Type*} [UniformSpace β] 
{f : β -> forall i, α i} : UniformContinuous f ↔ forall i, UniformContinuous fun
 x => f x …
· 使用定理 `ContinuousAlternatingMap.uniformContinuous_coe_fun`：uniformContinuous_co
e_fun [ContinuousSMul 𝕜 E] : UniformContinuous (DFunLike.coe : (E [⋀^ι]->L[𝕜] F)
 -> (ι -> E) -> F)
-/
theorem uniformContinuous_eval_const [ContinuousSMul 𝕜 E] (x : ι → E) :
    UniformContinuous fun f : E [⋀^ι]→L[𝕜] F ↦ f x :=
  uniformContinuous_pi.1 uniformContinuous_coe_fun x
/-
**ContinuousAlternatingMap.instIsUniformAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `Cont
inuousAlternatingMap`。
形式化陈述：instIsUniformAddGroup : IsUniformAddGroup (E [⋀^ι]->L[𝕜] F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.isUniformAddGroup`：∀ {G : Type u_1} {H : Type u_2} {ho
m : Type u_3} [inst : AddGroup G] [inst_1 : AddGroup H] [inst_2 : UniformSpace G
]   [inst_3 : UniformSpac…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用引理 `ContinuousAlternatingMap.isUniformEmbedding_toContinuousMultilinearMap`：
isUniformEmbedding_toContinuousMultilinearMap : IsUniformEmbedding (toContinuous
MultilinearMap : (E [⋀^ι]->L[𝕜] F) -> _) where injective
-/
instance instIsUniformAddGroup : IsUniformAddGroup (E [⋀^ι]→L[𝕜] F) :=
  isUniformEmbedding_toContinuousMultilinearMap.isUniformAddGroup
    (toContinuousMultilinearMapLinear (R := ℕ))
/-
**ContinuousAlternatingMap.instUniformContinuousConstSMul** 是 Mathlib 中的一个实例，位于命
名空间 `ContinuousAlternatingMap`。
形式化陈述：instUniformContinuousConstSMul {M : Type*} [Monoid M] [DistribMulAction M 
F] [SMulCommClass 𝕜 M F] [ContinuousConstSMul M F] : UniformContinuousConstSMul 
M (E [⋀^ι]->L[𝕜] F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUniformInducing.uniformContinuousConstSMul`：IsUniformInducing.uniformC
ontinuousConstSMul [SMul M Y] [UniformContinuousConstSMul M Y] {f : X -> Y} (hf 
: IsUniformInducing f) (hsmul : fo…
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用引理 `ContinuousAlternatingMap.isUniformEmbedding_toContinuousMultilinearMap`：
isUniformEmbedding_toContinuousMultilinearMap : IsUniformEmbedding (toContinuous
MultilinearMap : (E [⋀^ι]->L[𝕜] F) -> _) where injective
-/
instance instUniformContinuousConstSMul {M : Type*}
    [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜 M F] [ContinuousConstSMul M F] :
    UniformContinuousConstSMul M (E [⋀^ι]→L[𝕜] F) :=
  isUniformEmbedding_toContinuousMultilinearMap.uniformContinuousConstSMul fun _ _ ↦ rfl
/-
**ContinuousAlternatingMap.isUniformInducing_postcomp** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousAlternatingMap`。
形式化陈述：isUniformInducing_postcomp {G : Type*} [AddCommGroup G] [UniformSpace G] [
IsUniformAddGroup G] [Module 𝕜 G] (g : F ->L[𝕜] G) (hg : IsUniformInducing g) : 
IsUniformInducing (g.compContinuousAlternatingMap : (E [⋀^ι]->L[𝕜] F) -> (E [⋀^ι
]->L[𝕜] G))
参数：g : F ->L[𝕜] G；hg : IsUniformInducing g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUniformInducing.of_comp_iff`：IsUniformInducing.of_comp_iff {g : β -> γ
} (hg : IsUniformInducing g) {f : α -> β} : IsUniformInducing (g ∘ f) ↔ IsUnifor
mInducing f
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用引理 `ContinuousAlternatingMap.isUniformEmbedding_toContinuousMultilinearMap`：
isUniformEmbedding_toContinuousMultilinearMap : IsUniformEmbedding (toContinuous
MultilinearMap : (E [⋀^ι]->L[𝕜] F) -> _) where injective
· 使用定理 `IsUniformInducing.comp`：IsUniformInducing.comp {g : β -> γ} (hg : IsUnif
ormInducing g) {f : α -> β} (hf : IsUniformInducing f) : IsUniformInducing (g ∘ 
f)
· 使用定理 `ContinuousMultilinearMap.isUniformInducing_postcomp`：isUniformInducing_p
ostcomp {G : Type*} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] [Mod
ule 𝕜 G] (g : F ->L[𝕜] G) (hg : IsUniform…
-/
theorem isUniformInducing_postcomp {G : Type*} [AddCommGroup G] [UniformSpace G]
    [IsUniformAddGroup G] [Module 𝕜 G] (g : F →L[𝕜] G) (hg : IsUniformInducing g) :
    IsUniformInducing (g.compContinuousAlternatingMap : (E [⋀^ι]→L[𝕜] F) → (E [⋀^ι]→L[𝕜] G)) := by
  rw [← isUniformEmbedding_toContinuousMultilinearMap.1.of_comp_iff]
  exact (ContinuousMultilinearMap.isUniformInducing_postcomp g hg).comp
    isUniformEmbedding_toContinuousMultilinearMap.1

section CompleteSpace

variable [ContinuousSMul 𝕜 E] [ContinuousConstSMul 𝕜 F] [CompleteSpace F]

open UniformOnFun in
/-
**ContinuousAlternatingMap.completeSpace** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAl
ternatingMap`。
形式化陈述：completeSpace (h : IsCoherentWith {s : Set (ι -> E) | IsVonNBounded 𝕜 s}) 
: CompleteSpace (E [⋀^ι]->L[𝕜] F)
参数：h : IsCoherentWith {s : Set (ι -> E) | IsVonNBounded 𝕜 s}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `ContinuousMultilinearMap.completeSpace`：completeSpace (h : IsCoherentWit
h {s : Set (Π i, E i) | IsVonNBounded 𝕜 s}) : CompleteSpace (ContinuousMultiline
arMap 𝕜 E F)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `completeSpace_iff_isComplete_range`：completeSpace_iff_isComplete_range {
f : α -> β} (hf : IsUniformInducing f) : CompleteSpace α ↔ IsComplete (range f)
· 使用引理 `IsUniformEmbedding.isUniformInducing`：IsUniformEmbedding.isUniformInduci
ng {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformInducing f
· 使用引理 `ContinuousAlternatingMap.isUniformEmbedding_toContinuousMultilinearMap`：
isUniformEmbedding_toContinuousMultilinearMap : IsUniformEmbedding (toContinuous
MultilinearMap : (E [⋀^ι]->L[𝕜] F) -> _) where injective
· 使用定理 `IsClosed.isComplete`：IsClosed.isComplete [CompleteSpace α] {s : Set α} (
h : IsClosed s) : IsComplete s
· 使用引理 `ContinuousAlternatingMap.isClosed_range_toContinuousMultilinearMap`：isCl
osed_range_toContinuousMultilinearMap [ContinuousSMul 𝕜 E] [T2Space F] : IsClose
d (Set.range (toContinuousMultilinearMap : (E [⋀^ι]->L[𝕜…
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeparationQuotient.instIsUniformAddGroup`：∀ {G : Type u_1} [inst : AddGr
oup G] [inst_1 : UniformSpace G] [inst_2 : IsUniformAddGroup G],   IsUniformAddG
roup (SeparationQuotient G)
· 使用定理 `IsUniformInducing.completeSpace_congr`：IsUniformInducing.completeSpace_c
ongr {f : α -> β} (hf : IsUniformInducing f) (hsurj : f.Surjective) : CompleteSp
ace α ↔ CompleteSpace β
· 使用定理 `ContinuousAlternatingMap.isUniformInducing_postcomp`：isUniformInducing_p
ostcomp {G : Type*} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] [Mod
ule 𝕜 G] (g : F ->L[𝕜] G) (hg : IsUniform…
· 使用引理 `SeparationQuotient.isUniformInducing_mk`：SeparationQuotient.isUniformInd
ucing_mk : IsUniformInducing (mk : α -> SeparationQuotient α)
· 使用定理 `ContinuousAlternatingMap.ext`：ext {f g : M [⋀^ι]->L[R] N} (H : forall x,
 f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SeparationQuotient.mkCLM_apply`：∀ (R : Type u_1) (M : Type u_3) [inst : 
Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst_3 : 
TopologicalSpace M] …
· 使用定理 `SeparationQuotient.mk_outCLM`：mk_outCLM (x : SeparationQuotient E) : mk 
(outCLM K E x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
-/
theorem completeSpace (h : IsCoherentWith {s : Set (ι → E) | IsVonNBounded 𝕜 s}) :
    CompleteSpace (E [⋀^ι]→L[𝕜] F) := by
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
/-
**ContinuousAlternatingMap.instCompleteSpace** 是 Mathlib 中的一个实例，位于命名空间 `Continuo
usAlternatingMap`。
形式化陈述：instCompleteSpace [IsTopologicalAddGroup E] [SequentialSpace (ι -> E)] : C
ompleteSpace (E [⋀^ι]->L[𝕜] F)
参数：ι -> E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlternatingMap.completeSpace`：completeSpace (h : IsCoherentWit
h {s : Set (ι -> E) | IsVonNBounded 𝕜 s}) : CompleteSpace (E [⋀^ι]->L[𝕜] F)
· 使用引理 `Topology.IsCoherentWith.of_seq`：of_seq [SequentialSpace X] (h : forall ⦃
u : Nat -> X⦄ ⦃x : X⦄, Tendsto u atTop (𝓝 x) -> insert x (range u) in S) : IsCoh
erentWith S
· 使用定理 `Bornology.IsVonNBounded.insert`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : 
NormedField 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   [inst_3 
: TopologicalSpace E…
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `Filter.Tendsto.isVonNBounded_range`：Filter.Tendsto.isVonNBounded_range [
NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopological
AddGroup E] [ContinuousS…
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
-/
instance instCompleteSpace [IsTopologicalAddGroup E] [SequentialSpace (ι → E)] :
    CompleteSpace (E [⋀^ι]→L[𝕜] F) :=
  completeSpace <| .of_seq fun _u x hux ↦ (hux.isVonNBounded_range 𝕜).insert x

end CompleteSpace

section RestrictScalars

variable (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
  [Module 𝕜' E] [IsScalarTower 𝕜' 𝕜 E] [Module 𝕜' F] [IsScalarTower 𝕜' 𝕜 F] [ContinuousSMul 𝕜 E]

/-
**ContinuousAlternatingMap.isUniformEmbedding_restrictScalars** 是 Mathlib 中的一个定理
，位于命名空间 `ContinuousAlternatingMap`。
形式化陈述：isUniformEmbedding_restrictScalars : IsUniformEmbedding (restrictScalars 𝕜
' : E [⋀^ι]->L[𝕜] F -> E [⋀^ι]->L[𝕜'] F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUniformEmbedding.of_comp_iff`：IsUniformEmbedding.of_comp_iff {g : β ->
 γ} (hg : IsUniformEmbedding g) {f : α -> β} : IsUniformEmbedding (g ∘ f) ↔ IsUn
iformEmbedding f
· 使用引理 `ContinuousAlternatingMap.isUniformEmbedding_toContinuousMultilinearMap`：
isUniformEmbedding_toContinuousMultilinearMap : IsUniformEmbedding (toContinuous
MultilinearMap : (E [⋀^ι]->L[𝕜] F) -> _) where injective
· 使用定理 `IsUniformEmbedding.comp`：IsUniformEmbedding.comp {g : β -> γ} (hg : IsUn
iformEmbedding g) {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformEmbedding 
(g ∘ f) where…
· 使用定理 `ContinuousMultilinearMap.isUniformEmbedding_restrictScalars`：isUniformEm
bedding_restrictScalars : IsUniformEmbedding (restrictScalars 𝕜' : ContinuousMul
tilinearMap 𝕜 E F -> ContinuousMultilinearMap 𝕜' …
-/
theorem isUniformEmbedding_restrictScalars :
    IsUniformEmbedding (restrictScalars 𝕜' : E [⋀^ι]→L[𝕜] F → E [⋀^ι]→L[𝕜'] F) := by
  rw [← isUniformEmbedding_toContinuousMultilinearMap.of_comp_iff]
  exact (ContinuousMultilinearMap.isUniformEmbedding_restrictScalars 𝕜').comp
    isUniformEmbedding_toContinuousMultilinearMap
/-
**ContinuousAlternatingMap.uniformContinuous_restrictScalars** 是 Mathlib 中的一个定理，
位于命名空间 `ContinuousAlternatingMap`。
形式化陈述：uniformContinuous_restrictScalars : UniformContinuous (restrictScalars 𝕜' 
: E [⋀^ι]->L[𝕜] F -> E [⋀^ι]->L[𝕜'] F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用定理 `ContinuousAlternatingMap.isUniformEmbedding_restrictScalars`：isUniformEm
bedding_restrictScalars : IsUniformEmbedding (restrictScalars 𝕜' : E [⋀^ι]->L[𝕜]
 F -> E [⋀^ι]->L[𝕜'] F)
-/
theorem uniformContinuous_restrictScalars :
    UniformContinuous (restrictScalars 𝕜' : E [⋀^ι]→L[𝕜] F → E [⋀^ι]→L[𝕜'] F) :=
  (isUniformEmbedding_restrictScalars 𝕜').uniformContinuous

end RestrictScalars

end IsUniformAddGroup

variable [TopologicalSpace F] [IsTopologicalAddGroup F]

/-
**ContinuousAlternatingMap.isEmbedding_toContinuousMultilinearMap** 是 Mathlib 中的
一个引理，位于命名空间 `ContinuousAlternatingMap`。
形式化陈述：isEmbedding_toContinuousMultilinearMap : IsEmbedding (toContinuousMultilin
earMap : (E [⋀^ι]->L[𝕜] F -> _))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.isEmbedding`：∀ {α : Type u} {β : Type v} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Topo
logy.IsEmbedding f
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用引理 `ContinuousAlternatingMap.isUniformEmbedding_toContinuousMultilinearMap`：
isUniformEmbedding_toContinuousMultilinearMap : IsUniformEmbedding (toContinuous
MultilinearMap : (E [⋀^ι]->L[𝕜] F) -> _) where injective
-/
lemma isEmbedding_toContinuousMultilinearMap :
    IsEmbedding (toContinuousMultilinearMap : (E [⋀^ι]→L[𝕜] F → _)) :=
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  isUniformEmbedding_toContinuousMultilinearMap.isEmbedding
/-
**ContinuousAlternatingMap.instIsTopologicalAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `
ContinuousAlternatingMap`。
形式化陈述：instIsTopologicalAddGroup : IsTopologicalAddGroup (E [⋀^ι]->L[𝕜] F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.topologicalAddGroup`：∀ {G : Type w} {H : Type x} [in
st : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] {F : Ty
pe u_1}   [inst_3 : AddGroup …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用引理 `ContinuousAlternatingMap.isEmbedding_toContinuousMultilinearMap`：isEmbed
ding_toContinuousMultilinearMap : IsEmbedding (toContinuousMultilinearMap : (E [
⋀^ι]->L[𝕜] F -> _))
-/
instance instIsTopologicalAddGroup : IsTopologicalAddGroup (E [⋀^ι]→L[𝕜] F) :=
  isEmbedding_toContinuousMultilinearMap.topologicalAddGroup
    (toContinuousMultilinearMapLinear (R := ℕ))

@[continuity, fun_prop]
/-
**ContinuousAlternatingMap.continuous_toContinuousMultilinearMap** 是 Mathlib 中的一
个引理，位于命名空间 `ContinuousAlternatingMap`。
形式化陈述：continuous_toContinuousMultilinearMap : Continuous (toContinuousMultilinea
rMap : (E [⋀^ι]->L[𝕜] F -> _))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用引理 `ContinuousAlternatingMap.isEmbedding_toContinuousMultilinearMap`：isEmbed
ding_toContinuousMultilinearMap : IsEmbedding (toContinuousMultilinearMap : (E [
⋀^ι]->L[𝕜] F -> _))
-/
lemma continuous_toContinuousMultilinearMap :
    Continuous (toContinuousMultilinearMap : (E [⋀^ι]→L[𝕜] F → _)) :=
  isEmbedding_toContinuousMultilinearMap.continuous
/-
**ContinuousAlternatingMap.instContinuousConstSMul** 是 Mathlib 中的一个实例，位于命名空间 `Co
ntinuousAlternatingMap`。
形式化陈述：instContinuousConstSMul {M : Type*} [Monoid M] [DistribMulAction M F] [SMu
lCommClass 𝕜 M F] [ContinuousConstSMul M F] : ContinuousConstSMul M (E [⋀^ι]->L[
𝕜] F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.continuousConstSMul`：Topology.IsInducing.continuousC
onstSMul {N β : Type*} [SMul N β] [TopologicalSpace β] {g : β -> α} (hg : IsIndu
cing g) (f : N -> M) (hf : fo…
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用引理 `ContinuousAlternatingMap.isEmbedding_toContinuousMultilinearMap`：isEmbed
ding_toContinuousMultilinearMap : IsEmbedding (toContinuousMultilinearMap : (E [
⋀^ι]->L[𝕜] F -> _))
-/
instance instContinuousConstSMul
    {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜 M F] [ContinuousConstSMul M F] :
    ContinuousConstSMul M (E [⋀^ι]→L[𝕜] F) :=
  isEmbedding_toContinuousMultilinearMap.continuousConstSMul id rfl
/-
**ContinuousAlternatingMap.instContinuousSMul** 是 Mathlib 中的一个实例，位于命名空间 `Continu
ousAlternatingMap`。
形式化陈述：instContinuousSMul [ContinuousSMul 𝕜 F] : ContinuousSMul 𝕜 (E [⋀^ι]->L[𝕜] 
F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.continuousSMul`：Topology.IsInducing.continuousSMul {
N : Type*} [SMul N Y] [TopologicalSpace N] {f : N -> M} (hg : IsInducing g) (hf 
: Continuous f) (hsmul :…
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用引理 `ContinuousAlternatingMap.isEmbedding_toContinuousMultilinearMap`：isEmbed
ding_toContinuousMultilinearMap : IsEmbedding (toContinuousMultilinearMap : (E [
⋀^ι]->L[𝕜] F -> _))
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
instance instContinuousSMul [ContinuousSMul 𝕜 F] : ContinuousSMul 𝕜 (E [⋀^ι]→L[𝕜] F) :=
  isEmbedding_toContinuousMultilinearMap.continuousSMul continuous_id rfl
/-
**ContinuousAlternatingMap.hasBasis_nhds_zero_of_basis** 是 Mathlib 中的一个定理，位于命名空间
 `ContinuousAlternatingMap`。
形式化陈述：hasBasis_nhds_zero_of_basis {ι' : Type*} {p : ι' -> Prop} {b : ι' -> Set F
} (h : (𝓝 (0 : F)).HasBasis p b) : (𝓝 (0 : E [⋀^ι]->L[𝕜] F)).HasBasis (fun Si : 
Set (ι -> E) × ι' => IsVonNBounded 𝕜 Si.1 ∧ p Si.2) fun Si => { f | MapsTo f Si.
1 (b Si.2) }
参数：h : (𝓝 (0 : F)).HasBasis p b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `ContinuousMultilinearMap.hasBasis_nhds_zero_of_basis`：hasBasis_nhds_zero
_of_basis {ι : Type*} {p : ι -> Prop} {b : ι -> Set F} (h : (𝓝 (0 : F)).HasBasis
 p b) : (𝓝 (0 : ContinuousMultilinearMap 𝕜…
-/
theorem hasBasis_nhds_zero_of_basis {ι' : Type*} {p : ι' → Prop} {b : ι' → Set F}
    (h : (𝓝 (0 : F)).HasBasis p b) :
    (𝓝 (0 : E [⋀^ι]→L[𝕜] F)).HasBasis
      (fun Si : Set (ι → E) × ι' => IsVonNBounded 𝕜 Si.1 ∧ p Si.2)
      fun Si => { f | MapsTo f Si.1 (b Si.2) } := by
  rw [nhds_induced]
  exact (ContinuousMultilinearMap.hasBasis_nhds_zero_of_basis h).comap _
/-
**ContinuousAlternatingMap.hasBasis_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousAlternatingMap`。
形式化陈述：hasBasis_nhds_zero : (𝓝 (0 : E [⋀^ι]->L[𝕜] F)).HasBasis (fun SV : Set (ι -
> E) × Set F => IsVonNBounded 𝕜 SV.1 ∧ SV.2 in 𝓝 0) fun SV => { f | MapsTo f SV.
1 SV.2 }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlternatingMap.hasBasis_nhds_zero_of_basis`：hasBasis_nhds_zero
_of_basis {ι' : Type*} {p : ι' -> Prop} {b : ι' -> Set F} (h : (𝓝 (0 : F)).HasBa
sis p b) : (𝓝 (0 : E [⋀^ι]->L[𝕜] F)).HasBa…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem hasBasis_nhds_zero :
    (𝓝 (0 : E [⋀^ι]→L[𝕜] F)).HasBasis
      (fun SV : Set (ι → E) × Set F => IsVonNBounded 𝕜 SV.1 ∧ SV.2 ∈ 𝓝 0)
      fun SV => { f | MapsTo f SV.1 SV.2 } :=
  hasBasis_nhds_zero_of_basis (Filter.basis_sets _)

/-- The inclusion of *alternating* continuous multilinear maps into continuous multilinear maps
as a continuous linear map. -/
@[simps! -fullyApplied]
/-
**ContinuousAlternatingMap.toContinuousMultilinearMapCLM** 是 Mathlib 中的一个定义，位于命名
空间 `ContinuousAlternatingMap`。
形式化陈述：toContinuousMultilinearMapCLM (R : Type*) [Semiring R] [Module R F] [Conti
nuousConstSMul R F] [SMulCommClass 𝕜 R F] : E [⋀^ι]->L[𝕜] F ->L[R] ContinuousMul
tilinearMap 𝕜 (fun _ : ι => E) F
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of *alternating* continuous multilinear maps into continuous multi
linear maps
as a continuous linear map.
-/
def toContinuousMultilinearMapCLM
    (R : Type*) [Semiring R] [Module R F] [ContinuousConstSMul R F] [SMulCommClass 𝕜 R F] :
    E [⋀^ι]→L[𝕜] F →L[R] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F :=
  ⟨toContinuousMultilinearMapLinear, continuous_induced_dom⟩

section ContinuousSMul

variable [ContinuousSMul 𝕜 E]

/-
**ContinuousAlternatingMap.isClosedEmbedding_toContinuousMultilinearMap** 是 Math
lib 中的一个引理，位于命名空间 `ContinuousAlternatingMap`。
形式化陈述：isClosedEmbedding_toContinuousMultilinearMap [T2Space F] : IsClosedEmbeddi
ng (toContinuousMultilinearMap : (E [⋀^ι]->L[𝕜] F) -> ContinuousMultilinearMap 𝕜
 (fun _ : ι => E) F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousAlternatingMap.isEmbedding_toContinuousMultilinearMap`：isEmbed
ding_toContinuousMultilinearMap : IsEmbedding (toContinuousMultilinearMap : (E [
⋀^ι]->L[𝕜] F -> _))
· 使用引理 `ContinuousAlternatingMap.isClosed_range_toContinuousMultilinearMap`：isCl
osed_range_toContinuousMultilinearMap [ContinuousSMul 𝕜 E] [T2Space F] : IsClose
d (Set.range (toContinuousMultilinearMap : (E [⋀^ι]->L[𝕜…
-/
lemma isClosedEmbedding_toContinuousMultilinearMap [T2Space F] :
    IsClosedEmbedding (toContinuousMultilinearMap :
      (E [⋀^ι]→L[𝕜] F) → ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) :=
  ⟨isEmbedding_toContinuousMultilinearMap, isClosed_range_toContinuousMultilinearMap⟩
/-
**ContinuousAlternatingMap.instContinuousEvalConst** 是 Mathlib 中的一个实例，位于命名空间 `Co
ntinuousAlternatingMap`。
形式化陈述：instContinuousEvalConst : ContinuousEvalConst (E [⋀^ι]->L[𝕜] F) (ι -> E) F
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousEvalConst.of_continuous_forget`：ContinuousEvalConst.of_continu
ous_forget {F' : Type*} [FunLike F' α X] [TopologicalSpace F'] {f : F' -> F} (hc
 : Continuous f) (hf : forall …
· 使用定理 `ContinuousMultilinearMap.instContinuousEvalConstForall`：∀ {𝕜 : Type u_1}
 {ι : Type u_2} {E : ι → Type u_3} {F : Type u_4} [inst : NormedField 𝕜]   [inst
_1 : (i : ι) → TopologicalSpace (E i)] [inst…
· 使用引理 `ContinuousAlternatingMap.continuous_toContinuousMultilinearMap`：continuo
us_toContinuousMultilinearMap : Continuous (toContinuousMultilinearMap : (E [⋀^ι
]->L[𝕜] F -> _))
-/
instance instContinuousEvalConst : ContinuousEvalConst (E [⋀^ι]→L[𝕜] F) (ι → E) F :=
  .of_continuous_forget continuous_toContinuousMultilinearMap
/-
**ContinuousAlternatingMap.instT2Space** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlte
rnatingMap`。
形式化陈述：instT2Space [T2Space F] : T2Space (E [⋀^ι]->L[𝕜] F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `T2Space.of_injective_continuous`：T2Space.of_injective_continuous [Topolo
gicalSpace Y] [T2Space Y] {f : X -> Y} (hinj : Injective f) (hc : Continuous f) 
: T2Space X
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `continuous_coeFun`：continuous_coeFun : Continuous (DFunLike.coe : F -> α
 -> X)
-/
instance instT2Space [T2Space F] : T2Space (E [⋀^ι]→L[𝕜] F) :=
  .of_injective_continuous DFunLike.coe_injective continuous_coeFun
/-
**ContinuousAlternatingMap.instT3Space** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlte
rnatingMap`。
形式化陈述：instT3Space [T2Space F] : T3Space (E [⋀^ι]->L[𝕜] F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `IsTopologicalAddGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSp
ace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], RegularSpace G
-/
instance instT3Space [T2Space F] : T3Space (E [⋀^ι]→L[𝕜] F) :=
  inferInstance

section RestrictScalars

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
  [Module 𝕜' E] [IsScalarTower 𝕜' 𝕜 E] [Module 𝕜' F] [IsScalarTower 𝕜' 𝕜 F]

/-
**ContinuousAlternatingMap.isEmbedding_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间
 `ContinuousAlternatingMap`。
形式化陈述：isEmbedding_restrictScalars : IsEmbedding (restrictScalars 𝕜' : E [⋀^ι]->L
[𝕜] F -> E [⋀^ι]->L[𝕜'] F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.isEmbedding`：∀ {α : Type u} {β : Type v} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Topo
logy.IsEmbedding f
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `ContinuousAlternatingMap.isUniformEmbedding_restrictScalars`：isUniformEm
bedding_restrictScalars : IsUniformEmbedding (restrictScalars 𝕜' : E [⋀^ι]->L[𝕜]
 F -> E [⋀^ι]->L[𝕜'] F)
-/
theorem isEmbedding_restrictScalars :
    IsEmbedding (restrictScalars 𝕜' : E [⋀^ι]→L[𝕜] F → E [⋀^ι]→L[𝕜'] F) :=
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  (isUniformEmbedding_restrictScalars _).isEmbedding

@[continuity, fun_prop]
/-
**ContinuousAlternatingMap.continuous_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousAlternatingMap`。
形式化陈述：continuous_restrictScalars : Continuous (restrictScalars 𝕜' : E [⋀^ι]->L[𝕜
] F -> E [⋀^ι]->L[𝕜'] F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用定理 `ContinuousAlternatingMap.isEmbedding_restrictScalars`：isEmbedding_restri
ctScalars : IsEmbedding (restrictScalars 𝕜' : E [⋀^ι]->L[𝕜] F -> E [⋀^ι]->L[𝕜'] 
F)
-/
theorem continuous_restrictScalars :
    Continuous (restrictScalars 𝕜' : E [⋀^ι]→L[𝕜] F → E [⋀^ι]→L[𝕜'] F) :=
  isEmbedding_restrictScalars.continuous

variable (𝕜') in
/-- `ContinuousAlternatingMap.restrictScalars` as a `ContinuousLinearMap`. -/
@[simps -fullyApplied apply]
/-
**ContinuousAlternatingMap.restrictScalarsCLM** 是 Mathlib 中的一个定义，位于命名空间 `Continu
ousAlternatingMap`。
形式化陈述：restrictScalarsCLM [ContinuousConstSMul 𝕜' F] : E [⋀^ι]->L[𝕜] F ->L[𝕜'] E 
[⋀^ι]->L[𝕜'] F where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousAlternatingMap.restrictScalars` as a `ContinuousLinearMap`.
-/
def restrictScalarsCLM [ContinuousConstSMul 𝕜' F] :
    E [⋀^ι]→L[𝕜] F →L[𝕜'] E [⋀^ι]→L[𝕜'] F where
  toFun := restrictScalars 𝕜'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end RestrictScalars

end ContinuousSMul

section ContinuousConstSMul

variable {G : Type*} [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [ContinuousConstSMul 𝕜 F]

/-- Given a continuous linear map taking values in the space of continuous multilinear maps
such that all of its values are alternating maps,
lift it to a continuous linear map taking values in the space of continuous alternating maps. -/
/-
**ContinuousAlternatingMap.liftCLM** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlternat
ingMap`。
形式化陈述：liftCLM (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) (hf :
 forall x v i j, v i = v j -> i != j -> f x v = 0) : G ->L[𝕜] (E [⋀^ι]->L[𝕜] F) 
where toFun x
参数：f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F；hf : forall x v i 
j, v i = v j -> i != j -> f x v = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a continuous linear map taking values in the space of continuous multiline
ar maps
such that all of its values are alternating maps,
lift it to a continuous linear map taking values in the space of continuous alte
rnating maps.
-/
def liftCLM (f : G →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F)
    (hf : ∀ x v i j, v i = v j → i ≠ j → f x v = 0) : G →L[𝕜] (E [⋀^ι]→L[𝕜] F) where
  toFun x := ⟨f x, hf x⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  cont := continuous_induced_rng.mpr (map_continuous f)

@[simp]
/-
**ContinuousAlternatingMap.liftCLM_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousAl
ternatingMap`。
形式化陈述：liftCLM_apply (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F)
 (hf : forall x v i j, v i = v j -> i != j -> f x v = 0) (x : G) (v : ι -> E) : 
liftCLM f hf x v = f x v
参数：f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F；hf : forall x v i 
j, v i = v j -> i != j -> f x v = 0；x : G；v : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
lemma liftCLM_apply (f : G →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F)
    (hf : ∀ x v i j, v i = v j → i ≠ j → f x v = 0) (x : G) (v : ι → E) :
    liftCLM f hf x v = f x v :=
  rfl

section CompContinuousLinearMap

variable {E' : Type*} [AddCommGroup E'] [Module 𝕜 E'] [TopologicalSpace E']

/-- Composition of a continuous alternating map and a continuous linear map
as a bundled continuous linear map.

Note that for general topological vector spaces,
this function does not need to be continuous in `f`. -/
@[simps! apply]
/-
**ContinuousAlternatingMap.compContinuousLinearMapCLM** 是 Mathlib 中的一个定义，位于命名空间 
`ContinuousAlternatingMap`。
形式化陈述：compContinuousLinearMapCLM (f : E ->L[𝕜] E') : (E' [⋀^ι]->L[𝕜] F) ->L[𝕜] (
E [⋀^ι]->L[𝕜] F) where toLinearMap
参数：f : E ->L[𝕜] E'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of a continuous alternating map and a continuous linear map
as a bundled continuous linear map.

Note that for general topological vector spaces,
this function does not need to be continuous in `f`.
-/
def compContinuousLinearMapCLM (f : E →L[𝕜] E') : (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F) where
  toLinearMap := compContinuousLinearMapₗ f
  cont := by
    rw [isEmbedding_toContinuousMultilinearMap.continuous_iff]
    exact (map_continuous <| ContinuousMultilinearMap.compContinuousLinearMapL fun _ ↦ f).comp
      continuous_toContinuousMultilinearMap

end CompContinuousLinearMap

variable [ContinuousSMul 𝕜 E]
variable (𝕜 E F)

/-- The application of a multilinear map as a `ContinuousLinearMap`. -/
/-
**ContinuousAlternatingMap.apply** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlternatin
gMap`。
形式化陈述：apply (m : ι -> E) : E [⋀^ι]->L[𝕜] F ->L[𝕜] F where toFun c
参数：m : ι -> E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The application of a multilinear map as a `ContinuousLinearMap`.
-/
def apply (m : ι → E) : E [⋀^ι]→L[𝕜] F →L[𝕜] F where
  toFun c := c m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {𝕜 E F}

@[simp]
/-
**ContinuousAlternatingMap.apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousAlte
rnatingMap`。
形式化陈述：apply_apply {m : ι -> E} {c : E [⋀^ι]->L[𝕜] F} : apply 𝕜 E F m c = c m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
lemma apply_apply {m : ι → E} {c : E [⋀^ι]→L[𝕜] F} : apply 𝕜 E F m c = c m := rfl

end ContinuousConstSMul

variable [ContinuousSMul 𝕜 E] {α : Type*} {p : α → E [⋀^ι]→L[𝕜] F}

/-
**ContinuousAlternatingMap.hasSum_eval** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlte
rnatingMap`。
形式化陈述：hasSum_eval {q : E [⋀^ι]->L[𝕜] F} (h : HasSum p q) (m : ι -> E) : HasSum (
fun a => p a m) (q m)
参数：h : HasSum p q；m : ι -> E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `ContinuousEvalConst.continuous_eval_const`：∀ {F : Type u_1} {α : outPara
m (Type u_2)} {X : outParam (Type u_3)} {inst : FunLike F α X}   {inst_1 : Topol
ogicalSpace F} {inst_2 : Topolo…
-/
theorem hasSum_eval {q : E [⋀^ι]→L[𝕜] F} (h : HasSum p q) (m : ι → E) :
    HasSum (fun a => p a m) (q m) :=
  h.map (applyAddHom m) (continuous_eval_const m)
/-
**ContinuousAlternatingMap.tsum_eval** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAltern
atingMap`。
形式化陈述：tsum_eval [T2Space F] (hp : Summable p) (m : ι -> E) : (∑' a, p a) m = ∑' 
a, p a m
参数：hp : Summable p；m : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `ContinuousAlternatingMap.hasSum_eval`：hasSum_eval {q : E [⋀^ι]->L[𝕜] F} 
(h : HasSum p q) (m : ι -> E) : HasSum (fun a => p a m) (q m)
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
theorem tsum_eval [T2Space F] (hp : Summable p) (m : ι → E) : (∑' a, p a) m = ∑' a, p a m :=
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
/-
**ContinuousLinearMap.compContinuousAlternatingMapCLM** 是 Mathlib 中的一个定义，位于命名空间 
`ContinuousLinearMap`。
形式化陈述：compContinuousAlternatingMapCLM : (F ->L[𝕜] G) ->L[𝕜] (E [⋀^ι]->L[𝕜] F) ->
L[𝕜] (E [⋀^ι]->L[𝕜] G) where toFun g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousLinearMap.compContinuousAlternatingMap` as a bundled continuous bilin
ear map.

Given a continuous linear map `g : F →L[𝕜] G` and a continuous alternating map `
f : E [⋀^ι]→L[𝕜] F`,
it returns the continuous alternating map `g ∘ f`.
This function is continuous in `f` (for each `g`)
and in `g` (as a function taking values in continuous linear maps).
Note that for a general topological vector space,
the map is not guaranteed to be continuous in `(g, f)`.
-/
def compContinuousAlternatingMapCLM :
    (F →L[𝕜] G) →L[𝕜] (E [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] G) where
  toFun g :=
    { toLinearMap := compContinuousAlternatingMapₗ _ _ _ _ g
      cont := by
        rw [ContinuousAlternatingMap.isEmbedding_toContinuousMultilinearMap.continuous_iff]
        exact (map_continuous <| compContinuousMultilinearMapL 𝕜 (fun _ : ι ↦ E) F G g).comp
          ContinuousAlternatingMap.continuous_toContinuousMultilinearMap }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  cont := by
    rw [ContinuousLinearMap.isEmbedding_postcomp
      (ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜)
      ContinuousAlternatingMap.isEmbedding_toContinuousMultilinearMap |>.continuous_iff]
    exact map_continuous <|
      (precomp (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) G)
        ((ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜 : (E [⋀^ι]→L[𝕜] F) →L[𝕜] _))) ∘L
        (compContinuousMultilinearMapL 𝕜 (fun _ : ι ↦ E) F G)

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
/-
**ContinuousLinearEquiv.continuousAlternatingMapCongrRight** 是 Mathlib 中的一个定义，位于
命名空间 `ContinuousLinearEquiv`。
形式化陈述：continuousAlternatingMapCongrRight (g : F ≃L[𝕜] G) : (E [⋀^ι]->L[𝕜] F) ≃L[
𝕜] (E [⋀^ι]->L[𝕜] G) where __
参数：g : F ≃L[𝕜] G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousLinearMap.compContinuousAlternatingMap` as a bundled continuous linea
r equiv.

Given a continuous linear equivalence `g : F ≃L[𝕜] G`,
this function returns the equivalence between continuous alternating maps with c
odomain `F`
and continuous alternating maps with codomain `G`
that acts by composing these maps with `g`.
-/
def continuousAlternatingMapCongrRight (g : F ≃L[𝕜] G) :
    (E [⋀^ι]→L[𝕜] F) ≃L[𝕜] (E [⋀^ι]→L[𝕜] G) where
  __ := g.continuousAlternatingMapCongrRightEquiv
  __ := ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 E F G ι g.toContinuousLinearMap
  continuous_toFun := map_continuous <|
    ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 E F G ι g.toContinuousLinearMap
  continuous_invFun := map_continuous <|
    ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 E G F ι g.symm.toContinuousLinearMap

@[simp]
/-
**ContinuousLinearEquiv._root_.ContinuousLinearEquiv.continuousAlternatingMapCon
grRight_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**ContinuousLinearEquiv.continuousAlternatingMapCongrLeft** 是 Mathlib 中的一个定义，位于命
名空间 `ContinuousLinearEquiv`。
形式化陈述：continuousAlternatingMapCongrLeft (f : E ≃L[𝕜] E') : E [⋀^ι]->L[𝕜] F ≃L[𝕜]
 (E' [⋀^ι]->L[𝕜] F) where __
参数：f : E ≃L[𝕜] E'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a continuous linear isomorphism between the domains,
generate a continuous linear isomorphism between the spaces of continuous altern
ating maps.

This is `ContinuousAlternatingMap.compContinuousLinearMap` as an equivalence,
and is the continuous version of `AlternatingMap.domLCongr`.
-/
def continuousAlternatingMapCongrLeft (f : E ≃L[𝕜] E') :
    E [⋀^ι]→L[𝕜] F ≃L[𝕜] (E' [⋀^ι]→L[𝕜] F) where
  __ := f.continuousAlternatingMapCongrLeftEquiv
  __ := ContinuousAlternatingMap.compContinuousLinearMapCLM (f.symm : E' →L[𝕜] E)
  toFun g := g.compContinuousLinearMap (f.symm : E' →L[𝕜] E)
  continuous_invFun :=
    (ContinuousAlternatingMap.compContinuousLinearMapCLM (f : E →L[𝕜] E')).cont
  continuous_toFun :=
    (ContinuousAlternatingMap.compContinuousLinearMapCLM (f.symm : E' →L[𝕜] E)).cont

/-- Continuous linear equivalences between the domains and the codomains
generate a continuous linear equivalence between the spaces of continuous alternating maps. -/
@[simps! apply]
/-
**ContinuousLinearEquiv.continuousAlternatingMapCongr** 是 Mathlib 中的一个定义，位于命名空间 
`ContinuousLinearEquiv`。
形式化陈述：continuousAlternatingMapCongr (e : E ≃L[𝕜] E') (e' : F ≃L[𝕜] G) : (E [⋀^ι]
->L[𝕜] F) ≃L[𝕜] (E' [⋀^ι]->L[𝕜] G)
参数：e : E ≃L[𝕜] E'；e' : F ≃L[𝕜] G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous linear equivalences between the domains and the codomains
generate a continuous linear equivalence between the spaces of continuous altern
ating maps.
-/
def continuousAlternatingMapCongr (e : E ≃L[𝕜] E') (e' : F ≃L[𝕜] G) :
    (E [⋀^ι]→L[𝕜] F) ≃L[𝕜] (E' [⋀^ι]→L[𝕜] G) :=
  e.continuousAlternatingMapCongrLeft.trans <| e'.continuousAlternatingMapCongrRight
/-
**ContinuousLinearEquiv.coe_continuousAlternatingMapCongr** 是 Mathlib 中的一个引理，位于命
名空间 `ContinuousLinearEquiv`。
形式化陈述：coe_continuousAlternatingMapCongr (e : E ≃L[𝕜] E') (e' : F ≃L[𝕜] G) : (e.c
ontinuousAlternatingMapCongr e' (ι
参数：e : E ≃L[𝕜] E'；e' : F ≃L[𝕜] G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
lemma coe_continuousAlternatingMapCongr (e : E ≃L[𝕜] E') (e' : F ≃L[𝕜] G) :
    (e.continuousAlternatingMapCongr e' (ι := ι) : (E [⋀^ι]→L[𝕜] F) →L[𝕜] (E' [⋀^ι]→L[𝕜] G)) =
      ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 E' F G ι (e' : F →L[𝕜] G) ∘L
        ContinuousAlternatingMap.compContinuousLinearMapCLM e.symm :=
  rfl

end ContinuousLinearEquiv

