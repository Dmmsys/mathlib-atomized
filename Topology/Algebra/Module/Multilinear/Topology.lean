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

variable {𝕜 ι : Type*} {E : ι → Type*} {F : Type*}
  [NormedField 𝕜]
  [∀ i, TopologicalSpace (E i)] [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
  [AddCommGroup F] [Module 𝕜 F]

/-- An auxiliary definition used to define topology on `ContinuousMultilinearMap 𝕜 E F`. -/
/-
**ContinuousMultilinearMap.toUniformOnFun** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousM
ultilinearMap`。
形式化陈述：toUniformOnFun [TopologicalSpace F] (f : ContinuousMultilinearMap 𝕜 E F) :
 (Π i, E i) ->ᵤ[{s | IsVonNBounded 𝕜 s}] F
参数：f : ContinuousMultilinearMap 𝕜 E F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary definition used to define topology on `ContinuousMultilinearMap 𝕜 E
 F`.
-/
def toUniformOnFun [TopologicalSpace F] (f : ContinuousMultilinearMap 𝕜 E F) :
    (Π i, E i) →ᵤ[{s | IsVonNBounded 𝕜 s}] F :=
  UniformOnFun.ofFun _ f

open UniformOnFun in
/-
**ContinuousMultilinearMap.range_toUniformOnFun** 是 Mathlib 中的一个引理，位于命名空间 `Conti
nuousMultilinearMap`。
形式化陈述：range_toUniformOnFun [DecidableEq ι] [TopologicalSpace F] : range toUnifor
mOnFun = {f : (Π i, E i) ->ᵤ[{s | IsVonNBounded 𝕜 s}] F | Continuous (toFun _ f)
 ∧ (forall (m : Π i, E i) i x y, toFun _ f (update m i (x + y)) = toFun _ f (upd
ate m i x) + toFun _ f (update m i y)) ∧ (forall (m : Π i, E i) i (c : 𝕜) x, toF
un _ f (update m i (c • x)) = c • toFun _ f (update m i x))}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `ContinuousMultilinearMap.cont`：∀ {R : Type u} {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid (M₁
 i)] [inst_2 : AddC…
· 使用定理 `ContinuousMultilinearMap.map_update_add`：map_update_add [DecidableEq ι] 
(m : forall i, M₁ i) (i : ι) (x y : M₁ i) : f (update m i (x + y)) = f (update m
 i x) + f (update m i y)
· 使用定理 `ContinuousMultilinearMap.map_update_smul`：map_update_smul [DecidableEq ι
] (m : forall i, M₁ i) (i : ι) (c : R) (x : M₁ i) : f (update m i (c • x)) = c •
 f (update m i x)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
-/
lemma range_toUniformOnFun [DecidableEq ι] [TopologicalSpace F] :
    range toUniformOnFun =
      {f : (Π i, E i) →ᵤ[{s | IsVonNBounded 𝕜 s}] F |
        Continuous (toFun _ f) ∧
        (∀ (m : Π i, E i) i x y,
          toFun _ f (update m i (x + y)) = toFun _ f (update m i x) + toFun _ f (update m i y)) ∧
        (∀ (m : Π i, E i) i (c : 𝕜) x,
          toFun _ f (update m i (c • x)) = c • toFun _ f (update m i x))} := by
  ext f
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.cont, f.map_update_add, f.map_update_smul⟩
  · rintro ⟨hcont, hadd, hsmul⟩
    exact ⟨⟨⟨f, by intro; convert! hadd, by intro; convert! hsmul⟩, hcont⟩, rfl⟩

@[simp]
/-
**ContinuousMultilinearMap.toUniformOnFun_toFun** 是 Mathlib 中的一个引理，位于命名空间 `Conti
nuousMultilinearMap`。
形式化陈述：toUniformOnFun_toFun [TopologicalSpace F] (f : ContinuousMultilinearMap 𝕜 
E F) : UniformOnFun.toFun _ f.toUniformOnFun = f
参数：f : ContinuousMultilinearMap 𝕜 E F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toUniformOnFun_toFun [TopologicalSpace F] (f : ContinuousMultilinearMap 𝕜 E F) :
    UniformOnFun.toFun _ f.toUniformOnFun = f :=
  rfl
/-
**ContinuousMultilinearMap.instTopologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 `Conti
nuousMultilinearMap`。
形式化陈述：instTopologicalSpace [TopologicalSpace F] [IsTopologicalAddGroup F] : Topo
logicalSpace (ContinuousMultilinearMap 𝕜 E F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instTopologicalSpace [TopologicalSpace F] [IsTopologicalAddGroup F] :
    TopologicalSpace (ContinuousMultilinearMap 𝕜 E F) :=
  .induced toUniformOnFun <|
    @UniformOnFun.topologicalSpace _ _ (IsTopologicalAddGroup.rightUniformSpace F) _
/-
**ContinuousMultilinearMap.instUniformSpace** 是 Mathlib 中的一个实例，位于命名空间 `Continuou
sMultilinearMap`。
形式化陈述：instUniformSpace [UniformSpace F] [IsUniformAddGroup F] : UniformSpace (Co
ntinuousMultilinearMap 𝕜 E F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instUniformSpace [UniformSpace F] [IsUniformAddGroup F] :
    UniformSpace (ContinuousMultilinearMap 𝕜 E F) :=
  .replaceTopology (.comap toUniformOnFun <| UniformOnFun.uniformSpace _ _ _) <| by
    rw [instTopologicalSpace, IsUniformAddGroup.rightUniformSpace_eq]; rfl

section IsUniformAddGroup

variable [UniformSpace F] [IsUniformAddGroup F]

/-
**ContinuousMultilinearMap.isUniformInducing_toUniformOnFun** 是 Mathlib 中的一个引理，位
于命名空间 `ContinuousMultilinearMap`。
形式化陈述：isUniformInducing_toUniformOnFun : IsUniformInducing (toUniformOnFun : Con
tinuousMultilinearMap 𝕜 E F -> ((Π i, E i) ->ᵤ[{s | IsVonNBounded 𝕜 s}] F))
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isUniformInducing_toUniformOnFun :
    IsUniformInducing (toUniformOnFun :
      ContinuousMultilinearMap 𝕜 E F → ((Π i, E i) →ᵤ[{s | IsVonNBounded 𝕜 s}] F)) := ⟨rfl⟩
/-
**ContinuousMultilinearMap.isUniformEmbedding_toUniformOnFun** 是 Mathlib 中的一个引理，
位于命名空间 `ContinuousMultilinearMap`。
形式化陈述：isUniformEmbedding_toUniformOnFun : IsUniformEmbedding (toUniformOnFun : C
ontinuousMultilinearMap 𝕜 E F -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMultilinearMap.isUniformInducing_toUniformOnFun`：isUniformIndu
cing_toUniformOnFun : IsUniformInducing (toUniformOnFun : ContinuousMultilinearM
ap 𝕜 E F -> ((Π i, E i) ->ᵤ[{s | IsVonNBounded …
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
lemma isUniformEmbedding_toUniformOnFun :
    IsUniformEmbedding (toUniformOnFun : ContinuousMultilinearMap 𝕜 E F → _) :=
  ⟨isUniformInducing_toUniformOnFun, DFunLike.coe_injective⟩
/-
**ContinuousMultilinearMap.isEmbedding_toUniformOnFun** 是 Mathlib 中的一个引理，位于命名空间 
`ContinuousMultilinearMap`。
形式化陈述：isEmbedding_toUniformOnFun : IsEmbedding (toUniformOnFun : ContinuousMulti
linearMap 𝕜 E F -> ((Π i, E i) ->ᵤ[{s | IsVonNBounded 𝕜 s}] F))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.isEmbedding`：∀ {α : Type u} {β : Type v} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Topo
logy.IsEmbedding f
· 使用引理 `ContinuousMultilinearMap.isUniformEmbedding_toUniformOnFun`：isUniformEmb
edding_toUniformOnFun : IsUniformEmbedding (toUniformOnFun : ContinuousMultiline
arMap 𝕜 E F -> _)
-/
lemma isEmbedding_toUniformOnFun :
    IsEmbedding (toUniformOnFun : ContinuousMultilinearMap 𝕜 E F →
      ((Π i, E i) →ᵤ[{s | IsVonNBounded 𝕜 s}] F)) :=
  isUniformEmbedding_toUniformOnFun.isEmbedding

@[fun_prop]
/-
**ContinuousMultilinearMap.uniformContinuous_coe_fun** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousMultilinearMap`。
形式化陈述：uniformContinuous_coe_fun [forall i, ContinuousSMul 𝕜 (E i)] : UniformCont
inuous (DFunLike.coe : ContinuousMultilinearMap 𝕜 E F -> (Π i, E i) -> F)
参数：E i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `UniformOnFun.uniformContinuous_toFun`：∀ {α : Type u_1} {β : Type u_2} [i
nst : UniformSpace β] {𝔖 : Set (Set α)},   ⋃₀ 𝔖 = Set.univ → UniformContinuous ⇑
(UniformOnFun.toFun 𝔖)
· 使用定理 `Bornology.sUnion_isVonNBounded_eq_univ`：sUnion_isVonNBounded_eq_univ : ⋃
₀ Set.ofPred (IsVonNBounded 𝕜) = (Set.univ : Set E)
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用引理 `ContinuousMultilinearMap.isUniformEmbedding_toUniformOnFun`：isUniformEmb
edding_toUniformOnFun : IsUniformEmbedding (toUniformOnFun : ContinuousMultiline
arMap 𝕜 E F -> _)
-/
theorem uniformContinuous_coe_fun [∀ i, ContinuousSMul 𝕜 (E i)] :
    UniformContinuous (DFunLike.coe : ContinuousMultilinearMap 𝕜 E F → (Π i, E i) → F) :=
  (UniformOnFun.uniformContinuous_toFun sUnion_isVonNBounded_eq_univ).comp
    isUniformEmbedding_toUniformOnFun.uniformContinuous

@[fun_prop]
/-
**ContinuousMultilinearMap.uniformContinuous_eval_const** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousMultilinearMap`。
形式化陈述：uniformContinuous_eval_const [forall i, ContinuousSMul 𝕜 (E i)] (x : Π i, 
E i) : UniformContinuous fun f : ContinuousMultilinearMap 𝕜 E F => f x
参数：E i；x : Π i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `uniformContinuous_pi`：uniformContinuous_pi {β : Type*} [UniformSpace β] 
{f : β -> forall i, α i} : UniformContinuous f ↔ forall i, UniformContinuous fun
 x => f x …
· 使用定理 `ContinuousMultilinearMap.uniformContinuous_coe_fun`：uniformContinuous_co
e_fun [forall i, ContinuousSMul 𝕜 (E i)] : UniformContinuous (DFunLike.coe : Con
tinuousMultilinearMap 𝕜 E F -> (Π i, E i…
-/
theorem uniformContinuous_eval_const [∀ i, ContinuousSMul 𝕜 (E i)] (x : Π i, E i) :
    UniformContinuous fun f : ContinuousMultilinearMap 𝕜 E F ↦ f x :=
  uniformContinuous_pi.1 uniformContinuous_coe_fun x
/-
**ContinuousMultilinearMap.instIsUniformAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `Cont
inuousMultilinearMap`。
形式化陈述：instIsUniformAddGroup : IsUniformAddGroup (ContinuousMultilinearMap 𝕜 E F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `IsUniformInducing.isUniformAddGroup`：∀ {G : Type u_1} {H : Type u_2} {ho
m : Type u_3} [inst : AddGroup G] [inst_1 : AddGroup H] [inst_2 : UniformSpace G
]   [inst_3 : UniformSpac…
· 使用定理 `instIsUniformAddGroupUniformOnFun`：∀ {α : Type u_1} {G : Type u_2} [inst
 : AddGroup G] {𝔖 : Set (Set α)} [inst_1 : UniformSpace G] [IsUniformAddGroup G]
,   IsUniformAddGroup (…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用引理 `ContinuousMultilinearMap.isUniformEmbedding_toUniformOnFun`：isUniformEmb
edding_toUniformOnFun : IsUniformEmbedding (toUniformOnFun : ContinuousMultiline
arMap 𝕜 E F -> _)
-/
instance instIsUniformAddGroup : IsUniformAddGroup (ContinuousMultilinearMap 𝕜 E F) :=
  let φ : ContinuousMultilinearMap 𝕜 E F →+ (Π i, E i) →ᵤ[{s | IsVonNBounded 𝕜 s}] F :=
    { toFun := toUniformOnFun, map_add' := fun _ _ ↦ rfl, map_zero' := rfl }
  isUniformEmbedding_toUniformOnFun.isUniformAddGroup φ
/-
**ContinuousMultilinearMap.instUniformContinuousConstSMul** 是 Mathlib 中的一个实例，位于命
名空间 `ContinuousMultilinearMap`。
形式化陈述：instUniformContinuousConstSMul {M : Type*} [Monoid M] [DistribMulAction M 
F] [SMulCommClass 𝕜 M F] [ContinuousConstSMul M F] : UniformContinuousConstSMul 
M (ContinuousMultilinearMap 𝕜 E F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUniformInducing.uniformContinuousConstSMul`：IsUniformInducing.uniformC
ontinuousConstSMul [SMul M Y] [UniformContinuousConstSMul M Y] {f : X -> Y} (hf 
: IsUniformInducing f) (hsmul : fo…
· 使用定理 `uniformContinuousConstSMul_of_continuousConstSMul`：uniformContinuousCons
tSMul_of_continuousConstSMul [AddGroup M] [DistribSMul R M] [UniformSpace M] [Is
UniformAddGroup M] [ContinuousConstSMul…
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用引理 `ContinuousMultilinearMap.isUniformEmbedding_toUniformOnFun`：isUniformEmb
edding_toUniformOnFun : IsUniformEmbedding (toUniformOnFun : ContinuousMultiline
arMap 𝕜 E F -> _)
-/
instance instUniformContinuousConstSMul {M : Type*}
    [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜 M F] [ContinuousConstSMul M F] :
    UniformContinuousConstSMul M (ContinuousMultilinearMap 𝕜 E F) :=
  haveI := uniformContinuousConstSMul_of_continuousConstSMul M F
  isUniformEmbedding_toUniformOnFun.uniformContinuousConstSMul fun _ _ ↦ rfl

@[fun_prop]
/-
**ContinuousMultilinearMap.isUniformInducing_postcomp** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousMultilinearMap`。
形式化陈述：isUniformInducing_postcomp {G : Type*} [AddCommGroup G] [UniformSpace G] [
IsUniformAddGroup G] [Module 𝕜 G] (g : F ->L[𝕜] G) (hg : IsUniformInducing g) : 
IsUniformInducing (g.compContinuousMultilinearMap : ContinuousMultilinearMap 𝕜 E
 F -> ContinuousMultilinearMap 𝕜 E G)
参数：g : F ->L[𝕜] G；hg : IsUniformInducing g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUniformInducing.of_comp_iff`：IsUniformInducing.of_comp_iff {g : β -> γ
} (hg : IsUniformInducing g) {f : α -> β} : IsUniformInducing (g ∘ f) ↔ IsUnifor
mInducing f
· 使用引理 `ContinuousMultilinearMap.isUniformInducing_toUniformOnFun`：isUniformIndu
cing_toUniformOnFun : IsUniformInducing (toUniformOnFun : ContinuousMultilinearM
ap 𝕜 E F -> ((Π i, E i) ->ᵤ[{s | IsVonNBounded …
· 使用定理 `IsUniformInducing.comp`：IsUniformInducing.comp {g : β -> γ} (hg : IsUnif
ormInducing g) {f : α -> β} (hf : IsUniformInducing f) : IsUniformInducing (g ∘ 
f)
· 使用引理 `UniformOnFun.postcomp_isUniformInducing`：postcomp_isUniformInducing [Uni
formSpace γ] {f : γ -> β} (hf : IsUniformInducing f) : IsUniformInducing (ofFun 
𝔖 ∘ (f ∘ ·) ∘ toFun 𝔖)
-/
theorem isUniformInducing_postcomp
    {G : Type*} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] [Module 𝕜 G]
    (g : F →L[𝕜] G) (hg : IsUniformInducing g) :
    IsUniformInducing (g.compContinuousMultilinearMap :
      ContinuousMultilinearMap 𝕜 E F → ContinuousMultilinearMap 𝕜 E G) := by
  rw [← isUniformInducing_toUniformOnFun.of_comp_iff]
  exact (UniformOnFun.postcomp_isUniformInducing hg).comp isUniformInducing_toUniformOnFun

section CompleteSpace

variable [∀ i, ContinuousSMul 𝕜 (E i)] [ContinuousConstSMul 𝕜 F] [CompleteSpace F]

open UniformOnFun in
/-
**ContinuousMultilinearMap.completeSpace** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMu
ltilinearMap`。
形式化陈述：completeSpace (h : IsCoherentWith {s : Set (Π i, E i) | IsVonNBounded 𝕜 s}
) : CompleteSpace (ContinuousMultilinearMap 𝕜 E F)
参数：h : IsCoherentWith {s : Set (Π i, E i) | IsVonNBounded 𝕜 s}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `UniformOnFun.uniformContinuous_eval`：uniformContinuous_eval (h : ⋃₀ 𝔖 = 
univ) (x : α) : UniformContinuous ((Function.eval x : (α -> β) -> β) ∘ toFun 𝔖)
· 使用定理 `Bornology.sUnion_isVonNBounded_eq_univ`：sUnion_isVonNBounded_eq_univ : ⋃
₀ Set.ofPred (IsVonNBounded 𝕜) = (Set.univ : Set E)
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `completeSpace_iff_isComplete_range`：completeSpace_iff_isComplete_range {
f : α -> β} (hf : IsUniformInducing f) : CompleteSpace α ↔ IsComplete (range f)
· 使用引理 `ContinuousMultilinearMap.isUniformInducing_toUniformOnFun`：isUniformIndu
cing_toUniformOnFun : IsUniformInducing (toUniformOnFun : ContinuousMultilinearM
ap 𝕜 E F -> ((Π i, E i) ->ᵤ[{s | IsVonNBounded …
· 使用引理 `ContinuousMultilinearMap.range_toUniformOnFun`：range_toUniformOnFun [Dec
idableEq ι] [TopologicalSpace F] : range toUniformOnFun = {f : (Π i, E i) ->ᵤ[{s
 | IsVonNBounded 𝕜 s}] F | Continuo…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsClosed.isComplete`：IsClosed.isComplete [CompleteSpace α] {s : Set α} (
h : IsClosed s) : IsComplete s
· 使用定理 `UniformOnFun.instCompleteSpace`：∀ {α : Type u_1} {β : Type u_2} [inst : 
UniformSpace β] {𝔖 : Set (Set α)} [CompleteSpace β],   CompleteSpace (UniformOnF
un α β 𝔖)
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `UniformOnFun.isClosed_setOfPred_continuous`：isClosed_setOfPred_continuou
s [TopologicalSpace α] (h : IsCoherentWith 𝔖) : IsClosed {f : α ->ᵤ[𝔖] β | Conti
nuous (toFun 𝔖 f)}
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `Continuous.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 : A
dd M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : X 
→ M}…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `Continuous.const_smul`：Continuous.const_smul (hg : Continuous g) (c : M)
 : Continuous (c • g)
· 使用定理 `SeparationQuotient.instIsUniformAddGroup`：∀ {G : Type u_1} [inst : AddGr
oup G] [inst_1 : UniformSpace G] [inst_2 : IsUniformAddGroup G],   IsUniformAddG
roup (SeparationQuotient G)
· 使用定理 `IsUniformInducing.completeSpace_congr`：IsUniformInducing.completeSpace_c
ongr {f : α -> β} (hf : IsUniformInducing f) (hsurj : f.Surjective) : CompleteSp
ace α ↔ CompleteSpace β
· 使用定理 `ContinuousMultilinearMap.isUniformInducing_postcomp`：isUniformInducing_p
ostcomp {G : Type*} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] [Mod
ule 𝕜 G] (g : F ->L[𝕜] G) (hg : IsUniform…
· 使用引理 `SeparationQuotient.isUniformInducing_mk`：SeparationQuotient.isUniformInd
ucing_mk : IsUniformInducing (mk : α -> SeparationQuotient α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 38 条，此处仅展示前 30 条）
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
  have H : ∀ {m : Π i, E i},
      Continuous fun f : (Π i, E i) →ᵤ[{s | IsVonNBounded 𝕜 s}] F ↦ toFun _ f m :=
    (uniformContinuous_eval (sUnion_isVonNBounded_eq_univ) _).continuous
  rw [completeSpace_iff_isComplete_range isUniformInducing_toUniformOnFun, range_toUniformOnFun]
  simp only [ofPred_and, ofPred_forall]
  apply_rules [IsClosed.isComplete, IsClosed.inter]
  · exact UniformOnFun.isClosed_setOfPred_continuous h
  · exact isClosed_iInter fun m ↦ isClosed_iInter fun i ↦
      isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ isClosed_eq H (H.add H)
  · exact isClosed_iInter fun m ↦ isClosed_iInter fun i ↦
      isClosed_iInter fun c ↦ isClosed_iInter fun x ↦ isClosed_eq H (H.const_smul _)
/-
**ContinuousMultilinearMap.instCompleteSpace** 是 Mathlib 中的一个实例，位于命名空间 `Continuo
usMultilinearMap`。
形式化陈述：instCompleteSpace [forall i, IsTopologicalAddGroup (E i)] [SequentialSpace
 (Π i, E i)] : CompleteSpace (ContinuousMultilinearMap 𝕜 E F)
参数：E i；Π i, E i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.completeSpace`：completeSpace (h : IsCoherentWit
h {s : Set (Π i, E i) | IsVonNBounded 𝕜 s}) : CompleteSpace (ContinuousMultiline
arMap 𝕜 E F)
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
instance instCompleteSpace [∀ i, IsTopologicalAddGroup (E i)] [SequentialSpace (Π i, E i)] :
    CompleteSpace (ContinuousMultilinearMap 𝕜 E F) :=
  completeSpace <| .of_seq fun _u x hux ↦ (hux.isVonNBounded_range 𝕜).insert x

end CompleteSpace

section RestrictScalars

variable (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
  [∀ i, Module 𝕜' (E i)] [∀ i, IsScalarTower 𝕜' 𝕜 (E i)] [Module 𝕜' F] [IsScalarTower 𝕜' 𝕜 F]
  [∀ i, ContinuousSMul 𝕜 (E i)]

set_option backward.isDefEq.respectTransparency false in
@[fun_prop]
/-
**ContinuousMultilinearMap.isUniformEmbedding_restrictScalars** 是 Mathlib 中的一个定理
，位于命名空间 `ContinuousMultilinearMap`。
形式化陈述：isUniformEmbedding_restrictScalars : IsUniformEmbedding (restrictScalars 𝕜
' : ContinuousMultilinearMap 𝕜 E F -> ContinuousMultilinearMap 𝕜' E F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NontriviallyNormedField.non_trivial`：∀ {α : Type u_5} [self : Nontrivial
lyNormedField α], ∃ x, 1 < ‖x‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUniformEmbedding.of_comp_iff`：IsUniformEmbedding.of_comp_iff {g : β ->
 γ} (hg : IsUniformEmbedding g) {f : α -> β} : IsUniformEmbedding (g ∘ f) ↔ IsUn
iformEmbedding f
· 使用引理 `ContinuousMultilinearMap.isUniformEmbedding_toUniformOnFun`：isUniformEmb
edding_toUniformOnFun : IsUniformEmbedding (toUniformOnFun : ContinuousMultiline
arMap 𝕜 E F -> _)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Bornology.IsVonNBounded.extend_scalars`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_6} [inst_1 : AddCommGroup E]   [inst_2 : _root_.
Module 𝕜 E] (𝕝 : Type u_7) […
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `Bornology.IsVonNBounded.restrict_scalars`：∀ (𝕜 : Type u_1) {𝕜' : Type u_
2} {E : Type u_3} [inst : NormedField 𝕜] [inst_1 : NormedRing 𝕜']   [inst_2 : No
rmedAlgebra 𝕜 𝕜'] [inst_3 : Ze…
-/
theorem isUniformEmbedding_restrictScalars :
    IsUniformEmbedding
      (restrictScalars 𝕜' : ContinuousMultilinearMap 𝕜 E F → ContinuousMultilinearMap 𝕜' E F) := by
  let : NontriviallyNormedField 𝕜 :=
    ⟨let ⟨x, hx⟩ := @NontriviallyNormedField.non_trivial 𝕜' _; ⟨algebraMap 𝕜' 𝕜 x, by simpa⟩⟩
  rw [← isUniformEmbedding_toUniformOnFun.of_comp_iff]
  convert! isUniformEmbedding_toUniformOnFun using 4 with s
  exact ⟨fun h ↦ h.extend_scalars _, fun h ↦ h.restrict_scalars _⟩

@[fun_prop]
/-
**ContinuousMultilinearMap.uniformContinuous_restrictScalars** 是 Mathlib 中的一个定理，
位于命名空间 `ContinuousMultilinearMap`。
形式化陈述：uniformContinuous_restrictScalars : UniformContinuous (restrictScalars 𝕜' 
: ContinuousMultilinearMap 𝕜 E F -> ContinuousMultilinearMap 𝕜' E F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用定理 `ContinuousMultilinearMap.isUniformEmbedding_restrictScalars`：isUniformEm
bedding_restrictScalars : IsUniformEmbedding (restrictScalars 𝕜' : ContinuousMul
tilinearMap 𝕜 E F -> ContinuousMultilinearMap 𝕜' …
-/
theorem uniformContinuous_restrictScalars :
    UniformContinuous
      (restrictScalars 𝕜' : ContinuousMultilinearMap 𝕜 E F → ContinuousMultilinearMap 𝕜' E F) :=
  (isUniformEmbedding_restrictScalars 𝕜').uniformContinuous

end RestrictScalars

end IsUniformAddGroup

variable [TopologicalSpace F] [IsTopologicalAddGroup F]

/-
**ContinuousMultilinearMap.instIsTopologicalAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `
ContinuousMultilinearMap`。
形式化陈述：instIsTopologicalAddGroup : IsTopologicalAddGroup (ContinuousMultilinearMa
p 𝕜 E F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
-/
instance instIsTopologicalAddGroup : IsTopologicalAddGroup (ContinuousMultilinearMap 𝕜 E F) :=
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  inferInstance
/-
**ContinuousMultilinearMap.instContinuousConstSMul** 是 Mathlib 中的一个实例，位于命名空间 `Co
ntinuousMultilinearMap`。
形式化陈述：instContinuousConstSMul {M : Type*} [Monoid M] [DistribMulAction M F] [SMu
lCommClass 𝕜 M F] [ContinuousConstSMul M F] : ContinuousConstSMul M (ContinuousM
ultilinearMap 𝕜 E F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
-/
instance instContinuousConstSMul
    {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜 M F] [ContinuousConstSMul M F] :
    ContinuousConstSMul M (ContinuousMultilinearMap 𝕜 E F) := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  infer_instance
/-
**ContinuousMultilinearMap.instContinuousSMul** 是 Mathlib 中的一个实例，位于命名空间 `Continu
ousMultilinearMap`。
形式化陈述：instContinuousSMul [ContinuousSMul 𝕜 F] : ContinuousSMul 𝕜 (ContinuousMult
ilinearMap 𝕜 E F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用引理 `UniformOnFun.continuousSMul_induced_of_image_bounded`：UniformOnFun.conti
nuousSMul_induced_of_image_bounded (φ : hom) (hφ : IsInducing (ofFun 𝔖 ∘ φ)) (h 
: forall u : H, forall s in 𝔖, Bornology.I…
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用引理 `ContinuousMultilinearMap.isEmbedding_toUniformOnFun`：isEmbedding_toUnifo
rmOnFun : IsEmbedding (toUniformOnFun : ContinuousMultilinearMap 𝕜 E F -> ((Π i,
 E i) ->ᵤ[{s | IsVonNBounded 𝕜 s}] F))
· 使用定理 `Bornology.IsVonNBounded.image_multilinear`：image_multilinear [Continuous
SMul 𝕜 F] {s : Set (forall i, E i)} (hs : IsVonNBounded 𝕜 s) (f : ContinuousMult
ilinearMap 𝕜 E F) : IsVonNBound…
-/
instance instContinuousSMul [ContinuousSMul 𝕜 F] :
    ContinuousSMul 𝕜 (ContinuousMultilinearMap 𝕜 E F) :=
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  let φ : ContinuousMultilinearMap 𝕜 E F →ₗ[𝕜] (Π i, E i) → F :=
    { toFun := (↑), map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  UniformOnFun.continuousSMul_induced_of_image_bounded _ _ _ _ φ
    isEmbedding_toUniformOnFun.isInducing fun _ _ hu ↦ hu.image_multilinear _
/-
**ContinuousMultilinearMap.hasBasis_nhds_zero_of_basis** 是 Mathlib 中的一个定理，位于命名空间
 `ContinuousMultilinearMap`。
形式化陈述：hasBasis_nhds_zero_of_basis {ι : Type*} {p : ι -> Prop} {b : ι -> Set F} (
h : (𝓝 (0 : F)).HasBasis p b) : (𝓝 (0 : ContinuousMultilinearMap 𝕜 E F)).HasBasi
s (fun Si : Set (Π i, E i) × ι => IsVonNBounded 𝕜 Si.1 ∧ p Si.2) fun Si => { f |
 MapsTo f Si.1 (b Si.2) }
参数：h : (𝓝 (0 : F)).HasBasis p b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `UniformOnFun.hasBasis_nhds_zero_of_basis`：∀ {α : Type u_1} {G : Type u_2
} {ι : Type u_3} [inst : AddGroup G] [inst_1 : UniformSpace G] [IsUniformAddGrou
p G]   (𝔖 : Set (Set α)),   𝔖.…
· 使用定理 `Bornology.isVonNBounded_empty`：isVonNBounded_empty : IsVonNBounded 𝕜 (∅ 
: Set E)
· 使用定理 `directedOn_of_sup_mem`：directedOn_of_sup_mem [SemilatticeSup α] {S : Set
 α} (H : forall ⦃i j⦄, i in S -> j in S -> i ⊔ j in S) : DirectedOn (· <= ·) S
· 使用定理 `Bornology.IsVonNBounded.union`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : S
eminormedRing 𝕜] [inst_1 : SMul 𝕜 E] [inst_2 : Zero E]   [inst_3 : TopologicalSp
ace E] {s₁ s₂ : Set…
-/
theorem hasBasis_nhds_zero_of_basis {ι : Type*} {p : ι → Prop} {b : ι → Set F}
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
/-
**ContinuousMultilinearMap.hasBasis_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousMultilinearMap`。
形式化陈述：hasBasis_nhds_zero : (𝓝 (0 : ContinuousMultilinearMap 𝕜 E F)).HasBasis (fu
n SV : Set (Π i, E i) × Set F => IsVonNBounded 𝕜 SV.1 ∧ SV.2 in 𝓝 0) fun SV => {
 f | MapsTo f SV.1 SV.2 }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.hasBasis_nhds_zero_of_basis`：hasBasis_nhds_zero
_of_basis {ι : Type*} {p : ι -> Prop} {b : ι -> Set F} (h : (𝓝 (0 : F)).HasBasis
 p b) : (𝓝 (0 : ContinuousMultilinearMap 𝕜…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem hasBasis_nhds_zero :
    (𝓝 (0 : ContinuousMultilinearMap 𝕜 E F)).HasBasis
      (fun SV : Set (Π i, E i) × Set F => IsVonNBounded 𝕜 SV.1 ∧ SV.2 ∈ 𝓝 0) fun SV =>
      { f | MapsTo f SV.1 SV.2 } :=
  hasBasis_nhds_zero_of_basis (Filter.basis_sets _)
/-
**ContinuousMultilinearMap.eventually_nhds_zero_mapsTo** 是 Mathlib 中的一个定理，位于命名空间
 `ContinuousMultilinearMap`。
形式化陈述：eventually_nhds_zero_mapsTo {s : Set (forall i, E i)} (hs : IsVonNBounded 
𝕜 s) {U : Set F} (hu : U in 𝓝 0) : forallᶠ f : ContinuousMultilinearMap 𝕜 E F in
 𝓝 0, MapsTo f s U
参数：forall i, E i；hs : IsVonNBounded 𝕜 s；hu : U in 𝓝 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `ContinuousMultilinearMap.hasBasis_nhds_zero`：hasBasis_nhds_zero : (𝓝 (0 
: ContinuousMultilinearMap 𝕜 E F)).HasBasis (fun SV : Set (Π i, E i) × Set F => 
IsVonNBounded 𝕜 SV.1 ∧ SV.2 in 𝓝 …
-/
theorem eventually_nhds_zero_mapsTo {s : Set (∀ i, E i)} (hs : IsVonNBounded 𝕜 s)
    {U : Set F} (hu : U ∈ 𝓝 0) :
    ∀ᶠ f : ContinuousMultilinearMap 𝕜 E F in 𝓝 0, MapsTo f s U :=
  hasBasis_nhds_zero.mem_of_mem (i := (s, U)) ⟨hs, hu⟩
/-
**ContinuousMultilinearMap.isVonNBounded_image2_apply** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousMultilinearMap`。
形式化陈述：isVonNBounded_image2_apply [ContinuousConstSMul 𝕜 F] {S : Set (ContinuousM
ultilinearMap 𝕜 E F)} (hS : IsVonNBounded 𝕜 S) {s : Set (forall i, E i)} (hs : I
sVonNBounded 𝕜 s) : IsVonNBounded 𝕜 (Set.image2 (fun f x => f x) S s)
参数：ContinuousMultilinearMap 𝕜 E F；hS : IsVonNBounded 𝕜 S；forall i, E i；hs : IsVo
nNBounded 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `ContinuousMultilinearMap.eventually_nhds_zero_mapsTo`：eventually_nhds_ze
ro_mapsTo {s : Set (forall i, E i)} (hs : IsVonNBounded 𝕜 s) {U : Set F} (hu : U
 in 𝓝 0) : forallᶠ f : ContinuousMultiline…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image2_subset_iff`：image2_subset_iff {u : Set γ} : image2 f s t subs
eteq u ↔ forall x in s, forall y in t, f x y in u
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
-/
theorem isVonNBounded_image2_apply [ContinuousConstSMul 𝕜 F]
    {S : Set (ContinuousMultilinearMap 𝕜 E F)} (hS : IsVonNBounded 𝕜 S)
    {s : Set (∀ i, E i)} (hs : IsVonNBounded 𝕜 s) :
    IsVonNBounded 𝕜 (Set.image2 (fun f x ↦ f x) S s) := by
  intro U hU
  filter_upwards [hS (eventually_nhds_zero_mapsTo hs hU)] with c hc
  rw [image2_subset_iff]
  intro f hf x hx
  rcases hc hf with ⟨g, hg, rfl⟩
  exact smul_mem_smul_set (hg hx)

section CompContinuousLinearMap
variable {E₁ : ι → Type*} [∀ i, TopologicalSpace (E₁ i)] [ContinuousConstSMul 𝕜 F]
  [∀ i, AddCommGroup (E₁ i)] [∀ i, Module 𝕜 (E₁ i)]

/-- `ContinuousMultilinearMap.compContinuousLinearMap` as a bundled continuous linear map.
Given a family of continuous linear maps `f : Π i, E i →L[𝕜] E₁ i`,
this function returns a continuous linear maps between the spaces of continuous multilinear maps
on `Π i, E₁ i` and on `Π i, E i`.
The map sends `g` to the map given by `v ↦ g (fun i ↦ f i (v i))`.

Actually, the map is multilinear in `f`,
see `ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear`.

For a version fixing `g` and varying `f`, see `compContinuousLinearMapLRight`. -/
@[simps! apply]
/-
**ContinuousMultilinearMap.compContinuousLinearMapL** 是 Mathlib 中的一个定义，位于命名空间 `C
ontinuousMultilinearMap`。
形式化陈述：compContinuousLinearMapL (f : forall i, E i ->L[𝕜] E₁ i) : ContinuousMulti
linearMap 𝕜 E₁ F ->L[𝕜] ContinuousMultilinearMap 𝕜 E F
参数：f : forall i, E i ->L[𝕜] E₁ i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousMultilinearMap.compContinuousLinearMap` as a bundled continuous linea
r map.
Given a family of continuous linear maps `f : Π i, E i →L[𝕜] E₁ i`,
this function returns a continuous linear maps between the spaces of continuous 
multilinear maps
on `Π i, E₁ i` and on `Π i, E i`.
The map sends `g` to the map given by `v ↦ g (fun i ↦ f i (v i))`.

Actually, the map is multilinear in `f`,
see `ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear`.

For a version fixing `g` and varying `f`, see `compContinuousLinearMapLRight`.
-/
def compContinuousLinearMapL (f : ∀ i, E i →L[𝕜] E₁ i) :
    ContinuousMultilinearMap 𝕜 E₁ F →L[𝕜] ContinuousMultilinearMap 𝕜 E F :=
  letI aux : ContinuousMultilinearMap 𝕜 E₁ F →ₗ[𝕜] ContinuousMultilinearMap 𝕜 E F :=
    { toFun g := g.compContinuousLinearMap f
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
  { toLinearMap := aux
    cont := by
      apply continuous_of_tendsto_nhds_zero aux
      rw [hasBasis_nhds_zero.tendsto_iff hasBasis_nhds_zero]
      rintro ⟨U, V⟩ ⟨hU, hV⟩
      set φ : (∀ i, E i) →L[𝕜] (∀ i, E₁ i) := .piMap f
      exact ⟨(φ '' U, V), ⟨hU.image φ, hV⟩, fun g hg ↦ hg.comp (mapsTo_image _ _)⟩ }

@[fun_prop]
/-
**ContinuousMultilinearMap.continuous_precomp** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousMultilinearMap`。
形式化陈述：continuous_precomp (f : forall i, E i ->L[𝕜] E₁ i) : Continuous fun g : Co
ntinuousMultilinearMap 𝕜 E₁ F => g.compContinuousLinearMap f
参数：f : forall i, E i ->L[𝕜] E₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem continuous_precomp (f : ∀ i, E i →L[𝕜] E₁ i) :
    Continuous fun g : ContinuousMultilinearMap 𝕜 E₁ F ↦ g.compContinuousLinearMap f :=
  map_continuous (compContinuousLinearMapL f)

end CompContinuousLinearMap

variable [∀ i, ContinuousSMul 𝕜 (E i)]

/-
**ContinuousMultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMultilinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousEvalConst (ContinuousMultilinearMap 𝕜 E F) (Π i, E i) F where
  continuous_eval_const x :=
    let _ := IsTopologicalAddGroup.rightUniformSpace F
    have _ := isUniformAddGroup_of_addCommGroup (G := F)
    (uniformContinuous_eval_const x).continuous
/-
**ContinuousMultilinearMap.instT2Space** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMult
ilinearMap`。
形式化陈述：instT2Space [T2Space F] : T2Space (ContinuousMultilinearMap 𝕜 E F)
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
· 使用定理 `ContinuousMultilinearMap.instContinuousEvalConstForall`：∀ {𝕜 : Type u_1}
 {ι : Type u_2} {E : ι → Type u_3} {F : Type u_4} [inst : NormedField 𝕜]   [inst
_1 : (i : ι) → TopologicalSpace (E i)] [inst…
-/
instance instT2Space [T2Space F] : T2Space (ContinuousMultilinearMap 𝕜 E F) :=
  .of_injective_continuous DFunLike.coe_injective continuous_coeFun
/-
**ContinuousMultilinearMap.instT3Space** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMult
ilinearMap`。
形式化陈述：instT3Space [T2Space F] : T3Space (ContinuousMultilinearMap 𝕜 E F)
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
instance instT3Space [T2Space F] : T3Space (ContinuousMultilinearMap 𝕜 E F) :=
  inferInstance

section RestrictScalars

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
  [∀ i, Module 𝕜' (E i)] [∀ i, IsScalarTower 𝕜' 𝕜 (E i)] [Module 𝕜' F] [IsScalarTower 𝕜' 𝕜 F]

/-
**ContinuousMultilinearMap.isEmbedding_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间
 `ContinuousMultilinearMap`。
形式化陈述：isEmbedding_restrictScalars : IsEmbedding (restrictScalars 𝕜' : Continuous
MultilinearMap 𝕜 E F -> ContinuousMultilinearMap 𝕜' E F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.isEmbedding`：∀ {α : Type u} {β : Type v} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Topo
logy.IsEmbedding f
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `ContinuousMultilinearMap.isUniformEmbedding_restrictScalars`：isUniformEm
bedding_restrictScalars : IsUniformEmbedding (restrictScalars 𝕜' : ContinuousMul
tilinearMap 𝕜 E F -> ContinuousMultilinearMap 𝕜' …
-/
theorem isEmbedding_restrictScalars :
    IsEmbedding
      (restrictScalars 𝕜' : ContinuousMultilinearMap 𝕜 E F → ContinuousMultilinearMap 𝕜' E F) :=
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  (isUniformEmbedding_restrictScalars _).isEmbedding

@[continuity, fun_prop]
/-
**ContinuousMultilinearMap.continuous_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousMultilinearMap`。
形式化陈述：continuous_restrictScalars : Continuous (restrictScalars 𝕜' : ContinuousMu
ltilinearMap 𝕜 E F -> ContinuousMultilinearMap 𝕜' E F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用定理 `ContinuousMultilinearMap.isEmbedding_restrictScalars`：isEmbedding_restri
ctScalars : IsEmbedding (restrictScalars 𝕜' : ContinuousMultilinearMap 𝕜 E F -> 
ContinuousMultilinearMap 𝕜' E F)
-/
theorem continuous_restrictScalars :
    Continuous
      (restrictScalars 𝕜' : ContinuousMultilinearMap 𝕜 E F → ContinuousMultilinearMap 𝕜' E F) :=
  isEmbedding_restrictScalars.continuous

variable (𝕜') in
/-- `ContinuousMultilinearMap.restrictScalars` as a `ContinuousLinearMap`. -/
@[simps -fullyApplied apply]
/-
**ContinuousMultilinearMap.restrictScalarsLinear** 是 Mathlib 中的一个定义，位于命名空间 `Cont
inuousMultilinearMap`。
形式化陈述：restrictScalarsLinear [ContinuousConstSMul 𝕜' F] : ContinuousMultilinearMa
p 𝕜 E F ->L[𝕜'] ContinuousMultilinearMap 𝕜' E F where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousMultilinearMap.restrictScalars` as a `ContinuousLinearMap`.
-/
def restrictScalarsLinear [ContinuousConstSMul 𝕜' F] :
    ContinuousMultilinearMap 𝕜 E F →L[𝕜'] ContinuousMultilinearMap 𝕜' E F where
  toFun := restrictScalars 𝕜'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end RestrictScalars

variable (𝕜 E F)

/-- The application of a multilinear map as a `ContinuousLinearMap`. -/
/-
**ContinuousMultilinearMap.apply** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMultilinea
rMap`。
形式化陈述：apply [ContinuousConstSMul 𝕜 F] (m : Π i, E i) : ContinuousMultilinearMap 
𝕜 E F ->L[𝕜] F where toFun c
参数：m : Π i, E i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The application of a multilinear map as a `ContinuousLinearMap`.
-/
def apply [ContinuousConstSMul 𝕜 F] (m : Π i, E i) : ContinuousMultilinearMap 𝕜 E F →L[𝕜] F where
  toFun c := c m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {𝕜 E F}

@[simp]
/-
**ContinuousMultilinearMap.apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMult
ilinearMap`。
形式化陈述：apply_apply [ContinuousConstSMul 𝕜 F] {m : Π i, E i} {c : ContinuousMultil
inearMap 𝕜 E F} : apply 𝕜 E F m c = c m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
lemma apply_apply [ContinuousConstSMul 𝕜 F] {m : Π i, E i} {c : ContinuousMultilinearMap 𝕜 E F} :
    apply 𝕜 E F m c = c m := rfl
/-
**ContinuousMultilinearMap.hasSum_eval** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMult
ilinearMap`。
形式化陈述：hasSum_eval {α : Type*} {p : α -> ContinuousMultilinearMap 𝕜 E F} {q : Con
tinuousMultilinearMap 𝕜 E F} (h : HasSum p q) (m : Π i, E i) : HasSum (fun a => 
p a m) (q m)
参数：h : HasSum p q；m : Π i, E i。
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
· 使用定理 `ContinuousMultilinearMap.instContinuousEvalConstForall`：∀ {𝕜 : Type u_1}
 {ι : Type u_2} {E : ι → Type u_3} {F : Type u_4} [inst : NormedField 𝕜]   [inst
_1 : (i : ι) → TopologicalSpace (E i)] [inst…
-/
theorem hasSum_eval {α : Type*} {p : α → ContinuousMultilinearMap 𝕜 E F}
    {q : ContinuousMultilinearMap 𝕜 E F} (h : HasSum p q) (m : Π i, E i) :
    HasSum (fun a => p a m) (q m) :=
  h.map (applyAddHom m) (continuous_eval_const m)
/-
**ContinuousMultilinearMap.tsum_eval** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMultil
inearMap`。
形式化陈述：tsum_eval [T2Space F] {α : Type*} {p : α -> ContinuousMultilinearMap 𝕜 E F
} (hp : Summable p) (m : Π i, E i) : (∑' a, p a) m = ∑' a, p a m
参数：hp : Summable p；m : Π i, E i。
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
· 使用定理 `ContinuousMultilinearMap.hasSum_eval`：hasSum_eval {α : Type*} {p : α -> 
ContinuousMultilinearMap 𝕜 E F} {q : ContinuousMultilinearMap 𝕜 E F} (h : HasSum
 p q) (m : Π i, E i) : Has…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
theorem tsum_eval [T2Space F] {α : Type*} {p : α → ContinuousMultilinearMap 𝕜 E F} (hp : Summable p)
    (m : Π i, E i) : (∑' a, p a) m = ∑' a, p a m :=
  (hasSum_eval hp.hasSum m).tsum_eq.symm

end ContinuousMultilinearMap

namespace ContinuousLinearMap

variable {𝕜 ι : Type*} {E : ι → Type*} {F G : Type*} [NormedField 𝕜] [∀ i, TopologicalSpace (E i)]
  [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul 𝕜 F]
  [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousConstSMul 𝕜 G]

variable (𝕜 E F G) in
/-- `ContinuousLinearMap.compContinuousMultilinearMap` as a bundled continuous bilinear map.

Given a continuous linear map `f : F →L[𝕜] G`
and a continuous multilinear map `g` from `Π i, E i` to `F`,
this function returns `f ∘ g` as a continuous multilinear map.

With this order of arguments, the function is continuous in `g` (for each fixed `f`)
and is continuous in `f` (as a function to the space of continuous linear maps).
Note that for general topological vector spaces, it is not guaranteed to be continuous in `(g, f)`.
-/
/-
**ContinuousLinearMap.compContinuousMultilinearMapL** 是 Mathlib 中的一个定义，位于命名空间 `C
ontinuousLinearMap`。
形式化陈述：compContinuousMultilinearMapL : (F ->L[𝕜] G) ->L[𝕜] ContinuousMultilinearM
ap 𝕜 E F ->L[𝕜] ContinuousMultilinearMap 𝕜 E G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousLinearMap.compContinuousMultilinearMap` as a bundled continuous bilin
ear map.

Given a continuous linear map `f : F →L[𝕜] G`
and a continuous multilinear map `g` from `Π i, E i` to `F`,
this function returns `f ∘ g` as a continuous multilinear map.

With this order of arguments, the function is continuous in `g` (for each fixed 
`f`)
and is continuous in `f` (as a function to the space of continuous linear maps).
Note that for general topological vector spaces, it is not guaranteed to be cont
inuous in `(g, f)`.
-/
def compContinuousMultilinearMapL :
    (F →L[𝕜] G) →L[𝕜] ContinuousMultilinearMap 𝕜 E F →L[𝕜] ContinuousMultilinearMap 𝕜 E G :=
  letI aux : (F →L[𝕜] G) →ₗ[𝕜]
      ContinuousMultilinearMap 𝕜 E F →L[𝕜] ContinuousMultilinearMap 𝕜 E G :=
    { toFun g :=
        letI aux₁ : ContinuousMultilinearMap 𝕜 E F →ₗ[𝕜] ContinuousMultilinearMap 𝕜 E G :=
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
            · exact (map_continuous g).tendsto 0 <| by simpa
            · exact fun f hf ↦ hf
        }
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
  { toLinearMap := aux
    cont := by
      apply continuous_of_tendsto_nhds_zero aux
      rw [ContinuousLinearMap.hasBasis_nhds_zero.tendsto_iff <|
        ContinuousLinearMap.hasBasis_nhds_zero_of_basis <|
        ContinuousMultilinearMap.hasBasis_nhds_zero]
      rintro ⟨U, V, W⟩ ⟨hU, hV, hW⟩
      refine ⟨(.image2 (fun f v ↦ f v) U V, W), ⟨?_, hW⟩, ?_⟩
      · exact ContinuousMultilinearMap.isVonNBounded_image2_apply hU hV
      · exact fun g hg f hf m hm ↦ hg _ <| mem_image2_of_mem hf hm }

@[simp]
/-
**ContinuousLinearMap.compContinuousMultilinearMapL_apply** 是 Mathlib 中的一个定理，位于命
名空间 `ContinuousLinearMap`。
形式化陈述：compContinuousMultilinearMapL_apply (g : F ->L[𝕜] G) (f : ContinuousMultil
inearMap 𝕜 E F) : compContinuousMultilinearMapL 𝕜 E F G g f = g.compContinuousMu
ltilinearMap f
参数：g : F ->L[𝕜] G；f : ContinuousMultilinearMap 𝕜 E F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
-/
theorem compContinuousMultilinearMapL_apply (g : F →L[𝕜] G) (f : ContinuousMultilinearMap 𝕜 E F) :
    compContinuousMultilinearMapL 𝕜 E F G g f = g.compContinuousMultilinearMap f :=
  rfl

@[fun_prop]
/-
**ContinuousLinearMap._root_.ContinuousLinearMap.continuous_postcomp_continuousM
ultilinearMap** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearMap.continuous_postcomp_continuousMultilinearMap (g : F →L[𝕜] G) :
    Continuous (g.compContinuousMultilinearMap (M₁ := E)) :=
  map_continuous (compContinuousMultilinearMapL 𝕜 E F G g)

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable {𝕜 ι : Type*} {E E₁ : ι → Type*} {F G : Type*} [NormedField 𝕜]
  [∀ i, TopologicalSpace (E i)] [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
  [∀ i, TopologicalSpace (E₁ i)] [∀ i, AddCommGroup (E₁ i)] [∀ i, Module 𝕜 (E₁ i)]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul 𝕜 F]
  [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousConstSMul 𝕜 G]

variable (F) in
/-- `ContinuousMultilinearMap.compContinuousLinearMap` as a bundled continuous linear equiv.
Given a family of continuous linear equivalences `f : Π i, E i ≃L[𝕜] E₁ i`,
this function returns a continuous linear equivalence
between the space of continuous multilinear maps with domain `Π i, E i` and codomain `F`
and the space of multilinear maps with domain `Π i, E₁ i` and the same codomain,
by composing the multilinear maps with `f`. -/
/-
**ContinuousLinearEquiv.continuousMultilinearMapCongrLeft** 是 Mathlib 中的一个定义，位于命
名空间 `ContinuousLinearEquiv`。
形式化陈述：continuousMultilinearMapCongrLeft (f : forall i, E i ≃L[𝕜] E₁ i) : Continu
ousMultilinearMap 𝕜 E₁ F ≃L[𝕜] ContinuousMultilinearMap 𝕜 E F where __
参数：f : forall i, E i ≃L[𝕜] E₁ i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousMultilinearMap.compContinuousLinearMap` as a bundled continuous linea
r equiv.
Given a family of continuous linear equivalences `f : Π i, E i ≃L[𝕜] E₁ i`,
this function returns a continuous linear equivalence
between the space of continuous multilinear maps with domain `Π i, E i` and codo
main `F`
and the space of multilinear maps with domain `Π i, E₁ i` and the same codomain,
by composing the multilinear maps with `f`.
-/
def continuousMultilinearMapCongrLeft (f : ∀ i, E i ≃L[𝕜] E₁ i) :
    ContinuousMultilinearMap 𝕜 E₁ F ≃L[𝕜] ContinuousMultilinearMap 𝕜 E F where
  __ := ContinuousMultilinearMap.compContinuousLinearMapL fun i ↦ ↑(f i)
  invFun := ContinuousMultilinearMap.compContinuousLinearMapL fun i ↦ ↑(f i).symm
  left_inv g := by ext; simp
  right_inv g := by ext; simp

@[simp]
/-
**ContinuousLinearEquiv.continuousMultilinearMapCongrLeft_symm** 是 Mathlib 中的一个定
理，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：continuousMultilinearMapCongrLeft_symm (f : forall i, E i ≃L[𝕜] E₁ i) : (C
ontinuousLinearEquiv.continuousMultilinearMapCongrLeft F f).symm = .continuousMu
ltilinearMapCongrLeft F fun i : ι => (f i).symm
参数：f : forall i, E i ≃L[𝕜] E₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem continuousMultilinearMapCongrLeft_symm
    (f : ∀ i, E i ≃L[𝕜] E₁ i) :
    (ContinuousLinearEquiv.continuousMultilinearMapCongrLeft F f).symm =
      .continuousMultilinearMapCongrLeft F fun i : ι ↦ (f i).symm :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.continuousMultilinearMapCongrLeft_apply** 是 Mathlib 中的一个
定理，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：continuousMultilinearMapCongrLeft_apply (g : ContinuousMultilinearMap 𝕜 E₁
 F) (f : forall i, E i ≃L[𝕜] E₁ i) : ContinuousLinearEquiv.continuousMultilinear
MapCongrLeft F f g = g.compContinuousLinearMap fun i => (f i : E i ->L[𝕜] E₁ i)
参数：g : ContinuousMultilinearMap 𝕜 E₁ F；f : forall i, E i ≃L[𝕜] E₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem continuousMultilinearMapCongrLeft_apply
    (g : ContinuousMultilinearMap 𝕜 E₁ F) (f : ∀ i, E i ≃L[𝕜] E₁ i) :
    ContinuousLinearEquiv.continuousMultilinearMapCongrLeft F f g =
      g.compContinuousLinearMap fun i ↦ (f i : E i →L[𝕜] E₁ i) :=
  rfl

variable (E) in
/-- `ContinuousLinearMap.compContinuousMultilinearMap` as a bundled continuous linear equiv.
Given a continuous linear equivalence `g : F ≃L[𝕜] G`,
this function builds a continuous linear equivalence
between the space of continuous multilinear maps with codomain `F`
and the space of continuous multilinear maps with codomain `G`,
by composing these maps with `g` or `g.symm`. -/
/-
**ContinuousLinearEquiv.continuousMultilinearMapCongrRight** 是 Mathlib 中的一个定义，位于
命名空间 `ContinuousLinearEquiv`。
形式化陈述：continuousMultilinearMapCongrRight (g : F ≃L[𝕜] G) : ContinuousMultilinear
Map 𝕜 E F ≃L[𝕜] ContinuousMultilinearMap 𝕜 E G where __
参数：g : F ≃L[𝕜] G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousLinearMap.compContinuousMultilinearMap` as a bundled continuous linea
r equiv.
Given a continuous linear equivalence `g : F ≃L[𝕜] G`,
this function builds a continuous linear equivalence
between the space of continuous multilinear maps with codomain `F`
and the space of continuous multilinear maps with codomain `G`,
by composing these maps with `g` or `g.symm`.
-/
def continuousMultilinearMapCongrRight (g : F ≃L[𝕜] G) :
    ContinuousMultilinearMap 𝕜 E F ≃L[𝕜] ContinuousMultilinearMap 𝕜 E G where
  __ := ContinuousLinearMap.compContinuousMultilinearMapL _ _ _ _ g
  invFun := ContinuousLinearMap.compContinuousMultilinearMapL _ _ _ _ g.symm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

@[simp]
/-
**ContinuousLinearEquiv.continuousMultilinearMapCongrRight_symm** 是 Mathlib 中的一个
定理，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：continuousMultilinearMapCongrRight_symm (g : F ≃L[𝕜] G) : (g.continuousMul
tilinearMapCongrRight E).symm = g.symm.continuousMultilinearMapCongrRight E
参数：g : F ≃L[𝕜] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem continuousMultilinearMapCongrRight_symm (g : F ≃L[𝕜] G) :
    (g.continuousMultilinearMapCongrRight E).symm = g.symm.continuousMultilinearMapCongrRight E :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.continuousMultilinearMapCongrRight_apply** 是 Mathlib 中的一
个定理，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：continuousMultilinearMapCongrRight_apply (g : F ≃L[𝕜] G) (f : ContinuousMu
ltilinearMap 𝕜 E F) : g.continuousMultilinearMapCongrRight E f = (g : F ->L[𝕜] G
).compContinuousMultilinearMap f
参数：g : F ≃L[𝕜] G；f : ContinuousMultilinearMap 𝕜 E F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem continuousMultilinearMapCongrRight_apply (g : F ≃L[𝕜] G)
    (f : ContinuousMultilinearMap 𝕜 E F) :
    g.continuousMultilinearMapCongrRight E f = (g : F →L[𝕜] G).compContinuousMultilinearMap f :=
  rfl

end ContinuousLinearEquiv

