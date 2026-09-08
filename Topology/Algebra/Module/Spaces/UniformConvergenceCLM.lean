/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Yury Kudryashov
-/
module

public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import Mathlib.Topology.Hom.ContinuousEvalConst
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.SeparationQuotient.Section
import Mathlib.Topology.Algebra.Module.UniformConvergence

/-!
# Topologies of uniform convergence on the space of continuous linear maps

In this file, we define the "topology of `𝔖`-convergence" on `E →L[𝕜] F`, where
`𝔖 : Set (Set E)`. It is the topology of uniform convergence on the elements of `𝔖`.
Similarly to `UniformOnFun`, we define a type synonym `UniformConvergenceCLM` for
`E →L[𝕜] F` endowed with this topology.

The lemma `UniformOnFun.continuousSMul_of_image_bounded` tells us that this is a
vector space topology if the continuous linear image of any element of `𝔖` is bounded (in the sense
of `Bornology.IsVonNBounded`).

The most important examples for such topologies are:
- the topology of bounded convergence (also called the "strong topology" on the dual space),
  when `𝔖` is the set of `IsVonNBounded` subsets.
  This coincides with the operator norm topology in the case of `NormedSpace`s,
  and is declared as an instance on `E →L[𝕜] F`
- the topology of pointwise convergence (also called "weak-\* topology"
  or "strong-operator topology" depending on the context), when `𝔖` is the set of finite
  sets or the set of singletons. This is declared as an instance on `PointwiseConvergenceCLM`.
- the topology of compact convergence, when `𝔖` is the set of compact
  sets. This is declared as an instance on `CompactConvergenceCLM`.

## Main definitions

* `UniformConvergenceCLM` is a type synonym for `E →SL[σ] F` equipped with the `𝔖`-topology.
  We denote it by `E →SLᵤ[σ, 𝔖] F`.
* `UniformConvergenceCLM.instTopologicalSpace` is the topology mentioned above for an arbitrary `𝔖`.

## Main statements

* `UniformConvergenceCLM.instIsTopologicalAddGroup` and
  `UniformConvergenceCLM.instContinuousSMul` show that the strong topology
  makes `E →L[𝕜] F` a topological vector space, with the assumptions on `𝔖` mentioned above.

## Notation

* `E →SLᵤ[σ, 𝔖] F` is space of continuous linear maps equipped with the topology
  of `𝔖`-convergence.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

uniform convergence, bounded convergence
-/

@[expose] public section

open Bornology Filter Function Set Topology
open scoped UniformConvergence Uniformity

/-! ### 𝔖-Topologies -/

variable {𝕜₁ 𝕜₂ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂)
  {E F G : Type*}
  [AddCommGroup E] [Module 𝕜₁ E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜₂ F]
variable (F)

/-- Given `E` and `F` two topological vector spaces and `𝔖 : Set (Set E)`, then
`UniformConvergenceCLM σ F 𝔖` (denoted `E →SLᵤ[σ, 𝔖] F`) is a type synonym of `E →SL[σ] F` equipped
with the "topology of uniform convergence on the elements of `𝔖`".

If the continuous linear image of any element of `𝔖` is bounded, this makes `E →SL[σ] F` a
topological vector space. -/
@[nolint unusedArguments]
/-
**UniformConvergenceCLM** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UniformConvergenceCLM [TopologicalSpace F] (_ : Set (Set E))
参数：_ : Set (Set E)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `E` and `F` two topological vector spaces and `𝔖 : Set (Set E)`, then
`UniformConvergenceCLM σ F 𝔖` (denoted `E →SLᵤ[σ, 𝔖] F`) is a type synonym of `E
 →SL[σ] F` equipped
with the "topology of uniform convergence on the elements of `𝔖`".

If the continuous linear image of any element of `𝔖` is bounded, this makes `E →
SL[σ] F` a
topological vector space.
-/
def UniformConvergenceCLM [TopologicalSpace F] (_ : Set (Set E)) := E →SL[σ] F

-- There seems to be a Lean bug here: the following causes troubles later
-- `notation:25 E " →SLᵤ[" σ ", " 𝔖 "] " F => UniformConvergenceCLM σ (E := E) F 𝔖`
-- (probably because of `(E := E)` ?)

@[inherit_doc UniformConvergenceCLM]
scoped[UniformConvergenceCLM]
notation3:25 E' " →SLᵤ[" σ ", " 𝔖 "] " F => UniformConvergenceCLM σ (E := E') F 𝔖

@[inherit_doc UniformConvergenceCLM]
scoped[UniformConvergenceCLM]
notation3:25 E' " →Lᵤ[" R ", " 𝔖 "] " F => UniformConvergenceCLM (RingHom.id R) (E := E') F 𝔖

namespace UniformConvergenceCLM

/-- Reinterpret `f : E →SL[σ] F` as an element of `E →SLᵤ[σ, 𝔖] F`. -/
@[instance_reducible]
/-
**UniformConvergenceCLM.ofFun** 是 Mathlib 中的一个定义，位于命名空间 `UniformConvergenceCLM`。
形式化陈述：ofFun [TopologicalSpace F] (𝔖 : Set (Set E)) : (E ->SL[σ] F) ≃ (E ->SLᵤ[σ,
 𝔖] F)
参数：𝔖 : Set (Set E)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret `f : E →SL[σ] F` as an element of `E →SLᵤ[σ, 𝔖] F`.
-/
def ofFun [TopologicalSpace F] (𝔖 : Set (Set E)) : (E →SL[σ] F) ≃ (E →SLᵤ[σ, 𝔖] F) :=
  ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩
/-
**UniformConvergenceCLM.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `UniformConvergenc
eCLM`。
形式化陈述：instFunLike [TopologicalSpace F] (𝔖 : Set (Set E)) : FunLike (E ->SLᵤ[σ, 𝔖
] F) E F
参数：𝔖 : Set (Set E)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike [TopologicalSpace F] (𝔖 : Set (Set E)) :
    FunLike (E →SLᵤ[σ, 𝔖] F) E F :=
  inferInstanceAs <| FunLike (E →SL[σ] F) E F

@[ext]
/-
**UniformConvergenceCLM.ext** 是 Mathlib 中的一个定理，位于命名空间 `UniformConvergenceCLM`。
形式化陈述：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f g : E ->SLᵤ[σ, 𝔖] F} (h : fo
rall x, f x = g x) : f = g
参数：Set E；h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f g : E →SLᵤ[σ, 𝔖] F}
    (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h
/-
**UniformConvergenceCLM.instContinuousSemilinearMapClass** 是 Mathlib 中的一个实例，位于命名
空间 `UniformConvergenceCLM`。
形式化陈述：instContinuousSemilinearMapClass [TopologicalSpace F] (𝔖 : Set (Set E)) : 
ContinuousSemilinearMapClass (E ->SLᵤ[σ, 𝔖] F) σ E F
参数：𝔖 : Set (Set E)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instContinuousSemilinearMapClass [TopologicalSpace F] (𝔖 : Set (Set E)) :
    ContinuousSemilinearMapClass (E →SLᵤ[σ, 𝔖] F) σ E F :=
  inferInstanceAs <| ContinuousSemilinearMapClass (E →SL[σ] F) σ E F
/-
**UniformConvergenceCLM.instTopologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 `UniformC
onvergenceCLM`。
形式化陈述：instTopologicalSpace [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : S
et (Set E)) : TopologicalSpace (E ->SLᵤ[σ, 𝔖] F)
参数：𝔖 : Set (Set E)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instTopologicalSpace [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E)) :
    TopologicalSpace (E →SLᵤ[σ, 𝔖] F) :=
  (@UniformOnFun.topologicalSpace E F (IsTopologicalAddGroup.rightUniformSpace F) 𝔖).induced
    (DFunLike.coe : (E →SLᵤ[σ, 𝔖] F) → (E →ᵤ[𝔖] F))
/-
**UniformConvergenceCLM.topologicalSpace_eq** 是 Mathlib 中的一个定理，位于命名空间 `UniformCo
nvergenceCLM`。
形式化陈述：topologicalSpace_eq [UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E
)) : instTopologicalSpace σ F 𝔖 = TopologicalSpace.induced (UniformOnFun.ofFun 𝔖
 ∘ DFunLike.coe) (UniformOnFun.topologicalSpace E F 𝔖)
参数：𝔖 : Set (Set E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformConvergenceCLM.instTopologicalSpace.eq_1`：∀ {𝕜₁ : Type u_1} {𝕜₂ :
 Type u_2} [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E 
: Type u_3}   (F : Type u_4) [inst_2 …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `IsUniformAddGroup.rightUniformSpace_eq`：∀ {G : Type u_2} [u : UniformSpa
ce G] [inst : AddGroup G] [inst_1 : IsUniformAddGroup G],   IsTopologicalAddGrou
p.rightUniformSpace G = u
-/
theorem topologicalSpace_eq [UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) :
    instTopologicalSpace σ F 𝔖 = TopologicalSpace.induced (UniformOnFun.ofFun 𝔖 ∘ DFunLike.coe)
      (UniformOnFun.topologicalSpace E F 𝔖) := by
  rw [instTopologicalSpace]
  congr
  exact IsUniformAddGroup.rightUniformSpace_eq

/-- The uniform structure associated with `ContinuousLinearMap.strongTopology`. We make sure
that this has nice definitional properties. -/
/-
**UniformConvergenceCLM.instUniformSpace** 是 Mathlib 中的一个实例，位于命名空间 `UniformConve
rgenceCLM`。
形式化陈述：instUniformSpace [UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) 
: UniformSpace (E ->SLᵤ[σ, 𝔖] F)
参数：𝔖 : Set (Set E)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The uniform structure associated with `ContinuousLinearMap.strongTopology`. We m
ake sure
that this has nice definitional properties.
-/
instance instUniformSpace [UniformSpace F] [IsUniformAddGroup F]
    (𝔖 : Set (Set E)) : UniformSpace (E →SLᵤ[σ, 𝔖] F) :=
  UniformSpace.replaceTopology
    ((UniformOnFun.uniformSpace E F 𝔖).comap (UniformOnFun.ofFun 𝔖 ∘ DFunLike.coe))
    (by
      rw [UniformConvergenceCLM.instTopologicalSpace, IsUniformAddGroup.rightUniformSpace_eq]; rfl)
/-
**UniformConvergenceCLM.uniformSpace_eq** 是 Mathlib 中的一个定理，位于命名空间 `UniformConver
genceCLM`。
形式化陈述：uniformSpace_eq [UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) :
 instUniformSpace σ F 𝔖 = UniformSpace.comap (UniformOnFun.ofFun 𝔖 ∘ DFunLike.co
e) (UniformOnFun.uniformSpace E F 𝔖)
参数：𝔖 : Set (Set E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformConvergenceCLM.instUniformSpace.eq_1`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Typ
e u_2} [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E : Ty
pe u_3}   (F : Type u_4) [inst_2 …
· 使用定理 `UniformSpace.replaceTopology_eq`：UniformSpace.replaceTopology_eq {α : Ty
pe*} [i : TopologicalSpace α] (u : UniformSpace α) (h : i = u.toTopologicalSpace
) : u.replaceTopology…
-/
theorem uniformSpace_eq [UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) :
    instUniformSpace σ F 𝔖 =
      UniformSpace.comap (UniformOnFun.ofFun 𝔖 ∘ DFunLike.coe)
        (UniformOnFun.uniformSpace E F 𝔖) := by
  rw [instUniformSpace, UniformSpace.replaceTopology_eq]

@[simp]
/-
**UniformConvergenceCLM.uniformity_toTopologicalSpace_eq** 是 Mathlib 中的一个定理，位于命名
空间 `UniformConvergenceCLM`。
形式化陈述：uniformity_toTopologicalSpace_eq [UniformSpace F] [IsUniformAddGroup F] (𝔖
 : Set (Set E)) : (UniformConvergenceCLM.instUniformSpace σ F 𝔖).toTopologicalSp
ace = UniformConvergenceCLM.instTopologicalSpace σ F 𝔖
参数：𝔖 : Set (Set E)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniformity_toTopologicalSpace_eq [UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) :
    (UniformConvergenceCLM.instUniformSpace σ F 𝔖).toTopologicalSpace =
      UniformConvergenceCLM.instTopologicalSpace σ F 𝔖 :=
  rfl
/-
**UniformConvergenceCLM.isUniformInducing_coeFn** 是 Mathlib 中的一个定理，位于命名空间 `Unifo
rmConvergenceCLM`。
形式化陈述：isUniformInducing_coeFn [UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (S
et E)) : IsUniformInducing (α
参数：𝔖 : Set (Set E)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isUniformInducing_coeFn [UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) :
    IsUniformInducing (α := E →SLᵤ[σ, 𝔖] F) (UniformOnFun.ofFun 𝔖 ∘ DFunLike.coe) :=
  ⟨rfl⟩
/-
**UniformConvergenceCLM.isUniformEmbedding_coeFn** 是 Mathlib 中的一个定理，位于命名空间 `Unif
ormConvergenceCLM`。
形式化陈述：isUniformEmbedding_coeFn [UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (
Set E)) : IsUniformEmbedding (α
参数：𝔖 : Set (Set E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.isUniformInducing_coeFn`：isUniformInducing_coeFn [
UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) : IsUniformInducing (α
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem isUniformEmbedding_coeFn [UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) :
    IsUniformEmbedding (α := E →SLᵤ[σ, 𝔖] F) (UniformOnFun.ofFun 𝔖 ∘ DFunLike.coe) :=
  ⟨isUniformInducing_coeFn .., DFunLike.coe_injective⟩
/-
**UniformConvergenceCLM.isEmbedding_coeFn** 是 Mathlib 中的一个定理，位于命名空间 `UniformConv
ergenceCLM`。
形式化陈述：isEmbedding_coeFn [UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E))
 : IsEmbedding (X
参数：𝔖 : Set (Set E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.isEmbedding`：∀ {α : Type u} {β : Type v} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Topo
logy.IsEmbedding f
· 使用定理 `UniformConvergenceCLM.isUniformEmbedding_coeFn`：isUniformEmbedding_coeFn
 [UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) : IsUniformEmbedding (
α
-/
theorem isEmbedding_coeFn [UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) :
    IsEmbedding (X := E →SLᵤ[σ, 𝔖] F) (Y := E →ᵤ[𝔖] F)
      (UniformOnFun.ofFun 𝔖 ∘ DFunLike.coe) :=
  IsUniformEmbedding.isEmbedding (isUniformEmbedding_coeFn _ _ _)

-- This instance exists to avoid nsmul and zsmul diamonds.
/-
**UniformConvergenceCLM.** 是 Mathlib 中的一个实例，位于命名空间 `UniformConvergenceCLM`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : Type*) [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
    [TopologicalSpace F] [ContinuousConstSMul M F] (𝔖 : Set (Set E)) :
    SMul M (E →SLᵤ[σ, 𝔖] F) where
  smul c f := (ofFun σ F 𝔖) (c • (ofFun σ F 𝔖).symm f)
/-
**UniformConvergenceCLM.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `UniformConve
rgenceCLM`。
形式化陈述：instAddCommGroup [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (
Set E)) : AddCommGroup (E ->SLᵤ[σ, 𝔖] F)
参数：𝔖 : Set (Set E)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroup [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E)) :
    AddCommGroup (E →SLᵤ[σ, 𝔖] F) :=
  inferInstanceAs <| AddCommGroup (E →SL[σ] F)
/-
**UniformConvergenceCLM.** 是 Mathlib 中的一个实例，位于命名空间 `UniformConvergenceCLM`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E)) :
    IsNegApply (E →SLᵤ[σ, 𝔖] F) E F where
  neg_apply _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias neg_apply := neg_apply
/-
**UniformConvergenceCLM.** 是 Mathlib 中的一个实例，位于命名空间 `UniformConvergenceCLM`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E)) :
    IsAddApply (E →SLᵤ[σ, 𝔖] F) E F where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias add_apply := add_apply

@[deprecated (since := "2026-06-10")] protected alias sum_apply := sum_apply
/-
**UniformConvergenceCLM.** 是 Mathlib 中的一个实例，位于命名空间 `UniformConvergenceCLM`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E)) :
    IsSubApply (E →SLᵤ[σ, 𝔖] F) E F where
  sub_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias sub_apply := sub_apply
/-
**UniformConvergenceCLM.** 是 Mathlib 中的一个实例，位于命名空间 `UniformConvergenceCLM`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E)) :
    IsZeroApply (E →SLᵤ[σ, 𝔖] F) E F where
  zero_apply _ := rfl

@[deprecated (since := "2026-06-10")] protected alias coe_zero := FunLike.coe_zero
/-
**UniformConvergenceCLM.instIsUniformAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `Uniform
ConvergenceCLM`。
形式化陈述：instIsUniformAddGroup [UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set
 E)) : IsUniformAddGroup (E ->SLᵤ[σ, 𝔖] F)
参数：𝔖 : Set (Set E)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
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
· 使用定理 `UniformConvergenceCLM.isUniformEmbedding_coeFn`：isUniformEmbedding_coeFn
 [UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) : IsUniformEmbedding (
α
-/
instance instIsUniformAddGroup [UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) :
    IsUniformAddGroup (E →SLᵤ[σ, 𝔖] F) := by
  let φ : (E →SLᵤ[σ, 𝔖] F) →+ E →ᵤ[𝔖] F :=
    ⟨⟨(DFunLike.coe : (E →SLᵤ[σ, 𝔖] F) → E →ᵤ[𝔖] F), rfl⟩, fun _ _ => rfl⟩
  exact (isUniformEmbedding_coeFn _ _ _).isUniformAddGroup φ
/-
**UniformConvergenceCLM.instIsTopologicalAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `Uni
formConvergenceCLM`。
形式化陈述：instIsTopologicalAddGroup [TopologicalSpace F] [IsTopologicalAddGroup F] (
𝔖 : Set (Set E)) : IsTopologicalAddGroup (E ->SLᵤ[σ, 𝔖] F)
参数：𝔖 : Set (Set E)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
-/
instance instIsTopologicalAddGroup [TopologicalSpace F] [IsTopologicalAddGroup F]
    (𝔖 : Set (Set E)) : IsTopologicalAddGroup (E →SLᵤ[σ, 𝔖] F) := by
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  have : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  infer_instance
/-
**UniformConvergenceCLM.continuousEvalConst** 是 Mathlib 中的一个定理，位于命名空间 `UniformCo
nvergenceCLM`。
形式化陈述：continuousEvalConst [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Se
t (Set E)) (h𝔖 : ⋃₀ 𝔖 = Set.univ) : ContinuousEvalConst (E ->SLᵤ[σ, 𝔖] F) E F wh
ere continuous_eval_const x
参数：𝔖 : Set (Set E)；h𝔖 : ⋃₀ 𝔖 = Set.univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `UniformOnFun.uniformContinuous_eval`：uniformContinuous_eval (h : ⋃₀ 𝔖 = 
univ) (x : α) : UniformContinuous ((Function.eval x : (α -> β) -> β) ∘ toFun 𝔖)
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `UniformConvergenceCLM.isEmbedding_coeFn`：isEmbedding_coeFn [UniformSpace
 F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) : IsEmbedding (X
-/
theorem continuousEvalConst [TopologicalSpace F] [IsTopologicalAddGroup F]
    (𝔖 : Set (Set E)) (h𝔖 : ⋃₀ 𝔖 = Set.univ) :
    ContinuousEvalConst (E →SLᵤ[σ, 𝔖] F) E F where
  continuous_eval_const x := by
    let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
    have : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
    exact (UniformOnFun.uniformContinuous_eval h𝔖 x).continuous.comp
      (isEmbedding_coeFn σ F 𝔖).continuous
/-
**UniformConvergenceCLM.t2Space** 是 Mathlib 中的一个定理，位于命名空间 `UniformConvergenceCLM
`。
形式化陈述：t2Space [TopologicalSpace F] [IsTopologicalAddGroup F] [T2Space F] (𝔖 : Se
t (Set E)) (h𝔖 : ⋃₀ 𝔖 = univ) : T2Space (E ->SLᵤ[σ, 𝔖] F)
参数：𝔖 : Set (Set E)；h𝔖 : ⋃₀ 𝔖 = univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `UniformOnFun.t2Space_of_covering`：t2Space_of_covering [T2Space β] (h : ⋃
₀ 𝔖 = univ) : T2Space (α ->ᵤ[𝔖] β) where t2 f g hfg
· 使用定理 `Topology.IsEmbedding.t2Space`：Topology.IsEmbedding.t2Space [TopologicalS
pace Y] [T2Space Y] {f : X -> Y} (hf : IsEmbedding f) : T2Space X
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `UniformConvergenceCLM.isEmbedding_coeFn`：isEmbedding_coeFn [UniformSpace
 F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) : IsEmbedding (X
-/
theorem t2Space [TopologicalSpace F] [IsTopologicalAddGroup F] [T2Space F]
    (𝔖 : Set (Set E)) (h𝔖 : ⋃₀ 𝔖 = univ) : T2Space (E →SLᵤ[σ, 𝔖] F) := by
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  have : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  have : T2Space (E →ᵤ[𝔖] F) := UniformOnFun.t2Space_of_covering h𝔖
  exact (isEmbedding_coeFn σ F 𝔖).t2Space
/-
**UniformConvergenceCLM.instDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `UniformC
onvergenceCLM`。
形式化陈述：instDistribMulAction (M : Type*) [Monoid M] [DistribMulAction M F] [SMulCo
mmClass 𝕜₂ M F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstS
Mul M F] (𝔖 : Set (Set E)) : DistribMulAction M (E ->SLᵤ[σ, 𝔖] F)
参数：M : Type*；𝔖 : Set (Set E)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribMulAction (M : Type*) [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul M F] (𝔖 : Set (Set E)) :
    DistribMulAction M (E →SLᵤ[σ, 𝔖] F) :=
  inferInstanceAs <| DistribMulAction M (E →SL[σ] F)
/-
**UniformConvergenceCLM.** 是 Mathlib 中的一个实例，位于命名空间 `UniformConvergenceCLM`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
    [TopologicalSpace F] [ContinuousConstSMul M F] (𝔖 : Set (Set E)) :
    IsSMulApply M (E →SLᵤ[σ, 𝔖] F) E F where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias smul_apply := smul_apply
/-
**UniformConvergenceCLM.instModule** 是 Mathlib 中的一个实例，位于命名空间 `UniformConvergence
CLM`。
形式化陈述：instModule (R : Type*) [Semiring R] [Module R F] [SMulCommClass 𝕜₂ R F] [T
opologicalSpace F] [ContinuousConstSMul R F] [IsTopologicalAddGroup F] (𝔖 : Set 
(Set E)) : Module R (E ->SLᵤ[σ, 𝔖] F)
参数：R : Type*；𝔖 : Set (Set E)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule (R : Type*) [Semiring R] [Module R F] [SMulCommClass 𝕜₂ R F]
    [TopologicalSpace F] [ContinuousConstSMul R F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E)) :
    Module R (E →SLᵤ[σ, 𝔖] F) :=
  inferInstanceAs <| Module R (E →SL[σ] F)

section Tower

variable {S T : Type*} [TopologicalSpace F] [IsTopologicalAddGroup F]
variable [Monoid S] [DistribMulAction S F] [SMulCommClass 𝕜₂ S F] [ContinuousConstSMul S F]
variable [Monoid T] [DistribMulAction T F] [SMulCommClass 𝕜₂ T F] [ContinuousConstSMul T F]

/-
**UniformConvergenceCLM.isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `UniformConverge
nceCLM`。
形式化陈述：isScalarTower [SMul S T] [IsScalarTower S T F] (𝔖 : Set (Set E)) : IsScala
rTower S T (E ->SLᵤ[σ, 𝔖] F)
参数：𝔖 : Set (Set E)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FunLike.isScalarTower`：∀ {M : Type u_1} {M' : Type u_2} {F : Type u_3} {
α : Type u_4} {β : Type u_5} [i : FunLike F α β] [inst : SMul M β]   [inst_1 : S
Mul M' β] […
· 使用定理 `UniformConvergenceCLM.instIsSMulApply`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2}
 [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E : Type u_3
}   (F : Type u_4) [inst_2 …
-/
instance isScalarTower [SMul S T] [IsScalarTower S T F] (𝔖 : Set (Set E)) :
    IsScalarTower S T (E →SLᵤ[σ, 𝔖] F) := FunLike.isScalarTower
/-
**UniformConvergenceCLM.smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `UniformConverge
nceCLM`。
形式化陈述：smulCommClass [SMulCommClass S T F] (𝔖 : Set (Set E)) : SMulCommClass S T 
(E ->SLᵤ[σ, 𝔖] F)
参数：𝔖 : Set (Set E)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FunLike.smulCommClass`：∀ {M : Type u_1} {M' : Type u_2} {F : Type u_3} {
α : Type u_4} {β : Type u_5} [i : FunLike F α β] [inst : SMul M β]   [inst_1 : S
Mul M' β] […
· 使用定理 `UniformConvergenceCLM.instIsSMulApply`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2}
 [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E : Type u_3
}   (F : Type u_4) [inst_2 …
-/
instance smulCommClass [SMulCommClass S T F] (𝔖 : Set (Set E)) :
    SMulCommClass S T (E →SLᵤ[σ, 𝔖] F) :=
  FunLike.smulCommClass

end Tower

/-
**UniformConvergenceCLM.continuousSMul** 是 Mathlib 中的一个定理，位于命名空间 `UniformConverg
enceCLM`。
形式化陈述：continuousSMul [RingHomSurjective σ] [RingHomIsometric σ] [TopologicalSpac
e F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜₂ F] (𝔖 : Set (Set E)) (h𝔖₃ : fo
rall S in 𝔖, IsVonNBounded 𝕜₁ S) : ContinuousSMul 𝕜₂ (E ->SLᵤ[σ, 𝔖] F)
参数：𝔖 : Set (Set E)；h𝔖₃ : forall S in 𝔖, IsVonNBounded 𝕜₁ S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用引理 `UniformOnFun.continuousSMul_induced_of_image_bounded`：UniformOnFun.conti
nuousSMul_induced_of_image_bounded (φ : hom) (hφ : IsInducing (ofFun 𝔖 ∘ φ)) (h 
: forall u : H, forall s in 𝔖, Bornology.I…
· 使用定理 `Bornology.IsVonNBounded.image`：∀ {E : Type u_3} {F : Type u_4} {𝕜₁ : Typ
e u_6} {𝕜₂ : Type u_7} [inst : NormedDivisionRing 𝕜₁]   [inst_1 : NormedDivision
Ring 𝕜₂] [inst_2 : …
-/
theorem continuousSMul [RingHomSurjective σ] [RingHomIsometric σ]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜₂ F] (𝔖 : Set (Set E))
    (h𝔖₃ : ∀ S ∈ 𝔖, IsVonNBounded 𝕜₁ S) :
    ContinuousSMul 𝕜₂ (E →SLᵤ[σ, 𝔖] F) := by
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  have : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  let φ : (E →SLᵤ[σ, 𝔖] F) →ₗ[𝕜₂] E → F :=
    ⟨⟨DFunLike.coe, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  exact UniformOnFun.continuousSMul_induced_of_image_bounded 𝕜₂ E F (E →SLᵤ[σ, 𝔖] F) φ
    ⟨rfl⟩ fun u s hs => (h𝔖₃ s hs).image u
/-
**UniformConvergenceCLM.hasBasis_nhds_zero_of_basis** 是 Mathlib 中的一个定理，位于命名空间 `U
niformConvergenceCLM`。
形式化陈述：hasBasis_nhds_zero_of_basis [TopologicalSpace F] [IsTopologicalAddGroup F]
 {ι : Type*} (𝔖 : Set (Set E)) (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedOn (· subseteq 
·) 𝔖) {p : ι -> Prop} {b : ι -> Set F} (h : (𝓝 0 : Filter F).HasBasis p b) : (𝓝 
(0 : E ->SLᵤ[σ, 𝔖] F)).HasBasis (fun Si : Set E × ι => Si.1 in 𝔖 ∧ p Si.2) fun S
i => { f : E ->SLᵤ[σ, 𝔖] F | forall x in Si.1, f x in b Si.2 }
参数：𝔖 : Set (Set E)；h𝔖₁ : 𝔖.Nonempty；h𝔖₂ : DirectedOn (· subseteq ·) 𝔖；h : (𝓝 0 :
 Filter F).HasBasis p b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用定理 `UniformConvergenceCLM.isEmbedding_coeFn`：isEmbedding_coeFn [UniformSpace
 F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) : IsEmbedding (X
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `UniformOnFun.hasBasis_nhds_zero_of_basis`：∀ {α : Type u_1} {G : Type u_2
} {ι : Type u_3} [inst : AddGroup G] [inst_1 : UniformSpace G] [IsUniformAddGrou
p G]   (𝔖 : Set (Set α)),   𝔖.…
-/
theorem hasBasis_nhds_zero_of_basis [TopologicalSpace F] [IsTopologicalAddGroup F]
    {ι : Type*} (𝔖 : Set (Set E)) (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) {p : ι → Prop}
    {b : ι → Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    (𝓝 (0 : E →SLᵤ[σ, 𝔖] F)).HasBasis
      (fun Si : Set E × ι => Si.1 ∈ 𝔖 ∧ p Si.2)
      fun Si => { f : E →SLᵤ[σ, 𝔖] F | ∀ x ∈ Si.1, f x ∈ b Si.2 } := by
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  have : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  rw [(isEmbedding_coeFn σ F 𝔖).isInducing.nhds_eq_comap]
  exact (UniformOnFun.hasBasis_nhds_zero_of_basis 𝔖 h𝔖₁ h𝔖₂ h).comap DFunLike.coe
/-
**UniformConvergenceCLM.hasBasis_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `UniformCon
vergenceCLM`。
形式化陈述：hasBasis_nhds_zero [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set
 (Set E)) (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedOn (· subseteq ·) 𝔖) : (𝓝 (0 : E ->S
Lᵤ[σ, 𝔖] F)).HasBasis (fun SV : Set E × Set F => SV.1 in 𝔖 ∧ SV.2 in (𝓝 0 : Filt
er F)) fun SV => { f : E ->SLᵤ[σ, 𝔖] F | forall x in SV.1, f x in SV.2 }
参数：𝔖 : Set (Set E)；h𝔖₁ : 𝔖.Nonempty；h𝔖₂ : DirectedOn (· subseteq ·) 𝔖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.hasBasis_nhds_zero_of_basis`：hasBasis_nhds_zero_of
_basis [TopologicalSpace F] [IsTopologicalAddGroup F] {ι : Type*} (𝔖 : Set (Set 
E)) (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedO…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem hasBasis_nhds_zero [TopologicalSpace F] [IsTopologicalAddGroup F]
    (𝔖 : Set (Set E)) (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) :
    (𝓝 (0 : E →SLᵤ[σ, 𝔖] F)).HasBasis
      (fun SV : Set E × Set F => SV.1 ∈ 𝔖 ∧ SV.2 ∈ (𝓝 0 : Filter F)) fun SV =>
      { f : E →SLᵤ[σ, 𝔖] F | ∀ x ∈ SV.1, f x ∈ SV.2 } :=
  hasBasis_nhds_zero_of_basis σ F 𝔖 h𝔖₁ h𝔖₂ (𝓝 0).basis_sets
/-
**UniformConvergenceCLM.nhds_zero_eq_of_basis** 是 Mathlib 中的一个定理，位于命名空间 `Uniform
ConvergenceCLM`。
形式化陈述：nhds_zero_eq_of_basis [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : 
Set (Set E)) {ι : Type*} {p : ι -> Prop} {b : ι -> Set F} (h : (𝓝 0 : Filter F).
HasBasis p b) : 𝓝 (0 : E ->SLᵤ[σ, 𝔖] F) = ⨅ (s : Set E) (_ : s in 𝔖) (i : ι) (_ 
: p i), 𝓟 {f : E ->SLᵤ[σ, 𝔖] F | MapsTo f s (b i)}
参数：𝔖 : Set (Set E)；h : (𝓝 0 : Filter F).HasBasis p b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用定理 `UniformConvergenceCLM.isEmbedding_coeFn`：isEmbedding_coeFn [UniformSpace
 F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) : IsEmbedding (X
· 使用定理 `UniformOnFun.nhds_eq_of_basis`：∀ {α : Type u_1} (β : Type u_2) [inst : U
niformSpace β] (𝔖 : Set (Set α)) {ι : Sort u_5} {p : ι → Prop}   {V : ι → Set (β
 × β)},   (uniformi…
· 使用定理 `Filter.HasBasis.uniformity_of_nhds_zero`：∀ {α : Type u_1} [inst : Unifor
mSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α] {ι : Sort u_3} {p : ι → Pr
op}   {U : ι → Set α}, (nhds …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `FunLike.coe_zero`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst :
 FunLike F α β] [inst_1 : Zero F] [inst_2 : Zero β]   [IsZeroApply F α β], ⇑0 = 
0
· 使用定理 `UniformConvergenceCLM.instIsZeroApply`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2}
 [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E : Type u_3
}   (F : Type u_4) [inst_2 …
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Filter.comap_iInf`：comap_iInf {f : ι -> Filter β} : comap m (⨅ i, f i) =
 ⨅ i, comap m (f i)
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nhds_zero_eq_of_basis [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E))
    {ι : Type*} {p : ι → Prop} {b : ι → Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    𝓝 (0 : E →SLᵤ[σ, 𝔖] F) =
      ⨅ (s : Set E) (_ : s ∈ 𝔖) (i : ι) (_ : p i),
        𝓟 {f : E →SLᵤ[σ, 𝔖] F | MapsTo f s (b i)} := by
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  have : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  rw [(isEmbedding_coeFn σ F 𝔖).isInducing.nhds_eq_comap,
    UniformOnFun.nhds_eq_of_basis _ _ h.uniformity_of_nhds_zero]
  simp [MapsTo]
/-
**UniformConvergenceCLM.nhds_zero_eq** 是 Mathlib 中的一个定理，位于命名空间 `UniformConvergen
ceCLM`。
形式化陈述：nhds_zero_eq [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set 
E)) : 𝓝 (0 : E ->SLᵤ[σ, 𝔖] F) = ⨅ s in 𝔖, ⨅ t in 𝓝 (0 : F), 𝓟 {f : E ->SLᵤ[σ, 𝔖]
 F | MapsTo f s t}
参数：𝔖 : Set (Set E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.nhds_zero_eq_of_basis`：nhds_zero_eq_of_basis [Topo
logicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E)) {ι : Type*} {p : ι -
> Prop} {b : ι -> Set F} (h : (𝓝 …
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem nhds_zero_eq [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E)) :
    𝓝 (0 : E →SLᵤ[σ, 𝔖] F) =
      ⨅ s ∈ 𝔖, ⨅ t ∈ 𝓝 (0 : F),
        𝓟 {f : E →SLᵤ[σ, 𝔖] F | MapsTo f s t} :=
  nhds_zero_eq_of_basis _ _ _ (𝓝 0).basis_sets

variable {F} in
/-
**UniformConvergenceCLM.eventually_nhds_zero_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `U
niformConvergenceCLM`。
形式化陈述：eventually_nhds_zero_mapsTo [TopologicalSpace F] [IsTopologicalAddGroup F]
 {𝔖 : Set (Set E)} {s : Set E} (hs : s in 𝔖) {U : Set F} (hu : U in 𝓝 0) : foral
lᶠ f : E ->SLᵤ[σ, 𝔖] F in 𝓝 0, MapsTo f s U
参数：Set E；hs : s in 𝔖；hu : U in 𝓝 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformConvergenceCLM.nhds_zero_eq`：nhds_zero_eq [TopologicalSpace F] [I
sTopologicalAddGroup F] (𝔖 : Set (Set E)) : 𝓝 (0 : E ->SLᵤ[σ, 𝔖] F) = ⨅ s in 𝔖, 
⨅ t in 𝓝 (0 : F), 𝓟 {f :…
· 使用定理 `Filter.mem_iInf_of_mem`：mem_iInf_of_mem {f : ι -> Filter α} (i : ι) {s} 
(hs : s in f i) : s in ⨅ i, f i
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s
-/
theorem eventually_nhds_zero_mapsTo [TopologicalSpace F] [IsTopologicalAddGroup F]
    {𝔖 : Set (Set E)} {s : Set E} (hs : s ∈ 𝔖) {U : Set F} (hu : U ∈ 𝓝 0) :
    ∀ᶠ f : E →SLᵤ[σ, 𝔖] F in 𝓝 0, MapsTo f s U := by
  rw [nhds_zero_eq]
  apply_rules [mem_iInf_of_mem, mem_principal_self]

variable {σ F} in
/-
**UniformConvergenceCLM.isVonNBounded_image2_apply** 是 Mathlib 中的一个定理，位于命名空间 `Un
iformConvergenceCLM`。
形式化陈述：isVonNBounded_image2_apply {R : Type*} [SeminormedRing R] [TopologicalSpac
e F] [IsTopologicalAddGroup F] [DistribMulAction R F] [ContinuousConstSMul R F] 
[SMulCommClass 𝕜₂ R F] {𝔖 : Set (Set E)} {S : Set (E ->SLᵤ[σ, 𝔖] F)} (hS : IsVon
NBounded R S) {s : Set E} (hs : s in 𝔖) : IsVonNBounded R (Set.image2 (fun f x =
> f x) S s)
参数：Set E；E ->SLᵤ[σ, 𝔖] F；hS : IsVonNBounded R S；hs : s in 𝔖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `UniformConvergenceCLM.eventually_nhds_zero_mapsTo`：eventually_nhds_zero_
mapsTo [TopologicalSpace F] [IsTopologicalAddGroup F] {𝔖 : Set (Set E)} {s : Set
 E} (hs : s in 𝔖) {U : Set F} (hu : U i…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image2_subset_iff`：image2_subset_iff {u : Set γ} : image2 f s t subs
eteq u ↔ forall x in s, forall y in t, f x y in u
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem isVonNBounded_image2_apply {R : Type*} [SeminormedRing R]
    [TopologicalSpace F] [IsTopologicalAddGroup F]
    [DistribMulAction R F] [ContinuousConstSMul R F] [SMulCommClass 𝕜₂ R F]
    {𝔖 : Set (Set E)} {S : Set (E →SLᵤ[σ, 𝔖] F)} (hS : IsVonNBounded R S)
    {s : Set E} (hs : s ∈ 𝔖) : IsVonNBounded R (Set.image2 (fun f x ↦ f x) S s) := by
  intro U hU
  filter_upwards [hS (eventually_nhds_zero_mapsTo σ hs hU)] with c hc
  rw [image2_subset_iff]
  intro f hf x hx
  rcases hc hf with ⟨g, hg, rfl⟩
  exact smul_mem_smul_set (hg hx)

variable {σ F} in
/-- A set `S` of continuous linear maps with topology of uniform convergence on sets `s ∈ 𝔖`
is von Neumann bounded iff for any `s ∈ 𝔖`,
the set `{f x | (f ∈ S) (x ∈ s)}` is von Neumann bounded. -/
/-
**UniformConvergenceCLM.isVonNBounded_iff** 是 Mathlib 中的一个定理，位于命名空间 `UniformConv
ergenceCLM`。
形式化陈述：isVonNBounded_iff {R : Type*} [NormedDivisionRing R] [TopologicalSpace F] 
[IsTopologicalAddGroup F] [Module R F] [ContinuousConstSMul R F] [SMulCommClass 
𝕜₂ R F] {𝔖 : Set (Set E)} {S : Set (E ->SLᵤ[σ, 𝔖] F)} : IsVonNBounded R S ↔ fora
ll s in 𝔖, IsVonNBounded R (Set.image2 (fun f x => f x) S s)
参数：Set E；E ->SLᵤ[σ, 𝔖] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.isVonNBounded_image2_apply`：isVonNBounded_image2_a
pply {R : Type*} [SeminormedRing R] [TopologicalSpace F] [IsTopologicalAddGroup 
F] [DistribMulAction R F] [ContinuousC…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformConvergenceCLM.nhds_zero_eq`：nhds_zero_eq [TopologicalSpace F] [I
sTopologicalAddGroup F] (𝔖 : Set (Set E)) : 𝓝 (0 : E ->SLᵤ[σ, 𝔖] F) = ⨅ s in 𝔖, 
⨅ t in 𝓝 (0 : F), 𝓟 {f :…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Filter.mem_absorbing`：Filter.mem_absorbing : s in absorbing G₀ u ↔ Absor
bs G₀ s u
· 使用定理 `Absorbs.eq_1`：∀ (M : Type u_1) {α : Type u_2} [inst : Bornology M] [inst
_1 : SMul M α] (s t : Set α),   Absorbs M s t = ∀ᶠ (a : M) in Bornology.cobounde
d …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `Bornology.eventually_ne_cobounded`：eventually_ne_cobounded (a : α) : for
allᶠ x in cobounded α, x != a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `Set.mem_smul_set_iff_inv_smul_mem₀`：mem_smul_set_iff_inv_smul_mem₀ (ha :
 a != 0) (A : Set β) (x : β) : x in a • A ↔ a⁻¹ • x in A
· 使用定理 `Set.mem_image2_of_mem`：mem_image2_of_mem (ha : a in s) (hb : b in t) : f
 a b in image2 f s t

--- 原说明 ---
A set `S` of continuous linear maps with topology of uniform convergence on sets
 `s ∈ 𝔖`
is von Neumann bounded iff for any `s ∈ 𝔖`,
the set `{f x | (f ∈ S) (x ∈ s)}` is von Neumann bounded.
-/
theorem isVonNBounded_iff {R : Type*} [NormedDivisionRing R]
    [TopologicalSpace F] [IsTopologicalAddGroup F]
    [Module R F] [ContinuousConstSMul R F] [SMulCommClass 𝕜₂ R F]
    {𝔖 : Set (Set E)} {S : Set (E →SLᵤ[σ, 𝔖] F)} :
    IsVonNBounded R S ↔ ∀ s ∈ 𝔖, IsVonNBounded R (Set.image2 (fun f x ↦ f x) S s) := by
  refine ⟨fun hS s hs ↦ isVonNBounded_image2_apply hS hs, fun h ↦ ?_⟩
  simp_rw [isVonNBounded_iff_absorbing_le, nhds_zero_eq, le_iInf_iff, le_principal_iff]
  intro s hs U hU
  rw [Filter.mem_absorbing, Absorbs]
  filter_upwards [h s hs hU, eventually_ne_cobounded 0] with c hc hc₀ f hf
  rw [mem_smul_set_iff_inv_smul_mem₀ hc₀]
  intro x hx
  simpa only [mem_smul_set_iff_inv_smul_mem₀ hc₀] using! hc (mem_image2_of_mem hf hx)
/-
**UniformConvergenceCLM.instUniformContinuousConstSMul** 是 Mathlib 中的一个实例，位于命名空间
 `UniformConvergenceCLM`。
形式化陈述：instUniformContinuousConstSMul (M : Type*) [Monoid M] [DistribMulAction M 
F] [SMulCommClass 𝕜₂ M F] [UniformSpace F] [IsUniformAddGroup F] [UniformContinu
ousConstSMul M F] (𝔖 : Set (Set E)) : UniformContinuousConstSMul M (E ->SLᵤ[σ, 𝔖
] F)
参数：M : Type*；𝔖 : Set (Set E)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUniformInducing.uniformContinuousConstSMul`：IsUniformInducing.uniformC
ontinuousConstSMul [SMul M Y] [UniformContinuousConstSMul M Y] {f : X -> Y} (hf 
: IsUniformInducing f) (hsmul : fo…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `UniformConvergenceCLM.isUniformInducing_coeFn`：isUniformInducing_coeFn [
UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) : IsUniformInducing (α
-/
instance instUniformContinuousConstSMul (M : Type*)
    [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
    [UniformSpace F] [IsUniformAddGroup F] [UniformContinuousConstSMul M F] (𝔖 : Set (Set E)) :
    UniformContinuousConstSMul M (E →SLᵤ[σ, 𝔖] F) :=
  (isUniformInducing_coeFn σ F 𝔖).uniformContinuousConstSMul fun _ _ ↦ by rfl
/-
**UniformConvergenceCLM.instContinuousConstSMul** 是 Mathlib 中的一个实例，位于命名空间 `Unifo
rmConvergenceCLM`。
形式化陈述：instContinuousConstSMul (M : Type*) [Monoid M] [DistribMulAction M F] [SMu
lCommClass 𝕜₂ M F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousCon
stSMul M F] (𝔖 : Set (Set E)) : ContinuousConstSMul M (E ->SLᵤ[σ, 𝔖] F)
参数：M : Type*；𝔖 : Set (Set E)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `uniformContinuousConstSMul_of_continuousConstSMul`：uniformContinuousCons
tSMul_of_continuousConstSMul [AddGroup M] [DistribSMul R M] [UniformSpace M] [Is
UniformAddGroup M] [ContinuousConstSMul…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
-/
instance instContinuousConstSMul (M : Type*)
    [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul M F] (𝔖 : Set (Set E)) :
    ContinuousConstSMul M (E →SLᵤ[σ, 𝔖] F) :=
  let _ := IsTopologicalAddGroup.rightUniformSpace F
  have _ : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  have _ := uniformContinuousConstSMul_of_continuousConstSMul M F
  inferInstance
/-
**UniformConvergenceCLM.tendsto_iff_tendstoUniformlyOn** 是 Mathlib 中的一个定理，位于命名空间
 `UniformConvergenceCLM`。
形式化陈述：tendsto_iff_tendstoUniformlyOn {ι : Type*} {p : Filter ι} [UniformSpace F]
 [IsUniformAddGroup F] (𝔖 : Set (Set E)) {a : ι -> E ->SLᵤ[σ, 𝔖] F} {a₀ : E ->SL
ᵤ[σ, 𝔖] F} : Filter.Tendsto a p (𝓝 a₀) ↔ forall s in 𝔖, TendstoUniformlyOn (a · 
·) a₀ p s
参数：𝔖 : Set (Set E)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsEmbedding.tendsto_nhds_iff`：∀ {Y : Type u_2} {Z : Type u_3} {
ι : Type u_4} {g : Y → Z} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace
 Z]   {f : ι → Y} {l : Filt…
· 使用定理 `UniformConvergenceCLM.isEmbedding_coeFn`：isEmbedding_coeFn [UniformSpace
 F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) : IsEmbedding (X
· 使用定理 `UniformOnFun.tendsto_iff_tendstoUniformlyOn`：∀ {α : Type u_1} {β : Type 
u_2} {ι : Type u_4} {p : Filter ι} [inst : UniformSpace β] {𝔖 : Set (Set α)}   {
F : ι → UniformOnFun α β 𝔖} {f : …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_iff_tendstoUniformlyOn {ι : Type*} {p : Filter ι} [UniformSpace F]
    [IsUniformAddGroup F] (𝔖 : Set (Set E)) {a : ι → E →SLᵤ[σ, 𝔖] F}
    {a₀ : E →SLᵤ[σ, 𝔖] F} :
    Filter.Tendsto a p (𝓝 a₀) ↔ ∀ s ∈ 𝔖, TendstoUniformlyOn (a · ·) a₀ p s := by
  rw [(isEmbedding_coeFn σ F 𝔖).tendsto_nhds_iff, UniformOnFun.tendsto_iff_tendstoUniformlyOn]
  rfl

set_option backward.isDefEq.respectTransparency false in
variable {F} in
/-
**UniformConvergenceCLM.isUniformInducing_postcomp** 是 Mathlib 中的一个定理，位于命名空间 `Un
iformConvergenceCLM`。
形式化陈述：isUniformInducing_postcomp [AddCommGroup G] [UniformSpace G] [IsUniformAdd
Group G] {𝕜₃ : Type*} [NormedField 𝕜₃] [Module 𝕜₃ G] {τ : 𝕜₂ ->+* 𝕜₃} {ρ : 𝕜₁ ->
+* 𝕜₃} [RingHomCompTriple σ τ ρ] [UniformSpace F] [IsUniformAddGroup F] (g : F -
>SL[τ] G) (hg : IsUniformInducing g) (𝔖 : Set (Set E)) : IsUniformInducing (α
参数：g : F ->SL[τ] G；hg : IsUniformInducing g；𝔖 : Set (Set E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUniformInducing.of_comp_iff`：IsUniformInducing.of_comp_iff {g : β -> γ
} (hg : IsUniformInducing g) {f : α -> β} : IsUniformInducing (g ∘ f) ↔ IsUnifor
mInducing f
· 使用定理 `UniformConvergenceCLM.isUniformInducing_coeFn`：isUniformInducing_coeFn [
UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) : IsUniformInducing (α
· 使用定理 `IsUniformInducing.comp`：IsUniformInducing.comp {g : β -> γ} (hg : IsUnif
ormInducing g) {f : α -> β} (hf : IsUniformInducing f) : IsUniformInducing (g ∘ 
f)
· 使用引理 `UniformOnFun.postcomp_isUniformInducing`：postcomp_isUniformInducing [Uni
formSpace γ] {f : γ -> β} (hf : IsUniformInducing f) : IsUniformInducing (ofFun 
𝔖 ∘ (f ∘ ·) ∘ toFun 𝔖)
-/
theorem isUniformInducing_postcomp
    [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
    {𝕜₃ : Type*} [NormedField 𝕜₃] [Module 𝕜₃ G]
    {τ : 𝕜₂ →+* 𝕜₃} {ρ : 𝕜₁ →+* 𝕜₃} [RingHomCompTriple σ τ ρ] [UniformSpace F] [IsUniformAddGroup F]
    (g : F →SL[τ] G) (hg : IsUniformInducing g) (𝔖 : Set (Set E)) :
    IsUniformInducing (α := E →SLᵤ[σ, 𝔖] F) (β := E →SLᵤ[ρ, 𝔖] G)
      g.comp := by
  rw [← (isUniformInducing_coeFn _ _ _).of_comp_iff]
  exact (UniformOnFun.postcomp_isUniformInducing hg).comp (isUniformInducing_coeFn _ _ _)

variable {F} in
/-
**UniformConvergenceCLM.isUniformEmbedding_postcomp** 是 Mathlib 中的一个定理，位于命名空间 `U
niformConvergenceCLM`。
形式化陈述：isUniformEmbedding_postcomp [AddCommGroup G] [UniformSpace G] [IsUniformAd
dGroup G] {𝕜₃ : Type*} [NormedField 𝕜₃] [Module 𝕜₃ G] {τ : 𝕜₂ ->+* 𝕜₃} {ρ : 𝕜₁ -
>+* 𝕜₃} [RingHomCompTriple σ τ ρ] [UniformSpace F] [IsUniformAddGroup F] (g : F 
->SL[τ] G) (hg : IsUniformEmbedding g) (𝔖 : Set (Set E)) : IsUniformEmbedding (α
参数：g : F ->SL[τ] G；hg : IsUniformEmbedding g；𝔖 : Set (Set E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.isUniformInducing_postcomp`：isUniformInducing_post
comp [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] {𝕜₃ : Type*} [Norme
dField 𝕜₃] [Module 𝕜₃ G] {τ : 𝕜₂ ->+* …
· 使用引理 `IsUniformEmbedding.isUniformInducing`：IsUniformEmbedding.isUniformInduci
ng {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformInducing f
· 使用定理 `ContinuousLinearMap.cancel_left`：cancel_left {g : M₂ ->SL[σ₂₃] M₃} {f₁ f
₂ : M₁ ->SL[σ₁₂] M₂} (hg : Function.Injective g) (h : g ∘SL f₁ = g ∘SL f₂) : f₁ 
= f₂
· 使用定理 `IsUniformEmbedding.injective`：∀ {α : Type ua} {β : Type ub} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Func
tion.Injective f
-/
theorem isUniformEmbedding_postcomp
    [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
    {𝕜₃ : Type*} [NormedField 𝕜₃] [Module 𝕜₃ G]
    {τ : 𝕜₂ →+* 𝕜₃} {ρ : 𝕜₁ →+* 𝕜₃} [RingHomCompTriple σ τ ρ] [UniformSpace F] [IsUniformAddGroup F]
    (g : F →SL[τ] G) (hg : IsUniformEmbedding g) (𝔖 : Set (Set E)) :
    IsUniformEmbedding (α := E →SLᵤ[σ, 𝔖] F) (β := E →SLᵤ[ρ, 𝔖] G)
      g.comp :=
  .mk (isUniformInducing_postcomp _ g hg.isUniformInducing _) fun _ _ ↦ g.cancel_left hg.injective
/-
**UniformConvergenceCLM.completeSpace** 是 Mathlib 中的一个定理，位于命名空间 `UniformConverge
nceCLM`。
形式化陈述：completeSpace [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜₂ F]
 [CompleteSpace F] {𝔖 : Set (Set E)} (h𝔖 : IsCoherentWith 𝔖) (h𝔖U : ⋃₀ 𝔖 = univ)
 : CompleteSpace (E ->SLᵤ[σ, 𝔖] F)
参数：Set E；h𝔖 : IsCoherentWith 𝔖；h𝔖U : ⋃₀ 𝔖 = univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `completeSpace_iff_isComplete_range`：completeSpace_iff_isComplete_range {
f : α -> β} (hf : IsUniformInducing f) : CompleteSpace α ↔ IsComplete (range f)
· 使用定理 `UniformConvergenceCLM.isUniformInducing_coeFn`：isUniformInducing_coeFn [
UniformSpace F] [IsUniformAddGroup F] (𝔖 : Set (Set E)) : IsUniformInducing (α
· 使用定理 `IsClosed.isComplete`：IsClosed.isComplete [CompleteSpace α] {s : Set α} (
h : IsClosed s) : IsComplete s
· 使用定理 `UniformOnFun.instCompleteSpace`：∀ {α : Type u_1} {β : Type u_2} [inst : 
UniformSpace β] {𝔖 : Set (Set α)} [CompleteSpace β],   CompleteSpace (UniformOnF
un α β 𝔖)
· 使用定理 `UniformOnFun.isClosed_setOfPred_continuous`：isClosed_setOfPred_continuou
s [TopologicalSpace α] (h : IsCoherentWith 𝔖) : IsClosed {f : α ->ᵤ[𝔖] β | Conti
nuous (toFun 𝔖 f)}
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.range_coeFn_eq`：range_coeFn_eq : Set.range ((⇑) : (M
₁ ->SL[σ₁₂] M₂) -> (M₁ -> M₂)) = {f | Continuous f} inter Set.range ((⇑) : (M₁ -
>ₛₗ[σ₁₂] M₂) -> (M₁ -> M…
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `UniformOnFun.uniformContinuous_toFun`：∀ {α : Type u_1} {β : Type u_2} [i
nst : UniformSpace β] {𝔖 : Set (Set α)},   ⋃₀ 𝔖 = Set.univ → UniformContinuous ⇑
(UniformOnFun.toFun 𝔖)
· 使用定理 `LinearMap.isClosed_range_coe`：LinearMap.isClosed_range_coe : IsClosed (S
et.range ((↑) : (M₁ ->ₛₗ[σ] M₂) -> M₁ -> M₂))
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `SeparationQuotient.instIsUniformAddGroup`：∀ {G : Type u_1} [inst : AddGr
oup G] [inst_1 : UniformSpace G] [inst_2 : IsUniformAddGroup G],   IsUniformAddG
roup (SeparationQuotient G)
· 使用定理 `IsUniformInducing.completeSpace_congr`：IsUniformInducing.completeSpace_c
ongr {f : α -> β} (hf : IsUniformInducing f) (hsurj : f.Surjective) : CompleteSp
ace α ↔ CompleteSpace β
· 使用定理 `UniformConvergenceCLM.isUniformInducing_postcomp`：isUniformInducing_post
comp [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] {𝕜₃ : Type*} [Norme
dField 𝕜₃] [Module 𝕜₃ G] {τ : 𝕜₂ ->+* …
· 使用引理 `SeparationQuotient.isUniformInducing_mk`：SeparationQuotient.isUniformInd
ucing_mk : IsUniformInducing (mk : α -> SeparationQuotient α)
· 使用定理 `SeparationQuotient.postcomp_mkCLM_surjective`：postcomp_mkCLM_surjective 
{L : Type*} [Semiring L] (σ : L ->+* K) (F : Type*) [AddCommMonoid F] [Module L 
F] [TopologicalSpace F] : Function…
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalAddGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSp
ace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], RegularSpace G
-/
theorem completeSpace [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜₂ F] [CompleteSpace F]
    {𝔖 : Set (Set E)} (h𝔖 : IsCoherentWith 𝔖) (h𝔖U : ⋃₀ 𝔖 = univ) :
    CompleteSpace (E →SLᵤ[σ, 𝔖] F) := by
  wlog hF : T2Space F generalizing F
  · rw [(isUniformInducing_postcomp σ (SeparationQuotient.mkCLM 𝕜₂ F)
      SeparationQuotient.isUniformInducing_mk _).completeSpace_congr]
    exacts [this _ inferInstance, SeparationQuotient.postcomp_mkCLM_surjective F σ E]
  rw [completeSpace_iff_isComplete_range (isUniformInducing_coeFn _ _ _)]
  apply IsClosed.isComplete
  have H₁ : IsClosed {f : E →ᵤ[𝔖] F | Continuous ((UniformOnFun.toFun 𝔖) f)} :=
    UniformOnFun.isClosed_setOfPred_continuous h𝔖
  convert!
    H₁.inter <|
      (LinearMap.isClosed_range_coe E F σ).preimage
        (UniformOnFun.uniformContinuous_toFun h𝔖U).continuous
  exact ContinuousLinearMap.range_coeFn_eq

variable {𝔖₁ 𝔖₂ : Set (Set E)}
/-
**UniformConvergenceCLM.uniformSpace_mono** 是 Mathlib 中的一个定理，位于命名空间 `UniformConv
ergenceCLM`。
形式化陈述：uniformSpace_mono [UniformSpace F] [IsUniformAddGroup F] (h : 𝔖₂ subseteq 
𝔖₁) : instUniformSpace σ F 𝔖₁ <= instUniformSpace σ F 𝔖₂
参数：h : 𝔖₂ subseteq 𝔖₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformConvergenceCLM.uniformSpace_eq`：uniformSpace_eq [UniformSpace F] 
[IsUniformAddGroup F] (𝔖 : Set (Set E)) : instUniformSpace σ F 𝔖 = UniformSpace.
comap (UniformOnFun.ofFun 𝔖…
· 使用定理 `UniformSpace.comap_mono`：UniformSpace.comap_mono {α γ} {f : α -> γ} : Mo
notone fun u : UniformSpace γ => u.comap f
· 使用定理 `UniformOnFun.mono`：∀ {α : Type u_1} {γ : Type u_3} ⦃u₁ u₂ : UniformSpace
 γ⦄,   u₁ ≤ u₂ → ∀ ⦃𝔖₁ 𝔖₂ : Set (Set α)⦄, 𝔖₂ ⊆ 𝔖₁ → UniformOnFun.uniformSpace α 
γ 𝔖₁ ≤ …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem uniformSpace_mono [UniformSpace F] [IsUniformAddGroup F] (h : 𝔖₂ ⊆ 𝔖₁) :
    instUniformSpace σ F 𝔖₁ ≤ instUniformSpace σ F 𝔖₂ := by
  simp_rw [uniformSpace_eq]
  exact UniformSpace.comap_mono (UniformOnFun.mono (le_refl _) h)
/-
**UniformConvergenceCLM.topologicalSpace_mono** 是 Mathlib 中的一个定理，位于命名空间 `Uniform
ConvergenceCLM`。
形式化陈述：topologicalSpace_mono [TopologicalSpace F] [IsTopologicalAddGroup F] (h : 
𝔖₂ subseteq 𝔖₁) : instTopologicalSpace σ F 𝔖₁ <= instTopologicalSpace σ F 𝔖₂
参数：h : 𝔖₂ subseteq 𝔖₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `UniformSpace.toTopologicalSpace_mono`：toTopologicalSpace_mono {u₁ u₂ : U
niformSpace α} (h : u₁ <= u₂) : @UniformSpace.toTopologicalSpace _ u₁ <= @Unifor
mSpace.toTopologicalSpace …
· 使用定理 `UniformConvergenceCLM.uniformSpace_mono`：uniformSpace_mono [UniformSpace
 F] [IsUniformAddGroup F] (h : 𝔖₂ subseteq 𝔖₁) : instUniformSpace σ F 𝔖₁ <= inst
UniformSpace σ F 𝔖₂
-/
theorem topologicalSpace_mono [TopologicalSpace F] [IsTopologicalAddGroup F] (h : 𝔖₂ ⊆ 𝔖₁) :
    instTopologicalSpace σ F 𝔖₁ ≤ instTopologicalSpace σ F 𝔖₂ := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  simp_rw [← uniformity_toTopologicalSpace_eq]
  exact UniformSpace.toTopologicalSpace_mono (uniformSpace_mono σ F h)

variable {𝕜₁ : Type*} [NontriviallyNormedField 𝕜₁] {σ : 𝕜₁ →+* 𝕜₂} [Module 𝕜₁ E] in
variable {F} in
/-- Let `𝔖` be a family of bounded subsets of `F`, and `B : E × F → G` a bilinear map.
If `B` is (jointly) continuous, then it is `𝔖`-**hypocontinuous**:
in curried form, it defines a continuous linear map `E →L[𝕜] (F →Lᵤ[𝕜, 𝔖] G)`.

Note that, in full generality, the converse is not true.
See also `ContinuousLinearMap.continuous_of_continuous_uncurry`. -/
/-
**UniformConvergenceCLM.continuous_of_continuous_uncurry** 是 Mathlib 中的一个定理，位于命名
空间 `UniformConvergenceCLM`。
形式化陈述：∀ {𝕜₂ : Type u_2} [inst : NormedField 𝕜₂] {E : Type u_3} {F : Type u_4} {G
 : Type u_5} [inst_1 : AddCommGroup E]   [inst_2 : TopologicalSpace E] [inst_3 :
 AddCommGroup F] [inst_4 : _root_.Module 𝕜₂ F] {𝕜₁ : Type u_6}   [inst_5 : Nontr
iviallyNormedField 𝕜₁] {σ : 𝕜₁ →+* 𝕜₂} [inst_6 : _root_.Module 𝕜₁ E] [inst_7 : A
ddCommGroup G]   {𝕜₃ : Type u_7} [inst_8 : NormedField 𝕜₃] [inst_9 : _root_.Modu
le 𝕜₃ G] {τ : 𝕜₃ →+* 𝕜₂} [RingHomSurjective τ]   [inst_11 : TopologicalSpace F] 
[inst_12 : IsTopologicalAddGroup F] [inst_13 : ContinuousConstSMul 𝕜₂ F]   [inst
_14 : TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G] {
𝔖 : Set (Set E)},   (∀ s ∈ 𝔖, Bornology.IsVonNBounded 𝕜₁ s) →     ∀ (B : G →ₛₗ[τ
] UniformConvergenceCLM σ F 𝔖), (Continuous fun p => (B p.1) p.2) → Continuous ⇑
B
参数：Set E；∀ s ∈ 𝔖, Bornology.IsVonNBounded 𝕜₁ s；B : G →ₛₗ[τ] UniformConvergenceCL
M σ F 𝔖；Continuous fun p => (B p.1) p.2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_tendsto_nhds_zero`：∀ {G : Type w} [inst : TopologicalSpace
 G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] {M : Type u_1}   {hom : Type
 u_2} [inst_3 : AddZe…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_prod_iff`：mem_nhds_prod_iff {x : X} {y : Y} {s : Set (X × Y)} :
 s in 𝓝 (x, y) ↔ exists u in 𝓝 x, exists v in 𝓝 y, u ×ˢ v subseteq s
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `UniformConvergenceCLM.instIsZeroApply`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2}
 [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E : Type u_3
}   (F : Type u_4) [inst_2 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Absorbs.eventually_nhdsNE_zero`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : 
NormedDivisionRing 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   {
s t : Set E}, Absorb…
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用定理 `RingHom.surjective`：RingHom.surjective (σ : R₁ ->+* R₂) [t : RingHomSurj
ective σ] : Function.Surjective σ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_ne_zero`：map_ne_zero : f a != 0 ↔ a != 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `set_smul_mem_nhds_zero_iff`：set_smul_mem_nhds_zero_iff {s : Set α} {c : 
G₀} (hc : c != 0) : c • s in 𝓝 (0 : α) ↔ s in 𝓝 (0 : α)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
Let `𝔖` be a family of bounded subsets of `F`, and `B : E × F → G` a bilinear ma
p.
If `B` is (jointly) continuous, then it is `𝔖`-**hypocontinuous**:
in curried form, it defines a continuous linear map `E →L[𝕜] (F →Lᵤ[𝕜, 𝔖] G)`.

Note that, in full generality, the converse is not true.
See also `ContinuousLinearMap.continuous_of_continuous_uncurry`.
-/
protected theorem continuous_of_continuous_uncurry [AddCommGroup G]
    {𝕜₃ : Type*} [NormedField 𝕜₃] [Module 𝕜₃ G]
    {τ : 𝕜₃ →+* 𝕜₂} [RingHomSurjective τ]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]
    {𝔖 : Set (Set E)} (h𝔖 : ∀ s ∈ 𝔖, IsVonNBounded 𝕜₁ s)
    (B : G →ₛₗ[τ] (E →SLᵤ[σ, 𝔖] F))
    (hB : Continuous (fun p : G × E ↦ B p.1 p.2)) :
    Continuous B := by
  apply continuous_of_tendsto_nhds_zero
  suffices ∀ s ∈ 𝔖, ∀ U ∈ 𝓝 0, ∀ᶠ (g : G) in 𝓝 0, ∀ e ∈ s, B g e ∈ U by
    simpa [UniformConvergenceCLM.nhds_zero_eq, MapsTo]
  intro S hS U hU
  rcases mem_nhds_prod_iff.mp <| hB.tendsto' (0 : G × E) 0 (by simp) hU
    with ⟨V, hV, W, hW, hVW⟩
  rcases (h𝔖 S hS) hW |>.eventually_nhdsNE_zero.and eventually_mem_nhdsWithin |>.exists with
    ⟨c, hc, c_ne : c ≠ 0⟩
  rcases RingHom.surjective τ (σ c) with ⟨d, hd⟩
  have d_ne : d ≠ 0 := by rwa [← map_ne_zero τ, hd, map_ne_zero σ]
  filter_upwards [(set_smul_mem_nhds_zero_iff d_ne).mpr hV]
  rintro _ ⟨a, ha, rfl⟩ x hx
  rw [map_smulₛₗ, hd, smul_apply, ← map_smulₛₗ]
  exact @hVW ⟨_, _⟩ ⟨ha, hc hx⟩

section Equiv

variable [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F] (𝔖 : Set (Set E))

/-- The linear equivalence that maps a continuous linear map to the type copy endowed with the
uniform convergence topology. -/
/-
**UniformConvergenceCLM._root_.ContinuousLinearMap.toUniformConvergenceCLM** 是 M
athlib 中的一个定义，位于命名空间 `UniformConvergenceCLM`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equivalence that maps a continuous linear map to the type copy endowe
d with the
uniform convergence topology.
-/
def _root_.ContinuousLinearMap.toUniformConvergenceCLM :
    (E →SL[σ] F) ≃ₗ[𝕜₂] E →SLᵤ[σ, 𝔖] F where
  __ := LinearEquiv.refl _ _

variable {σ F 𝔖}

@[simp]
/-
**UniformConvergenceCLM._root_.ContinuousLinearMap.toUniformConvergenceCLM_apply
** 是 Mathlib 中的一个引理，位于命名空间 `UniformConvergenceCLM`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContinuousLinearMap.toUniformConvergenceCLM_apply {A : E →SL[σ] F} {x : E} :
    ContinuousLinearMap.toUniformConvergenceCLM σ F 𝔖 A x = A x := rfl

@[simp]
/-
**UniformConvergenceCLM._root_.ContinuousLinearMap.toUniformConvergenceCLM_symm_
apply** 是 Mathlib 中的一个引理，位于命名空间 `UniformConvergenceCLM`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContinuousLinearMap.toUniformConvergenceCLM_symm_apply
    {A : E →SLᵤ[σ, 𝔖] F} {x : E} :
    (ContinuousLinearMap.toUniformConvergenceCLM σ F 𝔖).symm A x = A x := rfl

end Equiv

end UniformConvergenceCLM

namespace ContinuousLinearMap

open scoped UniformConvergenceCLM

variable {𝕜₁ 𝕜₂ 𝕜₃ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃] {σ : 𝕜₁ →+* 𝕜₂}
  {τ : 𝕜₂ →+* 𝕜₃} {ρ : 𝕜₁ →+* 𝕜₃} [RingHomCompTriple σ τ ρ] {E F G : Type*} [AddCommGroup E]
  [Module 𝕜₁ E] [AddCommGroup F] [Module 𝕜₂ F]
  [AddCommGroup G] [Module 𝕜₃ G] [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]

variable (𝔖 : Set (Set E)) (𝔗 : Set (Set F))

set_option backward.isDefEq.respectTransparency false in
variable (G) in
/-- Pre-composition by a *fixed* continuous linear map as a continuous linear map for the uniform
convergence topology. -/
@[simps]
/-
**ContinuousLinearMap.precompUniformConvergenceCLM** 是 Mathlib 中的一个定义，位于命名空间 `Co
ntinuousLinearMap`。
形式化陈述：precompUniformConvergenceCLM [IsTopologicalAddGroup G] [ContinuousConstSMu
l 𝕜₃ G] (L : E ->SL[σ] F) (hL : MapsTo (L '' ·) 𝔖 𝔗) : (F ->SLᵤ[τ, 𝔗] G) ->L[𝕜₃]
 (E ->SLᵤ[ρ, 𝔖] G) where toFun f
参数：L : E ->SL[σ] F；hL : MapsTo (L '' ·) 𝔖 𝔗。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pre-composition by a *fixed* continuous linear map as a continuous linear map fo
r the uniform
convergence topology.
-/
def precompUniformConvergenceCLM [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]
    (L : E →SL[σ] F) (hL : MapsTo (L '' ·) 𝔖 𝔗) :
    (F →SLᵤ[τ, 𝔗] G) →L[𝕜₃] (E →SLᵤ[ρ, 𝔖] G) where
  toFun f := f.comp L
  map_add' f g := add_comp f g L
  map_smul' a f := smul_comp a f L
  cont := by
    let : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
    have : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
    rw [(UniformConvergenceCLM.isEmbedding_coeFn _ _ _).continuous_iff]
    exact (UniformOnFun.precomp_uniformContinuous hL).continuous.comp
        (UniformConvergenceCLM.isEmbedding_coeFn _ _ _).continuous

@[deprecated (since := "2026-01-27")]
alias precomp_uniformConvergenceCLM := precompUniformConvergenceCLM

@[deprecated (since := "2026-01-27")]
alias precomp_uniformConvergenceCLM_apply := precompUniformConvergenceCLM_apply

set_option backward.isDefEq.respectTransparency false in
/-- Post-composition by a *fixed* continuous linear map as a continuous linear map for the uniform
convergence topology. -/
@[simps]
/-
**ContinuousLinearMap.postcompUniformConvergenceCLM** 是 Mathlib 中的一个定义，位于命名空间 `C
ontinuousLinearMap`。
形式化陈述：postcompUniformConvergenceCLM [IsTopologicalAddGroup F] [IsTopologicalAddG
roup G] [ContinuousConstSMul 𝕜₃ G] [ContinuousConstSMul 𝕜₂ F] (L : F ->SL[τ] G) 
: (E ->SLᵤ[σ, 𝔖] F) ->SL[τ] (E ->SLᵤ[ρ, 𝔖] G) where toFun f
参数：L : F ->SL[τ] G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Post-composition by a *fixed* continuous linear map as a continuous linear map f
or the uniform
convergence topology.
-/
def postcompUniformConvergenceCLM [IsTopologicalAddGroup F] [IsTopologicalAddGroup G]
    [ContinuousConstSMul 𝕜₃ G] [ContinuousConstSMul 𝕜₂ F] (L : F →SL[τ] G) :
    (E →SLᵤ[σ, 𝔖] F) →SL[τ] (E →SLᵤ[ρ, 𝔖] G) where
  toFun f := L.comp f
  map_add' := comp_add L
  map_smul' := comp_smulₛₗ L
  cont := by
    let : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
    have : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
    let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
    have : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
    rw [(UniformConvergenceCLM.isEmbedding_coeFn _ _ _).continuous_iff]
    exact
      (UniformOnFun.postcomp_uniformContinuous L.uniformContinuous).continuous.comp
        (UniformConvergenceCLM.isEmbedding_coeFn _ _ _).continuous

@[deprecated (since := "2026-01-27")]
alias postcomp_uniformConvergenceCLM := postcompUniformConvergenceCLM

@[deprecated (since := "2026-01-27")]
alias postcomp_uniformConvergenceCLM_apply := postcompUniformConvergenceCLM_apply

end ContinuousLinearMap

/-! ### Continuous linear equivalences -/

section Pi

open scoped UniformConvergenceCLM

variable (𝕜 : Type*) [NormedField 𝕜] {E ι : Type*} (F : ι → Type*)
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [∀ i, AddCommGroup (F i)] [∀ i, Module 𝕜 (F i)] [∀ i, TopologicalSpace (F i)]
  [∀ i, IsTopologicalAddGroup (F i)] [∀ i, ContinuousConstSMul 𝕜 (F i)]

set_option backward.isDefEq.respectTransparency.types false in
/-- `ContinuousLinearMap.pi`, upgraded to a continuous linear equivalence between
`Π i, E →Lᵤ[𝕜, 𝔖] F i` and `E →Lᵤ[𝕜, 𝔖] Π i, F i`. -/
/-
**UniformConvergenceCLM.piEquivL** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UniformConvergenceCLM.piEquivL (𝔖 : Set (Set E)) : (Π i, E ->Lᵤ[𝕜, 𝔖] F i)
 ≃L[𝕜] (E ->Lᵤ[𝕜, 𝔖] Π i, F i)
参数：𝔖 : Set (Set E)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousLinearMap.pi`, upgraded to a continuous linear equivalence between
`Π i, E →Lᵤ[𝕜, 𝔖] F i` and `E →Lᵤ[𝕜, 𝔖] Π i, F i`.
-/
def UniformConvergenceCLM.piEquivL (𝔖 : Set (Set E)) :
    (Π i, E →Lᵤ[𝕜, 𝔖] F i) ≃L[𝕜] (E →Lᵤ[𝕜, 𝔖] Π i, F i) :=
  letI : ∀ i, UniformSpace (F i) := fun i ↦ IsTopologicalAddGroup.rightUniformSpace (F i)
  haveI : ∀ i, IsUniformAddGroup (F i) := fun i ↦ isUniformAddGroup_of_addCommGroup
  { toFun F := ContinuousLinearMap.pi F
    invFun f i := (ContinuousLinearMap.proj i).comp f
    map_add' _ _ := by ext; rfl
    map_smul' _ _ := by ext; rfl
    left_inv _ := by ext; rfl
    right_inv _ := by ext; rfl
    continuous_toFun := by
      rw [UniformConvergenceCLM.isEmbedding_coeFn _ _ _ |>.continuous_iff]
      rw [UniformOnFun.uniformEquivPiComm _ _ |>.isUniformEmbedding.isEmbedding.continuous_iff]
      refine continuous_pi fun i ↦ ?_
      exact UniformConvergenceCLM.isEmbedding_coeFn _ _ _ |>.continuous.comp (continuous_apply i)
    continuous_invFun := by
      apply continuous_pi (A := fun i ↦ E →Lᵤ[𝕜, 𝔖] F i) fun i ↦ ?_
      exact (ContinuousLinearMap.proj i : (Π j, F j) →L[𝕜] F i).postcompUniformConvergenceCLM 𝔖
        |>.continuous}

@[simp]
/-
**UniformConvergenceCLM.piEquivL_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformConvergenceCLM.piEquivL_apply (𝔖 : Set (Set E)) (T : Π i, E ->Lᵤ[𝕜,
 𝔖] F i) (e : E) (i : ι) : piEquivL 𝕜 F 𝔖 T e i = T i e
参数：𝔖 : Set (Set E)；T : Π i, E ->Lᵤ[𝕜, 𝔖] F i；e : E；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instContinuousConstSMulForall`：∀ {M : Type u_1} {ι : Type u_4} {γ : ι → 
Type u_5} [inst : (i : ι) → TopologicalSpace (γ i)]   [inst_1 : (i : ι) → SMul M
 (γ i)] [∀ (i : ι),…
-/
lemma UniformConvergenceCLM.piEquivL_apply (𝔖 : Set (Set E))
    (T : Π i, E →Lᵤ[𝕜, 𝔖] F i) (e : E) (i : ι) :
    piEquivL 𝕜 F 𝔖 T e i = T i e :=
  rfl

@[simp]
/-
**UniformConvergenceCLM.piEquivL_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformConvergenceCLM.piEquivL_symm_apply (𝔖 : Set (Set E)) (T : E ->Lᵤ[𝕜,
 𝔖] Π i, F i) (e : E) (i : ι) : (piEquivL 𝕜 F 𝔖).symm T i e = T e i
参数：𝔖 : Set (Set E)；T : E ->Lᵤ[𝕜, 𝔖] Π i, F i；e : E；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instContinuousConstSMulForall`：∀ {M : Type u_1} {ι : Type u_4} {γ : ι → 
Type u_5} [inst : (i : ι) → TopologicalSpace (γ i)]   [inst_1 : (i : ι) → SMul M
 (γ i)] [∀ (i : ι),…
-/
lemma UniformConvergenceCLM.piEquivL_symm_apply (𝔖 : Set (Set E))
    (T : E →Lᵤ[𝕜, 𝔖] Π i, F i) (e : E) (i : ι) :
    (piEquivL 𝕜 F 𝔖).symm T i e = T e i :=
  rfl

end Pi

open ContinuousLinearMap

namespace ContinuousLinearEquiv

open scoped UniformConvergenceCLM

section Semilinear

variable {𝕜 : Type*} {𝕜₂ : Type*} {𝕜₃ : Type*} {𝕜₄ : Type*} {E : Type*} {F : Type*}
  {G : Type*} {H : Type*} [AddCommGroup E] [AddCommGroup F] [AddCommGroup G] [AddCommGroup H]
  [NormedField 𝕜] [NormedField 𝕜₂] [NormedField 𝕜₃] [NormedField 𝕜₄]
  [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜₃ G] [Module 𝕜₄ H]
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalAddGroup G] [IsTopologicalAddGroup H]
  [ContinuousConstSMul 𝕜₃ G] [ContinuousConstSMul 𝕜₄ H]
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
  {σ₃₄ : 𝕜₃ →+* 𝕜₄} {σ₄₃ : 𝕜₄ →+* 𝕜₃} {σ₂₄ : 𝕜₂ →+* 𝕜₄} {σ₁₄ : 𝕜 →+* 𝕜₄} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂] [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄]
  [RingHomCompTriple σ₂₁ σ₁₄ σ₂₄] [RingHomCompTriple σ₂₄ σ₄₃ σ₂₃] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
  [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄]

/-- A pair of continuous (semi)linear equivalences generates a (semi)linear equivalence between the
spaces of continuous (semi)linear maps. This version is for the type alias
`UniformConvergenceCLM`. -/
/-
**ContinuousLinearEquiv.uniformConvergenceCLMCongrSL** 是 Mathlib 中的一个定义，位于命名空间 `
ContinuousLinearEquiv`。
形式化陈述：uniformConvergenceCLMCongrSL (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G) (𝔖 
: Set (Set E)) (𝔗 : Set (Set F)) (h : forall t, t in 𝔗 ↔ e₁₂ ⁻¹' t in 𝔖) : (E ->
SLᵤ[σ₁₄, 𝔖] H) ≃SL[σ₄₃] (F ->SLᵤ[σ₂₃, 𝔗] G)
参数：e₁₂ : E ≃SL[σ₁₂] F；e₄₃ : H ≃SL[σ₄₃] G；𝔖 : Set (Set E)；𝔗 : Set (Set F)；h : for
all t, t in 𝔗 ↔ e₁₂ ⁻¹' t in 𝔖。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pair of continuous (semi)linear equivalences generates a (semi)linear equivale
nce between the
spaces of continuous (semi)linear maps. This version is for the type alias
`UniformConvergenceCLM`.
-/
def uniformConvergenceCLMCongrSL (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G)
    (𝔖 : Set (Set E)) (𝔗 : Set (Set F))
    (h : ∀ t, t ∈ 𝔗 ↔ e₁₂ ⁻¹' t ∈ 𝔖) :
    (E →SLᵤ[σ₁₄, 𝔖] H) ≃SL[σ₄₃] (F →SLᵤ[σ₂₃, 𝔗] G) :=
  haveI mapsto₁ : MapsTo (e₁₂ '' ·) 𝔖 𝔗 := fun s ↦ by simp [h, preimage_image_eq _ e₁₂.injective]
  haveI mapsto₂ : MapsTo (e₁₂.symm '' ·) 𝔗 𝔖 := fun t ↦ by simp [h, e₁₂.image_symm_eq_preimage]
  { e₁₂.arrowCongrEquivₛₗ e₄₃ with
    -- given explicitly to help `simps`
    toFun := fun L => (e₄₃ : H →SL[σ₄₃] G).comp (L.comp (e₁₂.symm : F →SL[σ₂₁] E))
    -- given explicitly to help `simps`
    invFun := fun L => (e₄₃.symm : G →SL[σ₃₄] H).comp (L.comp (e₁₂ : E →SL[σ₁₂] F))
    continuous_toFun := ((postcompUniformConvergenceCLM _ e₄₃.toContinuousLinearMap).comp
      (precompUniformConvergenceCLM H _ _ e₁₂.symm.toContinuousLinearMap mapsto₂)).continuous
    continuous_invFun :=
      ((precompUniformConvergenceCLM H _ _ e₁₂.toContinuousLinearMap mapsto₁).comp
        (postcompUniformConvergenceCLM _ e₄₃.symm.toContinuousLinearMap)).continuous }

@[simp]
/-
**ContinuousLinearEquiv.uniformConvergenceCLMCongrSL_apply** 是 Mathlib 中的一个引理，位于
命名空间 `ContinuousLinearEquiv`。
形式化陈述：uniformConvergenceCLMCongrSL_apply (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] 
G) (𝔖 : Set (Set E)) (𝔗 : Set (Set F)) (h : forall t, t in 𝔗 ↔ e₁₂ ⁻¹' t in 𝔖) (
φ : E ->SLᵤ[σ₁₄, 𝔖] H) (f : F) : uniformConvergenceCLMCongrSL e₁₂ e₄₃ 𝔖 𝔗 h φ f 
= e₄₃ (φ (e₁₂.symm f))
参数：e₁₂ : E ≃SL[σ₁₂] F；e₄₃ : H ≃SL[σ₄₃] G；𝔖 : Set (Set E)；𝔗 : Set (Set F)；h : for
all t, t in 𝔗 ↔ e₁₂ ⁻¹' t in 𝔖；φ : E ->SLᵤ[σ₁₄, 𝔖] H；f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma uniformConvergenceCLMCongrSL_apply (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G)
    (𝔖 : Set (Set E)) (𝔗 : Set (Set F))
    (h : ∀ t, t ∈ 𝔗 ↔ e₁₂ ⁻¹' t ∈ 𝔖) (φ : E →SLᵤ[σ₁₄, 𝔖] H) (f : F) :
    uniformConvergenceCLMCongrSL e₁₂ e₄₃ 𝔖 𝔗 h φ f = e₄₃ (φ (e₁₂.symm f)) :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.uniformConvergenceCLMCongrSL_symm_apply** 是 Mathlib 中的一个
引理，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：uniformConvergenceCLMCongrSL_symm_apply (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[
σ₄₃] G) (𝔖 : Set (Set E)) (𝔗 : Set (Set F)) (h : forall t, t in 𝔗 ↔ e₁₂ ⁻¹' t in
 𝔖) (φ : F ->SLᵤ[σ₂₃, 𝔗] G) (e : E) : (uniformConvergenceCLMCongrSL e₁₂ e₄₃ 𝔖 𝔗 
h).symm φ e = e₄₃.symm (φ (e₁₂ e))
参数：e₁₂ : E ≃SL[σ₁₂] F；e₄₃ : H ≃SL[σ₄₃] G；𝔖 : Set (Set E)；𝔗 : Set (Set F)；h : for
all t, t in 𝔗 ↔ e₁₂ ⁻¹' t in 𝔖；φ : F ->SLᵤ[σ₂₃, 𝔗] G；e : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma uniformConvergenceCLMCongrSL_symm_apply (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G)
    (𝔖 : Set (Set E)) (𝔗 : Set (Set F))
    (h : ∀ t, t ∈ 𝔗 ↔ e₁₂ ⁻¹' t ∈ 𝔖) (φ : F →SLᵤ[σ₂₃, 𝔗] G) (e : E) :
    (uniformConvergenceCLMCongrSL e₁₂ e₄₃ 𝔖 𝔗 h).symm φ e = e₄₃.symm (φ (e₁₂ e)) :=
  rfl

end Semilinear

section Linear

variable {𝕜 : Type*} {E : Type*} {F : Type*} {G : Type*} {H : Type*}
  [AddCommGroup E] [AddCommGroup F] [AddCommGroup G] [AddCommGroup H]
  [NormedField 𝕜] [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 G] [Module 𝕜 H]
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalAddGroup G] [IsTopologicalAddGroup H]
  [ContinuousConstSMul 𝕜 G] [ContinuousConstSMul 𝕜 H]

/-- A pair of continuous linear equivalences generates a continuous linear equivalence between
the spaces of continuous linear maps. This version is for the type alias
`UniformConvergenceCLM`. -/
/-
**ContinuousLinearEquiv.uniformConvergenceCLMCongr** 是 Mathlib 中的一个定义，位于命名空间 `Co
ntinuousLinearEquiv`。
形式化陈述：uniformConvergenceCLMCongr (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) (𝔖 : Set (Set
 E)) (𝔗 : Set (Set F)) (h : forall t, t in 𝔗 ↔ e₁ ⁻¹' t in 𝔖) : (E ->Lᵤ[𝕜, 𝔖] H)
 ≃L[𝕜] (F ->Lᵤ[𝕜, 𝔗] G)
参数：e₁ : E ≃L[𝕜] F；e₂ : H ≃L[𝕜] G；𝔖 : Set (Set E)；𝔗 : Set (Set F)；h : forall t, t
 in 𝔗 ↔ e₁ ⁻¹' t in 𝔖。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pair of continuous linear equivalences generates a continuous linear equivalen
ce between
the spaces of continuous linear maps. This version is for the type alias
`UniformConvergenceCLM`.
-/
def uniformConvergenceCLMCongr (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G)
    (𝔖 : Set (Set E)) (𝔗 : Set (Set F))
    (h : ∀ t, t ∈ 𝔗 ↔ e₁ ⁻¹' t ∈ 𝔖) :
    (E →Lᵤ[𝕜, 𝔖] H) ≃L[𝕜] (F →Lᵤ[𝕜, 𝔗] G) :=
  e₁.uniformConvergenceCLMCongrSL e₂ 𝔖 𝔗 h

@[simp]
/-
**ContinuousLinearEquiv.uniformConvergenceCLMCongr_apply** 是 Mathlib 中的一个引理，位于命名
空间 `ContinuousLinearEquiv`。
形式化陈述：uniformConvergenceCLMCongr_apply (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) (𝔖 : Se
t (Set E)) (𝔗 : Set (Set F)) (h : forall t, t in 𝔗 ↔ e₁ ⁻¹' t in 𝔖) (φ : E ->Lᵤ[
𝕜, 𝔖] H) (f : F) : uniformConvergenceCLMCongr e₁ e₂ 𝔖 𝔗 h φ f = e₂ (φ (e₁.symm f
))
参数：e₁ : E ≃L[𝕜] F；e₂ : H ≃L[𝕜] G；𝔖 : Set (Set E)；𝔗 : Set (Set F)；h : forall t, t
 in 𝔗 ↔ e₁ ⁻¹' t in 𝔖；φ : E ->Lᵤ[𝕜, 𝔖] H；f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma uniformConvergenceCLMCongr_apply (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G)
    (𝔖 : Set (Set E)) (𝔗 : Set (Set F))
    (h : ∀ t, t ∈ 𝔗 ↔ e₁ ⁻¹' t ∈ 𝔖) (φ : E →Lᵤ[𝕜, 𝔖] H) (f : F) :
    uniformConvergenceCLMCongr e₁ e₂ 𝔖 𝔗 h φ f = e₂ (φ (e₁.symm f)) :=
  rfl

@[simp]
/-
**ContinuousLinearEquiv.uniformConvergenceCLMCongr_symm_apply** 是 Mathlib 中的一个引理
，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：uniformConvergenceCLMCongr_symm_apply (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) (𝔖
 : Set (Set E)) (𝔗 : Set (Set F)) (h : forall t, t in 𝔗 ↔ e₁ ⁻¹' t in 𝔖) (φ : F 
->Lᵤ[𝕜, 𝔗] G) (e : E) : (uniformConvergenceCLMCongr e₁ e₂ 𝔖 𝔗 h).symm φ e = e₂.s
ymm (φ (e₁ e))
参数：e₁ : E ≃L[𝕜] F；e₂ : H ≃L[𝕜] G；𝔖 : Set (Set E)；𝔗 : Set (Set F)；h : forall t, t
 in 𝔗 ↔ e₁ ⁻¹' t in 𝔖；φ : F ->Lᵤ[𝕜, 𝔗] G；e : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma uniformConvergenceCLMCongr_symm_apply (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G)
    (𝔖 : Set (Set E)) (𝔗 : Set (Set F))
    (h : ∀ t, t ∈ 𝔗 ↔ e₁ ⁻¹' t ∈ 𝔖) (φ : F →Lᵤ[𝕜, 𝔗] G) (e : E) :
    (uniformConvergenceCLMCongr e₁ e₂ 𝔖 𝔗 h).symm φ e = e₂.symm (φ (e₁ e)) :=
  rfl

end Linear

end ContinuousLinearEquiv

