/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# The weak operator topology

This file defines a type copy of `E →L[𝕜] F` (where `E` and `F` are topological vector spaces)
which is endowed with the weak operator topology (WOT) rather than the topology of bounded
convergence (which is the usual one induced by the operator norm in the normed setting).
The WOT is defined as the coarsest topology such that the functional `fun A => y (A x)` is
continuous for any `x : E` and `y : StrongDual 𝕜 F`. Equivalently, a function `f` tends to
`A : E →WOT[𝕜] F` along filter `l` iff `y (f a x)` tends to `y (A x)` along the same filter.

Basic non-topological properties of `E →L[𝕜] F` (such as the module structure) are copied over to
the type copy.

We also prove that the WOT is induced by the family of seminorms `‖y (A x)‖` for `x : E` and
`y : StrongDual 𝕜 F`.

## Main declarations

* `ContinuousLinearMapWOT σ E F`: The type copy of `E →SL[σ] F` endowed with the weak operator
  topology.
* `ContinuousLinearMapWOT.tendsto_iff_forall_dual_apply_tendsto`: a function `f` tends to
  `A : E →WOT[𝕜] F` along filter `l` iff `y ((f a) x)` tends to `y (A x)` along the same filter.
* `ContinuousLinearMap.toWOT`: the inclusion map from `E →SL[σ] F` to the type copy
* `ContinuousLinearMap.continuous_toWOT`: the inclusion map is continuous, i.e. the WOT is coarser
  than the norm topology.
* `ContinuousLinearMapWOT.withSeminorms`: the WOT is induced by the family of seminorms
  `‖y (A x)‖` for `x : E` and `y : StrongDual 𝕜 F`.

## Notation

* The type copy of `E →L[𝕜] F` endowed with the weak operator topology is denoted by
  `E →WOT[𝕜] F` and the copy of `E →SL[σ] F` is denoted by `E →SWOT[σ] F`.
* We locally use the notation `F⋆` for `StrongDual 𝕜 F`.

## Implementation notes

In most of the literature, the WOT is defined on maps between Banach spaces. Here, we only assume
that the domain and codomains are topological vector spaces over a normed field.
-/

@[expose] public section

open Topology

/-- The type copy of `E →SL[σ] F` endowed with the weak operator topology, denoted as
`E →SWOT[σ] F`. Likewise, when `σ := RingHom.id 𝕜`, the notation `E →WOT[𝕜] F` is available. -/
/-
**ContinuousLinearMapWOT** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{𝕜₁ : Type u_1} →   {𝕜₂ : Type u_2} →     [inst : Semiring 𝕜₁] →       [in
st_1 : Semiring 𝕜₂] →         (𝕜₁ →+* 𝕜₂) →           (E : Type u_3) →          
   (F : Type u_4) →               [inst_2 : AddCommGroup E] →                 [T
opologicalSpace E] →                   [_root_.Module 𝕜₁ E] →                   
  [inst : AddCommGroup F] → [TopologicalSpace F] → [_root_.Module 𝕜₂ F] → Type (
max u_3 u_4)
参数：𝕜₁ →+* 𝕜₂；E : Type u_3；F : Type u_4；max u_3 u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type copy of `E →SL[σ] F` endowed with the weak operator topology, denoted a
s
`E →SWOT[σ] F`. Likewise, when `σ := RingHom.id 𝕜`, the notation `E →WOT[𝕜] F` i
s available.
-/
structure ContinuousLinearMapWOT {𝕜₁ 𝕜₂ : Type*} [Semiring 𝕜₁] [Semiring 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂)
    (E F : Type*) [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E] [AddCommGroup F]
    [TopologicalSpace F] [Module 𝕜₂ F] where
  /-- Construct an element of `E →SWOT[σ] F` from a continuous linear map. -/
  ofCLM ::
  /-- The continuous linear map underlying an element of `E →SWOT[σ] F`. -/
  toCLM : E →SL[σ] F


namespace ContinuousLinearMapWOT

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `ofCLM A` being printed as `{ toCLM := x }` by `delabStructureInstance`. -/
@[app_delab ContinuousLinearMapWOT.ofCLM]
meta def delabOfCLM : Delab := delabApp

@[inherit_doc]
notation:25 E " →SWOT[" σ "] " F => ContinuousLinearMapWOT σ E F

@[inherit_doc]
notation:25 E " →WOT[" 𝕜 "] " F => ContinuousLinearMapWOT (RingHom.id 𝕜) E F

end Notation

variable {𝕜₁ 𝕜₂ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂]
  {σ : 𝕜₁ →+* 𝕜₂}
  {E F : Type*}
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E]
  [AddCommGroup F] [TopologicalSpace F] [Module 𝕜₂ F]

local notation X "⋆" => StrongDual 𝕜₂ X

/-!
### Basic properties common with `E →L[𝕜] F`

The section copies basic non-topological properties of `E →L[𝕜] F` over to `E →WOT[𝕜] F`, such as
the module structure, `FunLike`, etc.
-/
section Basic

/-- The equivalence between `ContinuousLinearMapWOT` and `ContinuousLinearMap`. -/
@[simps]
/-
**ContinuousLinearMapWOT.equiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMapWOT
`。
形式化陈述：equiv : (E ->SWOT[σ] F) ≃ (E ->SL[σ] F) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `ContinuousLinearMapWOT` and `ContinuousLinearMap`.
-/
def equiv : (E →SWOT[σ] F) ≃ (E →SL[σ] F) where
  toFun := toCLM
  invFun := ofCLM
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
/-
**ContinuousLinearMapWOT.toCLM_injective** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLi
nearMapWOT`。
形式化陈述：toCLM_injective : Function.Injective (toCLM : (E ->SWOT[σ] F) -> E ->SL[σ]
 F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma toCLM_injective : Function.Injective (toCLM : (E →SWOT[σ] F) → E →SL[σ] F) :=
  equiv.injective

@[simp]
/-
**ContinuousLinearMapWOT.toCLM_surjective** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousL
inearMapWOT`。
形式化陈述：toCLM_surjective : Function.Surjective (toCLM : (E ->SWOT[σ] F) -> E ->SL[
σ] F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
lemma toCLM_surjective : Function.Surjective (toCLM : (E →SWOT[σ] F) → E →SL[σ] F) :=
  equiv.surjective
/-
**ContinuousLinearMapWOT.toCLM_bijective** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLi
nearMapWOT`。
形式化陈述：toCLM_bijective : Function.Bijective (toCLM : (E ->SWOT[σ] F) -> E ->SL[σ]
 F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
lemma toCLM_bijective : Function.Bijective (toCLM : (E →SWOT[σ] F) → E →SL[σ] F) :=
  equiv.bijective

@[simp]
/-
**ContinuousLinearMapWOT.ofCLM_injective** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLi
nearMapWOT`。
形式化陈述：ofCLM_injective : Function.Injective (ofCLM : (E ->SL[σ] F) -> E ->SWOT[σ]
 F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma ofCLM_injective : Function.Injective (ofCLM : (E →SL[σ] F) → E →SWOT[σ] F) :=
  equiv.symm.injective

@[simp]
/-
**ContinuousLinearMapWOT.ofCLM_surjective** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousL
inearMapWOT`。
形式化陈述：ofCLM_surjective : Function.Surjective (ofCLM : (E ->SL[σ] F) -> E ->SWOT[
σ] F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma ofCLM_surjective : Function.Surjective (ofCLM : (E →SL[σ] F) → E →SWOT[σ] F) :=
  equiv.symm.surjective
/-
**ContinuousLinearMapWOT.ofCLM_bijective** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLi
nearMapWOT`。
形式化陈述：ofCLM_bijective : Function.Bijective (ofCLM : (E ->SL[σ] F) -> E ->SWOT[σ]
 F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma ofCLM_bijective : Function.Bijective (ofCLM : (E →SL[σ] F) → E →SWOT[σ] F) :=
  equiv.symm.bijective
/-
**ContinuousLinearMapWOT.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousL
inearMapWOT`。
形式化陈述：instAddCommGroup [IsTopologicalAddGroup F] : AddCommGroup (E ->SWOT[σ] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroup [IsTopologicalAddGroup F] :
    AddCommGroup (E →SWOT[σ] F) :=
  equiv.addCommGroup
/-
**ContinuousLinearMapWOT.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap
WOT`。
形式化陈述：instSMul {S : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F] [ContinuousC
onstSMul S F] : SMul S (E ->SWOT[σ] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul {S : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F] [ContinuousConstSMul S F] :
    SMul S (E →SWOT[σ] F) :=
  equiv.smul S
/-
**ContinuousLinearMapWOT.instModule** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearM
apWOT`。
形式化陈述：instModule {S : Type*} [Semiring S] [Module S F] [SMulCommClass 𝕜₂ S F] [C
ontinuousConstSMul S F] [IsTopologicalAddGroup F] : Module S (E ->SWOT[σ] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule {S : Type*} [Semiring S] [Module S F] [SMulCommClass 𝕜₂ S F]
    [ContinuousConstSMul S F] [IsTopologicalAddGroup F] :
    Module S (E →SWOT[σ] F) :=
  equiv.module S
/-
**ContinuousLinearMapWOT.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `Continuous
LinearMapWOT`。
形式化陈述：instIsScalarTower {S T : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F] [
ContinuousConstSMul S F] [DistribSMul T F] [SMulCommClass 𝕜₂ T F] [ContinuousCon
stSMul T F] [SMul S T] [IsScalarTower S T F] : IsScalarTower S T (E ->SWOT[σ] F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.isScalarTower`：∀ (M : Type u_1) (N : Type u_2) {α : Type u_4} {β :
 Type u_5} [inst : SMul M N] [inst_1 : SMul M β] [inst_2 : SMul N β]   (e : α ≃ 
β) [IsSca…
-/
instance instIsScalarTower {S T : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F]
    [ContinuousConstSMul S F] [DistribSMul T F] [SMulCommClass 𝕜₂ T F]
    [ContinuousConstSMul T F] [SMul S T] [IsScalarTower S T F] :
    IsScalarTower S T (E →SWOT[σ] F) :=
  equiv.isScalarTower S T
/-
**ContinuousLinearMapWOT.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `Continuous
LinearMapWOT`。
形式化陈述：instSMulCommClass {S T : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F] [
ContinuousConstSMul S F] [DistribSMul T F] [SMulCommClass 𝕜₂ T F] [ContinuousCon
stSMul T F] [SMulCommClass S T F] : SMulCommClass S T (E ->SWOT[σ] F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.smulCommClass`：∀ (M : Type u_1) (N : Type u_2) {α : Type u_4} {β :
 Type u_5} [inst : SMul M β] [inst_1 : SMul N β] (e : α ≃ β)   [SMulCommClass M 
N β], SMu…
-/
instance instSMulCommClass {S T : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F]
    [ContinuousConstSMul S F] [DistribSMul T F] [SMulCommClass 𝕜₂ T F]
    [ContinuousConstSMul T F] [SMulCommClass S T F] :
    SMulCommClass S T (E →SWOT[σ] F) :=
  equiv.smulCommClass S T
/-
**ContinuousLinearMapWOT.instIsCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `Continuo
usLinearMapWOT`。
形式化陈述：instIsCentralScalar {S : Type*} [Semiring S] [Module S F] [SMulCommClass 𝕜
₂ S F] [ContinuousConstSMul S F] [Module Sᵐᵒᵖ F] [IsCentralScalar S F] : IsCentr
alScalar S (E ->SWOT[σ] F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.isCentralScalar`：∀ (M : Type u_1) {α : Type u_4} {β : Type u_5} [i
nst : SMul M β] [inst_1 : SMul Mᵐᵒᵖ β] (e : α ≃ β)   [IsCentralScalar M β], IsCe
ntralScalar…
· 使用定理 `SMulCommClass.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul N α] [inst_2 : SMul Nᵐᵒᵖ α]   [IsCentralScalar N
 α] [SMulCom…
-/
instance instIsCentralScalar {S : Type*} [Semiring S] [Module S F] [SMulCommClass 𝕜₂ S F]
    [ContinuousConstSMul S F] [Module Sᵐᵒᵖ F] [IsCentralScalar S F] :
    IsCentralScalar S (E →SWOT[σ] F) :=
  equiv.isCentralScalar S
/-
**ContinuousLinearMapWOT.instRing** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap
WOT`。
形式化陈述：instRing [IsTopologicalAddGroup E] : Ring (E ->WOT[𝕜₁] E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRing [IsTopologicalAddGroup E] : Ring (E →WOT[𝕜₁] E) :=
  equiv.ring
/-
**ContinuousLinearMapWOT.instAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinear
MapWOT`。
形式化陈述：instAlgebra {S : Type*} [CommSemiring S] [Module S E] [SMulCommClass 𝕜₁ S 
E] [SMul S 𝕜₁] [IsScalarTower S 𝕜₁ E] [ContinuousConstSMul S E] [IsTopologicalAd
dGroup E] : Algebra S (E ->WOT[𝕜₁] E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAlgebra {S : Type*} [CommSemiring S] [Module S E] [SMulCommClass 𝕜₁ S E] [SMul S 𝕜₁]
    [IsScalarTower S 𝕜₁ E] [ContinuousConstSMul S E] [IsTopologicalAddGroup E] :
    Algebra S (E →WOT[𝕜₁] E) :=
  equiv.algebra S

/-- The additive group equivalence between `ContinuousLinearMapWOT` and `ContinuousLinearMap`. -/
@[simps!]
/-
**ContinuousLinearMapWOT.addEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap
WOT`。
形式化陈述：addEquiv [IsTopologicalAddGroup F] : (E ->SWOT[σ] F) ≃+ (E ->SL[σ] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive group equivalence between `ContinuousLinearMapWOT` and `ContinuousL
inearMap`.
-/
def addEquiv [IsTopologicalAddGroup F] : (E →SWOT[σ] F) ≃+ (E →SL[σ] F) :=
  equiv.addEquiv

/-- The linear equivalence between `ContinuousLinearMapWOT` and `ContinuousLinearMap`. -/
@[simps!]
/-
**ContinuousLinearMapWOT.linearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinear
MapWOT`。
形式化陈述：linearEquiv (S : Type*) [Semiring S] [Module S F] [SMulCommClass 𝕜₂ S F] [
ContinuousConstSMul S F] [IsTopologicalAddGroup F] : (E ->SWOT[σ] F) ≃ₗ[S] (E ->
SL[σ] F)
参数：S : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equivalence between `ContinuousLinearMapWOT` and `ContinuousLinearMap
`.
-/
def linearEquiv (S : Type*) [Semiring S] [Module S F] [SMulCommClass 𝕜₂ S F]
    [ContinuousConstSMul S F] [IsTopologicalAddGroup F] :
    (E →SWOT[σ] F) ≃ₗ[S] (E →SL[σ] F) :=
  equiv.linearEquiv S

/-- The ring equivalence between `ContinuousLinearMapWOT` and `ContinuousLinearMap`. -/
@[simps!]
/-
**ContinuousLinearMapWOT.ringEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMa
pWOT`。
形式化陈述：ringEquiv [IsTopologicalAddGroup E] : (E ->WOT[𝕜₁] E) ≃+* (E ->L[𝕜₁] E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring equivalence between `ContinuousLinearMapWOT` and `ContinuousLinearMap`.
-/
def ringEquiv [IsTopologicalAddGroup E] : (E →WOT[𝕜₁] E) ≃+* (E →L[𝕜₁] E) :=
  equiv.ringEquiv

/-- The algebra equivalence between `ContinuousLinearMapWOT` and `ContinuousLinearMap`. -/
@[simps!]
/-
**ContinuousLinearMapWOT.algEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap
WOT`。
形式化陈述：algEquiv (S : Type*) [CommSemiring S] [Module S E] [SMulCommClass 𝕜₁ S E] 
[SMul S 𝕜₁] [IsScalarTower S 𝕜₁ E] [ContinuousConstSMul S E] [IsTopologicalAddGr
oup E] : (E ->WOT[𝕜₁] E) ≃ₐ[S] (E ->L[𝕜₁] E)
参数：S : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra equivalence between `ContinuousLinearMapWOT` and `ContinuousLinearMa
p`.
-/
def algEquiv (S : Type*) [CommSemiring S] [Module S E] [SMulCommClass 𝕜₁ S E] [SMul S 𝕜₁]
    [IsScalarTower S 𝕜₁ E] [ContinuousConstSMul S E] [IsTopologicalAddGroup E] :
    (E →WOT[𝕜₁] E) ≃ₐ[S] (E →L[𝕜₁] E) :=
  equiv.algEquiv S
/-
**ContinuousLinearMapWOT.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinear
MapWOT`。
形式化陈述：instFunLike : FunLike (E ->SWOT[σ] F) E F where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (E →SWOT[σ] F) E F where
  coe f := toCLM f
  coe_injective := DFunLike.coe_injective.comp toCLM_injective

@[simp]
/-
**ContinuousLinearMapWOT.coe_toCLM** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMa
pWOT`。
形式化陈述：coe_toCLM (A : E ->SWOT[σ] F) : ⇑(toCLM A : E ->SL[σ] F) = A
参数：A : E ->SWOT[σ] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_toCLM (A : E →SWOT[σ] F) : ⇑(toCLM A : E →SL[σ] F) = A := rfl

@[simp]
/-
**ContinuousLinearMapWOT.coe_ofCLM** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMa
pWOT`。
形式化陈述：coe_ofCLM (A : E ->SL[σ] F) : ⇑(ofCLM A : E ->SWOT[σ] F) = A
参数：A : E ->SL[σ] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_ofCLM (A : E →SL[σ] F) : ⇑(ofCLM A : E →SWOT[σ] F) = A := rfl
/-
**ContinuousLinearMapWOT.instContinuousLinearMapClass** 是 Mathlib 中的一个实例，位于命名空间 
`ContinuousLinearMapWOT`。
形式化陈述：instContinuousLinearMapClass : ContinuousSemilinearMapClass (E ->SWOT[σ] F
) σ E F where map_add f x y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousLinearMap.map_smulₛₗ`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
instance instContinuousLinearMapClass : ContinuousSemilinearMapClass (E →SWOT[σ] F) σ E F where
  map_add f x y := by simp [← coe_toCLM]
  map_smulₛₗ f r x := by simp [← coe_toCLM]
  map_continuous f := f.toCLM.continuous

@[simp]
/-
**ContinuousLinearMapWOT.ofCLM_toCLM** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinear
MapWOT`。
形式化陈述：ofCLM_toCLM (A : E ->SWOT[σ] F) : ofCLM (toCLM A) = A
参数：A : E ->SWOT[σ] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofCLM_toCLM (A : E →SWOT[σ] F) : ofCLM (toCLM A) = A := rfl

-- not marked `simp` because Lean just sees `A` on the left-hand side
/-
**ContinuousLinearMapWOT.toCLM_ofCLM** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinear
MapWOT`。
形式化陈述：toCLM_ofCLM (A : E ->SL[σ] F) : toCLM (ofCLM A) = A
参数：A : E ->SL[σ] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toCLM_ofCLM (A : E →SL[σ] F) : toCLM (ofCLM A) = A := rfl

@[simp]
/-
**ContinuousLinearMapWOT.toCLM_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinear
MapWOT`。
形式化陈述：toCLM_apply {A : E ->SWOT[σ] F} {x : E} : toCLM A x = A x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toCLM_apply {A : E →SWOT[σ] F} {x : E} : toCLM A x = A x := rfl

@[simp]
/-
**ContinuousLinearMapWOT.ofCLM_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinear
MapWOT`。
形式化陈述：ofCLM_apply {A : E ->SL[σ] F} {x : E} : ofCLM A x = A x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofCLM_apply {A : E →SL[σ] F} {x : E} : ofCLM A x = A x := rfl

@[deprecated (since := "2026-04-10")] alias _root_.ContinuousLinearMap.toWOT_apply := ofCLM_apply

@[ext]
/-
**ContinuousLinearMapWOT.ext** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMapWOT`。
形式化陈述：ext {A B : E ->SWOT[σ] F} (h : forall x, A x = B x) : A = B
参数：h : forall x, A x = B x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMapWOT.toCLM_injective`：toCLM_injective : Function.Injec
tive (toCLM : (E ->SWOT[σ] F) -> E ->SL[σ] F)
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
-/
lemma ext {A B : E →SWOT[σ] F} (h : ∀ x, A x = B x) : A = B :=
  toCLM_injective <| ContinuousLinearMap.ext h

-- This `ext` lemma is set at a lower priority than the default of 1000, so that the
-- version with an inner product (`ContinuousLinearMapWOT.ext_inner`) takes precedence
-- in the case of Hilbert spaces.
@[ext 900]
/-
**ContinuousLinearMapWOT.ext_dual** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMap
WOT`。
形式化陈述：ext_dual [H : SeparatingDual 𝕜₂ F] {A B : E ->SWOT[σ] F} (h : forall x (y 
: F⋆), y (A x) = y (B x)) : A = B
参数：h : forall x (y : F⋆), y (A x) = y (B x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `separatingDual_iff_injective`：∀ {R : Type u_1} {V : Type u_2} [inst : Fi
eld R] [inst_1 : AddCommGroup V] [inst_2 : TopologicalSpace R]   [inst_3 : Topol
ogicalSpace V] [in…
-/
lemma ext_dual [H : SeparatingDual 𝕜₂ F] {A B : E →SWOT[σ] F}
    (h : ∀ x (y : F⋆), y (A x) = y (B x)) : A = B := by
  simp_rw [ContinuousLinearMapWOT.ext_iff, ← (separatingDual_iff_injective.mp H).eq_iff,
    LinearMap.ext_iff]
  exact h

section SMul

variable {S : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F] [ContinuousConstSMul S F]

/-
**ContinuousLinearMapWOT.ofCLM_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
apWOT`。
形式化陈述：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} [inst : NormedField 𝕜₁] [inst_1 : Normed
Field 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_3}   {F : Type u_4} [inst_2 : AddCommGroup
 E] [inst_3 : TopologicalSpace E] [inst_4 : _root_.Module 𝕜₁ E]   [inst_5 : AddC
ommGroup F] [inst_6 : TopologicalSpace F] [inst_7 : _root_.Module 𝕜₂ F] {S : Typ
e u_5}   [inst_8 : DistribSMul S F] [inst_9 : SMulCommClass 𝕜₂ S F] [inst_10 : C
ontinuousConstSMul S F] {c : S}   {f : E →SL[σ] F}, ContinuousLinearMapWOT.ofCLM
 (c • f) = c • ContinuousLinearMapWOT.ofCLM f
参数：c • f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofCLM_smul {c : S} {f : E →SL[σ] F} : ofCLM (c • f) = c • ofCLM f := rfl
/-
**ContinuousLinearMapWOT.toCLM_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
apWOT`。
形式化陈述：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} [inst : NormedField 𝕜₁] [inst_1 : Normed
Field 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_3}   {F : Type u_4} [inst_2 : AddCommGroup
 E] [inst_3 : TopologicalSpace E] [inst_4 : _root_.Module 𝕜₁ E]   [inst_5 : AddC
ommGroup F] [inst_6 : TopologicalSpace F] [inst_7 : _root_.Module 𝕜₂ F] {S : Typ
e u_5}   [inst_8 : DistribSMul S F] [inst_9 : SMulCommClass 𝕜₂ S F] [inst_10 : C
ontinuousConstSMul S F] {c : S}   {f : E →SWOT[σ] F}, (c • f).toCLM = c • f.toCL
M
参数：c • f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toCLM_smul {c : S} {f : E →SWOT[σ] F} : toCLM (c • f) = c • toCLM f := rfl
/-
**ContinuousLinearMapWOT.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
apWOT`。
形式化陈述：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} [inst : NormedField 𝕜₁] [inst_1 : Normed
Field 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_3}   {F : Type u_4} [inst_2 : AddCommGroup
 E] [inst_3 : TopologicalSpace E] [inst_4 : _root_.Module 𝕜₁ E]   [inst_5 : AddC
ommGroup F] [inst_6 : TopologicalSpace F] [inst_7 : _root_.Module 𝕜₂ F] {S : Typ
e u_5}   [inst_8 : DistribSMul S F] [inst_9 : SMulCommClass 𝕜₂ S F] [inst_10 : C
ontinuousConstSMul S F] {f : E →SWOT[σ] F}   (c : S) (x : E), (c • f) x = c • f 
x
参数：c : S；x : E；c • f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma smul_apply {f : E →SWOT[σ] F} (c : S) (x : E) : (c • f) x = c • (f x) := rfl

end SMul

section Algebra

variable {S : Type*} [CommSemiring S] [Module S E] [SMulCommClass 𝕜₁ S E] [SMul S 𝕜₁]
    [IsScalarTower S 𝕜₁ E] [ContinuousConstSMul S E] [IsTopologicalAddGroup E]

/-
**ContinuousLinearMapWOT.toCLM_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMapWOT`。
形式化陈述：∀ {𝕜₁ : Type u_1} [inst : NormedField 𝕜₁] {E : Type u_3} [inst_1 : AddComm
Group E] [inst_2 : TopologicalSpace E]   [inst_3 : _root_.Module 𝕜₁ E] {S : Type
 u_5} [inst_4 : CommSemiring S] [inst_5 : _root_.Module S E]   [inst_6 : SMulCom
mClass 𝕜₁ S E] [inst_7 : SMul S 𝕜₁] [inst_8 : IsScalarTower S 𝕜₁ E]   [inst_9 : 
ContinuousConstSMul S E] [inst_10 : IsTopologicalAddGroup E] (c : S),   ((algebr
aMap S (E →WOT[𝕜₁] E)) c).toCLM = (algebraMap S (E →L[𝕜₁] E)) c
参数：c : S；(algebraMap S (E →WOT[𝕜₁] E)) c；algebraMap S (E →L[𝕜₁] E)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toCLM_algebraMap (c : S) :
    toCLM (algebraMap S (E →WOT[𝕜₁] E) c) = algebraMap S (E →L[𝕜₁] E) c :=
  rfl
/-
**ContinuousLinearMapWOT.ofCLM_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMapWOT`。
形式化陈述：∀ {𝕜₁ : Type u_1} [inst : NormedField 𝕜₁] {E : Type u_3} [inst_1 : AddComm
Group E] [inst_2 : TopologicalSpace E]   [inst_3 : _root_.Module 𝕜₁ E] {S : Type
 u_5} [inst_4 : CommSemiring S] [inst_5 : _root_.Module S E]   [inst_6 : SMulCom
mClass 𝕜₁ S E] [inst_7 : SMul S 𝕜₁] [inst_8 : IsScalarTower S 𝕜₁ E]   [inst_9 : 
ContinuousConstSMul S E] [inst_10 : IsTopologicalAddGroup E] (c : S),   Continuo
usLinearMapWOT.ofCLM ((algebraMap S (E →L[𝕜₁] E)) c) = (algebraMap S (E →WOT[𝕜₁]
 E)) c
参数：c : S；(algebraMap S (E →L[𝕜₁] E)) c；algebraMap S (E →WOT[𝕜₁] E)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
@[simp] lemma ofCLM_algebraMap (c : S) :
    ofCLM (algebraMap S (E →L[𝕜₁] E) c) = algebraMap S (E →WOT[𝕜₁] E) c :=
  rfl
/-
**ContinuousLinearMapWOT.algebraMapCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMapWOT`。
形式化陈述：∀ {𝕜₁ : Type u_1} [inst : NormedField 𝕜₁] {E : Type u_3} [inst_1 : AddComm
Group E] [inst_2 : TopologicalSpace E]   [inst_3 : _root_.Module 𝕜₁ E] {S : Type
 u_5} [inst_4 : CommSemiring S] [inst_5 : _root_.Module S E]   [inst_6 : SMulCom
mClass 𝕜₁ S E] [inst_7 : SMul S 𝕜₁] [inst_8 : IsScalarTower S 𝕜₁ E]   [inst_9 : 
ContinuousConstSMul S E] [inst_10 : IsTopologicalAddGroup E] (c : S) (x : E),   
((algebraMap S (E →WOT[𝕜₁] E)) c) x = c • x
参数：c : S；x : E；(algebraMap S (E →WOT[𝕜₁] E)) c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma algebraMapCLM_apply (c : S) (x : E) :
    (algebraMap S (E →WOT[𝕜₁] E) c) x = c • x :=
  rfl

end Algebra

variable [IsTopologicalAddGroup F]

/-
**ContinuousLinearMapWOT.ofCLM_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
apWOT`。
形式化陈述：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} [inst : NormedField 𝕜₁] [inst_1 : Normed
Field 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_3}   {F : Type u_4} [inst_2 : AddCommGroup
 E] [inst_3 : TopologicalSpace E] [inst_4 : _root_.Module 𝕜₁ E]   [inst_5 : AddC
ommGroup F] [inst_6 : TopologicalSpace F] [inst_7 : _root_.Module 𝕜₂ F]   [inst_
8 : IsTopologicalAddGroup F], ContinuousLinearMapWOT.ofCLM 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofCLM_zero : ofCLM (0 : E →SL[σ] F) = 0 := rfl
/-
**ContinuousLinearMapWOT.ofCLM_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
pWOT`。
形式化陈述：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} [inst : NormedField 𝕜₁] [inst_1 : Normed
Field 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_3}   {F : Type u_4} [inst_2 : AddCommGroup
 E] [inst_3 : TopologicalSpace E] [inst_4 : _root_.Module 𝕜₁ E]   [inst_5 : AddC
ommGroup F] [inst_6 : TopologicalSpace F] [inst_7 : _root_.Module 𝕜₂ F]   [inst_
8 : IsTopologicalAddGroup F] {f g : E →SL[σ] F},   ContinuousLinearMapWOT.ofCLM 
(f + g) = ContinuousLinearMapWOT.ofCLM f + ContinuousLinearMapWOT.ofCLM g
参数：f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
@[simp] lemma ofCLM_add {f g : E →SL[σ] F} : ofCLM (f + g) = ofCLM f + ofCLM g := rfl
/-
**ContinuousLinearMapWOT.ofCLM_sub** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
pWOT`。
形式化陈述：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} [inst : NormedField 𝕜₁] [inst_1 : Normed
Field 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_3}   {F : Type u_4} [inst_2 : AddCommGroup
 E] [inst_3 : TopologicalSpace E] [inst_4 : _root_.Module 𝕜₁ E]   [inst_5 : AddC
ommGroup F] [inst_6 : TopologicalSpace F] [inst_7 : _root_.Module 𝕜₂ F]   [inst_
8 : IsTopologicalAddGroup F] {f g : E →SL[σ] F},   ContinuousLinearMapWOT.ofCLM 
(f - g) = ContinuousLinearMapWOT.ofCLM f - ContinuousLinearMapWOT.ofCLM g
参数：f - g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofCLM_sub {f g : E →SL[σ] F} : ofCLM (f - g) = ofCLM f - ofCLM g := rfl
/-
**ContinuousLinearMapWOT.ofCLM_neg** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
pWOT`。
形式化陈述：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} [inst : NormedField 𝕜₁] [inst_1 : Normed
Field 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_3}   {F : Type u_4} [inst_2 : AddCommGroup
 E] [inst_3 : TopologicalSpace E] [inst_4 : _root_.Module 𝕜₁ E]   [inst_5 : AddC
ommGroup F] [inst_6 : TopologicalSpace F] [inst_7 : _root_.Module 𝕜₂ F]   [inst_
8 : IsTopologicalAddGroup F] {f : E →SL[σ] F},   ContinuousLinearMapWOT.ofCLM (-
f) = -ContinuousLinearMapWOT.ofCLM f
参数：-f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofCLM_neg {f : E →SL[σ] F} : ofCLM (-f) = -ofCLM f := rfl
/-
**ContinuousLinearMapWOT.ofCLM_mul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
pWOT`。
形式化陈述：∀ {𝕜₂ : Type u_2} [inst : NormedField 𝕜₂] {F : Type u_4} [inst_1 : AddComm
Group F] [inst_2 : TopologicalSpace F]   [inst_3 : _root_.Module 𝕜₂ F] [inst_4 :
 IsTopologicalAddGroup F] (f g : F →L[𝕜₂] F),   ContinuousLinearMapWOT.ofCLM (f 
* g) = ContinuousLinearMapWOT.ofCLM f * ContinuousLinearMapWOT.ofCLM g
参数：f g : F →L[𝕜₂] F；f * g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofCLM_mul (f g : F →L[𝕜₂] F) : ofCLM (f * g) = ofCLM f * ofCLM g := rfl
/-
**ContinuousLinearMapWOT.ofCLM_one** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
pWOT`。
形式化陈述：∀ {𝕜₂ : Type u_2} [inst : NormedField 𝕜₂] {F : Type u_4} [inst_1 : AddComm
Group F] [inst_2 : TopologicalSpace F]   [inst_3 : _root_.Module 𝕜₂ F] [inst_4 :
 IsTopologicalAddGroup F], ContinuousLinearMapWOT.ofCLM 1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofCLM_one : ofCLM (1 : F →L[𝕜₂] F) = 1 := rfl
/-
**ContinuousLinearMapWOT.ofCLM_pow** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
pWOT`。
形式化陈述：∀ {𝕜₂ : Type u_2} [inst : NormedField 𝕜₂] {F : Type u_4} [inst_1 : AddComm
Group F] [inst_2 : TopologicalSpace F]   [inst_3 : _root_.Module 𝕜₂ F] [inst_4 :
 IsTopologicalAddGroup F] (f : F →L[𝕜₂] F) (n : ℕ),   ContinuousLinearMapWOT.ofC
LM (f ^ n) = ContinuousLinearMapWOT.ofCLM f ^ n
参数：f : F →L[𝕜₂] F；n : ℕ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
@[simp] lemma ofCLM_pow (f : F →L[𝕜₂] F) (n : ℕ) : ofCLM (f ^ n) = ofCLM f ^ n := rfl
/-
**ContinuousLinearMapWOT.ofCLM_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMapWOT`。
形式化陈述：∀ {𝕜₂ : Type u_2} [inst : NormedField 𝕜₂] {F : Type u_4} [inst_1 : AddComm
Group F] [inst_2 : TopologicalSpace F]   [inst_3 : _root_.Module 𝕜₂ F] [inst_4 :
 IsTopologicalAddGroup F] (n : ℕ), ContinuousLinearMapWOT.ofCLM ↑n = ↑n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
@[simp] lemma ofCLM_natCast (n : ℕ) : ofCLM (n : F →L[𝕜₂] F) = n := rfl
/-
**ContinuousLinearMapWOT.ofCLM_intCast** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMapWOT`。
形式化陈述：∀ {𝕜₂ : Type u_2} [inst : NormedField 𝕜₂] {F : Type u_4} [inst_1 : AddComm
Group F] [inst_2 : TopologicalSpace F]   [inst_3 : _root_.Module 𝕜₂ F] [inst_4 :
 IsTopologicalAddGroup F] (n : ℤ), ContinuousLinearMapWOT.ofCLM ↑n = ↑n
参数：n : ℤ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofCLM_intCast (n : ℤ) : ofCLM (n : F →L[𝕜₂] F) = n := rfl
/-
**ContinuousLinearMapWOT.toCLM_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
apWOT`。
形式化陈述：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} [inst : NormedField 𝕜₁] [inst_1 : Normed
Field 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_3}   {F : Type u_4} [inst_2 : AddCommGroup
 E] [inst_3 : TopologicalSpace E] [inst_4 : _root_.Module 𝕜₁ E]   [inst_5 : AddC
ommGroup F] [inst_6 : TopologicalSpace F] [inst_7 : _root_.Module 𝕜₂ F]   [inst_
8 : IsTopologicalAddGroup F], ContinuousLinearMapWOT.toCLM 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toCLM_zero : toCLM (0 : E →SWOT[σ] F) = 0 := rfl
/-
**ContinuousLinearMapWOT.toCLM_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
pWOT`。
形式化陈述：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} [inst : NormedField 𝕜₁] [inst_1 : Normed
Field 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_3}   {F : Type u_4} [inst_2 : AddCommGroup
 E] [inst_3 : TopologicalSpace E] [inst_4 : _root_.Module 𝕜₁ E]   [inst_5 : AddC
ommGroup F] [inst_6 : TopologicalSpace F] [inst_7 : _root_.Module 𝕜₂ F]   [inst_
8 : IsTopologicalAddGroup F] {f g : E →SWOT[σ] F}, (f + g).toCLM = f.toCLM + g.t
oCLM
参数：f + g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toCLM_add {f g : E →SWOT[σ] F} : toCLM (f + g) = toCLM f + toCLM g := rfl
/-
**ContinuousLinearMapWOT.toCLM_sub** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
pWOT`。
形式化陈述：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} [inst : NormedField 𝕜₁] [inst_1 : Normed
Field 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_3}   {F : Type u_4} [inst_2 : AddCommGroup
 E] [inst_3 : TopologicalSpace E] [inst_4 : _root_.Module 𝕜₁ E]   [inst_5 : AddC
ommGroup F] [inst_6 : TopologicalSpace F] [inst_7 : _root_.Module 𝕜₂ F]   [inst_
8 : IsTopologicalAddGroup F] {f g : E →SWOT[σ] F}, (f - g).toCLM = f.toCLM - g.t
oCLM
参数：f - g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toCLM_sub {f g : E →SWOT[σ] F} : toCLM (f - g) = toCLM f - toCLM g := rfl
/-
**ContinuousLinearMapWOT.toCLM_neg** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
pWOT`。
形式化陈述：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} [inst : NormedField 𝕜₁] [inst_1 : Normed
Field 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_3}   {F : Type u_4} [inst_2 : AddCommGroup
 E] [inst_3 : TopologicalSpace E] [inst_4 : _root_.Module 𝕜₁ E]   [inst_5 : AddC
ommGroup F] [inst_6 : TopologicalSpace F] [inst_7 : _root_.Module 𝕜₂ F]   [inst_
8 : IsTopologicalAddGroup F] {f : E →SWOT[σ] F}, (-f).toCLM = -f.toCLM
参数：-f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toCLM_neg {f : E →SWOT[σ] F} : toCLM (-f) = -toCLM f := rfl
/-
**ContinuousLinearMapWOT.toCLM_mul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
pWOT`。
形式化陈述：∀ {𝕜₂ : Type u_2} [inst : NormedField 𝕜₂] {F : Type u_4} [inst_1 : AddComm
Group F] [inst_2 : TopologicalSpace F]   [inst_3 : _root_.Module 𝕜₂ F] [inst_4 :
 IsTopologicalAddGroup F] (f g : F →WOT[𝕜₂] F),   (f * g).toCLM = f.toCLM * g.to
CLM
参数：f g : F →WOT[𝕜₂] F；f * g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toCLM_mul (f g : F →WOT[𝕜₂] F) : toCLM (f * g) = toCLM f * toCLM g := rfl
/-
**ContinuousLinearMapWOT.toCLM_one** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
pWOT`。
形式化陈述：∀ {𝕜₂ : Type u_2} [inst : NormedField 𝕜₂] {F : Type u_4} [inst_1 : AddComm
Group F] [inst_2 : TopologicalSpace F]   [inst_3 : _root_.Module 𝕜₂ F] [inst_4 :
 IsTopologicalAddGroup F], ContinuousLinearMapWOT.toCLM 1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toCLM_one : toCLM (1 : F →WOT[𝕜₂] F) = 1 := rfl
/-
**ContinuousLinearMapWOT.toCLM_pow** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
pWOT`。
形式化陈述：∀ {𝕜₂ : Type u_2} [inst : NormedField 𝕜₂] {F : Type u_4} [inst_1 : AddComm
Group F] [inst_2 : TopologicalSpace F]   [inst_3 : _root_.Module 𝕜₂ F] [inst_4 :
 IsTopologicalAddGroup F] (f : F →WOT[𝕜₂] F) (n : ℕ),   (f ^ n).toCLM = f.toCLM 
^ n
参数：f : F →WOT[𝕜₂] F；n : ℕ；f ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toCLM_pow (f : F →WOT[𝕜₂] F) (n : ℕ) : (f ^ n).toCLM = f.toCLM ^ n := rfl
/-
**ContinuousLinearMapWOT.toCLM_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMapWOT`。
形式化陈述：∀ {𝕜₂ : Type u_2} [inst : NormedField 𝕜₂] {F : Type u_4} [inst_1 : AddComm
Group F] [inst_2 : TopologicalSpace F]   [inst_3 : _root_.Module 𝕜₂ F] [inst_4 :
 IsTopologicalAddGroup F] (n : ℕ), (↑n).toCLM = ↑n
参数：n : ℕ；↑n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toCLM_natCast (n : ℕ) : (n : F →WOT[𝕜₂] F).toCLM = n := rfl
/-
**ContinuousLinearMapWOT.toCLM_intCast** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMapWOT`。
形式化陈述：∀ {𝕜₂ : Type u_2} [inst : NormedField 𝕜₂] {F : Type u_4} [inst_1 : AddComm
Group F] [inst_2 : TopologicalSpace F]   [inst_3 : _root_.Module 𝕜₂ F] [inst_4 :
 IsTopologicalAddGroup F] (n : ℤ), (↑n).toCLM = ↑n
参数：n : ℤ；↑n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toCLM_intCast (n : ℤ) : (n : F →WOT[𝕜₂] F).toCLM = n := rfl
/-
**ContinuousLinearMapWOT.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
apWOT`。
形式化陈述：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} [inst : NormedField 𝕜₁] [inst_1 : Normed
Field 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_3}   {F : Type u_4} [inst_2 : AddCommGroup
 E] [inst_3 : TopologicalSpace E] [inst_4 : _root_.Module 𝕜₁ E]   [inst_5 : AddC
ommGroup F] [inst_6 : TopologicalSpace F] [inst_7 : _root_.Module 𝕜₂ F]   [inst_
8 : IsTopologicalAddGroup F] (x : E), 0 x = 0
参数：x : E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma zero_apply (x : E) : (0 : E →SWOT[σ] F) x = 0 := rfl
/-
**ContinuousLinearMapWOT.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
pWOT`。
形式化陈述：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} [inst : NormedField 𝕜₁] [inst_1 : Normed
Field 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_3}   {F : Type u_4} [inst_2 : AddCommGroup
 E] [inst_3 : TopologicalSpace E] [inst_4 : _root_.Module 𝕜₁ E]   [inst_5 : AddC
ommGroup F] [inst_6 : TopologicalSpace F] [inst_7 : _root_.Module 𝕜₂ F]   [inst_
8 : IsTopologicalAddGroup F] {f g : E →SWOT[σ] F} (x : E), (f + g) x = f x + g x
参数：x : E；f + g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma add_apply {f g : E →SWOT[σ] F} (x : E) : (f + g) x = f x + g x := rfl
/-
**ContinuousLinearMapWOT.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
pWOT`。
形式化陈述：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} [inst : NormedField 𝕜₁] [inst_1 : Normed
Field 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_3}   {F : Type u_4} [inst_2 : AddCommGroup
 E] [inst_3 : TopologicalSpace E] [inst_4 : _root_.Module 𝕜₁ E]   [inst_5 : AddC
ommGroup F] [inst_6 : TopologicalSpace F] [inst_7 : _root_.Module 𝕜₂ F]   [inst_
8 : IsTopologicalAddGroup F] {f g : E →SWOT[σ] F} (x : E), (f - g) x = f x - g x
参数：x : E；f - g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma sub_apply {f g : E →SWOT[σ] F} (x : E) : (f - g) x = f x - g x := rfl
/-
**ContinuousLinearMapWOT.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
pWOT`。
形式化陈述：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} [inst : NormedField 𝕜₁] [inst_1 : Normed
Field 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_3}   {F : Type u_4} [inst_2 : AddCommGroup
 E] [inst_3 : TopologicalSpace E] [inst_4 : _root_.Module 𝕜₁ E]   [inst_5 : AddC
ommGroup F] [inst_6 : TopologicalSpace F] [inst_7 : _root_.Module 𝕜₂ F]   [inst_
8 : IsTopologicalAddGroup F] {f : E →SWOT[σ] F} (x : E), (-f) x = -f x
参数：x : E；-f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma neg_apply {f : E →SWOT[σ] F} (x : E) : (-f) x = -(f x) := rfl
/-
**ContinuousLinearMapWOT.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
pWOT`。
形式化陈述：∀ {𝕜₂ : Type u_2} [inst : NormedField 𝕜₂] {F : Type u_4} [inst_1 : AddComm
Group F] [inst_2 : TopologicalSpace F]   [inst_3 : _root_.Module 𝕜₂ F] [inst_4 :
 IsTopologicalAddGroup F] (f g : F →WOT[𝕜₂] F) (x : F), (f * g) x = f (g x)
参数：f g : F →WOT[𝕜₂] F；x : F；f * g；g x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mul_apply (f g : F →WOT[𝕜₂] F) (x : F) : (f * g) x = f (g x) := rfl
/-
**ContinuousLinearMapWOT.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
pWOT`。
形式化陈述：∀ {𝕜₂ : Type u_2} [inst : NormedField 𝕜₂] {F : Type u_4} [inst_1 : AddComm
Group F] [inst_2 : TopologicalSpace F]   [inst_3 : _root_.Module 𝕜₂ F] [inst_4 :
 IsTopologicalAddGroup F] (x : F), 1 x = x
参数：x : F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma one_apply (x : F) : (1 : F →WOT[𝕜₂] F) x = x := rfl
/-
**ContinuousLinearMapWOT.natCast_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMapWOT`。
形式化陈述：∀ {𝕜₂ : Type u_2} [inst : NormedField 𝕜₂] {F : Type u_4} [inst_1 : AddComm
Group F] [inst_2 : TopologicalSpace F]   [inst_3 : _root_.Module 𝕜₂ F] [inst_4 :
 IsTopologicalAddGroup F] (n : ℕ) (x : F), ↑n x = n • x
参数：n : ℕ；x : F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma natCast_apply (n : ℕ) (x : F) : (n : F →WOT[𝕜₂] F) x = n • x := rfl
/-
**ContinuousLinearMapWOT.intCast_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMapWOT`。
形式化陈述：∀ {𝕜₂ : Type u_2} [inst : NormedField 𝕜₂] {F : Type u_4} [inst_1 : AddComm
Group F] [inst_2 : TopologicalSpace F]   [inst_3 : _root_.Module 𝕜₂ F] [inst_4 :
 IsTopologicalAddGroup F] (n : ℤ) (x : F), ↑n x = n • x
参数：n : ℤ；x : F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma intCast_apply (n : ℤ) (x : F) : (n : F →WOT[𝕜₂] F) x = n • x := rfl

end Basic

/-!
### The topology of `E →WOT[𝕜] F`

The section endows `E →WOT[𝕜] F` with the weak operator topology and shows the basic properties
of this topology. In particular, we show that it is a topological vector space.
-/
section Topology

variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F]

variable (σ E F) in
/-- The function that induces the topology on `E →WOT[𝕜] F`, namely the function that takes
an `A` and maps it to `fun ⟨x, y⟩ => y (A x)` in `E × F⋆ → 𝕜`, bundled as a linear map to make
it easier to prove that it is a TVS. -/
/-
**ContinuousLinearMapWOT.inducingFn** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearM
apWOT`。
形式化陈述：inducingFn : (E ->SWOT[σ] F) ->ₗ[𝕜₂] (E × F⋆ -> 𝕜₂) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function that induces the topology on `E →WOT[𝕜] F`, namely the function tha
t takes
an `A` and maps it to `fun ⟨x, y⟩ => y (A x)` in `E × F⋆ → 𝕜`, bundled as a line
ar map to make
it easier to prove that it is a TVS.
-/
def inducingFn : (E →SWOT[σ] F) →ₗ[𝕜₂] (E × F⋆ → 𝕜₂) where
  toFun := fun A ⟨x, y⟩ => y (A x)
  map_add' := fun x y => by ext; simp
  map_smul' := fun x y => by ext; simp

@[simp]
/-
**ContinuousLinearMapWOT.inducingFn_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousL
inearMapWOT`。
形式化陈述：inducingFn_apply {f : E ->SWOT[σ] F} {x : E} {y : F⋆} : inducingFn σ E F f
 (x, y) = y (f x)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inducingFn_apply {f : E →SWOT[σ] F} {x : E} {y : F⋆} :
    inducingFn σ E F f (x, y) = y (f x) :=
  rfl

/-- The weak operator topology is the coarsest topology such that `fun A => y (A x)` is
continuous for all `x, y`. -/
/-
**ContinuousLinearMapWOT.instTopologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 `Continu
ousLinearMapWOT`。
形式化陈述：instTopologicalSpace : TopologicalSpace (E ->SWOT[σ] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weak operator topology is the coarsest topology such that `fun A => y (A x)`
 is
continuous for all `x, y`.
-/
instance instTopologicalSpace : TopologicalSpace (E →SWOT[σ] F) :=
  .induced (inducingFn _ _ _) Pi.topologicalSpace

@[fun_prop]
/-
**ContinuousLinearMapWOT.continuous_inducingFn** 是 Mathlib 中的一个引理，位于命名空间 `Contin
uousLinearMapWOT`。
形式化陈述：continuous_inducingFn : Continuous (inducingFn σ E F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
-/
lemma continuous_inducingFn : Continuous (inducingFn σ E F) :=
  continuous_induced_dom
/-
**ContinuousLinearMapWOT.continuous_dual_apply** 是 Mathlib 中的一个引理，位于命名空间 `Contin
uousLinearMapWOT`。
形式化陈述：continuous_dual_apply (x : E) (y : F⋆) : Continuous fun (A : E ->SWOT[σ] F
) => y (A x)
参数：x : E；y : F⋆。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_pi_iff`：continuous_pi_iff : Continuous f ↔ forall i, Continuo
us fun a => f a i
· 使用引理 `ContinuousLinearMapWOT.continuous_inducingFn`：continuous_inducingFn : Co
ntinuous (inducingFn σ E F)
-/
lemma continuous_dual_apply (x : E) (y : F⋆) : Continuous fun (A : E →SWOT[σ] F) => y (A x) := by
  refine (continuous_pi_iff.mp continuous_inducingFn) ⟨x, y⟩

@[fun_prop]
/-
**ContinuousLinearMapWOT.continuous_of_dual_apply_continuous** 是 Mathlib 中的一个引理，
位于命名空间 `ContinuousLinearMapWOT`。
形式化陈述：continuous_of_dual_apply_continuous {α : Type*} [TopologicalSpace α] {g : 
α -> E ->SWOT[σ] F} (h : forall x (y : F⋆), Continuous fun a => y (g a x)) : Con
tinuous g
参数：h : forall x (y : F⋆), Continuous fun a => y (g a x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `continuous_pi_iff`：continuous_pi_iff : Continuous f ↔ forall i, Continuo
us fun a => f a i
-/
lemma continuous_of_dual_apply_continuous {α : Type*} [TopologicalSpace α] {g : α → E →SWOT[σ] F}
    (h : ∀ x (y : F⋆), Continuous fun a => y (g a x)) : Continuous g :=
  continuous_induced_rng.2 (continuous_pi_iff.mpr fun p => h p.1 p.2)

@[fun_prop]
/-
**ContinuousLinearMapWOT.isInducing_inducingFn** 是 Mathlib 中的一个引理，位于命名空间 `Contin
uousLinearMapWOT`。
形式化陈述：isInducing_inducingFn : IsInducing (inducingFn σ E F)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isInducing_inducingFn : IsInducing (inducingFn σ E F) := ⟨rfl⟩

@[fun_prop]
/-
**ContinuousLinearMapWOT.isEmbedding_inducingFn** 是 Mathlib 中的一个引理，位于命名空间 `Conti
nuousLinearMapWOT`。
形式化陈述：isEmbedding_inducingFn [SeparatingDual 𝕜₂ F] : IsEmbedding (inducingFn σ E
 F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isEmbedding_induced`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [t : TopologicalSpace Y], Function.Injective f → Topology.IsEmbeddin
g f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMapWOT.ext_dual_iff`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} [
inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_3} 
  {F : Type u_4} [inst_2 …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma isEmbedding_inducingFn [SeparatingDual 𝕜₂ F] : IsEmbedding (inducingFn σ E F) := by
  refine Function.Injective.isEmbedding_induced fun A B hAB => ?_
  rw [ContinuousLinearMapWOT.ext_dual_iff]
  simpa [funext_iff] using hAB

open Filter in
/-- The defining property of the weak operator topology: a function `f` tends to
`A : E →WOT[𝕜] F` along filter `l` iff `y (f a x)` tends to `y (A x)` along the same filter. -/
/-
**ContinuousLinearMapWOT.tendsto_iff_forall_dual_apply_tendsto** 是 Mathlib 中的一个引
理，位于命名空间 `ContinuousLinearMapWOT`。
形式化陈述：tendsto_iff_forall_dual_apply_tendsto {α : Type*} {l : Filter α} {f : α ->
 E ->SWOT[σ] F} {A : E ->SWOT[σ] F} : Tendsto f l (𝓝 A) ↔ forall x (y : F⋆), Ten
dsto (fun a => y (f a x)) l (𝓝 (y (A x)))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsInducing.tendsto_nhds_iff`：tendsto_nhds_iff {f : ι -> Y} {l :
 Filter ι} {y : Y} (hg : IsInducing g) : Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (
𝓝 (g y))
· 使用引理 `ContinuousLinearMapWOT.isInducing_inducingFn`：isInducing_inducingFn : Is
Inducing (inducingFn σ E F)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The defining property of the weak operator topology: a function `f` tends to
`A : E →WOT[𝕜] F` along filter `l` iff `y (f a x)` tends to `y (A x)` along the 
same filter.
-/
lemma tendsto_iff_forall_dual_apply_tendsto {α : Type*} {l : Filter α} {f : α → E →SWOT[σ] F}
    {A : E →SWOT[σ] F} :
    Tendsto f l (𝓝 A) ↔ ∀ x (y : F⋆), Tendsto (fun a => y (f a x)) l (𝓝 (y (A x))) := by
  simp [isInducing_inducingFn.tendsto_nhds_iff, tendsto_pi_nhds]
/-
**ContinuousLinearMapWOT.le_nhds_iff_forall_dual_apply_le_nhds** 是 Mathlib 中的一个引
理，位于命名空间 `ContinuousLinearMapWOT`。
形式化陈述：le_nhds_iff_forall_dual_apply_le_nhds {l : Filter (E ->SWOT[σ] F)} {A : E 
->SWOT[σ] F} : l <= 𝓝 A ↔ forall x (y : F⋆), l.map (fun T => y (T x)) <= 𝓝 (y (A
 x))
参数：E ->SWOT[σ] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMapWOT.tendsto_iff_forall_dual_apply_tendsto`：tendsto_if
f_forall_dual_apply_tendsto {α : Type*} {l : Filter α} {f : α -> E ->SWOT[σ] F} 
{A : E ->SWOT[σ] F} : Tendsto f l (𝓝 A) ↔ forall x…
-/
lemma le_nhds_iff_forall_dual_apply_le_nhds {l : Filter (E →SWOT[σ] F)} {A : E →SWOT[σ] F} :
    l ≤ 𝓝 A ↔ ∀ x (y : F⋆), l.map (fun T => y (T x)) ≤ 𝓝 (y (A x)) :=
  tendsto_iff_forall_dual_apply_tendsto (f := id)
/-
**ContinuousLinearMapWOT.instT3Space** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinear
MapWOT`。
形式化陈述：instT3Space [SeparatingDual 𝕜₂ F] : T3Space (E ->SWOT[σ] F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t3Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] [T3Space Y] {f : X → Y},   Topol
ogy.IsEmbedding f …
· 使用定理 `instT3SpaceForall`：∀ {ι : Type u_3} {X : ι → Type u_4} [inst : (i : ι) →
 TopologicalSpace (X i)] [∀ (i : ι), T3Space (X i)],   T3Space ((i : ι) → X i)
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用引理 `ContinuousLinearMapWOT.isEmbedding_inducingFn`：isEmbedding_inducingFn [S
eparatingDual 𝕜₂ F] : IsEmbedding (inducingFn σ E F)
-/
instance instT3Space [SeparatingDual 𝕜₂ F] : T3Space (E →SWOT[σ] F) :=
  isEmbedding_inducingFn.t3Space
/-
**ContinuousLinearMapWOT.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMapWOT`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F] [ContinuousConstSMul S F]
    [SMul S 𝕜₂] [IsScalarTower S 𝕜₂ 𝕜₂] [IsScalarTower S 𝕜₂ F] :
    ContinuousConstSMul S (F →WOT[𝕜₂] F) where
  continuous_const_smul c := by
    apply continuous_of_dual_apply_continuous fun _ _ ↦ ?_
    simp only [smul_apply, ContinuousLinearMap.map_smul_of_tower]
    exact continuous_const_smul c |>.comp <| continuous_dual_apply ..
/-
**ContinuousLinearMapWOT.instContinuousSMul** 是 Mathlib 中的一个实例，位于命名空间 `Continuou
sLinearMapWOT`。
形式化陈述：instContinuousSMul {S : Type*} [Semiring S] [Module S F] [SMulCommClass 𝕜₂
 S F] [Module S 𝕜₂] [IsScalarTower S 𝕜₂ F] [IsScalarTower S 𝕜₂ 𝕜₂] [ContinuousCo
nstSMul S F] [TopologicalSpace S] [ContinuousSMul S 𝕜₂] : ContinuousSMul S (E ->
SWOT[σ] F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousSMul.induced`：ContinuousSMul.induced {R : Type*} {α : Type*} {
β : Type*} {F : Type*} [FunLike F α β] [Semiring R] [AddCommMonoid α] [AddCommMo
noid β] [Mod…
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `LinearMap.CompatibleSMul.pi`：∀ (R : Type u_1) (S : Type u_2) (M : Type u
_3) (N : Type u_4) (ι : Type u_5) [inst : Semiring S]   [inst_1 : AddCommMonoid 
M] [inst_2 : AddC…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
-/
instance instContinuousSMul {S : Type*} [Semiring S] [Module S F] [SMulCommClass 𝕜₂ S F]
    [Module S 𝕜₂] [IsScalarTower S 𝕜₂ F] [IsScalarTower S 𝕜₂ 𝕜₂] [ContinuousConstSMul S F]
    [TopologicalSpace S] [ContinuousSMul S 𝕜₂] :
  ContinuousSMul S (E →SWOT[σ] F) := .induced <| (inducingFn σ E F).restrictScalars S
/-
**ContinuousLinearMapWOT.instIsTopologicalAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `Co
ntinuousLinearMapWOT`。
形式化陈述：instIsTopologicalAddGroup : IsTopologicalAddGroup (E ->SWOT[σ] F) where to
ContinuousAdd
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAdd.induced`：∀ {α : Type u_6} {β : Type u_7} {F : Type u_8} [i
nst : FunLike F α β] [inst_1 : Add α] [inst_2 : Add β]   [AddHomClass F α β] [tβ
 : Topologi…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Pi.continuousAdd'`：∀ {ι : Type u_1} {M : Type u_3} [inst : TopologicalSp
ace M] [inst_1 : Add M] [ContinuousAdd M], ContinuousAdd (ι → M)
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
· 使用定理 `ContinuousNeg.induced`：∀ {α : Type u_1} {β : Type u_2} {F : Type u_3} [i
nst : FunLike F α β] [inst_1 : AddGroup α]   [inst_2 : SubtractionMonoid β] [Add
MonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Pi.has_continuous_neg'`：∀ {G : Type w} [inst : TopologicalSpace G] [inst
_1 : Neg G] [ContinuousNeg G] {ι : Type u_1}, ContinuousNeg (ι → G)
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
-/
instance instIsTopologicalAddGroup : IsTopologicalAddGroup (E →SWOT[σ] F) where
  toContinuousAdd := .induced (inducingFn σ E F)
  toContinuousNeg := .induced (inducingFn σ E F)
/-
**ContinuousLinearMapWOT.instUniformSpace** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousL
inearMapWOT`。
形式化陈述：instUniformSpace : UniformSpace (E ->SWOT[σ] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instUniformSpace : UniformSpace (E →SWOT[σ] F) := .comap (inducingFn σ E F) inferInstance
/-
**ContinuousLinearMapWOT.instIsUniformAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `Contin
uousLinearMapWOT`。
形式化陈述：instIsUniformAddGroup : IsUniformAddGroup (E ->SWOT[σ] F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformAddGroup.comap`：∀ {G : Type u_1} {H : Type u_2} {hom : Type u_3
} [inst : AddGroup G] [inst_1 : AddGroup H] {u : UniformSpace H}   [IsUniformAdd
Group H] [ins…
· 使用定理 `Pi.instIsUniformAddGroup`：∀ {ι : Type u_4} {G : ι → Type u_5} [inst : (i
 : ι) → UniformSpace (G i)] [inst_1 : (i : ι) → AddGroup (G i)]   [∀ (i : ι), Is
UniformAddGrou…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
instance instIsUniformAddGroup : IsUniformAddGroup (E →SWOT[σ] F) := .comap (inducingFn σ E F)

end Topology

/-! ### The WOT is induced by a family of seminorms -/
section Seminorms

variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F]

/-- The family of seminorms that induce the weak operator topology, namely `‖y (A x)‖` for
all `x` and `y`. -/
/-
**ContinuousLinearMapWOT.seminorm** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap
WOT`。
形式化陈述：seminorm (x : E) (y : F⋆) : Seminorm 𝕜₂ (E ->SWOT[σ] F) where toFun A
参数：x : E；y : F⋆。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of seminorms that induce the weak operator topology, namely `‖y (A x)
‖` for
all `x` and `y`.
-/
def seminorm (x : E) (y : F⋆) : Seminorm 𝕜₂ (E →SWOT[σ] F) where
  toFun A := ‖y (A x)‖
  map_zero' := by simp
  add_le' A B := by simpa using norm_add_le _ _
  neg' A := by simp
  smul' r A := by simp

variable (σ E F) in
/-- The family of seminorms that induce the weak operator topology, namely `‖y (A x)‖` for
all `x` and `y`. -/
/-
**ContinuousLinearMapWOT.seminormFamily** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLin
earMapWOT`。
形式化陈述：seminormFamily : SeminormFamily 𝕜₂ (E ->SWOT[σ] F) (E × F⋆)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of seminorms that induce the weak operator topology, namely `‖y (A x)
‖` for
all `x` and `y`.
-/
def seminormFamily : SeminormFamily 𝕜₂ (E →SWOT[σ] F) (E × F⋆) :=
  fun ⟨x, y⟩ => seminorm x y
/-
**ContinuousLinearMapWOT.withSeminorms** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLine
arMapWOT`。
形式化陈述：withSeminorms : WithSeminorms (seminormFamily σ E F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Topology.IsInducing.withSeminorms`：Topology.IsInducing.withSeminorms {q 
: SeminormFamily 𝕜₂ F ι} (hq : WithSeminorms q) [TopologicalSpace E] {f : E ->ₛₗ
[σ₁₂] F} (hf : IsInduci…
· 使用定理 `WithSeminorms.congr_equiv`：∀ {𝕜 : Type u_2} {E : Type u_6} {ι : Type u_9
} {ι' : Type u_10} [inst : NormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : 
_root_.Module 𝕜…
· 使用定理 `withSeminorms_pi`：withSeminorms_pi {κ : ι -> Type*} {E : ι -> Type*} [fo
rall i, AddCommGroup (E i)] [forall i, Module 𝕜 (E i)] [forall i, TopologicalSpa
ce (E …
· 使用定理 `norm_withSeminorms`：norm_withSeminorms (𝕜 E) [NormedField 𝕜] [Seminormed
AddCommGroup E] [NormedSpace 𝕜 E] : WithSeminorms fun _ : Fin 1 => normSeminorm 
𝕜 E
· 使用引理 `ContinuousLinearMapWOT.isInducing_inducingFn`：isInducing_inducingFn : Is
Inducing (inducingFn σ E F)
-/
lemma withSeminorms : WithSeminorms (seminormFamily σ E F) :=
  let e : E × F⋆ ≃ (Σ _ : E × F⋆, Fin 1) := .symm <| .sigmaUnique _ _
  isInducing_inducingFn.withSeminorms <| withSeminorms_pi (fun _ ↦ norm_withSeminorms 𝕜₂ 𝕜₂)
    |>.congr_equiv e
/-
**ContinuousLinearMapWOT.hasBasis_seminorms** 是 Mathlib 中的一个引理，位于命名空间 `Continuou
sLinearMapWOT`。
形式化陈述：hasBasis_seminorms : (𝓝 (0 : E ->SWOT[σ] F)).HasBasis (· in (seminormFamil
y σ E F).basisSets) id
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.hasBasis`：WithSeminorms.hasBasis (hp : WithSeminorms p) : 
(𝓝 (0 : E)).HasBasis (fun s : Set E => s in p.basisSets) id
· 使用引理 `ContinuousLinearMapWOT.withSeminorms`：withSeminorms : WithSeminorms (sem
inormFamily σ E F)
-/
lemma hasBasis_seminorms :
    (𝓝 (0 : E →SWOT[σ] F)).HasBasis (· ∈ (seminormFamily σ E F).basisSets) id :=
  withSeminorms.hasBasis
/-
**ContinuousLinearMapWOT.instLocallyConvexSpace** 是 Mathlib 中的一个实例，位于命名空间 `Conti
nuousLinearMapWOT`。
形式化陈述：instLocallyConvexSpace [NormedSpace Real 𝕜₂] [Module Real (E ->SWOT[σ] F)]
 [IsScalarTower Real 𝕜₂ (E ->SWOT[σ] F)] : LocallyConvexSpace Real (E ->SWOT[σ] 
F)
参数：E ->SWOT[σ] F；E ->SWOT[σ] F。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.toLocallyConvexSpace`：WithSeminorms.toLocallyConvexSpace {
p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) : LocallyConvexSpace Real E
· 使用引理 `ContinuousLinearMapWOT.withSeminorms`：withSeminorms : WithSeminorms (sem
inormFamily σ E F)
-/
instance instLocallyConvexSpace [NormedSpace ℝ 𝕜₂] [Module ℝ (E →SWOT[σ] F)]
    [IsScalarTower ℝ 𝕜₂ (E →SWOT[σ] F)] :
    LocallyConvexSpace ℝ (E →SWOT[σ] F) :=
  withSeminorms.toLocallyConvexSpace

end Seminorms

section toWOT_continuous

variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F] [ContinuousSMul 𝕜₁ E]

/-- The weak operator topology is coarser than the bounded convergence topology, i.e. the inclusion
map is continuous. -/
@[continuity, fun_prop]
/-
**ContinuousLinearMapWOT.continuous_ofCLM** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousL
inearMapWOT`。
形式化陈述：continuous_ofCLM : Continuous (ofCLM : (E ->SL[σ] F) -> (E ->SWOT[σ] F))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMapWOT.continuous_of_dual_apply_continuous`：continuous_o
f_dual_apply_continuous {α : Type*} [TopologicalSpace α] {g : α -> E ->SWOT[σ] F
} (h : forall x (y : F⋆), Continuous fun a => y …
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousLinearMap.cont`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiri
ng R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_3}   [inst_2 : Topological
Space M] [inst…
· 使用定理 `ContinuousEvalConst.continuous_eval_const`：∀ {F : Type u_1} {α : outPara
m (Type u_2)} {X : outParam (Type u_3)} {inst : FunLike F α X}   {inst_1 : Topol
ogicalSpace F} {inst_2 : Topolo…

--- 原说明 ---
The weak operator topology is coarser than the bounded convergence topology, i.e
. the inclusion
map is continuous.
-/
lemma continuous_ofCLM :
    Continuous (ofCLM : (E →SL[σ] F) → (E →SWOT[σ] F)) :=
  ContinuousLinearMapWOT.continuous_of_dual_apply_continuous fun x y ↦
    y.cont.comp <| continuous_eval_const x

@[deprecated (since := "2026-04-10")] alias ContinuousLinearMap.continuous_toWOT := continuous_ofCLM

/-- The inclusion map from `E →[𝕜] F` to `E →WOT[𝕜] F`, bundled as a continuous linear map. -/
/-
**ContinuousLinearMapWOT._root_.ContinuousLinearMap.WOTofCLM** 是 Mathlib 中的一个定义，
位于命名空间 `ContinuousLinearMapWOT`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion map from `E →[𝕜] F` to `E →WOT[𝕜] F`, bundled as a continuous line
ar map.
-/
def _root_.ContinuousLinearMap.WOTofCLM : (E →SL[σ] F) →L[𝕜₂] (E →SWOT[σ] F) where
  toLinearMap := linearEquiv 𝕜₂ |>.symm.toLinearMap
  cont := continuous_ofCLM

@[deprecated (since := "2026-04-10")]
alias ContinuousLinearMap.toWOTCLM := ContinuousLinearMap.WOTofCLM

end toWOT_continuous


section Comp

variable {𝕜₁ 𝕜₂ 𝕜₃ 𝕜₄ : Type*} {E F G H : Type*}
    [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃] [NormedField 𝕜₄]
    {σ₁₂ : 𝕜₁ →+* 𝕜₂} {σ₁₃ : 𝕜₁ →+* 𝕜₃} {σ₁₄ : 𝕜₁ →+* 𝕜₄}
    {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₂₄ : 𝕜₂ →+* 𝕜₄} {σ₃₄ : 𝕜₃ →+* 𝕜₄}
    [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄]
    [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄]
    [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E]
    [AddCommGroup F] [TopologicalSpace F] [Module 𝕜₂ F]
    [AddCommGroup G] [TopologicalSpace G] [Module 𝕜₃ G]
    [AddCommGroup H] [TopologicalSpace H] [Module 𝕜₄ H]

variable (𝕜₂ F) in
/-- The identity as a continuous linear map on the type synonym equipped with the weak operator
topology -/
/-
**ContinuousLinearMapWOT.id** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMapWOT`。
形式化陈述：(𝕜₂ : Type u_6) →   (F : Type u_10) →     [inst : NormedField 𝕜₂] →       
[inst_1 : AddCommGroup F] → [inst_2 : TopologicalSpace F] → [inst_3 : _root_.Mod
ule 𝕜₂ F] → F →WOT[𝕜₂] F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity as a continuous linear map on the type synonym equipped with the we
ak operator
topology
-/
protected def id : F →WOT[𝕜₂] F := ofCLM <| .id 𝕜₂ F

@[simp]
/-
**ContinuousLinearMapWOT.toCLM_id** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMap
WOT`。
形式化陈述：toCLM_id : (.id 𝕜₂ F : F ->WOT[𝕜₂] F).toCLM = .id 𝕜₂ F
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toCLM_id : (.id 𝕜₂ F : F →WOT[𝕜₂] F).toCLM = .id 𝕜₂ F := rfl

/-- Composition of continuous linear maps on the type synonym equipped with the weak operator
topology. -/
/-
**ContinuousLinearMapWOT.comp** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMapWOT`
。
形式化陈述：comp (g : F ->SWOT[σ₂₃] G) (f : E ->SWOT[σ₁₂] F) : E ->SWOT[σ₁₃] G
参数：g : F ->SWOT[σ₂₃] G；f : E ->SWOT[σ₁₂] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of continuous linear maps on the type synonym equipped with the weak
 operator
topology.
-/
def comp (g : F →SWOT[σ₂₃] G) (f : E →SWOT[σ₁₂] F) : E →SWOT[σ₁₃] G :=
  ofCLM <| g.toCLM.comp f.toCLM

@[simp]
/-
**ContinuousLinearMapWOT.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearM
apWOT`。
形式化陈述：comp_apply (g : F ->SWOT[σ₂₃] G) (f : E ->SWOT[σ₁₂] F) (x : E) : g.comp f 
x = g (f x)
参数：g : F ->SWOT[σ₂₃] G；f : E ->SWOT[σ₁₂] F；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_apply (g : F →SWOT[σ₂₃] G) (f : E →SWOT[σ₁₂] F) (x : E) :
    g.comp f x = g (f x) := by
  simp [comp]
/-
**ContinuousLinearMapWOT.toCLM_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
apWOT`。
形式化陈述：∀ {𝕜₁ : Type u_5} {𝕜₂ : Type u_6} {𝕜₃ : Type u_7} {E : Type u_9} {F : Type
 u_10} {G : Type u_11} [inst : NormedField 𝕜₁]   [inst_1 : NormedField 𝕜₂] [inst
_2 : NormedField 𝕜₃] {σ₁₂ : 𝕜₁ →+* 𝕜₂} {σ₁₃ : 𝕜₁ →+* 𝕜₃} {σ₂₃ : 𝕜₂ →+* 𝕜₃}   [in
st_3 : RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [inst_4 : AddCommGroup E] [inst_5 : Topolo
gicalSpace E]   [inst_6 : _root_.Module 𝕜₁ E] [inst_7 : AddCommGroup F] [inst_8 
: TopologicalSpace F] [inst_9 : _root_.Module 𝕜₂ F]   [inst_10 : AddCommGroup G]
 [inst_11 : TopologicalSpace G] [inst_12 : _root_.Module 𝕜₃ G] (g : F →SWOT[σ₂₃]
 G)   (f : E →SWOT[σ₁₂] F), (g.comp f).toCLM = g.toCLM ∘SL f.toCLM
参数：g : F →SWOT[σ₂₃] G；f : E →SWOT[σ₁₂] F；g.comp f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toCLM_comp (g : F →SWOT[σ₂₃] G) (f : E →SWOT[σ₁₂] F) :
    (g.comp f).toCLM = g.toCLM.comp f.toCLM :=
  rfl
/-
**ContinuousLinearMapWOT.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMapW
OT`。
形式化陈述：∀ {𝕜₁ : Type u_5} {𝕜₂ : Type u_6} {E : Type u_9} {F : Type u_10} [inst : N
ormedField 𝕜₁] [inst_1 : NormedField 𝕜₂]   {σ₁₂ : 𝕜₁ →+* 𝕜₂} [inst_2 : AddCommGr
oup E] [inst_3 : TopologicalSpace E] [inst_4 : _root_.Module 𝕜₁ E]   [inst_5 : A
ddCommGroup F] [inst_6 : TopologicalSpace F] [inst_7 : _root_.Module 𝕜₂ F] (f : 
E →SWOT[σ₁₂] F),   (ContinuousLinearMapWOT.id 𝕜₂ F).comp f = f
参数：f : E →SWOT[σ₁₂] F；ContinuousLinearMapWOT.id 𝕜₂ F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.id_comp`：id_comp (f : M₁ ->SL[σ₁₂] M₂) : .id R₂ M₂ ∘
SL f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma comp_id (f : E →SWOT[σ₁₂] F) : comp (.id 𝕜₂ F) f = f := by simp [comp]
/-
**ContinuousLinearMapWOT.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMapW
OT`。
形式化陈述：∀ {𝕜₂ : Type u_6} {𝕜₃ : Type u_7} {F : Type u_10} {G : Type u_11} [inst : 
NormedField 𝕜₂] [inst_1 : NormedField 𝕜₃]   {σ₂₃ : 𝕜₂ →+* 𝕜₃} [inst_2 : AddCommG
roup F] [inst_3 : TopologicalSpace F] [inst_4 : _root_.Module 𝕜₂ F]   [inst_5 : 
AddCommGroup G] [inst_6 : TopologicalSpace G] [inst_7 : _root_.Module 𝕜₃ G] (g :
 F →SWOT[σ₂₃] G),   g.comp (ContinuousLinearMapWOT.id 𝕜₂ F) = g
参数：g : F →SWOT[σ₂₃] G；ContinuousLinearMapWOT.id 𝕜₂ F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp_id`：comp_id (f : M₁ ->SL[σ₁₂] M₂) : f ∘SL .id R
₁ M₁ = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma id_comp (g : F →SWOT[σ₂₃] G) : comp g (.id 𝕜₂ F) = g := by simp [comp]
/-
**ContinuousLinearMapWOT.comp_assoc** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearM
apWOT`。
形式化陈述：comp_assoc (g₃₄ : G ->SWOT[σ₃₄] H) (g₂₃ : F ->SWOT[σ₂₃] G) (g₁₂ : E ->SWOT
[σ₁₂] F) : (g₃₄.comp g₂₃).comp g₁₂ = g₃₄.comp (g₂₃.comp g₁₂)
参数：g₃₄ : G ->SWOT[σ₃₄] H；g₂₃ : F ->SWOT[σ₂₃] G；g₁₂ : E ->SWOT[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_assoc (g₃₄ : G →SWOT[σ₃₄] H) (g₂₃ : F →SWOT[σ₂₃] G) (g₁₂ : E →SWOT[σ₁₂] F) :
    (g₃₄.comp g₂₃).comp g₁₂ = g₃₄.comp (g₂₃.comp g₁₂) := by
  simp only [comp, ContinuousLinearMap.comp_assoc]
/-
**ContinuousLinearMapWOT.mul_eq_comp** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinear
MapWOT`。
形式化陈述：mul_eq_comp [IsTopologicalAddGroup F] (f g : F ->WOT[𝕜₂] F) : f * g = f.co
mp g
参数：f g : F ->WOT[𝕜₂] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_eq_comp [IsTopologicalAddGroup F] (f g : F →WOT[𝕜₂] F) : f * g = f.comp g := rfl

@[fun_prop]
/-
**ContinuousLinearMapWOT.continuous_precomp** 是 Mathlib 中的一个引理，位于命名空间 `Continuou
sLinearMapWOT`。
形式化陈述：continuous_precomp [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G] (f
 : E ->SWOT[σ₁₂] F) : Continuous (fun g : F ->SWOT[σ₂₃] G => g.comp f)
参数：f : E ->SWOT[σ₁₂] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMapWOT.continuous_of_dual_apply_continuous`：continuous_o
f_dual_apply_continuous {α : Type*} [TopologicalSpace α] {g : α -> E ->SWOT[σ] F
} (h : forall x (y : F⋆), Continuous fun a => y …
· 使用引理 `ContinuousLinearMapWOT.continuous_dual_apply`：continuous_dual_apply (x :
 E) (y : F⋆) : Continuous fun (A : E ->SWOT[σ] F) => y (A x)
-/
lemma continuous_precomp [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G] (f : E →SWOT[σ₁₂] F) :
    Continuous (fun g : F →SWOT[σ₂₃] G ↦ g.comp f) :=
  continuous_of_dual_apply_continuous fun _ _ ↦ continuous_dual_apply ..

variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F]
variable [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]

/-- While `RingHomSurjective σ₂₃` is not a strict requirement, there are obstructions to
this without any assumption on `σ₂₃` (in particular, on the dimension of the extension of `𝕜₃` over
`σ₂₃(𝕜₂)`), and in the only common case, which is when `σ₂₃` is conjugation, this type class is
guaranteed. Likewise, it would suffice if `RingHomIsometric` were replaced with the weaker
`Continuous σ₂₃`, but we opt for this because we have these type classes available. -/
@[fun_prop]
/-
**ContinuousLinearMapWOT.continuous_postcomp** 是 Mathlib 中的一个引理，位于命名空间 `Continuo
usLinearMapWOT`。
形式化陈述：continuous_postcomp [RingHomSurjective σ₂₃] [RingHomIsometric σ₂₃] (g : F 
->SWOT[σ₂₃] G) : Continuous (fun f : E ->SWOT[σ₁₂] F => g.comp f)
参数：g : F ->SWOT[σ₂₃] G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMapWOT.continuous_of_dual_apply_continuous`：continuous_o
f_dual_apply_continuous {α : Type*} [TopologicalSpace α] {g : α -> E ->SWOT[σ] F
} (h : forall x (y : F⋆), Continuous fun a => y …
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `RingHomSurjective.is_surjective`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {inst
 : Semiring R₁} {inst_1 : Semiring R₂} {σ : R₁ →+* R₂}   [self : RingHomSurjecti
ve σ], Function.Surje…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用引理 `RingHomInvPair.of_ringEquiv`：of_ringEquiv (e : R₁ ≃+* R₂) : RingHomInvPa
ir (↑e : R₁ ->+* R₂) ↑e.symm
· 使用定理 `RingHomInvPair.symm`：symm (σ₁₂ : R₁ ->+* R₂) (σ₂₁ : R₂ ->+* R₁) [RingHom
InvPair σ₁₂ σ₂₁] : RingHomInvPair σ₂₁ σ₁₂
· 使用定理 `RingHomIsometric.norm_map`：∀ {R₁ : Type u_5} {R₂ : Type u_6} {inst : Sem
iring R₁} {inst_1 : Semiring R₂} {inst_2 : Norm R₁} {inst_3 : Norm R₂}   {σ : R₁
 →+* R₂} [self …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : E₂) : e (e.s
ymm x) = x
· 使用引理 `ContinuousLinearMapWOT.comp_apply`：comp_apply (g : F ->SWOT[σ₂₃] G) (f :
 E ->SWOT[σ₁₂] F) (x : E) : g.comp f x = g (f x)
· 使用引理 `ContinuousLinearMapWOT.toCLM_apply`：toCLM_apply {A : E ->SWOT[σ] F} {x :
 E} : toCLM A x = A x
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `LinearIsometryEquiv.continuous`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Ty
pe u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+
* R₂} {σ₂₁ : R₂ →+* …
· 使用引理 `ContinuousLinearMapWOT.continuous_dual_apply`：continuous_dual_apply (x :
 E) (y : F⋆) : Continuous fun (A : E ->SWOT[σ] F) => y (A x)

--- 原说明 ---
While `RingHomSurjective σ₂₃` is not a strict requirement, there are obstruction
s to
this without any assumption on `σ₂₃` (in particular, on the dimension of the ext
ension of `𝕜₃` over
`σ₂₃(𝕜₂)`), and in the only common case, which is when `σ₂₃` is conjugation, thi
s type class is
guaranteed. Likewise, it would suffice if `RingHomIsometric` were replaced with 
the weaker
`Continuous σ₂₃`, but we opt for this because we have these type classes availab
le.
-/
lemma continuous_postcomp [RingHomSurjective σ₂₃] [RingHomIsometric σ₂₃] (g : F →SWOT[σ₂₃] G) :
    Continuous (fun f : E →SWOT[σ₁₂] F ↦ g.comp f) := by
  refine continuous_of_dual_apply_continuous fun x z ↦ ?_
  have σ_bij : Function.Bijective σ₂₃ := ⟨σ₂₃.injective, RingHomSurjective.is_surjective⟩
  let σ_equiv : 𝕜₂ ≃+* 𝕜₃ := RingEquiv.ofBijective σ₂₃ σ_bij
  let invPair : RingHomInvPair σ₂₃ σ_equiv.symm := RingHomInvPair.of_ringEquiv σ_equiv
  let invPair_symm := invPair.symm
  let σ_li : 𝕜₂ ≃ₛₗᵢ[σ₂₃] 𝕜₃ :=
    { toLinearEquiv := .ofBijective σ₂₃.toSemilinearMap σ_bij
      norm_map' _ := RingHomIsometric.norm_map }
  conv => enter [1, a]; rw [← σ_li.apply_symm_apply (z _), comp_apply, ← toCLM_apply]
  apply σ_li.continuous.comp
  exact continuous_dual_apply x <| σ_li.symm.toLinearIsometry.toContinuousLinearMap.comp <|
    z.comp g.toCLM

/-- Precomposition by a fixed continuous linear map, as a continuous linear map when all spaces
of continuous linear maps are equipped with the weak operator topology. -/
@[simps]
/-
**ContinuousLinearMapWOT.precompCLM** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearM
apWOT`。
形式化陈述：precompCLM (f : E ->SWOT[σ₁₂] F) : (F ->SWOT[σ₂₃] G) ->L[𝕜₃] (E ->SWOT[σ₁₃
] G) where toFun g
参数：f : E ->SWOT[σ₁₂] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Precomposition by a fixed continuous linear map, as a continuous linear map when
 all spaces
of continuous linear maps are equipped with the weak operator topology.
-/
def precompCLM (f : E →SWOT[σ₁₂] F) : (F →SWOT[σ₂₃] G) →L[𝕜₃] (E →SWOT[σ₁₃] G) where
  toFun g := g.comp f
  map_add' := by simp [comp]
  map_smul' := by simp [comp]

/-- Precomposition by a fixed continuous linear map, as a continuous linear map when all spaces
of continuous linear maps are equipped with the weak operator topology. -/
@[simps]
/-
**ContinuousLinearMapWOT.postcompCLM** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinear
MapWOT`。
形式化陈述：postcompCLM [RingHomSurjective σ₂₃] [RingHomIsometric σ₂₃] (g : F ->SWOT[σ
₂₃] G) : (E ->SWOT[σ₁₂] F) ->SL[σ₂₃] (E ->SWOT[σ₁₃] G) where toFun f
参数：g : F ->SWOT[σ₂₃] G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Precomposition by a fixed continuous linear map, as a continuous linear map when
 all spaces
of continuous linear maps are equipped with the weak operator topology.
-/
def postcompCLM [RingHomSurjective σ₂₃] [RingHomIsometric σ₂₃] (g : F →SWOT[σ₂₃] G) :
    (E →SWOT[σ₁₂] F) →SL[σ₂₃] (E →SWOT[σ₁₃] G) where
  toFun f := g.comp f
  map_add' := by simp [comp]
  map_smul' := by simp [comp]
/-
**ContinuousLinearMapWOT.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMapWOT`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSemitopologicalRing (F →WOT[𝕜₂] F) where
  continuous_const_mul {_} := by simp_rw [mul_eq_comp]; fun_prop
  continuous_mul_const {_} := by simp_rw [mul_eq_comp]; fun_prop

end Comp

end ContinuousLinearMapWOT

