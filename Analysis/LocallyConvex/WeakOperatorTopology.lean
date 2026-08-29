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

/--
Definition of `ContinuousLinearMapWOT` / `ContinuousLinearMapWOT` 的定义

English:
structure ContinuousLinearMapWOT
  parameters: {𝕜₁ 𝕜₂ : Type*} [Semiring 𝕜₁] [Semiring 𝕜₂] (σ : 𝕜₁ ->+* 𝕜₂)
  axioms and operations (2):
    - ofCLM : :
    - toCLM : E ->SL[σ] F

中文:
结构 余ntinuousLinearMapWOT
  参数: {𝕜₁ 𝕜₂ : 类型} [半环 𝕜₁] [半环 𝕜₂] (σ : 𝕜₁ ->+* 𝕜₂)
  公理与运算 (2 个):
    - ofCLM : :
    - toCLM : E ->SL[σ] F
-/
structure ContinuousLinearMapWOT {𝕜₁ 𝕜₂ : Type*} [Semiring 𝕜₁] [Semiring 𝕜₂] (σ : 𝕜₁ ->+* 𝕜₂)
    (E F : Type*) [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E] [AddCommGroup F]
    [TopologicalSpace F] [Module 𝕜₂ F] where
  /-- Construct an element of `E →SWOT[σ] F` from a continuous linear map. -/
  ofCLM ::
  /-- The continuous linear map underlying an element of `E →SWOT[σ] F`. -/
  toCLM : E ->SL[σ] F


namespace ContinuousLinearMapWOT

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `ofCLM A` being printed as `{ toCLM := x }` by `delabStructureInstance`. -/
@[app_delab ContinuousLinearMapWOT.ofCLM]
meta def delabOfCLM : Delab := delabApp

@[inherit_doc]
notation:25 E " ->SWOT[" σ "] " F => ContinuousLinearMapWOT σ E F

@[inherit_doc]
notation:25 E " ->WOT[" 𝕜 "] " F => ContinuousLinearMapWOT (RingHom.id 𝕜) E F

end Notation

variable {𝕜₁ 𝕜₂ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂]
  {σ : 𝕜₁ ->+* 𝕜₂}
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
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : (E ->SWOT[σ] F) ≃ (E ->SL[σ] F) where
  body: toCLM
  invFun := ofCLM
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]

中文:
定义 equiv
  签名: : (E ->SWOT[σ] F) ≃ (E ->SL[σ] F) where
  定义体: toCLM
  invFun := ofCLM
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
-/
def equiv : (E ->SWOT[σ] F) ≃ (E ->SL[σ] F) where
  toFun := toCLM
  invFun := ofCLM
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
/--
lemma `toCLM_injective` / 引理 `toCLM_injective`

English:
lemma toCLM_injective
  statement: Function.Injective (toCLM : (E ->SWOT[σ] F) -> E ->SL[σ] F)
  proof: equiv.injective

@[simp]

中文:
引理 toCLM_injective
  结论: 函数.单射 (toCLM : (E ->SWOT[σ] F) -> E ->SL[σ] F)
  证明: equiv.injective

@[simp]

Depends on / 依赖: equiv.injective, injective
-/
lemma toCLM_injective : Function.Injective (toCLM : (E ->SWOT[σ] F) -> E ->SL[σ] F) :=
  equiv.injective

@[simp]
/--
lemma `toCLM_surjective` / 引理 `toCLM_surjective`

English:
lemma toCLM_surjective
  statement: Function.Surjective (toCLM : (E ->SWOT[σ] F) -> E ->SL[σ] F)
  proof: equiv.surjective

中文:
引理 toCLM_surjective
  结论: 函数.满射 (toCLM : (E ->SWOT[σ] F) -> E ->SL[σ] F)
  证明: equiv.surjective

Depends on / 依赖: equiv.surjective, surjective
-/
lemma toCLM_surjective : Function.Surjective (toCLM : (E ->SWOT[σ] F) -> E ->SL[σ] F) :=
  equiv.surjective

/--
lemma `toCLM_bijective` / 引理 `toCLM_bijective`

English:
lemma toCLM_bijective
  statement: Function.Bijective (toCLM : (E ->SWOT[σ] F) -> E ->SL[σ] F)
  proof: equiv.bijective

@[simp]

中文:
引理 toCLM_bijective
  结论: 函数.双射 (toCLM : (E ->SWOT[σ] F) -> E ->SL[σ] F)
  证明: equiv.bijective

@[simp]

Depends on / 依赖: bijective, equiv.bijective
-/
lemma toCLM_bijective : Function.Bijective (toCLM : (E ->SWOT[σ] F) -> E ->SL[σ] F) :=
  equiv.bijective

@[simp]
/--
lemma `ofCLM_injective` / 引理 `ofCLM_injective`

English:
lemma ofCLM_injective
  statement: Function.Injective (ofCLM : (E ->SL[σ] F) -> E ->SWOT[σ] F)
  proof: equiv.symm.injective

@[simp]

中文:
引理 ofCLM_injective
  结论: 函数.单射 (ofCLM : (E ->SL[σ] F) -> E ->SWOT[σ] F)
  证明: equiv.symm.injective

@[simp]

Depends on / 依赖: equiv.symm.injective, injective
-/
lemma ofCLM_injective : Function.Injective (ofCLM : (E ->SL[σ] F) -> E ->SWOT[σ] F) :=
  equiv.symm.injective

@[simp]
/--
lemma `ofCLM_surjective` / 引理 `ofCLM_surjective`

English:
lemma ofCLM_surjective
  statement: Function.Surjective (ofCLM : (E ->SL[σ] F) -> E ->SWOT[σ] F)
  proof: equiv.symm.surjective

中文:
引理 ofCLM_surjective
  结论: 函数.满射 (ofCLM : (E ->SL[σ] F) -> E ->SWOT[σ] F)
  证明: equiv.symm.surjective

Depends on / 依赖: equiv.symm.surjective, surjective
-/
lemma ofCLM_surjective : Function.Surjective (ofCLM : (E ->SL[σ] F) -> E ->SWOT[σ] F) :=
  equiv.symm.surjective

/--
lemma `ofCLM_bijective` / 引理 `ofCLM_bijective`

English:
lemma ofCLM_bijective
  statement: Function.Bijective (ofCLM : (E ->SL[σ] F) -> E ->SWOT[σ] F)
  proof: equiv.symm.bijective

中文:
引理 ofCLM_bijective
  结论: 函数.双射 (ofCLM : (E ->SL[σ] F) -> E ->SWOT[σ] F)
  证明: equiv.symm.bijective

Depends on / 依赖: bijective, equiv.symm.bijective
-/
lemma ofCLM_bijective : Function.Bijective (ofCLM : (E ->SL[σ] F) -> E ->SWOT[σ] F) :=
  equiv.symm.bijective

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: [IsTopologicalAddGroup F]
  body: equiv.addCommGroup

中文:
实例 instAddCommGroup
  签名: [是拓扑加群 F]
  定义体: equiv.addCommGroup

Depends on / 依赖: addCommGroup, equiv.addCommGroup
-/
instance instAddCommGroup [IsTopologicalAddGroup F] :
    AddCommGroup (E ->SWOT[σ] F) :=
  equiv.addCommGroup

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: {S : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F] [ContinuousConstSMul S F]
  body: equiv.smul S

中文:
实例 instSMul
  签名: {S : 类型} [分配标量乘法 S F] [标量交换类 𝕜₂ S F] [连续常数标量乘法 S F]
  定义体: equiv.smul S

Depends on / 依赖: equiv.smul
-/
instance instSMul {S : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F] [ContinuousConstSMul S F] :
    SMul S (E ->SWOT[σ] F) :=
  equiv.smul S

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: {S : Type*} [Semiring S] [Module S F] [SMulCommClass 𝕜₂ S F]
  body: equiv.module S

中文:
实例 instModule
  签名: {S : 类型} [半环 S] [模 S F] [标量交换类 𝕜₂ S F]
  定义体: equiv.module S

Depends on / 依赖: equiv.module, module
-/
instance instModule {S : Type*} [Semiring S] [Module S F] [SMulCommClass 𝕜₂ S F]
    [ContinuousConstSMul S F] [IsTopologicalAddGroup F] :
    Module S (E ->SWOT[σ] F) :=
  equiv.module S

/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: {S T : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F]
  body: equiv.isScalarTower S T

中文:
实例 instIsScalarTower
  签名: {S T : 类型} [分配标量乘法 S F] [标量交换类 𝕜₂ S F]
  定义体: equiv.isScalarTower S T

Depends on / 依赖: equiv.isScalarTower, isScalarTower
-/
instance instIsScalarTower {S T : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F]
    [ContinuousConstSMul S F] [DistribSMul T F] [SMulCommClass 𝕜₂ T F]
    [ContinuousConstSMul T F] [SMul S T] [IsScalarTower S T F] :
    IsScalarTower S T (E ->SWOT[σ] F) :=
  equiv.isScalarTower S T

/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: {S T : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F]
  body: equiv.smulCommClass S T

中文:
实例 instSMulCommClass
  签名: {S T : 类型} [分配标量乘法 S F] [标量交换类 𝕜₂ S F]
  定义体: equiv.smulCommClass S T

Depends on / 依赖: equiv.smulCommClass, smulCommClass
-/
instance instSMulCommClass {S T : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F]
    [ContinuousConstSMul S F] [DistribSMul T F] [SMulCommClass 𝕜₂ T F]
    [ContinuousConstSMul T F] [SMulCommClass S T F] :
    SMulCommClass S T (E ->SWOT[σ] F) :=
  equiv.smulCommClass S T

/--
Instance `instIsCentralScalar` / 实例 `instIsCentralScalar`

English:
instance instIsCentralScalar
  signature: {S : Type*} [Semiring S] [Module S F] [SMulCommClass 𝕜₂ S F]
  body: equiv.isCentralScalar S

中文:
实例 instIsCentralScalar
  签名: {S : 类型} [半环 S] [模 S F] [标量交换类 𝕜₂ S F]
  定义体: equiv.isCentralScalar S

Depends on / 依赖: equiv.isCentralScalar, isCentralScalar
-/
instance instIsCentralScalar {S : Type*} [Semiring S] [Module S F] [SMulCommClass 𝕜₂ S F]
    [ContinuousConstSMul S F] [Module Sᵐᵒᵖ F] [IsCentralScalar S F] :
    IsCentralScalar S (E ->SWOT[σ] F) :=
  equiv.isCentralScalar S

/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: [IsTopologicalAddGroup E]
  body: equiv.ring

中文:
实例 instRing
  签名: [是拓扑加群 E]
  定义体: equiv.ring

Depends on / 依赖: equiv.ring
-/
instance instRing [IsTopologicalAddGroup E] : Ring (E ->WOT[𝕜₁] E) :=
  equiv.ring

/--
Instance `instAlgebra` / 实例 `instAlgebra`

English:
instance instAlgebra
  signature: {S : Type*} [CommSemiring S] [Module S E] [SMulCommClass 𝕜₁ S E] [SMul S 𝕜₁]
  body: equiv.algebra S

中文:
实例 instAlgebra
  签名: {S : 类型} [交换半环 S] [模 S E] [标量交换类 𝕜₁ S E] [标量乘法 S 𝕜₁]
  定义体: equiv.algebra S

Depends on / 依赖: algebra, equiv.algebra
-/
instance instAlgebra {S : Type*} [CommSemiring S] [Module S E] [SMulCommClass 𝕜₁ S E] [SMul S 𝕜₁]
    [IsScalarTower S 𝕜₁ E] [ContinuousConstSMul S E] [IsTopologicalAddGroup E] :
    Algebra S (E ->WOT[𝕜₁] E) :=
  equiv.algebra S

/-- The additive group equivalence between `ContinuousLinearMapWOT` and `ContinuousLinearMap`. -/
@[simps!]
/--
Definition of `addEquiv` / `addEquiv` 的定义

English:
definition addEquiv
  signature: [IsTopologicalAddGroup F]
  body: equiv.addEquiv

中文:
定义 addEquiv
  签名: [是拓扑加群 F]
  定义体: equiv.addEquiv

Depends on / 依赖: addEquiv, equiv.addEquiv
-/
def addEquiv [IsTopologicalAddGroup F] : (E ->SWOT[σ] F) ≃+ (E ->SL[σ] F) :=
  equiv.addEquiv

/-- The linear equivalence between `ContinuousLinearMapWOT` and `ContinuousLinearMap`. -/
@[simps!]
/--
Definition of `linearEquiv` / `linearEquiv` 的定义

English:
definition linearEquiv
  signature: (S : Type*) [Semiring S] [Module S F] [SMulCommClass 𝕜₂ S F]
  body: equiv.linearEquiv S

中文:
定义 linearEquiv
  签名: (S : 类型) [半环 S] [模 S F] [标量交换类 𝕜₂ S F]
  定义体: equiv.linearEquiv S

Depends on / 依赖: equiv.linearEquiv, linearEquiv
-/
def linearEquiv (S : Type*) [Semiring S] [Module S F] [SMulCommClass 𝕜₂ S F]
    [ContinuousConstSMul S F] [IsTopologicalAddGroup F] :
    (E ->SWOT[σ] F) ≃ₗ[S] (E ->SL[σ] F) :=
  equiv.linearEquiv S

/-- The ring equivalence between `ContinuousLinearMapWOT` and `ContinuousLinearMap`. -/
@[simps!]
/--
Definition of `ringEquiv` / `ringEquiv` 的定义

English:
definition ringEquiv
  signature: [IsTopologicalAddGroup E]
  body: equiv.ringEquiv

中文:
定义 ringEquiv
  签名: [是拓扑加群 E]
  定义体: equiv.ringEquiv

Depends on / 依赖: equiv.ringEquiv, ringEquiv
-/
def ringEquiv [IsTopologicalAddGroup E] : (E ->WOT[𝕜₁] E) ≃+* (E ->L[𝕜₁] E) :=
  equiv.ringEquiv

/-- The algebra equivalence between `ContinuousLinearMapWOT` and `ContinuousLinearMap`. -/
@[simps!]
/--
Definition of `algEquiv` / `algEquiv` 的定义

English:
definition algEquiv
  signature: (S : Type*) [CommSemiring S] [Module S E] [SMulCommClass 𝕜₁ S E] [SMul S 𝕜₁]
  body: equiv.algEquiv S

中文:
定义 algEquiv
  签名: (S : 类型) [交换半环 S] [模 S E] [标量交换类 𝕜₁ S E] [标量乘法 S 𝕜₁]
  定义体: equiv.algEquiv S

Depends on / 依赖: algEquiv, equiv.algEquiv
-/
def algEquiv (S : Type*) [CommSemiring S] [Module S E] [SMulCommClass 𝕜₁ S E] [SMul S 𝕜₁]
    [IsScalarTower S 𝕜₁ E] [ContinuousConstSMul S E] [IsTopologicalAddGroup E] :
    (E ->WOT[𝕜₁] E) ≃ₐ[S] (E ->L[𝕜₁] E) :=
  equiv.algEquiv S

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (E ->SWOT[σ] F) E F where
  body: toCLM f
  coe_injective := DFunLike.coe_injective.comp toCLM_injective

@[simp]

中文:
实例 instFunLike
  签名: : 函数状 (E ->SWOT[σ] F) E F where
  定义体: toCLM f
  coe_injective := DFunLike.coe_injective.comp toCLM_injective

@[simp]
-/
instance instFunLike : FunLike (E ->SWOT[σ] F) E F where
  coe f := toCLM f
  coe_injective := DFunLike.coe_injective.comp toCLM_injective

@[simp]
/--
lemma `coe_toCLM` / 引理 `coe_toCLM`

English:
lemma coe_toCLM
  given: (A : E ->SWOT[σ] F)
  statement: ⇑(toCLM A : E ->SL[σ] F) = A
  proof: rfl

@[simp]

中文:
引理 coe_toCLM
  条件: (A : E ->SWOT[σ] F)
  结论: ⇑(toCLM A : E ->SL[σ] F) = A
  证明: rfl

@[simp]
-/
lemma coe_toCLM (A : E ->SWOT[σ] F) : ⇑(toCLM A : E ->SL[σ] F) = A := rfl

@[simp]
/--
lemma `coe_ofCLM` / 引理 `coe_ofCLM`

English:
lemma coe_ofCLM
  given: (A : E ->SL[σ] F)
  statement: ⇑(ofCLM A : E ->SWOT[σ] F) = A
  proof: rfl

中文:
引理 coe_ofCLM
  条件: (A : E ->SL[σ] F)
  结论: ⇑(ofCLM A : E ->SWOT[σ] F) = A
  证明: rfl
-/
lemma coe_ofCLM (A : E ->SL[σ] F) : ⇑(ofCLM A : E ->SWOT[σ] F) = A := rfl

/--
Instance `instContinuousLinearMapClass` / 实例 `instContinuousLinearMapClass`

English:
instance instContinuousLinearMapClass
  signature: : ContinuousSemilinearMapClass (E ->SWOT[σ] F) σ E F where
  body: by simp [← coe_toCLM]
  map_smulₛₗ f r x := by simp [← coe_toCLM]
  map_continuous f := f.toCLM.continuous

@[simp]

中文:
实例 instContinuousLinearMapClass
  签名: : 连续半线性映射类 (E ->SWOT[σ] F) σ E F where
  定义体: by simp [← coe_toCLM]
  map_smulₛₗ f r x := by simp [← coe_toCLM]
  map_continuous f := f.toCLM.continuous

@[simp]

Depends on / 依赖: coe_toCLM, continuous, f.toCLM.continuous, map_continuous
-/
instance instContinuousLinearMapClass : ContinuousSemilinearMapClass (E ->SWOT[σ] F) σ E F where
  map_add f x y := by simp [← coe_toCLM]
  map_smulₛₗ f r x := by simp [← coe_toCLM]
  map_continuous f := f.toCLM.continuous

@[simp]
/--
lemma `ofCLM_toCLM` / 引理 `ofCLM_toCLM`

English:
lemma ofCLM_toCLM
  given: (A : E ->SWOT[σ] F)
  statement: ofCLM (toCLM A) = A
  proof: rfl

中文:
引理 ofCLM_toCLM
  条件: (A : E ->SWOT[σ] F)
  结论: ofCLM (toCLM A) = A
  证明: rfl
-/
lemma ofCLM_toCLM (A : E ->SWOT[σ] F) : ofCLM (toCLM A) = A := rfl

-- not marked `simp` because Lean just sees `A` on the left-hand side
/--
lemma `toCLM_ofCLM` / 引理 `toCLM_ofCLM`

English:
lemma toCLM_ofCLM
  given: (A : E ->SL[σ] F)
  statement: toCLM (ofCLM A) = A
  proof: rfl

@[simp]

中文:
引理 toCLM_ofCLM
  条件: (A : E ->SL[σ] F)
  结论: toCLM (ofCLM A) = A
  证明: rfl

@[simp]
-/
lemma toCLM_ofCLM (A : E ->SL[σ] F) : toCLM (ofCLM A) = A := rfl

@[simp]
/--
lemma `toCLM_apply` / 引理 `toCLM_apply`

English:
lemma toCLM_apply
  given: {A : E ->SWOT[σ] F} {x : E}
  statement: toCLM A x = A x
  proof: rfl

@[simp]

中文:
引理 toCLM_apply
  条件: {A : E ->SWOT[σ] F} {x : E}
  结论: toCLM A x = A x
  证明: rfl

@[simp]
-/
lemma toCLM_apply {A : E ->SWOT[σ] F} {x : E} : toCLM A x = A x := rfl

@[simp]
/--
lemma `ofCLM_apply` / 引理 `ofCLM_apply`

English:
lemma ofCLM_apply
  given: {A : E ->SL[σ] F} {x : E}
  statement: ofCLM A x = A x
  proof: rfl

@[deprecated (since := "2026-04-10")] alias _root_.ContinuousLinearMap.toWOT_apply := ofCLM_apply

@[ext]

中文:
引理 ofCLM_apply
  条件: {A : E ->SL[σ] F} {x : E}
  结论: ofCLM A x = A x
  证明: rfl

@[deprecated (since := "2026-04-10")] alias _root_.ContinuousLinearMap.toWOT_apply := ofCLM_apply

@[ext]
-/
lemma ofCLM_apply {A : E ->SL[σ] F} {x : E} : ofCLM A x = A x := rfl

@[deprecated (since := "2026-04-10")] alias _root_.ContinuousLinearMap.toWOT_apply := ofCLM_apply

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {A B : E ->SWOT[σ] F} (h : forall x, A x = B x)
  statement: A = B
  proof: toCLM_injective ContinuousLinearMap.ext h

中文:
引理 ext
  条件: {A B : E ->SWOT[σ] F} (h : 对任意 x, A x = B x)
  结论: A = B
  证明: toCLM_injective ContinuousLinearMap.ext h

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext, toCLM_injective
-/
lemma ext {A B : E ->SWOT[σ] F} (h : forall x, A x = B x) : A = B :=
toCLM_injective ContinuousLinearMap.ext h

-- This `ext` lemma is set at a lower priority than the default of 1000, so that the
-- version with an inner product (`ContinuousLinearMapWOT.ext_inner`) takes precedence
-- in the case of Hilbert spaces.
@[ext 900]
/--
lemma `ext_dual` / 引理 `ext_dual`

English:
lemma ext_dual
  statement: [H : SeparatingDual 𝕜₂ F] {A B : E ->SWOT[σ] F}
  proof: by
  simp_rw [ContinuousLinearMapWOT.ext_iff, ← (separatingDual_iff_injective.mp H).eq_iff,
    LinearMap.ext_iff]
  exact h

中文:
引理 ext_dual
  结论: [H : SeparatingDual 𝕜₂ F] {A B : E ->SWOT[σ] F}
  证明: by
  simp_rw [ContinuousLinearMapWOT.ext_iff, ← (separatingDual_iff_injective.mp H).eq_iff,
    LinearMap.ext_iff]
  exact h

Depends on / 依赖: ContinuousLinearMapWOT, ContinuousLinearMapWOT.ext_iff, LinearMap, LinearMap.ext_iff, eq_iff, ext_iff, separatingDual_iff_injective, separatingDual_iff_injective.mp, simp_rw
-/
lemma ext_dual [H : SeparatingDual 𝕜₂ F] {A B : E ->SWOT[σ] F}
    (h : forall x (y : F⋆), y (A x) = y (B x)) : A = B := by
  simp_rw [ContinuousLinearMapWOT.ext_iff, ← (separatingDual_iff_injective.mp H).eq_iff,
    LinearMap.ext_iff]
  exact h

section SMul

variable {S : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F] [ContinuousConstSMul S F]

/--
lemma `ofCLM_smul` / 引理 `ofCLM_smul`

English:
lemma ofCLM_smul
  given: {c : S} {f : E ->SL[σ] F}
  statement: ofCLM (c • f) = c • ofCLM f
  proof: rfl

中文:
引理 ofCLM_smul
  条件: {c : S} {f : E ->SL[σ] F}
  结论: ofCLM (c • f) = c • ofCLM f
  证明: rfl
-/
@[simp] lemma ofCLM_smul {c : S} {f : E ->SL[σ] F} : ofCLM (c • f) = c • ofCLM f := rfl
/--
lemma `toCLM_smul` / 引理 `toCLM_smul`

English:
lemma toCLM_smul
  given: {c : S} {f : E ->SWOT[σ] F}
  statement: toCLM (c • f) = c • toCLM f
  proof: rfl

中文:
引理 toCLM_smul
  条件: {c : S} {f : E ->SWOT[σ] F}
  结论: toCLM (c • f) = c • toCLM f
  证明: rfl
-/
@[simp] lemma toCLM_smul {c : S} {f : E ->SWOT[σ] F} : toCLM (c • f) = c • toCLM f := rfl
/--
lemma `smul_apply` / 引理 `smul_apply`

English:
lemma smul_apply
  given: {f : E ->SWOT[σ] F} (c : S) (x : E)
  statement: (c • f) x = c • (f x)
  proof: rfl

中文:
引理 smul_apply
  条件: {f : E ->SWOT[σ] F} (c : S) (x : E)
  结论: (c • f) x = c • (f x)
  证明: rfl
-/
@[simp] lemma smul_apply {f : E ->SWOT[σ] F} (c : S) (x : E) : (c • f) x = c • (f x) := rfl

end SMul

section Algebra

variable {S : Type*} [CommSemiring S] [Module S E] [SMulCommClass 𝕜₁ S E] [SMul S 𝕜₁]
    [IsScalarTower S 𝕜₁ E] [ContinuousConstSMul S E] [IsTopologicalAddGroup E]

/--
lemma `toCLM_algebraMap` / 引理 `toCLM_algebraMap`

English:
lemma toCLM_algebraMap
  given: (c : S)
  proof: rfl

中文:
引理 toCLM_algebraMap
  条件: (c : S)
  证明: rfl
-/
@[simp] lemma toCLM_algebraMap (c : S) :
    toCLM (algebraMap S (E ->WOT[𝕜₁] E) c) = algebraMap S (E ->L[𝕜₁] E) c :=
  rfl

/--
lemma `ofCLM_algebraMap` / 引理 `ofCLM_algebraMap`

English:
lemma ofCLM_algebraMap
  given: (c : S)
  proof: rfl

中文:
引理 ofCLM_algebraMap
  条件: (c : S)
  证明: rfl
-/
@[simp] lemma ofCLM_algebraMap (c : S) :
    ofCLM (algebraMap S (E ->L[𝕜₁] E) c) = algebraMap S (E ->WOT[𝕜₁] E) c :=
  rfl

/--
lemma `algebraMapCLM_apply` / 引理 `algebraMapCLM_apply`

English:
lemma algebraMapCLM_apply
  given: (c : S) (x : E)
  proof: rfl

中文:
引理 algebraMapCLM_apply
  条件: (c : S) (x : E)
  证明: rfl
-/
@[simp] lemma algebraMapCLM_apply (c : S) (x : E) :
    (algebraMap S (E ->WOT[𝕜₁] E) c) x = c • x :=
  rfl

end Algebra

variable [IsTopologicalAddGroup F]

/--
lemma `ofCLM_zero` / 引理 `ofCLM_zero`

English:
lemma ofCLM_zero
  statement: ofCLM (0 : E ->SL[σ] F) = 0
  proof: rfl

中文:
引理 ofCLM_zero
  结论: ofCLM (0 : E ->SL[σ] F) = 0
  证明: rfl
-/
@[simp] lemma ofCLM_zero : ofCLM (0 : E ->SL[σ] F) = 0 := rfl
/--
lemma `ofCLM_add` / 引理 `ofCLM_add`

English:
lemma ofCLM_add
  given: {f g : E ->SL[σ] F}
  statement: ofCLM (f + g) = ofCLM f + ofCLM g
  proof: rfl

中文:
引理 ofCLM_add
  条件: {f g : E ->SL[σ] F}
  结论: ofCLM (f + g) = ofCLM f + ofCLM g
  证明: rfl
-/
@[simp] lemma ofCLM_add {f g : E ->SL[σ] F} : ofCLM (f + g) = ofCLM f + ofCLM g := rfl
/--
lemma `ofCLM_sub` / 引理 `ofCLM_sub`

English:
lemma ofCLM_sub
  given: {f g : E ->SL[σ] F}
  statement: ofCLM (f - g) = ofCLM f - ofCLM g
  proof: rfl

中文:
引理 ofCLM_sub
  条件: {f g : E ->SL[σ] F}
  结论: ofCLM (f - g) = ofCLM f - ofCLM g
  证明: rfl
-/
@[simp] lemma ofCLM_sub {f g : E ->SL[σ] F} : ofCLM (f - g) = ofCLM f - ofCLM g := rfl
/--
lemma `ofCLM_neg` / 引理 `ofCLM_neg`

English:
lemma ofCLM_neg
  given: {f : E ->SL[σ] F}
  statement: ofCLM (-f) = -ofCLM f
  proof: rfl

中文:
引理 ofCLM_neg
  条件: {f : E ->SL[σ] F}
  结论: ofCLM (-f) = -ofCLM f
  证明: rfl
-/
@[simp] lemma ofCLM_neg {f : E ->SL[σ] F} : ofCLM (-f) = -ofCLM f := rfl
/--
lemma `ofCLM_mul` / 引理 `ofCLM_mul`

English:
lemma ofCLM_mul
  given: (f g : F ->L[𝕜₂] F)
  statement: ofCLM (f * g) = ofCLM f * ofCLM g
  proof: rfl

中文:
引理 ofCLM_mul
  条件: (f g : F ->L[𝕜₂] F)
  结论: ofCLM (f * g) = ofCLM f * ofCLM g
  证明: rfl
-/
@[simp] lemma ofCLM_mul (f g : F ->L[𝕜₂] F) : ofCLM (f * g) = ofCLM f * ofCLM g := rfl
/--
lemma `ofCLM_one` / 引理 `ofCLM_one`

English:
lemma ofCLM_one
  statement: ofCLM (1 : F ->L[𝕜₂] F) = 1
  proof: rfl

中文:
引理 ofCLM_one
  结论: ofCLM (1 : F ->L[𝕜₂] F) = 1
  证明: rfl

Depends on / 依赖: fast_instance
-/
@[simp] lemma ofCLM_one : ofCLM (1 : F ->L[𝕜₂] F) = 1 := rfl
/--
lemma `ofCLM_pow` / 引理 `ofCLM_pow`

English:
lemma ofCLM_pow
  given: (f : F ->L[𝕜₂] F) (n : Nat)
  statement: ofCLM (f ^ n) = ofCLM f ^ n
  proof: rfl

中文:
引理 ofCLM_pow
  条件: (f : F ->L[𝕜₂] F) (n : 自然数)
  结论: ofCLM (f ^ n) = ofCLM f ^ n
  证明: rfl
-/
@[simp] lemma ofCLM_pow (f : F ->L[𝕜₂] F) (n : Nat) : ofCLM (f ^ n) = ofCLM f ^ n := rfl
/--
lemma `ofCLM_natCast` / 引理 `ofCLM_natCast`

English:
lemma ofCLM_natCast
  given: (n : Nat)
  statement: ofCLM (n : F ->L[𝕜₂] F) = n
  proof: rfl

中文:
引理 ofCLM_natCast
  条件: (n : 自然数)
  结论: ofCLM (n : F ->L[𝕜₂] F) = n
  证明: rfl
-/
@[simp] lemma ofCLM_natCast (n : Nat) : ofCLM (n : F ->L[𝕜₂] F) = n := rfl
/--
lemma `ofCLM_intCast` / 引理 `ofCLM_intCast`

English:
lemma ofCLM_intCast
  given: (n : Int)
  statement: ofCLM (n : F ->L[𝕜₂] F) = n
  proof: rfl

中文:
引理 ofCLM_intCast
  条件: (n : 整数)
  结论: ofCLM (n : F ->L[𝕜₂] F) = n
  证明: rfl
-/
@[simp] lemma ofCLM_intCast (n : Int) : ofCLM (n : F ->L[𝕜₂] F) = n := rfl

/--
lemma `toCLM_zero` / 引理 `toCLM_zero`

English:
lemma toCLM_zero
  statement: toCLM (0 : E ->SWOT[σ] F) = 0
  proof: rfl

中文:
引理 toCLM_zero
  结论: toCLM (0 : E ->SWOT[σ] F) = 0
  证明: rfl
-/
@[simp] lemma toCLM_zero : toCLM (0 : E ->SWOT[σ] F) = 0 := rfl
/--
lemma `toCLM_add` / 引理 `toCLM_add`

English:
lemma toCLM_add
  given: {f g : E ->SWOT[σ] F}
  statement: toCLM (f + g) = toCLM f + toCLM g
  proof: rfl

中文:
引理 toCLM_add
  条件: {f g : E ->SWOT[σ] F}
  结论: toCLM (f + g) = toCLM f + toCLM g
  证明: rfl
-/
@[simp] lemma toCLM_add {f g : E ->SWOT[σ] F} : toCLM (f + g) = toCLM f + toCLM g := rfl
/--
lemma `toCLM_sub` / 引理 `toCLM_sub`

English:
lemma toCLM_sub
  given: {f g : E ->SWOT[σ] F}
  statement: toCLM (f - g) = toCLM f - toCLM g
  proof: rfl

中文:
引理 toCLM_sub
  条件: {f g : E ->SWOT[σ] F}
  结论: toCLM (f - g) = toCLM f - toCLM g
  证明: rfl
-/
@[simp] lemma toCLM_sub {f g : E ->SWOT[σ] F} : toCLM (f - g) = toCLM f - toCLM g := rfl
/--
lemma `toCLM_neg` / 引理 `toCLM_neg`

English:
lemma toCLM_neg
  given: {f : E ->SWOT[σ] F}
  statement: toCLM (-f) = -toCLM f
  proof: rfl

中文:
引理 toCLM_neg
  条件: {f : E ->SWOT[σ] F}
  结论: toCLM (-f) = -toCLM f
  证明: rfl
-/
@[simp] lemma toCLM_neg {f : E ->SWOT[σ] F} : toCLM (-f) = -toCLM f := rfl
/--
lemma `toCLM_mul` / 引理 `toCLM_mul`

English:
lemma toCLM_mul
  given: (f g : F ->WOT[𝕜₂] F)
  statement: toCLM (f * g) = toCLM f * toCLM g
  proof: rfl

中文:
引理 toCLM_mul
  条件: (f g : F ->WOT[𝕜₂] F)
  结论: toCLM (f * g) = toCLM f * toCLM g
  证明: rfl
-/
@[simp] lemma toCLM_mul (f g : F ->WOT[𝕜₂] F) : toCLM (f * g) = toCLM f * toCLM g := rfl
/--
lemma `toCLM_one` / 引理 `toCLM_one`

English:
lemma toCLM_one
  statement: toCLM (1 : F ->WOT[𝕜₂] F) = 1
  proof: rfl

中文:
引理 toCLM_one
  结论: toCLM (1 : F ->WOT[𝕜₂] F) = 1
  证明: rfl
-/
@[simp] lemma toCLM_one : toCLM (1 : F ->WOT[𝕜₂] F) = 1 := rfl
/--
lemma `toCLM_pow` / 引理 `toCLM_pow`

English:
lemma toCLM_pow
  given: (f : F ->WOT[𝕜₂] F) (n : Nat)
  statement: (f ^ n).toCLM = f.toCLM ^ n
  proof: rfl

中文:
引理 toCLM_pow
  条件: (f : F ->WOT[𝕜₂] F) (n : 自然数)
  结论: (f ^ n).toCLM = f.toCLM ^ n
  证明: rfl
-/
@[simp] lemma toCLM_pow (f : F ->WOT[𝕜₂] F) (n : Nat) : (f ^ n).toCLM = f.toCLM ^ n := rfl
/--
lemma `toCLM_natCast` / 引理 `toCLM_natCast`

English:
lemma toCLM_natCast
  given: (n : Nat)
  statement: (n : F ->WOT[𝕜₂] F).toCLM = n
  proof: rfl

中文:
引理 toCLM_natCast
  条件: (n : 自然数)
  结论: (n : F ->WOT[𝕜₂] F).toCLM = n
  证明: rfl

Depends on / 依赖: smul_left_def
-/
@[simp] lemma toCLM_natCast (n : Nat) : (n : F ->WOT[𝕜₂] F).toCLM = n := rfl
/--
lemma `toCLM_intCast` / 引理 `toCLM_intCast`

English:
lemma toCLM_intCast
  given: (n : Int)
  statement: (n : F ->WOT[𝕜₂] F).toCLM = n
  proof: rfl

中文:
引理 toCLM_intCast
  条件: (n : 整数)
  结论: (n : F ->WOT[𝕜₂] F).toCLM = n
  证明: rfl

Depends on / 依赖: isScalarTower
-/
@[simp] lemma toCLM_intCast (n : Int) : (n : F ->WOT[𝕜₂] F).toCLM = n := rfl

/--
lemma `zero_apply` / 引理 `zero_apply`

English:
lemma zero_apply
  given: (x : E)
  statement: (0 : E ->SWOT[σ] F) x = 0
  proof: rfl

中文:
引理 zero_apply
  条件: (x : E)
  结论: (0 : E ->SWOT[σ] F) x = 0
  证明: rfl

Depends on / 依赖: smul_left_def, smul_right_def
-/
@[simp] lemma zero_apply (x : E) : (0 : E ->SWOT[σ] F) x = 0 := rfl
/--
lemma `add_apply` / 引理 `add_apply`

English:
lemma add_apply
  given: {f g : E ->SWOT[σ] F} (x : E)
  statement: (f + g) x = f x + g x
  proof: rfl

中文:
引理 add_apply
  条件: {f g : E ->SWOT[σ] F} (x : E)
  结论: (f + g) x = f x + g x
  证明: rfl
-/
@[simp] lemma add_apply {f g : E ->SWOT[σ] F} (x : E) : (f + g) x = f x + g x := rfl
/--
lemma `sub_apply` / 引理 `sub_apply`

English:
lemma sub_apply
  given: {f g : E ->SWOT[σ] F} (x : E)
  statement: (f - g) x = f x - g x
  proof: rfl

中文:
引理 sub_apply
  条件: {f g : E ->SWOT[σ] F} (x : E)
  结论: (f - g) x = f x - g x
  证明: rfl
-/
@[simp] lemma sub_apply {f g : E ->SWOT[σ] F} (x : E) : (f - g) x = f x - g x := rfl
/--
lemma `neg_apply` / 引理 `neg_apply`

English:
lemma neg_apply
  given: {f : E ->SWOT[σ] F} (x : E)
  statement: (-f) x = -(f x)
  proof: rfl

中文:
引理 neg_apply
  条件: {f : E ->SWOT[σ] F} (x : E)
  结论: (-f) x = -(f x)
  证明: rfl
-/
@[simp] lemma neg_apply {f : E ->SWOT[σ] F} (x : E) : (-f) x = -(f x) := rfl
/--
lemma `mul_apply` / 引理 `mul_apply`

English:
lemma mul_apply
  given: (f g : F ->WOT[𝕜₂] F) (x : F)
  statement: (f * g) x = f (g x)
  proof: rfl

中文:
引理 mul_apply
  条件: (f g : F ->WOT[𝕜₂] F) (x : F)
  结论: (f * g) x = f (g x)
  证明: rfl
-/
@[simp] lemma mul_apply (f g : F ->WOT[𝕜₂] F) (x : F) : (f * g) x = f (g x) := rfl
/--
lemma `one_apply` / 引理 `one_apply`

English:
lemma one_apply
  given: (x : F)
  statement: (1 : F ->WOT[𝕜₂] F) x = x
  proof: rfl

中文:
引理 one_apply
  条件: (x : F)
  结论: (1 : F ->WOT[𝕜₂] F) x = x
  证明: rfl
-/
@[simp] lemma one_apply (x : F) : (1 : F ->WOT[𝕜₂] F) x = x := rfl
/--
lemma `natCast_apply` / 引理 `natCast_apply`

English:
lemma natCast_apply
  given: (n : Nat) (x : F)
  statement: (n : F ->WOT[𝕜₂] F) x = n • x
  proof: rfl

中文:
引理 natCast_apply
  条件: (n : 自然数) (x : F)
  结论: (n : F ->WOT[𝕜₂] F) x = n • x
  证明: rfl
-/
@[simp] lemma natCast_apply (n : Nat) (x : F) : (n : F ->WOT[𝕜₂] F) x = n • x := rfl
/--
lemma `intCast_apply` / 引理 `intCast_apply`

English:
lemma intCast_apply
  given: (n : Int) (x : F)
  statement: (n : F ->WOT[𝕜₂] F) x = n • x
  proof: rfl

中文:
引理 intCast_apply
  条件: (n : 整数) (x : F)
  结论: (n : F ->WOT[𝕜₂] F) x = n • x
  证明: rfl

Depends on / 依赖: algebra, fast_instance
-/
@[simp] lemma intCast_apply (n : Int) (x : F) : (n : F ->WOT[𝕜₂] F) x = n • x := rfl

end Basic

/-!
### The topology of `E →WOT[𝕜] F`

The section endows `E →WOT[𝕜] F` with the weak operator topology and shows the basic properties
of this topology. In particular, we show that it is a topological vector space.
-/
section Topology

variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F]

variable (σ E F) in
/--
Definition of `inducingFn` / `inducingFn` 的定义

English:
definition inducingFn
  signature: : (E ->SWOT[σ] F) ->ₗ[𝕜₂] (E × F⋆ -> 𝕜₂) where
  body: fun A ⟨x, y⟩ => y (A x)
  map_add' := fun x y => by ext; simp
  map_smul' := fun x y => by ext; simp

@[simp]

中文:
定义 inducingFn
  签名: : (E ->SWOT[σ] F) ->ₗ[𝕜₂] (E × F⋆ -> 𝕜₂) where
  定义体: fun A ⟨x, y⟩ => y (A x)
  map_add' := fun x y => by ext; simp
  map_smul' := fun x y => by ext; simp

@[simp]
-/
def inducingFn : (E ->SWOT[σ] F) ->ₗ[𝕜₂] (E × F⋆ -> 𝕜₂) where
  toFun := fun A ⟨x, y⟩ => y (A x)
  map_add' := fun x y => by ext; simp
  map_smul' := fun x y => by ext; simp

@[simp]
/--
lemma `inducingFn_apply` / 引理 `inducingFn_apply`

English:
lemma inducingFn_apply
  given: {f : E ->SWOT[σ] F} {x : E} {y : F⋆}
  proof: rfl

中文:
引理 inducingFn_apply
  条件: {f : E ->SWOT[σ] F} {x : E} {y : F⋆}
  证明: rfl
-/
lemma inducingFn_apply {f : E ->SWOT[σ] F} {x : E} {y : F⋆} :
    inducingFn σ E F f (x, y) = y (f x) :=
  rfl

/--
Instance `instTopologicalSpace` / 实例 `instTopologicalSpace`

English:
instance instTopologicalSpace
  signature: : TopologicalSpace (E ->SWOT[σ] F)
  body: .induced (inducingFn _ _ _) Pi.topologicalSpace

@[fun_prop]

中文:
实例 instTopologicalSpace
  签名: : 拓扑空间 (E ->SWOT[σ] F)
  定义体: .induced (inducingFn _ _ _) Pi.topologicalSpace

@[fun_prop]

Depends on / 依赖: Pi.topologicalSpace, induced, inducingFn, topologicalSpace
-/
instance instTopologicalSpace : TopologicalSpace (E ->SWOT[σ] F) :=
  .induced (inducingFn _ _ _) Pi.topologicalSpace

@[fun_prop]
/--
lemma `continuous_inducingFn` / 引理 `continuous_inducingFn`

English:
lemma continuous_inducingFn
  statement: Continuous (inducingFn σ E F)
  proof: continuous_induced_dom

中文:
引理 continuous_inducingFn
  结论: 连续 (inducingFn σ E F)
  证明: continuous_induced_dom

Depends on / 依赖: continuous_induced_dom
-/
lemma continuous_inducingFn : Continuous (inducingFn σ E F) :=
  continuous_induced_dom

/--
lemma `continuous_dual_apply` / 引理 `continuous_dual_apply`

English:
lemma continuous_dual_apply
  given: (x : E) (y : F⋆)
  statement: Continuous fun (A : E ->SWOT[σ] F) => y (A x)
  proof: by
  refine (continuous_pi_iff.mp continuous_inducingFn) ⟨x, y⟩

@[fun_prop]

中文:
引理 continuous_dual_apply
  条件: (x : E) (y : F⋆)
  结论: 连续 fun (A : E ->SWOT[σ] F) => y (A x)
  证明: by
  refine (continuous_pi_iff.mp continuous_inducingFn) ⟨x, y⟩

@[fun_prop]

Depends on / 依赖: add_le, continuous_inducingFn, continuous_pi_iff, continuous_pi_iff.mp, eq_zero_of_map_eq_zero, map_zero, mul_le, norm_add_le, norm_eq_zero, norm_eq_zero.mp, norm_mul, norm_mul_le, norm_neg, norm_zero
-/
lemma continuous_dual_apply (x : E) (y : F⋆) : Continuous fun (A : E ->SWOT[σ] F) => y (A x) := by
  refine (continuous_pi_iff.mp continuous_inducingFn) ⟨x, y⟩

@[fun_prop]
/--
lemma `continuous_of_dual_apply_continuous` / 引理 `continuous_of_dual_apply_continuous`

English:
lemma continuous_of_dual_apply_continuous
  statement: {α : Type*} [TopologicalSpace α] {g : α -> E ->SWOT[σ] F}
  proof: continuous_induced_rng.2 (continuous_pi_iff.mpr fun p => h p.1 p.2)

@[fun_prop]

中文:
引理 continuous_of_dual_apply_continuous
  结论: {α : 类型} [拓扑空间 α] {g : α -> E ->SWOT[σ] F}
  证明: continuous_induced_rng.2 (continuous_pi_iff.mpr fun p => h p.1 p.2)

@[fun_prop]

Depends on / 依赖: continuous_induced_rng, continuous_pi_iff, continuous_pi_iff.mpr
-/
lemma continuous_of_dual_apply_continuous {α : Type*} [TopologicalSpace α] {g : α -> E ->SWOT[σ] F}
    (h : forall x (y : F⋆), Continuous fun a => y (g a x)) : Continuous g :=
  continuous_induced_rng.2 (continuous_pi_iff.mpr fun p => h p.1 p.2)

@[fun_prop]
/--
lemma `isInducing_inducingFn` / 引理 `isInducing_inducingFn`

English:
lemma isInducing_inducingFn
  statement: IsInducing (inducingFn σ E F)
  proof: ⟨rfl⟩

@[fun_prop]

中文:
引理 isInducing_inducingFn
  结论: 是Inducing (inducingFn σ E F)
  证明: ⟨rfl⟩

@[fun_prop]
-/
lemma isInducing_inducingFn : IsInducing (inducingFn σ E F) := ⟨rfl⟩

@[fun_prop]
/--
lemma `isEmbedding_inducingFn` / 引理 `isEmbedding_inducingFn`

English:
lemma isEmbedding_inducingFn
  given: [SeparatingDual 𝕜₂ F]
  statement: IsEmbedding (inducingFn σ E F)
  proof: by
  refine Function.Injective.isEmbedding_induced fun A B hAB => ?_
  rw [ContinuousLinearMapWOT.ext_dual_iff]
  simpa [funext_iff] using hAB

中文:
引理 isEmbedding_inducingFn
  条件: [SeparatingDual 𝕜₂ F]
  结论: 是嵌入 (inducingFn σ E F)
  证明: by
  refine Function.Injective.isEmbedding_induced fun A B hAB => ?_
  rw [ContinuousLinearMapWOT.ext_dual_iff]
  simpa [funext_iff] using hAB

Depends on / 依赖: ContinuousLinearMapWOT, ContinuousLinearMapWOT.ext_dual_iff, Function, Function.Injective.isEmbedding_induced, Injective, ext_dual_iff, funext_iff, isEmbedding_induced
-/
lemma isEmbedding_inducingFn [SeparatingDual 𝕜₂ F] : IsEmbedding (inducingFn σ E F) := by
  refine Function.Injective.isEmbedding_induced fun A B hAB => ?_
  rw [ContinuousLinearMapWOT.ext_dual_iff]
  simpa [funext_iff] using hAB

open Filter in
/--
lemma `tendsto_iff_forall_dual_apply_tendsto` / 引理 `tendsto_iff_forall_dual_apply_tendsto`

English:
lemma tendsto_iff_forall_dual_apply_tendsto
  statement: {α : Type*} {l : Filter α} {f : α -> E ->SWOT[σ] F}
  proof: by
  simp [isInducing_inducingFn.tendsto_nhds_iff, tendsto_pi_nhds]

中文:
引理 tendsto_iff_对任意_dual_apply_tendsto
  结论: {α : 类型} {l : 滤子 α} {f : α -> E ->SWOT[σ] F}
  证明: by
  simp [isInducing_inducingFn.tendsto_nhds_iff, tendsto_pi_nhds]

Depends on / 依赖: isInducing_inducingFn, isInducing_inducingFn.tendsto_nhds_iff, tendsto_nhds_iff, tendsto_pi_nhds
-/
lemma tendsto_iff_forall_dual_apply_tendsto {α : Type*} {l : Filter α} {f : α -> E ->SWOT[σ] F}
    {A : E ->SWOT[σ] F} :
    Tendsto f l (𝓝 A) ↔ forall x (y : F⋆), Tendsto (fun a => y (f a x)) l (𝓝 (y (A x))) := by
  simp [isInducing_inducingFn.tendsto_nhds_iff, tendsto_pi_nhds]

/--
lemma `le_nhds_iff_forall_dual_apply_le_nhds` / 引理 `le_nhds_iff_forall_dual_apply_le_nhds`

English:
lemma le_nhds_iff_forall_dual_apply_le_nhds
  given: {l : Filter (E ->SWOT[σ] F)} {A : E ->SWOT[σ] F}
  proof: tendsto_iff_forall_dual_apply_tendsto (f := id)

中文:
引理 le_nhds_iff_对任意_dual_apply_le_nhds
  条件: {l : 滤子 (E ->SWOT[σ] F)} {A : E ->SWOT[σ] F}
  证明: tendsto_iff_forall_dual_apply_tendsto (f := id)

Depends on / 依赖: tendsto_iff_forall_dual_apply_tendsto
-/
lemma le_nhds_iff_forall_dual_apply_le_nhds {l : Filter (E ->SWOT[σ] F)} {A : E ->SWOT[σ] F} :
    l <= 𝓝 A ↔ forall x (y : F⋆), l.map (fun T => y (T x)) <= 𝓝 (y (A x)) :=
  tendsto_iff_forall_dual_apply_tendsto (f := id)

/--
Instance `instT3Space` / 实例 `instT3Space`

English:
instance instT3Space
  signature: [SeparatingDual 𝕜₂ F]
  body: isEmbedding_inducingFn.t3Space

中文:
实例 instT3Space
  签名: [SeparatingDual 𝕜₂ F]
  定义体: isEmbedding_inducingFn.t3Space

Depends on / 依赖: isEmbedding_inducingFn, isEmbedding_inducingFn.t3Space, t3Space
-/
instance instT3Space [SeparatingDual 𝕜₂ F] : T3Space (E ->SWOT[σ] F) :=
  isEmbedding_inducingFn.t3Space

instance {S : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F] [ContinuousConstSMul S F]
    [SMul S 𝕜₂] [IsScalarTower S 𝕜₂ 𝕜₂] [IsScalarTower S 𝕜₂ F] :
    ContinuousConstSMul S (F ->WOT[𝕜₂] F) where
  continuous_const_smul c := by
    apply continuous_of_dual_apply_continuous fun _ _ => ?_
    simp only [smul_apply, ContinuousLinearMap.map_smul_of_tower]
.comp continuous_dual_apply .. exact continuous_const_smul c

/--
Instance `instContinuousSMul` / 实例 `instContinuousSMul`

English:
instance instContinuousSMul
  signature: {S : Type*} [Semiring S] [Module S F] [SMulCommClass 𝕜₂ S F]
  body: .induced (inducingFn σ E F).restrictScalars S

中文:
实例 instContinuousSMul
  签名: {S : 类型} [半环 S] [模 S F] [标量交换类 𝕜₂ S F]
  定义体: .induced (inducingFn σ E F).restrictScalars S

Depends on / 依赖: induced, inducingFn, restrictScalars
-/
instance instContinuousSMul {S : Type*} [Semiring S] [Module S F] [SMulCommClass 𝕜₂ S F]
    [Module S 𝕜₂] [IsScalarTower S 𝕜₂ F] [IsScalarTower S 𝕜₂ 𝕜₂] [ContinuousConstSMul S F]
    [TopologicalSpace S] [ContinuousSMul S 𝕜₂] :
ContinuousSMul S (E ->SWOT[σ] F) := .induced (inducingFn σ E F).restrictScalars S

/--
Instance `instIsTopologicalAddGroup` / 实例 `instIsTopologicalAddGroup`

English:
instance instIsTopologicalAddGroup
  signature: : IsTopologicalAddGroup (E ->SWOT[σ] F) where
  body: .induced (inducingFn σ E F)
  toContinuousNeg := .induced (inducingFn σ E F)

中文:
实例 instIsTopologicalAddGroup
  签名: : 是拓扑加群 (E ->SWOT[σ] F) where
  定义体: .induced (inducingFn σ E F)
  toContinuousNeg := .induced (inducingFn σ E F)

Depends on / 依赖: induced, inducingFn
-/
instance instIsTopologicalAddGroup : IsTopologicalAddGroup (E ->SWOT[σ] F) where
  toContinuousAdd := .induced (inducingFn σ E F)
  toContinuousNeg := .induced (inducingFn σ E F)

/--
Instance `instUniformSpace` / 实例 `instUniformSpace`

English:
instance instUniformSpace
  signature: : UniformSpace (E ->SWOT[σ] F)
  body: .comap (inducingFn σ E F) inferInstance

中文:
实例 instUniformSpace
  签名: : 一致空间 (E ->SWOT[σ] F)
  定义体: .comap (inducingFn σ E F) inferInstance

Depends on / 依赖: inducingFn
-/
instance instUniformSpace : UniformSpace (E ->SWOT[σ] F) := .comap (inducingFn σ E F) inferInstance

/--
Instance `instIsUniformAddGroup` / 实例 `instIsUniformAddGroup`

English:
instance instIsUniformAddGroup
  signature: : IsUniformAddGroup (E ->SWOT[σ] F)
  body: .comap (inducingFn σ E F)

中文:
实例 instIsUniformAddGroup
  签名: : 是UniformAdd群 (E ->SWOT[σ] F)
  定义体: .comap (inducingFn σ E F)

Depends on / 依赖: add_le, eq_zero_of_map_eq_zero, inducingFn, map_mul, map_one, map_zero, norm_add_le, norm_eq_zero, norm_eq_zero.mp, norm_mul, norm_neg, norm_one, norm_zero
-/
instance instIsUniformAddGroup : IsUniformAddGroup (E ->SWOT[σ] F) := .comap (inducingFn σ E F)

end Topology

/-! ### The WOT is induced by a family of seminorms -/
section Seminorms

variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F]

/--
Definition of `seminorm` / `seminorm` 的定义

English:
definition seminorm
  signature: (x : E) (y : F⋆)
  body: ‖y (A x)‖
  map_zero' := by simp
  add_le' A B := by simpa using norm_add_le _ _
  neg' A := by simp
  smul' r A := by simp

中文:
定义 seminorm
  签名: (x : E) (y : F⋆)
  定义体: ‖y (A x)‖
  map_zero' := by simp
  add_le' A B := by simpa using norm_add_le _ _
  neg' A := by simp
  smul' r A := by simp
-/
def seminorm (x : E) (y : F⋆) : Seminorm 𝕜₂ (E ->SWOT[σ] F) where
  toFun A := ‖y (A x)‖
  map_zero' := by simp
  add_le' A B := by simpa using norm_add_le _ _
  neg' A := by simp
  smul' r A := by simp

variable (σ E F) in
/--
Definition of `seminormFamily` / `seminormFamily` 的定义

English:
definition seminormFamily
  signature: : SeminormFamily 𝕜₂ (E ->SWOT[σ] F) (E × F⋆)
  body: fun ⟨x, y⟩ => seminorm x y

中文:
定义 seminormFamily
  签名: : SeminormFamily 𝕜₂ (E ->SWOT[σ] F) (E × F⋆)
  定义体: fun ⟨x, y⟩ => seminorm x y

Depends on / 依赖: seminorm
-/
def seminormFamily : SeminormFamily 𝕜₂ (E ->SWOT[σ] F) (E × F⋆) :=
  fun ⟨x, y⟩ => seminorm x y

/--
lemma `withSeminorms` / 引理 `withSeminorms`

English:
lemma withSeminorms
  statement: WithSeminorms (seminormFamily σ E F)
  proof: let e : E × F⋆ ≃ (Σ _ : E × F⋆, Fin 1) := .symm .sigmaUnique _ _
isInducing_inducingFn.withSeminorms withSeminorms_pi (fun _ => norm_withSeminorms 𝕜₂ 𝕜₂)
.congr_equiv e

中文:
引理 withSeminorms
  结论: WithSeminorms (seminormFamily σ E F)
  证明: let e : E × F⋆ ≃ (Σ _ : E × F⋆, Fin 1) := .symm .sigmaUnique _ _
isInducing_inducingFn.withSeminorms withSeminorms_pi (fun _ => norm_withSeminorms 𝕜₂ 𝕜₂)
.congr_equiv e

Depends on / 依赖: congr_equiv, isInducing_inducingFn, isInducing_inducingFn.withSeminorms, norm_withSeminorms, sigmaUnique, withSeminorms, withSeminorms_pi
-/
lemma withSeminorms : WithSeminorms (seminormFamily σ E F) :=
let e : E × F⋆ ≃ (Σ _ : E × F⋆, Fin 1) := .symm .sigmaUnique _ _
isInducing_inducingFn.withSeminorms withSeminorms_pi (fun _ => norm_withSeminorms 𝕜₂ 𝕜₂)
.congr_equiv e

/--
lemma `hasBasis_seminorms` / 引理 `hasBasis_seminorms`

English:
lemma hasBasis_seminorms
  proof: withSeminorms.hasBasis

中文:
引理 hasBasis_seminorms
  证明: withSeminorms.hasBasis

Depends on / 依赖: hasBasis, withSeminorms, withSeminorms.hasBasis
-/
lemma hasBasis_seminorms :
    (𝓝 (0 : E ->SWOT[σ] F)).HasBasis (· in (seminormFamily σ E F).basisSets) id :=
  withSeminorms.hasBasis

/--
Instance `instLocallyConvexSpace` / 实例 `instLocallyConvexSpace`

English:
instance instLocallyConvexSpace
  signature: [NormedSpace Real 𝕜₂] [Module Real (E ->SWOT[σ] F)]
  body: withSeminorms.toLocallyConvexSpace

中文:
实例 instLocallyConvexSpace
  签名: [赋范空间 实数 𝕜₂] [模 实数 (E ->SWOT[σ] F)]
  定义体: withSeminorms.toLocallyConvexSpace

Depends on / 依赖: toLocallyConvexSpace, withSeminorms, withSeminorms.toLocallyConvexSpace
-/
instance instLocallyConvexSpace [NormedSpace Real 𝕜₂] [Module Real (E ->SWOT[σ] F)]
    [IsScalarTower Real 𝕜₂ (E ->SWOT[σ] F)] :
    LocallyConvexSpace Real (E ->SWOT[σ] F) :=
  withSeminorms.toLocallyConvexSpace

end Seminorms

section toWOT_continuous

variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F] [ContinuousSMul 𝕜₁ E]

/-- The weak operator topology is coarser than the bounded convergence topology, i.e. the inclusion
map is continuous. -/
@[continuity, fun_prop]
/--
lemma `continuous_ofCLM` / 引理 `continuous_ofCLM`

English:
lemma continuous_ofCLM
  proof: ContinuousLinearMapWOT.continuous_of_dual_apply_continuous fun x y =>
y.cont.comp continuous_eval_const x

@[deprecated (since := "2026-04-10")] alias ContinuousLinearMap.continuous_toWOT := continuous_ofCLM

中文:
引理 continuous_ofCLM
  证明: ContinuousLinearMapWOT.continuous_of_dual_apply_continuous fun x y =>
y.cont.comp continuous_eval_const x

@[deprecated (since := "2026-04-10")] alias ContinuousLinearMap.continuous_toWOT := continuous_ofCLM

Depends on / 依赖: ContinuousLinearMapWOT, ContinuousLinearMapWOT.continuous_of_dual_apply_continuous, continuous_eval_const, continuous_of_dual_apply_continuous, y.cont.comp
-/
lemma continuous_ofCLM :
    Continuous (ofCLM : (E ->SL[σ] F) -> (E ->SWOT[σ] F)) :=
  ContinuousLinearMapWOT.continuous_of_dual_apply_continuous fun x y =>
y.cont.comp continuous_eval_const x

@[deprecated (since := "2026-04-10")] alias ContinuousLinearMap.continuous_toWOT := continuous_ofCLM

/--
Definition of `_root_.ContinuousLinearMap.WOTofCLM` / `_root_.ContinuousLinearMap.WOTofCLM` 的定义

English:
definition _root_.ContinuousLinearMap.WOTofCLM
  signature: : (E ->SL[σ] F) ->L[𝕜₂] (E ->SWOT[σ] F) where
  body: linearEquiv 𝕜₂
  cont := continuous_ofCLM

@[deprecated (since := "2026-04-10")]
alias ContinuousLinearMap.toWOTCLM := ContinuousLinearMap.WOTofCLM

中文:
定义 _root_.连续线性映射.WOTofCLM
  签名: : (E ->SL[σ] F) ->L[𝕜₂] (E ->SWOT[σ] F) where
  定义体: linearEquiv 𝕜₂
  cont := continuous_ofCLM

@[deprecated (since := "2026-04-10")]
alias ContinuousLinearMap.toWOTCLM := ContinuousLinearMap.WOTofCLM

Depends on / 依赖: linearEquiv
-/
def _root_.ContinuousLinearMap.WOTofCLM : (E ->SL[σ] F) ->L[𝕜₂] (E ->SWOT[σ] F) where
.symm.toLinearMap toLinearMap := linearEquiv 𝕜₂
  cont := continuous_ofCLM

@[deprecated (since := "2026-04-10")]
alias ContinuousLinearMap.toWOTCLM := ContinuousLinearMap.WOTofCLM

end toWOT_continuous


section Comp

variable {𝕜₁ 𝕜₂ 𝕜₃ 𝕜₄ : Type*} {E F G H : Type*}
    [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃] [NormedField 𝕜₄]
    {σ₁₂ : 𝕜₁ ->+* 𝕜₂} {σ₁₃ : 𝕜₁ ->+* 𝕜₃} {σ₁₄ : 𝕜₁ ->+* 𝕜₄}
    {σ₂₃ : 𝕜₂ ->+* 𝕜₃} {σ₂₄ : 𝕜₂ ->+* 𝕜₄} {σ₃₄ : 𝕜₃ ->+* 𝕜₄}
    [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄]
    [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄]
    [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E]
    [AddCommGroup F] [TopologicalSpace F] [Module 𝕜₂ F]
    [AddCommGroup G] [TopologicalSpace G] [Module 𝕜₃ G]
    [AddCommGroup H] [TopologicalSpace H] [Module 𝕜₄ H]

variable (𝕜₂ F) in
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : F ->WOT[𝕜₂] F
  body: ofCLM .id 𝕜₂ F

@[simp]

中文:
定义 id
  签名: : F ->WOT[𝕜₂] F
  定义体: ofCLM .id 𝕜₂ F

@[simp]
-/
protected def id : F ->WOT[𝕜₂] F := ofCLM .id 𝕜₂ F

@[simp]
/--
lemma `toCLM_id` / 引理 `toCLM_id`

English:
lemma toCLM_id
  statement: (.id 𝕜₂ F : F ->WOT[𝕜₂] F).toCLM = .id 𝕜₂ F
  proof: rfl

中文:
引理 toCLM_id
  结论: (.id 𝕜₂ F : F ->WOT[𝕜₂] F).toCLM = .id 𝕜₂ F
  证明: rfl
-/
lemma toCLM_id : (.id 𝕜₂ F : F ->WOT[𝕜₂] F).toCLM = .id 𝕜₂ F := rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : F ->SWOT[σ₂₃] G) (f : E ->SWOT[σ₁₂] F)
  body: ofCLM g.toCLM.comp f.toCLM

@[simp]

中文:
定义 comp
  签名: (g : F ->SWOT[σ₂₃] G) (f : E ->SWOT[σ₁₂] F)
  定义体: ofCLM g.toCLM.comp f.toCLM

@[simp]

Depends on / 依赖: f.toCLM, g.toCLM.comp
-/
def comp (g : F ->SWOT[σ₂₃] G) (f : E ->SWOT[σ₁₂] F) : E ->SWOT[σ₁₃] G :=
ofCLM g.toCLM.comp f.toCLM

@[simp]
/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: (g : F ->SWOT[σ₂₃] G) (f : E ->SWOT[σ₁₂] F) (x : E)
  proof: by
  simp [comp]

中文:
引理 comp_apply
  条件: (g : F ->SWOT[σ₂₃] G) (f : E ->SWOT[σ₁₂] F) (x : E)
  证明: by
  simp [comp]
-/
lemma comp_apply (g : F ->SWOT[σ₂₃] G) (f : E ->SWOT[σ₁₂] F) (x : E) :
    g.comp f x = g (f x) := by
  simp [comp]

/--
lemma `toCLM_comp` / 引理 `toCLM_comp`

English:
lemma toCLM_comp
  given: (g : F ->SWOT[σ₂₃] G) (f : E ->SWOT[σ₁₂] F)
  proof: rfl

中文:
引理 toCLM_comp
  条件: (g : F ->SWOT[σ₂₃] G) (f : E ->SWOT[σ₁₂] F)
  证明: rfl
-/
@[simp] lemma toCLM_comp (g : F ->SWOT[σ₂₃] G) (f : E ->SWOT[σ₁₂] F) :
    (g.comp f).toCLM = g.toCLM.comp f.toCLM :=
  rfl

/--
lemma `comp_id` / 引理 `comp_id`

English:
lemma comp_id
  given: (f : E ->SWOT[σ₁₂] F)
  statement: comp (.id 𝕜₂ F) f = f
  proof: by simp [comp]

中文:
引理 comp_id
  条件: (f : E ->SWOT[σ₁₂] F)
  结论: comp (.id 𝕜₂ F) f = f
  证明: by simp [comp]
-/
@[simp] lemma comp_id (f : E ->SWOT[σ₁₂] F) : comp (.id 𝕜₂ F) f = f := by simp [comp]
/--
lemma `id_comp` / 引理 `id_comp`

English:
lemma id_comp
  given: (g : F ->SWOT[σ₂₃] G)
  statement: comp g (.id 𝕜₂ F) = g
  proof: by simp [comp]

中文:
引理 id_comp
  条件: (g : F ->SWOT[σ₂₃] G)
  结论: comp g (.id 𝕜₂ F) = g
  证明: by simp [comp]
-/
@[simp] lemma id_comp (g : F ->SWOT[σ₂₃] G) : comp g (.id 𝕜₂ F) = g := by simp [comp]

/--
lemma `comp_assoc` / 引理 `comp_assoc`

English:
lemma comp_assoc
  given: (g₃₄ : G ->SWOT[σ₃₄] H) (g₂₃ : F ->SWOT[σ₂₃] G) (g₁₂ : E ->SWOT[σ₁₂] F)
  proof: by
  simp only [comp, ContinuousLinearMap.comp_assoc]

中文:
引理 comp_assoc
  条件: (g₃₄ : G ->SWOT[σ₃₄] H) (g₂₃ : F ->SWOT[σ₂₃] G) (g₁₂ : E ->SWOT[σ₁₂] F)
  证明: by
  simp only [comp, ContinuousLinearMap.comp_assoc]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_assoc, comp_assoc
-/
lemma comp_assoc (g₃₄ : G ->SWOT[σ₃₄] H) (g₂₃ : F ->SWOT[σ₂₃] G) (g₁₂ : E ->SWOT[σ₁₂] F) :
    (g₃₄.comp g₂₃).comp g₁₂ = g₃₄.comp (g₂₃.comp g₁₂) := by
  simp only [comp, ContinuousLinearMap.comp_assoc]

/--
lemma `mul_eq_comp` / 引理 `mul_eq_comp`

English:
lemma mul_eq_comp
  given: [IsTopologicalAddGroup F] (f g : F ->WOT[𝕜₂] F)
  statement: f * g = f.comp g
  proof: rfl

@[fun_prop]

中文:
引理 mul_eq_comp
  条件: [是拓扑加群 F] (f g : F ->WOT[𝕜₂] F)
  结论: f * g = f.comp g
  证明: rfl

@[fun_prop]
-/
lemma mul_eq_comp [IsTopologicalAddGroup F] (f g : F ->WOT[𝕜₂] F) : f * g = f.comp g := rfl

@[fun_prop]
/--
lemma `continuous_precomp` / 引理 `continuous_precomp`

English:
lemma continuous_precomp
  given: [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G] (f : E ->SWOT[σ₁₂] F)
  proof: continuous_of_dual_apply_continuous fun _ _ => continuous_dual_apply ..

中文:
引理 continuous_precomp
  条件: [是拓扑加群 G] [连续常数标量乘法 𝕜₃ G] (f : E ->SWOT[σ₁₂] F)
  证明: continuous_of_dual_apply_continuous fun _ _ => continuous_dual_apply ..

Depends on / 依赖: continuous_dual_apply, continuous_of_dual_apply_continuous
-/
lemma continuous_precomp [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G] (f : E ->SWOT[σ₁₂] F) :
    Continuous (fun g : F ->SWOT[σ₂₃] G => g.comp f) :=
  continuous_of_dual_apply_continuous fun _ _ => continuous_dual_apply ..

variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F]
variable [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]

/-- While `RingHomSurjective σ₂₃` is not a strict requirement, there are obstructions to
this without any assumption on `σ₂₃` (in particular, on the dimension of the extension of `𝕜₃` over
`σ₂₃(𝕜₂)`), and in the only common case, which is when `σ₂₃` is conjugation, this type class is
guaranteed. Likewise, it would suffice if `RingHomIsometric` were replaced with the weaker
`Continuous σ₂₃`, but we opt for this because we have these type classes available. -/
@[fun_prop]
/--
lemma `continuous_postcomp` / 引理 `continuous_postcomp`

English:
lemma continuous_postcomp
  given: [RingHomSurjective σ₂₃] [RingHomIsometric σ₂₃] (g : F ->SWOT[σ₂₃] G)
  proof: by
  refine continuous_of_dual_apply_continuous fun x z => ?_
  have σ_bij : Function.Bijective σ₂₃ := ⟨σ₂₃.injective, RingHomSurjective.is_surjective⟩
  let σ_equiv : 𝕜₂ ≃+* 𝕜₃ := RingEquiv.ofBijective σ₂₃ σ_bij
  let invPair : RingHomInvPair σ₂₃ σ_equiv.symm := RingHomInvPair.of_ringEquiv σ_equiv
  let invPair_symm := invPair.symm
  let σ_li : 𝕜₂ ≃ₛₗᵢ[σ₂₃] 𝕜₃ :=
    { toLinearEquiv := .ofBijective σ₂₃.toSemilinearMap σ_bij
      norm_map' _ := RingHomIsometric.norm_map }
  conv => enter [1, a]; rw [← σ_li.apply_symm_apply (z _), comp_apply, ← toCLM_apply]
  apply σ_li.continuous.comp
exact continuous_dual_apply x σ_li.symm.toLinearIsometry.toContinuousLinearMap.comp
    z.comp g.toCLM

中文:
引理 continuous_postcomp
  条件: [RingHomSurjective σ₂₃] [RingHomIsometric σ₂₃] (g : F ->SWOT[σ₂₃] G)
  证明: by
  refine continuous_of_dual_apply_continuous fun x z => ?_
  have σ_bij : Function.Bijective σ₂₃ := ⟨σ₂₃.injective, RingHomSurjective.is_surjective⟩
  let σ_equiv : 𝕜₂ ≃+* 𝕜₃ := RingEquiv.ofBijective σ₂₃ σ_bij
  let invPair : RingHomInvPair σ₂₃ σ_equiv.symm := RingHomInvPair.of_ringEquiv σ_equiv
  let invPair_symm := invPair.symm
  let σ_li : 𝕜₂ ≃ₛₗᵢ[σ₂₃] 𝕜₃ :=
    { toLinearEquiv := .ofBijective σ₂₃.toSemilinearMap σ_bij
      norm_map' _ := RingHomIsometric.norm_map }
  conv => enter [1, a]; rw [← σ_li.apply_symm_apply (z _), comp_apply, ← toCLM_apply]
  apply σ_li.continuous.comp
exact continuous_dual_apply x σ_li.symm.toLinearIsometry.toContinuousLinearMap.comp
    z.comp g.toCLM

Depends on / 依赖: Bijective, Function, Function.Bijective, RingEquiv, RingEquiv.ofBijective, RingHomInvPair, RingHomInvPair.of_ringEquiv, RingHomIsometric, RingHomIsometric.norm_map, RingHomSurjective, RingHomSurjective.is_surjective, _equiv.symm, _li.apply_symm_, apply_symm_, continuous_of_dual_apply_continuous, injective, invPair, invPair.symm, invPair_symm, is_surjective
-/
lemma continuous_postcomp [RingHomSurjective σ₂₃] [RingHomIsometric σ₂₃] (g : F ->SWOT[σ₂₃] G) :
    Continuous (fun f : E ->SWOT[σ₁₂] F => g.comp f) := by
  refine continuous_of_dual_apply_continuous fun x z => ?_
  have σ_bij : Function.Bijective σ₂₃ := ⟨σ₂₃.injective, RingHomSurjective.is_surjective⟩
  let σ_equiv : 𝕜₂ ≃+* 𝕜₃ := RingEquiv.ofBijective σ₂₃ σ_bij
  let invPair : RingHomInvPair σ₂₃ σ_equiv.symm := RingHomInvPair.of_ringEquiv σ_equiv
  let invPair_symm := invPair.symm
  let σ_li : 𝕜₂ ≃ₛₗᵢ[σ₂₃] 𝕜₃ :=
    { toLinearEquiv := .ofBijective σ₂₃.toSemilinearMap σ_bij
      norm_map' _ := RingHomIsometric.norm_map }
  conv => enter [1, a]; rw [← σ_li.apply_symm_apply (z _), comp_apply, ← toCLM_apply]
  apply σ_li.continuous.comp
exact continuous_dual_apply x σ_li.symm.toLinearIsometry.toContinuousLinearMap.comp
    z.comp g.toCLM

/-- Precomposition by a fixed continuous linear map, as a continuous linear map when all spaces
of continuous linear maps are equipped with the weak operator topology. -/
@[simps]
/--
Definition of `precompCLM` / `precompCLM` 的定义

English:
definition precompCLM
  signature: (f : E ->SWOT[σ₁₂] F)
  body: g.comp f
  map_add' := by simp [comp]
  map_smul' := by simp [comp]

中文:
定义 precompCLM
  签名: (f : E ->SWOT[σ₁₂] F)
  定义体: g.comp f
  map_add' := by simp [comp]
  map_smul' := by simp [comp]

Depends on / 依赖: g.comp
-/
def precompCLM (f : E ->SWOT[σ₁₂] F) : (F ->SWOT[σ₂₃] G) ->L[𝕜₃] (E ->SWOT[σ₁₃] G) where
  toFun g := g.comp f
  map_add' := by simp [comp]
  map_smul' := by simp [comp]

/-- Precomposition by a fixed continuous linear map, as a continuous linear map when all spaces
of continuous linear maps are equipped with the weak operator topology. -/
@[simps]
/--
Definition of `postcompCLM` / `postcompCLM` 的定义

English:
definition postcompCLM
  signature: [RingHomSurjective σ₂₃] [RingHomIsometric σ₂₃] (g : F ->SWOT[σ₂₃] G)
  body: g.comp f
  map_add' := by simp [comp]
  map_smul' := by simp [comp]

中文:
定义 postcompCLM
  签名: [RingHomSurjective σ₂₃] [RingHomIsometric σ₂₃] (g : F ->SWOT[σ₂₃] G)
  定义体: g.comp f
  map_add' := by simp [comp]
  map_smul' := by simp [comp]

Depends on / 依赖: g.comp
-/
def postcompCLM [RingHomSurjective σ₂₃] [RingHomIsometric σ₂₃] (g : F ->SWOT[σ₂₃] G) :
    (E ->SWOT[σ₁₂] F) ->SL[σ₂₃] (E ->SWOT[σ₁₃] G) where
  toFun f := g.comp f
  map_add' := by simp [comp]
  map_smul' := by simp [comp]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSemitopologicalRing (F ->WOT[𝕜₂] F)
  body: by simp_rw [mul_eq_comp]; fun_prop
  continuous_mul_const {_} := by simp_rw [mul_eq_comp]; fun_prop

中文:
实例 :
  签名: 是Semitopological环 (F ->WOT[𝕜₂] F)
  定义体: by simp_rw [mul_eq_comp]; fun_prop
  continuous_mul_const {_} := by simp_rw [mul_eq_comp]; fun_prop

Depends on / 依赖: continuous_mul_const, fun_prop, mul_eq_comp, simp_rw
-/
instance : IsSemitopologicalRing (F ->WOT[𝕜₂] F) where
  continuous_const_mul {_} := by simp_rw [mul_eq_comp]; fun_prop
  continuous_mul_const {_} := by simp_rw [mul_eq_comp]; fun_prop

end Comp

end ContinuousLinearMapWOT
