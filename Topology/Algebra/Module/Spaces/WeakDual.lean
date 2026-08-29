/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Moritz Doll
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.WeakBilin

/-!
# Weak dual topology

We continue in the setting of `Mathlib/Topology/Algebra/Module/WeakBilin.lean`,
which defines the weak topology given two vector spaces `E` and `F` over a commutative semiring
`𝕜` and a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`. The weak topology on `E` is the coarsest topology
such that for all `y : F` every map `fun x => B x y` is continuous.

In this file, we consider two special cases.
In the case that `F = E →L[𝕜] 𝕜` and `B` being the canonical pairing, we obtain the weak-\*
topology, `WeakDual 𝕜 E := (E →L[𝕜] 𝕜)`. Interchanging the arguments in the bilinear form yields the
weak topology `WeakSpace 𝕜 E := E`.

## Main definitions

The main definitions are the types `WeakDual 𝕜 E` and `WeakSpace 𝕜 E`,
with the respective topology instances on it.

* `WeakDual 𝕜 E` is a type synonym for `Dual 𝕜 E` (when the latter is defined): both are equal to
  the type `E →L[𝕜] 𝕜` of continuous linear maps from a module `E` over `𝕜` to the ring `𝕜`.
* The instance `WeakDual.instTopologicalSpace` is the weak-\* topology on `WeakDual 𝕜 E`, i.e., the
  coarsest topology making the evaluation maps at all `z : E` continuous.
* `WeakSpace 𝕜 E` is a type synonym for `E` (when the latter is defined).
* The instance `WeakSpace.instTopologicalSpace` is the weak topology on `E`, i.e., the
  coarsest topology such that all `v : dual 𝕜 E` remain continuous.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

weak-star, weak dual, duality

-/

@[expose] public section


noncomputable section

open Filter

open Topology

variable {α 𝕜 𝕝 E F : Type*}

/--
Definition of `WeakDual` / `WeakDual` 的定义

English:
definition WeakDual
  signature: (𝕜 E : Type*) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  body: WeakBilin (topDualPairing 𝕜 E)
deriving TopologicalSpace, Inhabited, FunLike, ContinuousLinearMapClass

中文:
定义 WeakDual
  签名: (𝕜 E : 类型) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  定义体: WeakBilin (topDualPairing 𝕜 E)
deriving TopologicalSpace, Inhabited, FunLike, ContinuousLinearMapClass

Depends on / 依赖: WeakBilin, topDualPairing
-/
def WeakDual (𝕜 E : Type*) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
    [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] :=
  WeakBilin (topDualPairing 𝕜 E)
deriving TopologicalSpace, Inhabited, FunLike, ContinuousLinearMapClass

namespace WeakDual

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
variable [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/--
Instance `instMulAction` / 实例 `instMulAction`

English:
instance instMulAction
  signature: (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
  body: inferInstanceAs MulAction M (E ->L[𝕜] 𝕜)

deriving instance AddCommMonoid, ContinuousAdd for WeakDual

中文:
实例 instMulAction
  签名: (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
  定义体: inferInstanceAs MulAction M (E ->L[𝕜] 𝕜)

deriving instance AddCommMonoid, ContinuousAdd for WeakDual

Depends on / 依赖: MulAction
-/
instance instMulAction (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [ContinuousConstSMul M 𝕜] : MulAction M (WeakDual 𝕜 E) :=
inferInstanceAs MulAction M (E ->L[𝕜] 𝕜)

deriving instance AddCommMonoid, ContinuousAdd for WeakDual

/--
Instance `instDistribMulAction` / 实例 `instDistribMulAction`

English:
instance instDistribMulAction
  signature: (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
  body: inferInstanceAs DistribMulAction M (E ->L[𝕜] 𝕜)

中文:
实例 instDistribMulAction
  签名: (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
  定义体: inferInstanceAs DistribMulAction M (E ->L[𝕜] 𝕜)

Depends on / 依赖: DistribMulAction
-/
instance instDistribMulAction (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [ContinuousConstSMul M 𝕜] : DistribMulAction M (WeakDual 𝕜 E) :=
inferInstanceAs DistribMulAction M (E ->L[𝕜] 𝕜)

/--
Instance `instContinuousConstSMul` / 实例 `instContinuousConstSMul`

English:
instance instContinuousConstSMul
  signature: (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
  body: ⟨fun m =>
continuous_induced_rng.2 (WeakBilin.coeFn_continuous (topDualPairing 𝕜 E)).const_smul m⟩

中文:
实例 instContinuousConstSMul
  签名: (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
  定义体: ⟨fun m =>
continuous_induced_rng.2 (WeakBilin.coeFn_continuous (topDualPairing 𝕜 E)).const_smul m⟩

Depends on / 依赖: WeakBilin, WeakBilin.coeFn_continuous, coeFn_continuous, const_smul, continuous_induced_rng, topDualPairing
-/
instance instContinuousConstSMul (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [ContinuousConstSMul M 𝕜] : ContinuousConstSMul M (WeakDual 𝕜 E) :=
  ⟨fun m =>
continuous_induced_rng.2 (WeakBilin.coeFn_continuous (topDualPairing 𝕜 E)).const_smul m⟩

/--
Instance `instContinuousSMul` / 实例 `instContinuousSMul`

English:
instance instContinuousSMul
  signature: (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
  body: ⟨continuous_induced_rng.2
      continuous_fst.smul ((WeakBilin.coeFn_continuous (topDualPairing 𝕜 E)).comp continuous_snd)⟩

中文:
实例 instContinuousSMul
  签名: (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
  定义体: ⟨continuous_induced_rng.2
      continuous_fst.smul ((WeakBilin.coeFn_continuous (topDualPairing 𝕜 E)).comp continuous_snd)⟩

Depends on / 依赖: WeakBilin, WeakBilin.coeFn_continuous, coeFn_continuous, continuous_fst, continuous_fst.smul, continuous_induced_rng, continuous_snd, topDualPairing
-/
instance instContinuousSMul (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [TopologicalSpace M] [ContinuousSMul M 𝕜] : ContinuousSMul M (WeakDual 𝕜 E) :=
⟨continuous_induced_rng.2
      continuous_fst.smul ((WeakBilin.coeFn_continuous (topDualPairing 𝕜 E)).comp continuous_snd)⟩

/-- If `𝕜` is a topological module over a semiring `R` and scalar multiplication commutes with the
multiplication on `𝕜`, then `WeakDual 𝕜 E` is a module over `R`. -/
instance (priority := 950) instModule'
    (R : Type*) [Semiring R] [Module R 𝕜] [SMulCommClass 𝕜 R 𝕜] [ContinuousConstSMul R 𝕜] :
    Module R (WeakDual 𝕜 E) :=
inferInstanceAs Module R (E ->L[𝕜] 𝕜)

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: : Module 𝕜 (WeakDual 𝕜 E)
  body: inferInstance

中文:
实例 instModule
  签名: : Module 𝕜 (WeakDual 𝕜 E)
  定义体: inferInstance
-/
instance instModule : Module 𝕜 (WeakDual 𝕜 E) := inferInstance

end WeakDual

namespace StrongDual

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
variable [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/--
Definition of `toWeakDual` / `toWeakDual` 的定义

English:
definition toWeakDual
  signature: : StrongDual 𝕜 E ≃ₗ[𝕜] WeakDual 𝕜 E
  body: LinearEquiv.refl 𝕜 (StrongDual 𝕜 E)

中文:
定义 toWeakDual
  签名: : StrongDual 𝕜 E ≃ₗ[𝕜] WeakDual 𝕜 E
  定义体: LinearEquiv.refl 𝕜 (StrongDual 𝕜 E)

Depends on / 依赖: LinearEquiv, LinearEquiv.refl, StrongDual
-/
def toWeakDual : StrongDual 𝕜 E ≃ₗ[𝕜] WeakDual 𝕜 E :=
  LinearEquiv.refl 𝕜 (StrongDual 𝕜 E)

/--
theorem `coe_toWeakDual` / 定理 `coe_toWeakDual`

English:
theorem coe_toWeakDual
  given: (x' : StrongDual 𝕜 E)
  statement: (toWeakDual x' : E -> 𝕜) = x'
  proof: rfl

@[simp]

中文:
定理 coe_toWeakDual
  条件: (x' : StrongDual 𝕜 E)
  结论: (toWeakDual x' : E -> 𝕜) = x'
  证明: rfl

@[simp]
-/
theorem coe_toWeakDual (x' : StrongDual 𝕜 E) : (toWeakDual x' : E -> 𝕜) = x' := rfl

@[simp]
/--
theorem `toWeakDual_apply` / 定理 `toWeakDual_apply`

English:
theorem toWeakDual_apply
  given: (x' : StrongDual 𝕜 E) (y : E)
  statement: (toWeakDual x') y = x' y
  proof: rfl

中文:
定理 toWeakDual_apply
  条件: (x' : StrongDual 𝕜 E) (y : E)
  结论: (toWeakDual x') y = x' y
  证明: rfl
-/
theorem toWeakDual_apply (x' : StrongDual 𝕜 E) (y : E) : (toWeakDual x') y = x' y := rfl

/--
theorem `toWeakDual_inj` / 定理 `toWeakDual_inj`

English:
theorem toWeakDual_inj
  given: (x' y' : StrongDual 𝕜 E)
  statement: toWeakDual x' = toWeakDual y' ↔ x' = y'
  proof: (LinearEquiv.injective toWeakDual).eq_iff

中文:
定理 toWeakDual_inj
  条件: (x' y' : StrongDual 𝕜 E)
  结论: toWeakDual x' = toWeakDual y' ↔ x' = y'
  证明: (LinearEquiv.injective toWeakDual).eq_iff

Depends on / 依赖: LinearEquiv, LinearEquiv.injective, eq_iff, injective, toWeakDual
-/
theorem toWeakDual_inj (x' y' : StrongDual 𝕜 E) : toWeakDual x' = toWeakDual y' ↔ x' = y' :=
  (LinearEquiv.injective toWeakDual).eq_iff

end StrongDual

namespace WeakDual

section Semiring

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
variable [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/--
Definition of `toStrongDual` / `toStrongDual` 的定义

English:
definition toStrongDual
  signature: : WeakDual 𝕜 E ≃ₗ[𝕜] StrongDual 𝕜 E
  body: StrongDual.toWeakDual.symm

@[simp]

中文:
定义 toStrongDual
  签名: : WeakDual 𝕜 E ≃ₗ[𝕜] StrongDual 𝕜 E
  定义体: StrongDual.toWeakDual.symm

@[simp]

Depends on / 依赖: StrongDual, StrongDual.toWeakDual.symm, toWeakDual
-/
def toStrongDual : WeakDual 𝕜 E ≃ₗ[𝕜] StrongDual 𝕜 E :=
  StrongDual.toWeakDual.symm

@[simp]
/--
theorem `symm_toStrongDual` / 定理 `symm_toStrongDual`

English:
theorem symm_toStrongDual
  proof: rfl

@[simp]

中文:
定理 symm_toStrongDual
  证明: rfl

@[simp]

Depends on / 依赖: StrongDual, StrongDual.toWeakDual, toWeakDual
-/
theorem symm_toStrongDual :
    (toStrongDual (𝕜 := 𝕜) (E := E)).symm = StrongDual.toWeakDual :=
  rfl

@[simp]
/--
theorem `_root_.StrongDual.symm_toWeakDual` / 定理 `_root_.StrongDual.symm_toWeakDual`

English:
theorem _root_.StrongDual.symm_toWeakDual
  proof: rfl

@[simp]

中文:
定理 _root_.StrongDual.symm_toWeakDual
  证明: rfl

@[simp]

Depends on / 依赖: toStrongDual
-/
theorem _root_.StrongDual.symm_toWeakDual :
    (StrongDual.toWeakDual (𝕜 := 𝕜) (E := E)).symm = toStrongDual :=
  rfl

@[simp]
/--
theorem `_root_.StrongDual.toStrongDual_toWeakDual` / 定理 `_root_.StrongDual.toStrongDual_toWeakDual`

English:
theorem _root_.StrongDual.toStrongDual_toWeakDual
  given: (x : StrongDual 𝕜 E)
  proof: rfl

@[simp]

中文:
定理 _root_.StrongDual.toStrongDual_toWeakDual
  条件: (x : StrongDual 𝕜 E)
  证明: rfl

@[simp]
-/
theorem _root_.StrongDual.toStrongDual_toWeakDual (x : StrongDual 𝕜 E) :
    x.toWeakDual.toStrongDual = x :=
  rfl

@[simp]
/--
theorem `toWeakDual_toStrongDual` / 定理 `toWeakDual_toStrongDual`

English:
theorem toWeakDual_toStrongDual
  given: (x : WeakDual 𝕜 E)
  statement: x.toStrongDual.toWeakDual = x
  proof: rfl

@[simp]

中文:
定理 toWeakDual_toStrongDual
  条件: (x : WeakDual 𝕜 E)
  结论: x.toStrongDual.toWeakDual = x
  证明: rfl

@[simp]
-/
theorem toWeakDual_toStrongDual (x : WeakDual 𝕜 E) : x.toStrongDual.toWeakDual = x :=
  rfl

@[simp]
/--
theorem `toStrongDual_apply` / 定理 `toStrongDual_apply`

English:
theorem toStrongDual_apply
  given: (x : WeakDual 𝕜 E) (y : E)
  statement: (toStrongDual x) y = x y
  proof: rfl

中文:
定理 toStrongDual_apply
  条件: (x : WeakDual 𝕜 E) (y : E)
  结论: (toStrongDual x) y = x y
  证明: rfl
-/
theorem toStrongDual_apply (x : WeakDual 𝕜 E) (y : E) : (toStrongDual x) y = x y := rfl

/--
theorem `coe_toStrongDual` / 定理 `coe_toStrongDual`

English:
theorem coe_toStrongDual
  given: (x' : WeakDual 𝕜 E)
  statement: (toStrongDual x' : E -> 𝕜) = x'
  proof: rfl

中文:
定理 coe_toStrongDual
  条件: (x' : WeakDual 𝕜 E)
  结论: (toStrongDual x' : E -> 𝕜) = x'
  证明: rfl
-/
theorem coe_toStrongDual (x' : WeakDual 𝕜 E) : (toStrongDual x' : E -> 𝕜) = x' := rfl

/--
theorem `toStrongDual_inj` / 定理 `toStrongDual_inj`

English:
theorem toStrongDual_inj
  given: (x' y' : WeakDual 𝕜 E)
  statement: toStrongDual x' = toStrongDual y' ↔ x' = y'
  proof: (LinearEquiv.injective toStrongDual).eq_iff

中文:
定理 toStrongDual_inj
  条件: (x' y' : WeakDual 𝕜 E)
  结论: toStrongDual x' = toStrongDual y' ↔ x' = y'
  证明: (LinearEquiv.injective toStrongDual).eq_iff

Depends on / 依赖: LinearEquiv, LinearEquiv.injective, eq_iff, injective, toStrongDual
-/
theorem toStrongDual_inj (x' y' : WeakDual 𝕜 E) : toStrongDual x' = toStrongDual y' ↔ x' = y' :=
  (LinearEquiv.injective toStrongDual).eq_iff


/--
theorem `coeFn_continuous` / 定理 `coeFn_continuous`

English:
theorem coeFn_continuous
  statement: Continuous fun (x : WeakDual 𝕜 E) y => x y
  proof: continuous_induced_dom

中文:
定理 coeFn_continuous
  结论: Continuous fun (x : WeakDual 𝕜 E) y => x y
  证明: continuous_induced_dom

Depends on / 依赖: continuous_induced_dom
-/
theorem coeFn_continuous : Continuous fun (x : WeakDual 𝕜 E) y => x y :=
  continuous_induced_dom

/--
theorem `eval_continuous` / 定理 `eval_continuous`

English:
theorem eval_continuous
  given: (y : E)
  statement: Continuous fun x : WeakDual 𝕜 E => x y
  proof: continuous_pi_iff.mp coeFn_continuous y

中文:
定理 eval_continuous
  条件: (y : E)
  结论: Continuous fun x : WeakDual 𝕜 E => x y
  证明: continuous_pi_iff.mp coeFn_continuous y

Depends on / 依赖: coeFn_continuous, continuous_pi_iff, continuous_pi_iff.mp
-/
theorem eval_continuous (y : E) : Continuous fun x : WeakDual 𝕜 E => x y :=
  continuous_pi_iff.mp coeFn_continuous y

/--
theorem `continuous_of_continuous_eval` / 定理 `continuous_of_continuous_eval`

English:
theorem continuous_of_continuous_eval
  statement: [TopologicalSpace α] {g : α -> WeakDual 𝕜 E}
  proof: continuous_induced_rng.2 (continuous_pi_iff.mpr h)

中文:
定理 continuous_of_continuous_eval
  结论: [TopologicalSpace α] {g : α -> WeakDual 𝕜 E}
  证明: continuous_induced_rng.2 (continuous_pi_iff.mpr h)

Depends on / 依赖: continuous_induced_rng, continuous_pi_iff, continuous_pi_iff.mpr
-/
theorem continuous_of_continuous_eval [TopologicalSpace α] {g : α -> WeakDual 𝕜 E}
    (h : forall y, Continuous fun a => (g a) y) : Continuous g :=
  continuous_induced_rng.2 (continuous_pi_iff.mpr h)

/--
Instance `instT2Space` / 实例 `instT2Space`

English:
instance instT2Space
  signature: [T2Space 𝕜]
  body: (WeakBilin.isEmbedding ContinuousLinearMap.coe_injective).t2Space

中文:
实例 instT2Space
  签名: [T2Space 𝕜]
  定义体: (WeakBilin.isEmbedding ContinuousLinearMap.coe_injective).t2Space

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coe_injective, WeakBilin, WeakBilin.isEmbedding, coe_injective, isEmbedding, t2Space
-/
instance instT2Space [T2Space 𝕜] : T2Space (WeakDual 𝕜 E) :=
  (WeakBilin.isEmbedding ContinuousLinearMap.coe_injective).t2Space

end Semiring

section Ring

variable [CommRing 𝕜] [TopologicalSpace 𝕜] [IsTopologicalAddGroup 𝕜] [ContinuousConstSMul 𝕜 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: : AddCommGroup (WeakDual 𝕜 E)
  body: inferInstanceAs AddCommGroup (WeakBilin (topDualPairing 𝕜 E))

中文:
实例 instAddCommGroup
  签名: : AddCommGroup (WeakDual 𝕜 E)
  定义体: inferInstanceAs AddCommGroup (WeakBilin (topDualPairing 𝕜 E))

Depends on / 依赖: AddCommGroup, WeakBilin, topDualPairing
-/
instance instAddCommGroup : AddCommGroup (WeakDual 𝕜 E) :=
inferInstanceAs AddCommGroup (WeakBilin (topDualPairing 𝕜 E))

/--
Instance `instIsTopologicalAddGroup` / 实例 `instIsTopologicalAddGroup`

English:
instance instIsTopologicalAddGroup
  signature: : IsTopologicalAddGroup (WeakDual 𝕜 E)
  body: WeakBilin.instIsTopologicalAddGroup (topDualPairing 𝕜 E)

中文:
实例 instIsTopologicalAddGroup
  签名: : IsTopologicalAddGroup (WeakDual 𝕜 E)
  定义体: WeakBilin.instIsTopologicalAddGroup (topDualPairing 𝕜 E)

Depends on / 依赖: WeakBilin, WeakBilin.instIsTopologicalAddGroup, instIsTopologicalAddGroup, topDualPairing
-/
instance instIsTopologicalAddGroup : IsTopologicalAddGroup (WeakDual 𝕜 E) :=
  WeakBilin.instIsTopologicalAddGroup (topDualPairing 𝕜 E)

end Ring

end WeakDual

/--
Definition of `WeakSpace` / `WeakSpace` 的定义

English:
definition WeakSpace
  signature: (𝕜 E) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  body: WeakBilin (topDualPairing 𝕜 E).flip
deriving TopologicalSpace

中文:
定义 WeakSpace
  签名: (𝕜 E) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  定义体: WeakBilin (topDualPairing 𝕜 E).flip
deriving TopologicalSpace

Depends on / 依赖: WeakBilin, topDualPairing
-/
def WeakSpace (𝕜 E) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
    [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] :=
  WeakBilin (topDualPairing 𝕜 E).flip
deriving TopologicalSpace

section Semiring

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
variable [ContinuousConstSMul 𝕜 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

-- The `SMul` instance exists to avoid an nsmul diamond.
variable [CommSemiring 𝕝] [Module 𝕝 E] in
deriving instance SMul 𝕝 for WeakSpace 𝕜 E

deriving instance AddCommMonoid, ContinuousAdd for WeakSpace

namespace WeakSpace

/--
Instance `instModule'` / 实例 `instModule'`

English:
instance instModule'
  signature: [CommSemiring 𝕝] [Module 𝕝 E]
  body: inferInstanceAs Module 𝕝 (WeakBilin (topDualPairing 𝕜 E).flip)

中文:
实例 instModule'
  签名: [CommSemiring 𝕝] [Module 𝕝 E]
  定义体: inferInstanceAs Module 𝕝 (WeakBilin (topDualPairing 𝕜 E).flip)

Depends on / 依赖: Module, WeakBilin, topDualPairing
-/
instance instModule' [CommSemiring 𝕝] [Module 𝕝 E] : Module 𝕝 (WeakSpace 𝕜 E) :=
inferInstanceAs Module 𝕝 (WeakBilin (topDualPairing 𝕜 E).flip)

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: : Module 𝕜 (WeakSpace 𝕜 E)
  body: inferInstance

中文:
实例 instModule
  签名: : Module 𝕜 (WeakSpace 𝕜 E)
  定义体: inferInstance
-/
instance instModule : Module 𝕜 (WeakSpace 𝕜 E) := inferInstance

/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: [CommSemiring 𝕝] [Module 𝕝 𝕜] [Module 𝕝 E] [IsScalarTower 𝕝 𝕜 E]
  body: WeakBilin.instIsScalarTower (topDualPairing 𝕜 E).flip

中文:
实例 instIsScalarTower
  签名: [CommSemiring 𝕝] [Module 𝕝 𝕜] [Module 𝕝 E] [IsScalarTower 𝕝 𝕜 E]
  定义体: WeakBilin.instIsScalarTower (topDualPairing 𝕜 E).flip

Depends on / 依赖: WeakBilin, WeakBilin.instIsScalarTower, instIsScalarTower, topDualPairing
-/
instance instIsScalarTower [CommSemiring 𝕝] [Module 𝕝 𝕜] [Module 𝕝 E] [IsScalarTower 𝕝 𝕜 E] :
    IsScalarTower 𝕝 𝕜 (WeakSpace 𝕜 E) :=
  WeakBilin.instIsScalarTower (topDualPairing 𝕜 E).flip

/--
Instance `instContinuousSMul` / 实例 `instContinuousSMul`

English:
instance instContinuousSMul
  signature: [ContinuousSMul 𝕜 𝕜]
  body: WeakBilin.instContinuousSMul _

中文:
实例 instContinuousSMul
  签名: [ContinuousSMul 𝕜 𝕜]
  定义体: WeakBilin.instContinuousSMul _

Depends on / 依赖: WeakBilin, WeakBilin.instContinuousSMul, instContinuousSMul
-/
instance instContinuousSMul [ContinuousSMul 𝕜 𝕜] : ContinuousSMul 𝕜 (WeakSpace 𝕜 E) :=
  WeakBilin.instContinuousSMul _

variable [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : E ->L[𝕜] F)
  body: { f with
    cont :=
      WeakBilin.continuous_of_continuous_eval _ fun l => WeakBilin.eval_continuous _ (l ∘L f) }

中文:
定义 map
  签名: (f : E ->L[𝕜] F)
  定义体: { f with
    cont :=
      WeakBilin.continuous_of_continuous_eval _ fun l => WeakBilin.eval_continuous _ (l ∘L f) }

Depends on / 依赖: WeakBilin, WeakBilin.continuous_of_continuous_eval, WeakBilin.eval_continuous, continuous_of_continuous_eval, eval_continuous
-/
def map (f : E ->L[𝕜] F) : WeakSpace 𝕜 E ->L[𝕜] WeakSpace 𝕜 F :=
  { f with
    cont :=
      WeakBilin.continuous_of_continuous_eval _ fun l => WeakBilin.eval_continuous _ (l ∘L f) }

/--
theorem `map_apply` / 定理 `map_apply`

English:
theorem map_apply
  given: (f : E ->L[𝕜] F) (x : E)
  statement: WeakSpace.map f x = f x
  proof: rfl

@[simp]

中文:
定理 map_apply
  条件: (f : E ->L[𝕜] F) (x : E)
  结论: WeakSpace.map f x = f x
  证明: rfl

@[simp]
-/
theorem map_apply (f : E ->L[𝕜] F) (x : E) : WeakSpace.map f x = f x :=
  rfl

@[simp]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  given: (f : E ->L[𝕜] F)
  statement: (WeakSpace.map f : E -> F) = f
  proof: rfl

中文:
定理 coe_map
  条件: (f : E ->L[𝕜] F)
  结论: (WeakSpace.map f : E -> F) = f
  证明: rfl
-/
theorem coe_map (f : E ->L[𝕜] F) : (WeakSpace.map f : E -> F) = f :=
  rfl

end WeakSpace

variable (𝕜 E) in
/--
Definition of `toWeakSpace` / `toWeakSpace` 的定义

English:
definition toWeakSpace
  signature: : E ≃ₗ[𝕜] WeakSpace 𝕜 E
  body: LinearEquiv.refl 𝕜 E

中文:
定义 toWeakSpace
  签名: : E ≃ₗ[𝕜] WeakSpace 𝕜 E
  定义体: LinearEquiv.refl 𝕜 E

Depends on / 依赖: LinearEquiv, LinearEquiv.refl
-/
def toWeakSpace : E ≃ₗ[𝕜] WeakSpace 𝕜 E := LinearEquiv.refl 𝕜 E

variable (𝕜 E) in
/--
Definition of `toWeakSpaceCLM` / `toWeakSpaceCLM` 的定义

English:
definition toWeakSpaceCLM
  signature: : E ->L[𝕜] WeakSpace 𝕜 E where
  body: toWeakSpace 𝕜 E
  cont := by
    apply WeakBilin.continuous_of_continuous_eval
    exact ContinuousLinearMap.continuous

中文:
定义 toWeakSpaceCLM
  签名: : E ->L[𝕜] WeakSpace 𝕜 E where
  定义体: toWeakSpace 𝕜 E
  cont := by
    apply WeakBilin.continuous_of_continuous_eval
    exact ContinuousLinearMap.continuous

Depends on / 依赖: toWeakSpace
-/
def toWeakSpaceCLM : E ->L[𝕜] WeakSpace 𝕜 E where
  __ := toWeakSpace 𝕜 E
  cont := by
    apply WeakBilin.continuous_of_continuous_eval
    exact ContinuousLinearMap.continuous

variable (𝕜 E) in
@[simp]
/--
theorem `toWeakSpaceCLM_eq_toWeakSpace` / 定理 `toWeakSpaceCLM_eq_toWeakSpace`

English:
theorem toWeakSpaceCLM_eq_toWeakSpace
  given: (x : E)
  proof: by rfl

中文:
定理 toWeakSpaceCLM_eq_toWeakSpace
  条件: (x : E)
  证明: by rfl
-/
theorem toWeakSpaceCLM_eq_toWeakSpace (x : E) :
    toWeakSpaceCLM 𝕜 E x = toWeakSpace 𝕜 E x := by rfl

/--
theorem `toWeakSpaceCLM_bijective` / 定理 `toWeakSpaceCLM_bijective`

English:
theorem toWeakSpaceCLM_bijective
  proof: (toWeakSpace 𝕜 E).bijective

中文:
定理 toWeakSpaceCLM_bijective
  证明: (toWeakSpace 𝕜 E).bijective

Depends on / 依赖: bijective, toWeakSpace
-/
theorem toWeakSpaceCLM_bijective :
    Function.Bijective (toWeakSpaceCLM 𝕜 E) :=
  (toWeakSpace 𝕜 E).bijective

/--
theorem `isOpenMap_toWeakSpace_symm` / 定理 `isOpenMap_toWeakSpace_symm`

English:
theorem isOpenMap_toWeakSpace_symm
  statement: IsOpenMap (toWeakSpace 𝕜 E).symm
  proof: IsOpenMap.of_inverse (toWeakSpaceCLM 𝕜 E).cont
    (toWeakSpace 𝕜 E).left_inv (toWeakSpace 𝕜 E).right_inv

中文:
定理 isOpenMap_toWeakSpace_symm
  结论: IsOpenMap (toWeakSpace 𝕜 E).symm
  证明: IsOpenMap.of_inverse (toWeakSpaceCLM 𝕜 E).cont
    (toWeakSpace 𝕜 E).left_inv (toWeakSpace 𝕜 E).right_inv

Depends on / 依赖: IsOpenMap, IsOpenMap.of_inverse, left_inv, of_inverse, right_inv, toWeakSpace, toWeakSpaceCLM
-/
theorem isOpenMap_toWeakSpace_symm : IsOpenMap (toWeakSpace 𝕜 E).symm :=
  IsOpenMap.of_inverse (toWeakSpaceCLM 𝕜 E).cont
    (toWeakSpace 𝕜 E).left_inv (toWeakSpace 𝕜 E).right_inv

/--
theorem `WeakSpace.isOpen_of_isOpen` / 定理 `WeakSpace.isOpen_of_isOpen`

English:
theorem WeakSpace.isOpen_of_isOpen
  statement: (V : Set E)
  proof: by
  simpa [Set.image_image] using isOpenMap_toWeakSpace_symm _ hV

中文:
定理 WeakSpace.isOpen_of_isOpen
  结论: (V : Set E)
  证明: by
  simpa [Set.image_image] using isOpenMap_toWeakSpace_symm _ hV

Depends on / 依赖: Set.image_image, image_image, isOpenMap_toWeakSpace_symm
-/
theorem WeakSpace.isOpen_of_isOpen (V : Set E)
    (hV : IsOpen ((toWeakSpaceCLM 𝕜 E) '' V : Set (WeakSpace 𝕜 E))) : IsOpen V := by
  simpa [Set.image_image] using isOpenMap_toWeakSpace_symm _ hV

/--
theorem `tendsto_iff_forall_eval_tendsto_topDualPairing` / 定理 `tendsto_iff_forall_eval_tendsto_topDualPairing`

English:
theorem tendsto_iff_forall_eval_tendsto_topDualPairing
  statement: {l : Filter α} {f : α -> WeakDual 𝕜 E}
  proof: WeakBilin.tendsto_iff_forall_eval_tendsto _ ContinuousLinearMap.coe_injective

中文:
定理 tendsto_iff_forall_eval_tendsto_topDualPairing
  结论: {l : Filter α} {f : α -> WeakDual 𝕜 E}
  证明: WeakBilin.tendsto_iff_forall_eval_tendsto _ ContinuousLinearMap.coe_injective

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coe_injective, WeakBilin, WeakBilin.tendsto_iff_forall_eval_tendsto, coe_injective, tendsto_iff_forall_eval_tendsto
-/
theorem tendsto_iff_forall_eval_tendsto_topDualPairing {l : Filter α} {f : α -> WeakDual 𝕜 E}
    {x : WeakDual 𝕜 E} :
    Tendsto f l (𝓝 x) ↔
      forall y, Tendsto (fun i => topDualPairing 𝕜 E (f i) y) l (𝓝 (topDualPairing 𝕜 E x y)) :=
  WeakBilin.tendsto_iff_forall_eval_tendsto _ ContinuousLinearMap.coe_injective

end Semiring

section Ring

namespace WeakSpace

variable [CommRing 𝕜] [TopologicalSpace 𝕜] [IsTopologicalAddGroup 𝕜] [ContinuousConstSMul 𝕜 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: : AddCommGroup (WeakSpace 𝕜 E)
  body: inferInstanceAs AddCommGroup (WeakBilin (topDualPairing 𝕜 E).flip)

中文:
实例 instAddCommGroup
  签名: : AddCommGroup (WeakSpace 𝕜 E)
  定义体: inferInstanceAs AddCommGroup (WeakBilin (topDualPairing 𝕜 E).flip)

Depends on / 依赖: AddCommGroup, WeakBilin, topDualPairing
-/
instance instAddCommGroup : AddCommGroup (WeakSpace 𝕜 E) :=
inferInstanceAs AddCommGroup (WeakBilin (topDualPairing 𝕜 E).flip)

/--
Instance `instIsTopologicalAddGroup` / 实例 `instIsTopologicalAddGroup`

English:
instance instIsTopologicalAddGroup
  signature: : IsTopologicalAddGroup (WeakSpace 𝕜 E)
  body: WeakBilin.instIsTopologicalAddGroup (topDualPairing 𝕜 E).flip

中文:
实例 instIsTopologicalAddGroup
  签名: : IsTopologicalAddGroup (WeakSpace 𝕜 E)
  定义体: WeakBilin.instIsTopologicalAddGroup (topDualPairing 𝕜 E).flip

Depends on / 依赖: WeakBilin, WeakBilin.instIsTopologicalAddGroup, instIsTopologicalAddGroup, topDualPairing
-/
instance instIsTopologicalAddGroup : IsTopologicalAddGroup (WeakSpace 𝕜 E) :=
  WeakBilin.instIsTopologicalAddGroup (topDualPairing 𝕜 E).flip

end WeakSpace

end Ring
