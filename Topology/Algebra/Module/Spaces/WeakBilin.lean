/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Moritz Doll
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Weak dual topology

This file defines the weak topology given two vector spaces `E` and `F` over a commutative semiring
`𝕜` and a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`. The weak topology on `E` is the coarsest topology
such that for all `y : F` every map `fun x => B x y` is continuous.

## Main definitions

The main definition is the type `WeakBilin B`.

* Given `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`, the type `WeakBilin B` is a type synonym for `E`.
* The instance `WeakBilin.instTopologicalSpace` is the weak topology induced by the bilinear form
  `B`.

## Main results

We establish that `WeakBilin B` has the following structure:
* `WeakBilin.instContinuousAdd`: The addition in `WeakBilin B` is continuous.
* `WeakBilin.instContinuousSMul`: The scalar multiplication in `WeakBilin B` is continuous.

We prove the following results characterizing the weak topology:
* `eval_continuous`: For any `y : F`, the evaluation mapping `fun x => B x y` is continuous.
* `continuous_of_continuous_eval`: For a mapping to `WeakBilin B` to be continuous,
  it suffices that its compositions with pairing with `B` at all points `y : F` is continuous.
* `tendsto_iff_forall_eval_tendsto`: Convergence in `WeakBilin B` can be characterized
  in terms of convergence of the evaluations at all points `y : F`.

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

section WeakTopology

/-- The space `E` equipped with the weak topology induced by the bilinear form `B`. -/
@[nolint unusedArguments]
/--
Definition of `WeakBilin` / `WeakBilin` 的定义

English:
definition WeakBilin
  signature: [CommSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]
  body: E

中文:
定义 WeakBilin
  签名: [交换半环 𝕜] [加法交换幺半群 E] [模 𝕜 E] [加法交换幺半群 F] [模 𝕜 F]
  定义体: E
-/
def WeakBilin [CommSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]
    (_ : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜) := E

namespace WeakBilin

variable [CommSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]
  (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜) [CommSemiring 𝕝] [Module 𝕝 E] in
deriving instance SMul 𝕝, AddCommMonoid, Module 𝕝 for WeakBilin B

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: [CommSemiring 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommMonoid F]
  body: inferInstanceAs AddCommGroup E

中文:
实例 instAddCommGroup
  签名: [交换半环 𝕜] [加法交换群 E] [模 𝕜 E] [加法交换幺半群 F]
  定义体: inferInstanceAs AddCommGroup E

Depends on / 依赖: AddCommGroup
-/
instance instAddCommGroup [CommSemiring 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommMonoid F]
    [Module 𝕜 F] (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜) : AddCommGroup (WeakBilin B) :=
inferInstanceAs AddCommGroup E

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemiring
  signature: 𝕜] [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]
  body: inferInstance

中文:
实例 [交换半环
  签名: 𝕜] [加法交换幺半群 E] [模 𝕜 E] [加法交换幺半群 F] [模 𝕜 F]
  定义体: inferInstance
-/
instance [CommSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]
    (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜) : Module 𝕜 (WeakBilin B) :=
  inferInstance

/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: [CommSemiring 𝕜] [CommSemiring 𝕝] [AddCommMonoid E] [Module 𝕜 E]
  body: inferInstanceAs IsScalarTower 𝕝 𝕜 E

中文:
实例 instIsScalarTower
  签名: [交换半环 𝕜] [交换半环 𝕝] [加法交换幺半群 E] [模 𝕜 E]
  定义体: inferInstanceAs IsScalarTower 𝕝 𝕜 E

Depends on / 依赖: IsScalarTower
-/
instance instIsScalarTower [CommSemiring 𝕜] [CommSemiring 𝕝] [AddCommMonoid E] [Module 𝕜 E]
    [AddCommMonoid F] [Module 𝕜 F] [SMul 𝕝 𝕜] [Module 𝕝 E] [IsScalarTower 𝕝 𝕜 E]
    (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜) : IsScalarTower 𝕝 𝕜 (WeakBilin B) :=
inferInstanceAs IsScalarTower 𝕝 𝕜 E

section Semiring

variable [TopologicalSpace 𝕜] [CommSemiring 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid F] [Module 𝕜 F]
variable (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜)

/--
Instance `instTopologicalSpace` / 实例 `instTopologicalSpace`

English:
instance instTopologicalSpace
  signature: : TopologicalSpace (WeakBilin B)
  body: TopologicalSpace.induced (fun x y => B x y) Pi.topologicalSpace

中文:
实例 instTopologicalSpace
  签名: : 拓扑空间 (WeakBilin B)
  定义体: TopologicalSpace.induced (fun x y => B x y) Pi.topologicalSpace

Depends on / 依赖: Pi.topologicalSpace, TopologicalSpace, TopologicalSpace.induced, induced, topologicalSpace
-/
instance instTopologicalSpace : TopologicalSpace (WeakBilin B) :=
  TopologicalSpace.induced (fun x y => B x y) Pi.topologicalSpace

/--
theorem `coeFn_continuous` / 定理 `coeFn_continuous`

English:
theorem coeFn_continuous
  statement: Continuous fun (x : WeakBilin B) y => B x y
  proof: continuous_induced_dom

@[fun_prop]

中文:
定理 coeFn_continuous
  结论: 连续 fun (x : WeakBilin B) y => B x y
  证明: continuous_induced_dom

@[fun_prop]

Depends on / 依赖: continuous_induced_dom
-/
theorem coeFn_continuous : Continuous fun (x : WeakBilin B) y => B x y :=
  continuous_induced_dom

@[fun_prop]
/--
theorem `eval_continuous` / 定理 `eval_continuous`

English:
theorem eval_continuous
  given: (y : F)
  statement: Continuous fun x : WeakBilin B => B x y
  proof: (continuous_pi_iff.mp (coeFn_continuous B)) y

中文:
定理 eval_continuous
  条件: (y : F)
  结论: 连续 fun x : WeakBilin B => B x y
  证明: (continuous_pi_iff.mp (coeFn_continuous B)) y

Depends on / 依赖: coeFn_continuous, continuous_pi_iff, continuous_pi_iff.mp
-/
theorem eval_continuous (y : F) : Continuous fun x : WeakBilin B => B x y :=
  (continuous_pi_iff.mp (coeFn_continuous B)) y

/--
theorem `continuous_of_continuous_eval` / 定理 `continuous_of_continuous_eval`

English:
theorem continuous_of_continuous_eval
  statement: [TopologicalSpace α] {g : α -> WeakBilin B}
  proof: continuous_induced_rng.2 (continuous_pi_iff.mpr h)

中文:
定理 continuous_of_continuous_eval
  结论: [拓扑空间 α] {g : α -> WeakBilin B}
  证明: continuous_induced_rng.2 (continuous_pi_iff.mpr h)

Depends on / 依赖: continuous_induced_rng, continuous_pi_iff, continuous_pi_iff.mpr
-/
theorem continuous_of_continuous_eval [TopologicalSpace α] {g : α -> WeakBilin B}
    (h : forall y, Continuous fun a => B (g a) y) : Continuous g :=
  continuous_induced_rng.2 (continuous_pi_iff.mpr h)

/--
theorem `isEmbedding` / 定理 `isEmbedding`

English:
theorem isEmbedding
  given: {B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜} (hB : Function.Injective B)
  proof: Function.Injective.isEmbedding_induced LinearMap.coe_injective.comp hB

中文:
定理 isEmbedding
  条件: {B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜} (hB : 函数.单射 B)
  证明: Function.Injective.isEmbedding_induced LinearMap.coe_injective.comp hB

Depends on / 依赖: Function, Function.Injective.isEmbedding_induced, Injective, LinearMap, LinearMap.coe_injective.comp, coe_injective, isEmbedding_induced
-/
theorem isEmbedding {B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜} (hB : Function.Injective B) :
    IsEmbedding fun (x : WeakBilin B) y => B x y :=
Function.Injective.isEmbedding_induced LinearMap.coe_injective.comp hB

/--
theorem `tendsto_iff_forall_eval_tendsto` / 定理 `tendsto_iff_forall_eval_tendsto`

English:
theorem tendsto_iff_forall_eval_tendsto
  statement: {l : Filter α} {f : α -> WeakBilin B} {x : WeakBilin B}
  proof: by
  rw [← tendsto_pi_nhds]; rw [(isEmbedding hB).tendsto_nhds_iff]
  rfl

中文:
定理 tendsto_iff_对任意_eval_tendsto
  结论: {l : 滤子 α} {f : α -> WeakBilin B} {x : WeakBilin B}
  证明: by
  rw [← tendsto_pi_nhds]; rw [(isEmbedding hB).tendsto_nhds_iff]
  rfl

Depends on / 依赖: isEmbedding, tendsto_nhds_iff, tendsto_pi_nhds
-/
theorem tendsto_iff_forall_eval_tendsto {l : Filter α} {f : α -> WeakBilin B} {x : WeakBilin B}
    (hB : Function.Injective B) :
    Tendsto f l (𝓝 x) ↔ forall y, Tendsto (fun i => B (f i) y) l (𝓝 (B x y)) := by
  rw [← tendsto_pi_nhds]; rw [(isEmbedding hB).tendsto_nhds_iff]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Instance `instContinuousAdd` / 实例 `instContinuousAdd`

English:
instance instContinuousAdd
  signature: [ContinuousAdd 𝕜]
  body: by
  refine ⟨continuous_induced_rng.2 ?_⟩
  refine
    cast (congr_arg _ ?_)
      (((coeFn_continuous B).comp continuous_fst).add ((coeFn_continuous B).comp continuous_snd))
  ext
  simp only [Function.comp_apply, Pi.add_apply, map_add, LinearMap.add_apply]

中文:
实例 instContinuousAdd
  签名: [连续加法 𝕜]
  定义体: by
  refine ⟨continuous_induced_rng.2 ?_⟩
  refine
    cast (congr_arg _ ?_)
      (((coeFn_continuous B).comp continuous_fst).add ((coeFn_continuous B).comp continuous_snd))
  ext
  simp only [Function.comp_apply, Pi.add_apply, map_add, LinearMap.add_apply]

Depends on / 依赖: Function, Function.comp_apply, LinearMap, LinearMap.add_apply, Pi.add_apply, add_apply, coeFn_continuous, comp_apply, congr_arg, continuous_fst, continuous_induced_rng, continuous_snd, map_add
-/
instance instContinuousAdd [ContinuousAdd 𝕜] : ContinuousAdd (WeakBilin B) := by
  refine ⟨continuous_induced_rng.2 ?_⟩
  refine
    cast (congr_arg _ ?_)
      (((coeFn_continuous B).comp continuous_fst).add ((coeFn_continuous B).comp continuous_snd))
  ext
  simp only [Function.comp_apply, Pi.add_apply, map_add, LinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `instContinuousSMul` / 实例 `instContinuousSMul`

English:
instance instContinuousSMul
  signature: [ContinuousSMul 𝕜 𝕜]
  body: by
  refine ⟨continuous_induced_rng.2 ?_⟩
  refine cast (congr_arg _ ?_) (continuous_fst.fun_smul ((coeFn_continuous B).comp continuous_snd))
  ext
  simp only [Function.comp_apply, Pi.smul_apply, map_smulₛₗ, RingHom.id_apply, LinearMap.smul_apply]

中文:
实例 instContinuousSMul
  签名: [连续标量乘法 𝕜 𝕜]
  定义体: by
  refine ⟨continuous_induced_rng.2 ?_⟩
  refine cast (congr_arg _ ?_) (continuous_fst.fun_smul ((coeFn_continuous B).comp continuous_snd))
  ext
  simp only [Function.comp_apply, Pi.smul_apply, map_smulₛₗ, RingHom.id_apply, LinearMap.smul_apply]

Depends on / 依赖: Function, Function.comp_apply, LinearMap, LinearMap.smul_apply, Pi.smul_apply, RingHom, RingHom.id_apply, coeFn_continuous, comp_apply, congr_arg, continuous_fst, continuous_fst.fun_smul, continuous_induced_rng, continuous_snd, fun_smul, id_apply, smul_apply
-/
instance instContinuousSMul [ContinuousSMul 𝕜 𝕜] : ContinuousSMul 𝕜 (WeakBilin B) := by
  refine ⟨continuous_induced_rng.2 ?_⟩
  refine cast (congr_arg _ ?_) (continuous_fst.fun_smul ((coeFn_continuous B).comp continuous_snd))
  ext
  simp only [Function.comp_apply, Pi.smul_apply, map_smulₛₗ, RingHom.id_apply, LinearMap.smul_apply]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]
  body: ⟨B.flip f, by fun_prop⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

中文:
定义 eval
  签名: [连续加法 𝕜] [连续常数标量乘法 𝕜 𝕜]
  定义体: ⟨B.flip f, by fun_prop⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

Depends on / 依赖: B.flip, fun_prop
-/
def eval [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜] :
    F ->ₗ[𝕜] StrongDual 𝕜 (WeakBilin B) where
  toFun f := ⟨B.flip f, by fun_prop⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

end Semiring

section Ring

variable [TopologicalSpace 𝕜] [CommRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup F] [Module 𝕜 F]


variable (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `instIsTopologicalAddGroup` / 实例 `instIsTopologicalAddGroup`

English:
instance instIsTopologicalAddGroup
  signature: [ContinuousAdd 𝕜]
  body: by infer_instance
  continuous_neg := by
    refine continuous_induced_rng.2 (continuous_pi_iff.mpr fun y => ?_)
    refine cast (congr_arg _ ?_) (eval_continuous B (-y))
    ext x
    simp only [map_neg, Function.comp_apply, LinearMap.neg_apply]

中文:
实例 instIsTopologicalAddGroup
  签名: [连续加法 𝕜]
  定义体: by infer_instance
  continuous_neg := by
    refine continuous_induced_rng.2 (continuous_pi_iff.mpr fun y => ?_)
    refine cast (congr_arg _ ?_) (eval_continuous B (-y))
    ext x
    simp only [map_neg, Function.comp_apply, LinearMap.neg_apply]

Depends on / 依赖: Function, Function.comp_apply, LinearMap, LinearMap.neg_apply, comp_apply, congr_arg, continuous_induced_rng, continuous_neg, continuous_pi_iff, continuous_pi_iff.mpr, eval_continuous, infer_instance, map_neg, neg_apply
-/
instance instIsTopologicalAddGroup [ContinuousAdd 𝕜] : IsTopologicalAddGroup (WeakBilin B) where
  toContinuousAdd := by infer_instance
  continuous_neg := by
    refine continuous_induced_rng.2 (continuous_pi_iff.mpr fun y => ?_)
    refine cast (congr_arg _ ?_) (eval_continuous B (-y))
    ext x
    simp only [map_neg, Function.comp_apply, LinearMap.neg_apply]

end Ring

end WeakBilin

end WeakTopology
