/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.LinearAlgebra.BilinearMap

/-! # Weak topologies on modules

Given a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`, the weak topology on `E` is the coarsest topology
such that for all `y : F` every map `(B · y)` is continuous; equivalently, it is the topology
on `E` induced by the map `(B · · : E → (F → 𝕜))`.

This file defines a `Prop`-valued typeclass `LinearMap.IsWeak` expressing that an existing topology
on `E` is the weak topology. Although this could be passed around explicitly as a hypothesis
`Topology.IsInducing (B · ·)`, given the ubiquity of weak topologies in functional analysis, the
numerous properties that can be deduced because the inducing map `B` is bilinear, the fact that
several theorems (e.g., one version of the bipolar theorem) require this hypothesis, and we can
instantiate this class for several extant types in Mathlib, we choose to make this a typeclass
instead.

Note that establishing `LinearMap.IsWeak` before proving theorems about a particular type can help
prevent abuse of definitional equalities. This because spaces equipped with a weak topology are
frequently type synonyms of some other type `E'`. For example, suppose `E'` is a type (potentially
with some extant topology other than the weak topology) and `B' : E' →ₗ[𝕜] F →ₗ[𝕜] 𝕜` is a
bilinear form. To consider the weak topology on `E'` induced by `B'`, in practice we must create a
type synonym `E` with an instance `TopologicalSpace E := .induced (B' · ·) Pi.topologicalSpace`.
It would then be tempting to create theorems such as:

```lean
example (y : F) : Continuous (fun x : E ↦ B' x y) := sorry
```

However, this statement contains an abuse of the the definitional equality `E := E'` since `x : E`,
but `B'` has domain `E'`. Moreover, one might be tempted to say that `B'.IsWeak`, but this is
impossible because the domain of `B'` is `E'`, which is equipped with the incorrect topology.
Instead, what one should do is to first define a new bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` by
composing `B'` with the linear equivalence between `E` and `E'`, and then establish `B.IsWeak`.
If then one proves theorems about `E` using only the `LinearMap.IsWeak` API, then one can have more
confidence that the statements are type correct.

## Main definitions

+ `LinearMap.IsWeak`: a typeclass expressing that the topology on `E` is the weak topology induced
  by the bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`.
+ `LinearMap.IsWeak.eval`: the evaluation map `F →ₗ[𝕜] StrongDual 𝕜 E` sending `y : F` to the
  continuous linear functional `(B · y)`.

## Main results

We prove the following results characterizing the weak topology:

* `LinearMap.IsWeak.continuous_eval`: For any `y : F`, the evaluation mapping `(B · y)` is
  continuous.
* `LinearMap.IsWeak.continuous_of_continuous_eval`: For a mapping to `WeakBilin B` to be continuous,
  it suffices that its compositions with pairing with `B` at all points `y : F` is continuous.
* `LinearMap.IsWeak.tendsto_iff_forall_eval_tendsto`: Convergence in `WeakBilin B` can be
  characterized in terms of convergence of the evaluations at all points `y : F`.

-/

@[expose] public section

open Topology Filter

section Basic

variable {α 𝕜 E F E' F' : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜]
    [AddCommMonoid E] [Module 𝕜 E]
    [AddCommMonoid F] [Module 𝕜 F]

/-- Typeclass expressing that the topology on `E` is the weak topology induced
by the bilinear form `B`. -/
@[mk_iff]
/--
Definition of `LinearMap.IsWeak` / `LinearMap.IsWeak` 的定义

English:
class LinearMap.IsWeak
  parameters: [t : TopologicalSpace E] (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜)
  axioms and operations (1):
    - eq_induced : t = .induced (B · ·) Pi.topologicalSpace

中文:
类 LinearMap.IsWeak
  参数: [t : TopologicalSpace E] (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜)
  公理与运算 (1 个):
    - eq_induced : t = .induced (B · ·) Pi.topologicalSpace
-/
class LinearMap.IsWeak [t : TopologicalSpace E] (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜) : Prop where
  eq_induced : t = .induced (B · ·) Pi.topologicalSpace

variable [inst : TopologicalSpace E] (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜) [hB : B.IsWeak]

namespace LinearMap.IsWeak

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: B.flip.flip.IsWeak
  body: hB

中文:
实例 :
  签名: B.flip.flip.IsWeak
  定义体: hB
-/
instance : B.flip.flip.IsWeak := hB

/--
theorem `coeFn_continuous` / 定理 `coeFn_continuous`

English:
theorem coeFn_continuous
  statement: Continuous (B · ·)
  proof: hB.eq_induced ▸ continuous_induced_dom

中文:
定理 coeFn_continuous
  结论: Continuous (B · ·)
  证明: hB.eq_induced ▸ continuous_induced_dom

Depends on / 依赖: continuous_induced_dom, eq_induced, hB.eq_induced
-/
theorem coeFn_continuous : Continuous (B · ·) :=
  hB.eq_induced ▸ continuous_induced_dom

/-- The evaluation map `(B · y) : E → 𝕜` is continuous for each `y : F`. -/
@[fun_prop]
/--
lemma `continuous_eval` / 引理 `continuous_eval`

English:
lemma continuous_eval
  given: (y : F)
  statement: Continuous (B · y)
  proof: continuous_pi_iff.mp (coeFn_continuous B) _

中文:
引理 continuous_eval
  条件: (y : F)
  结论: Continuous (B · y)
  证明: continuous_pi_iff.mp (coeFn_continuous B) _

Depends on / 依赖: coeFn_continuous, continuous_pi_iff, continuous_pi_iff.mp
-/
lemma continuous_eval (y : F) : Continuous (B · y) :=
  continuous_pi_iff.mp (coeFn_continuous B) _

/--
lemma `continuous_of_continuous_eval` / 引理 `continuous_of_continuous_eval`

English:
lemma continuous_of_continuous_eval
  statement: {α : Type*} [TopologicalSpace α]
  proof: hB.eq_induced ▸ continuous_induced_rng.mpr (continuous_pi_iff.mpr hf)

中文:
引理 continuous_of_continuous_eval
  结论: {α : 类型} [TopologicalSpace α]
  证明: hB.eq_induced ▸ continuous_induced_rng.mpr (continuous_pi_iff.mpr hf)

Depends on / 依赖: continuous_induced_rng, continuous_induced_rng.mpr, continuous_pi_iff, continuous_pi_iff.mpr, eq_induced, hB.eq_induced
-/
lemma continuous_of_continuous_eval {α : Type*} [TopologicalSpace α]
    {f : α -> E} (hf : forall y, Continuous (fun x => B (f x) y)) :
    Continuous f :=
  hB.eq_induced ▸ continuous_induced_rng.mpr (continuous_pi_iff.mpr hf)

/--
lemma `continuous_iff` / 引理 `continuous_iff`

English:
lemma continuous_iff
  given: {α : Type*} [TopologicalSpace α] {f : α -> E}
  proof: ⟨fun _ => by fun_prop, hB.continuous_of_continuous_eval⟩

中文:
引理 continuous_iff
  条件: {α : 类型} [TopologicalSpace α] {f : α -> E}
  证明: ⟨fun _ => by fun_prop, hB.continuous_of_continuous_eval⟩

Depends on / 依赖: continuous_of_continuous_eval, fun_prop, hB.continuous_of_continuous_eval
-/
lemma continuous_iff {α : Type*} [TopologicalSpace α] {f : α -> E} :
    Continuous f ↔ forall y, Continuous (fun x => B (f x) y) :=
  ⟨fun _ => by fun_prop, hB.continuous_of_continuous_eval⟩

/--
theorem `isInducing` / 定理 `isInducing`

English:
theorem isInducing
  statement: IsInducing (B · ·) where
  proof: hB.eq_induced

中文:
定理 isInducing
  结论: IsInducing (B · ·) where
  证明: hB.eq_induced

Depends on / 依赖: eq_induced, hB.eq_induced
-/
theorem isInducing : IsInducing (B · ·) where
  eq_induced := hB.eq_induced

variable {B} in
/--
theorem `isEmbedding` / 定理 `isEmbedding`

English:
theorem isEmbedding
  given: (hB_inj : Function.Injective B)
  proof: by
  convert! (LinearMap.coe_injective.comp hB_inj |>.isEmbedding_induced)
  exact hB.eq_induced

中文:
定理 isEmbedding
  条件: (hB_inj : Function.Injective B)
  证明: by
  convert! (LinearMap.coe_injective.comp hB_inj |>.isEmbedding_induced)
  exact hB.eq_induced

Depends on / 依赖: LinearMap, LinearMap.coe_injective.comp, coe_injective, convert, eq_induced, hB.eq_induced, hB_inj, isEmbedding_induced
-/
theorem isEmbedding (hB_inj : Function.Injective B) :
    IsEmbedding (B · ·) := by
  convert! (LinearMap.coe_injective.comp hB_inj |>.isEmbedding_induced)
  exact hB.eq_induced

variable {B} in
/--
theorem `tendsto_iff_forall_eval_tendsto` / 定理 `tendsto_iff_forall_eval_tendsto`

English:
theorem tendsto_iff_forall_eval_tendsto
  statement: {α : Type*} {l : Filter α} {f : α -> E} {x : E}
  proof: by
  rw [← tendsto_pi_nhds]; rw [(isEmbedding hB_inj).tendsto_nhds_iff]; rw [Function.comp_def]

中文:
定理 tendsto_iff_forall_eval_tendsto
  结论: {α : 类型} {l : Filter α} {f : α -> E} {x : E}
  证明: by
  rw [← tendsto_pi_nhds]; rw [(isEmbedding hB_inj).tendsto_nhds_iff]; rw [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comp_def, hB_inj, isEmbedding, tendsto_nhds_iff, tendsto_pi_nhds
-/
theorem tendsto_iff_forall_eval_tendsto {α : Type*} {l : Filter α} {f : α -> E} {x : E}
    (hB_inj : Function.Injective B) :
    Tendsto f l (𝓝 x) ↔ forall y, Tendsto (fun i => B (f i) y) l (𝓝 (B x y)) := by
  rw [← tendsto_pi_nhds]; rw [(isEmbedding hB_inj).tendsto_nhds_iff]; rw [Function.comp_def]

/--
theorem `congr` / 定理 `congr`

English:
theorem congr
  statement: [AddCommMonoid E'] [Module 𝕜 E']
  proof: by
    rw [e.symm.toHomeomorph.induced_eq.symm]
    apply congr(TopologicalSpace.induced e.symm $(hB.eq_induced)).trans
    simp_rw [induced_compose, ← hBB', induced_to_pi]
    rw [f.toEquiv.iInf_congr]
    simp

中文:
定理 congr
  结论: [AddCommMonoid E'] [Module 𝕜 E']
  证明: by
    rw [e.symm.toHomeomorph.induced_eq.symm]
    apply congr(TopologicalSpace.induced e.symm $(hB.eq_induced)).trans
    simp_rw [induced_compose, ← hBB', induced_to_pi]
    rw [f.toEquiv.iInf_congr]
    simp
-/
protected theorem congr [AddCommMonoid E'] [Module 𝕜 E']
    [AddCommMonoid F'] [Module 𝕜 F'] [TopologicalSpace E']
    (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜) (B' : E' ->ₗ[𝕜] F' ->ₗ[𝕜] 𝕜) (e : E ≃L[𝕜] E') (f : F ≃ₗ[𝕜] F')
    (hBB' : e.toLinearEquiv.arrowCongr (f.arrowCongr (.refl ..)) B = B') [hB : B.IsWeak] :
    B'.IsWeak where
  eq_induced := by
    rw [e.symm.toHomeomorph.induced_eq.symm]
    apply congr(TopologicalSpace.induced e.symm $(hB.eq_induced)).trans
    simp_rw [induced_compose, ← hBB', induced_to_pi]
    rw [f.toEquiv.iInf_congr]
    simp

/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]
  body: ⟨B.flip f, by fun_prop⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

include hB in

中文:
定义 eval
  签名: [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]
  定义体: ⟨B.flip f, by fun_prop⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

include hB in

Depends on / 依赖: B.flip, fun_prop
-/
def eval [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜] : F ->ₗ[𝕜] StrongDual 𝕜 E where
  toFun f := ⟨B.flip f, by fun_prop⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

include hB in
/--
theorem `continuousAdd` / 定理 `continuousAdd`

English:
theorem continuousAdd
  given: [ContinuousAdd 𝕜]
  statement: ContinuousAdd E where
  proof: by
    let t₁ : TopologicalSpace E := .induced (B · ·) Pi.topologicalSpace
    have : B.IsWeak := ⟨rfl⟩
    rw [hB.eq_induced]; rw [continuous_induced_rng]
    simp only [Function.comp_def, map_add, add_apply]
    fun_prop

include hB in

中文:
定理 continuousAdd
  条件: [ContinuousAdd 𝕜]
  结论: ContinuousAdd E where
  证明: by
    let t₁ : TopologicalSpace E := .induced (B · ·) Pi.topologicalSpace
    have : B.IsWeak := ⟨rfl⟩
    rw [hB.eq_induced]; rw [continuous_induced_rng]
    simp only [Function.comp_def, map_add, add_apply]
    fun_prop

include hB in

Depends on / 依赖: B.IsWeak, Function, Function.comp_def, IsWeak, Pi.topologicalSpace, TopologicalSpace, add_apply, comp_def, continuous_induced_rng, eq_induced, fun_prop, hB.eq_induced, induced, map_add, topologicalSpace
-/
theorem continuousAdd [ContinuousAdd 𝕜] : ContinuousAdd E where
  continuous_add := by
    let t₁ : TopologicalSpace E := .induced (B · ·) Pi.topologicalSpace
    have : B.IsWeak := ⟨rfl⟩
    rw [hB.eq_induced]; rw [continuous_induced_rng]
    simp only [Function.comp_def, map_add, add_apply]
    fun_prop

include hB in
/--
theorem `continuousSMul` / 定理 `continuousSMul`

English:
theorem continuousSMul
  given: [ContinuousSMul 𝕜 𝕜]
  statement: ContinuousSMul 𝕜 E where
  proof: by
    let t₁ : TopologicalSpace E := .induced (B · ·) Pi.topologicalSpace
    have : B.IsWeak := ⟨rfl⟩
    rw [hB.eq_induced]; rw [continuous_induced_rng]
    simp only [Function.comp_def, map_smul, smul_apply]
    fun_prop

中文:
定理 continuousSMul
  条件: [ContinuousSMul 𝕜 𝕜]
  结论: ContinuousSMul 𝕜 E where
  证明: by
    let t₁ : TopologicalSpace E := .induced (B · ·) Pi.topologicalSpace
    have : B.IsWeak := ⟨rfl⟩
    rw [hB.eq_induced]; rw [continuous_induced_rng]
    simp only [Function.comp_def, map_smul, smul_apply]
    fun_prop

Depends on / 依赖: B.IsWeak, Function, Function.comp_def, IsWeak, Pi.topologicalSpace, TopologicalSpace, comp_def, continuous_induced_rng, eq_induced, fun_prop, hB.eq_induced, induced, map_smul, smul_apply, topologicalSpace
-/
theorem continuousSMul [ContinuousSMul 𝕜 𝕜] : ContinuousSMul 𝕜 E where
  continuous_smul := by
    let t₁ : TopologicalSpace E := .induced (B · ·) Pi.topologicalSpace
    have : B.IsWeak := ⟨rfl⟩
    rw [hB.eq_induced]; rw [continuous_induced_rng]
    simp only [Function.comp_def, map_smul, smul_apply]
    fun_prop

/--
theorem `isTopologicalAddGroup` / 定理 `isTopologicalAddGroup`

English:
theorem isTopologicalAddGroup
  statement: {𝕜 E F : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜]
  proof: continuousAdd B
  continuous_neg := by
    let t₁ : TopologicalSpace E := .induced (B · ·) Pi.topologicalSpace
    have : B.IsWeak := ⟨rfl⟩
    rw [hB.eq_induced]; rw [continuous_induced_rng]; rw [continuous_pi_iff]
    simp_rw [Function.comp_apply, map_neg, neg_apply, ← map_neg (B _)]
    fun_prop

中文:
定理 isTopologicalAddGroup
  结论: {𝕜 E F : 类型} [CommRing 𝕜] [TopologicalSpace 𝕜]
  证明: continuousAdd B
  continuous_neg := by
    let t₁ : TopologicalSpace E := .induced (B · ·) Pi.topologicalSpace
    have : B.IsWeak := ⟨rfl⟩
    rw [hB.eq_induced]; rw [continuous_induced_rng]; rw [continuous_pi_iff]
    simp_rw [Function.comp_apply, map_neg, neg_apply, ← map_neg (B _)]
    fun_prop

Depends on / 依赖: continuousAdd
-/
theorem isTopologicalAddGroup {𝕜 E F : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace E]
    [ContinuousAdd 𝕜] (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜) [hB : B.IsWeak] : IsTopologicalAddGroup E where
  toContinuousAdd := continuousAdd B
  continuous_neg := by
    let t₁ : TopologicalSpace E := .induced (B · ·) Pi.topologicalSpace
    have : B.IsWeak := ⟨rfl⟩
    rw [hB.eq_induced]; rw [continuous_induced_rng]; rw [continuous_pi_iff]
    simp_rw [Function.comp_apply, map_neg, neg_apply, ← map_neg (B _)]
    fun_prop

end LinearMap.IsWeak

end Basic
