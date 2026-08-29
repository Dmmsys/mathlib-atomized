/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Yury Kudryashov, Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Analysis.Normed.Operator.Completeness
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import Mathlib.Topology.MetricSpace.PiNat
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.LocallyConvex.WeakDual

/-!
# Weak dual of normed space

Let `E` be a normed space over a field `𝕜`. This file is concerned with properties of the weak-\*
topology on the dual of `E`. By the dual, we mean either of the type synonyms
`StrongDual 𝕜 E` or `WeakDual 𝕜 E`, depending on whether it is viewed as equipped with its usual
operator norm topology or the weak-\* topology.

It is shown that the canonical mapping `StrongDual 𝕜 E → WeakDual 𝕜 E` is continuous, and
as a consequence the weak-\* topology is coarser than the topology obtained from the operator norm
(dual norm).

The file also equips `WeakDual 𝕜 E` with the norm bornology inherited from `StrongDual 𝕜 E`, so
that `IsBounded` refers to operator-norm boundedness. This is a pragmatic choice discussed
further in the implementation notes.

We establish the Banach-Alaoglu theorem about the compactness of closed balls in the dual of `E`
(as well as sets of somewhat more general form) with respect to the weak-\* topology.

The first main result concerns the comparison of the operator norm topology on `StrongDual 𝕜 E` and
the weak-\* topology on (its type synonym) `WeakDual 𝕜 E`:
* `dual_norm_topology_le_weak_dual_topology`: The weak-\* topology on the dual of a normed space is
  coarser (not necessarily strictly) than the operator norm topology.
* `WeakDual.isCompact_polar` (a version of the Banach-Alaoglu theorem): The polar set of a
  neighborhood of the origin in a normed space `E` over `𝕜` is compact in `WeakDual _ E`, if the
  nontrivially normed field `𝕜` is proper as a topological space.
* `WeakDual.isCompact_closedBall` (the most common special case of the Banach-Alaoglu theorem):
  Closed balls in the dual of a normed space `E` over `ℝ` or `ℂ` are compact in the weak-star
  topology.

## Main definitions

* `StrongDual.toWeakDual` and `WeakDual.toStrongDual`: Linear equivalences between the dual types.
* `WeakDual.instBornology`: The norm bornology on `WeakDual 𝕜 E`.
* `WeakDual.seminormFamily`: The family of seminorms `fun x f ↦ ‖f x‖` generating the weak-\*
  topology.
* `WeakDual.polar`: The polar set of `s : Set E` viewed as a subset of `WeakDual 𝕜 E`.

## Main results

### Topology comparison
* `NormedSpace.Dual.toWeakDual_continuous`: The weak-\* topology is coarser than the norm topology.

### Bornology and pointwise bounds
* `WeakDual.isBounded_iff_isVonNBounded`: Equivalence of norm and weak-\* boundedness for
  Banach spaces.

### Compactness and Banach-Alaoglu
* `WeakDual.isCompact_polar`: Polars of neighborhoods of the origin are weak-\* compact.
* `WeakDual.isCompact_closedBall`: Closed balls are weak-\* compact.
* `WeakDual.isSeqCompact_closedBall`: Sequential version for separable spaces.

## Implementation notes

* **Topology synonym:** When `M` is a vector space, the duals `StrongDual 𝕜 M` and `WeakDual 𝕜 M`
  are type synonyms with different topology instances.
* **Bornology choice:** The `Bornology` instance on `WeakDual 𝕜 E` is inherited from
  `StrongDual 𝕜 E` via `inferInstanceAs` and corresponds to the operator-norm bornology.
  While the natural bornology for a weak topology is technically the von Neumann bornology
  (pointwise boundedness), we use the norm bornology for several pragmatic reasons:
  1. **Practicality:** In the normed setting, "bounded" is almost universally synonymous with
     "norm-bounded". This allows `IsBounded` to be used directly in statements like Banach-Alaoglu.
  2. **Clarity:** It preserves a clear distinction between norm-boundedness (`IsBounded`) and
     topological weak-\* boundedness (`IsVonNBounded`).
  3. **Consistency:** By the Uniform Boundedness Principle, these notions coincide whenever
     `E` is a Banach space (`isBounded_iff_isVonNBounded`).
* **Polar sets:** The polar set `polar 𝕜 s` of a subset `s` of `E` is originally defined as a
  subset of the dual `StrongDual 𝕜 E`. We care about properties of these w.r.t. weak-\* topology,
  and for this purpose give the definition `WeakDual.polar 𝕜 s` for the "same" subset viewed as a
  subset of `WeakDual 𝕜 E` (a type synonym of the dual but with a different topology instance).
* **Banach-Alaoglu Proof:** The weak dual of `E` is embedded in the space of functions `E → 𝕜`
  with the topology of pointwise convergence.

## TODO
* Add that in finite dimensions, the weak-\* topology and the dual norm topology coincide.
* Add that in infinite dimensions, the weak-\* topology is strictly coarser than the dual norm
  topology.
* Add metrizability of the dual unit ball (more generally weak-star compact subsets) of
  `WeakDual 𝕜 E` under the assumption of separability of `E`.
* Add the sequential Banach-Alaoglu theorem: the dual unit ball of a separable normed space `E`
  is sequentially compact in the weak-star topology. This would follow from the metrizability above.

## References
* https://en.wikipedia.org/wiki/Weak_topology#Weak-*_topology
* https://en.wikipedia.org/wiki/Banach%E2%80%93Alaoglu_theorem

## Tags

weak-star, weak dual

-/

@[expose] public section

noncomputable section

open Filter Function Bornology Metric Set Topology Filter

variable {𝕜 M E : Type*}
variable [NontriviallyNormedField 𝕜]
variable [AddCommGroup M] [TopologicalSpace M] [Module 𝕜 M]
variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace WeakDual

section Bornology

/--
Instance `instBornology` / 实例 `instBornology`

English:
instance instBornology
  signature: : Bornology (WeakDual 𝕜 E)
  body: inferInstanceAs (Bornology (StrongDual 𝕜 E))

中文:
实例 instBornology
  签名: : Bornology (WeakDual 𝕜 E)
  定义体: inferInstanceAs (Bornology (StrongDual 𝕜 E))

Depends on / 依赖: Bornology, StrongDual
-/
instance instBornology : Bornology (WeakDual 𝕜 E) := inferInstanceAs (Bornology (StrongDual 𝕜 E))

/-- A set in `WeakDual 𝕜 E` is bounded iff its image in `StrongDual 𝕜 E` is bounded. -/
@[simp]
/--
theorem `isBounded_toStrongDual_preimage_iff_isBounded` / 定理 `isBounded_toStrongDual_preimage_iff_isBounded`

English:
theorem isBounded_toStrongDual_preimage_iff_isBounded
  given: {s : Set (StrongDual 𝕜 E)}
  proof: Iff.rfl

中文:
定理 isBounded_toStrongDual_preimage_iff_isBounded
  条件: {s : Set (StrongDual 𝕜 E)}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isBounded_toStrongDual_preimage_iff_isBounded {s : Set (StrongDual 𝕜 E)} :
    IsBounded (WeakDual.toStrongDual ⁻¹' s) ↔ IsBounded s := Iff.rfl

/-- A set in `StrongDual 𝕜 E` is bounded iff its image in `WeakDual 𝕜 E` is bounded. -/
@[simp]
/--
theorem `isBounded_toWeakDual_preimage_iff_isBounded` / 定理 `isBounded_toWeakDual_preimage_iff_isBounded`

English:
theorem isBounded_toWeakDual_preimage_iff_isBounded
  given: {s : Set (WeakDual 𝕜 E)}
  proof: Iff.rfl

中文:
定理 isBounded_toWeakDual_preimage_iff_isBounded
  条件: {s : Set (WeakDual 𝕜 E)}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isBounded_toWeakDual_preimage_iff_isBounded {s : Set (WeakDual 𝕜 E)} :
    IsBounded (StrongDual.toWeakDual ⁻¹' s) ↔ IsBounded s := Iff.rfl

end Bornology

end WeakDual

/-!
### Weak star topology on duals of normed spaces

In this section, we prove properties about the weak-\* topology on duals of normed spaces.
We prove in particular that the canonical mapping `StrongDual 𝕜 E → WeakDual 𝕜 E` is continuous,
i.e., that the weak-\* topology is coarser (not necessarily strictly) than the topology given
by the dual-norm (i.e. the operator-norm).
-/

namespace NormedSpace

namespace Dual

@[fun_prop]
/--
theorem `toWeakDual_continuous` / 定理 `toWeakDual_continuous`

English:
theorem toWeakDual_continuous
  statement: Continuous fun x' : StrongDual 𝕜 E => StrongDual.toWeakDual x'
  proof: WeakBilin.continuous_of_continuous_eval _ fun z => (ContinuousLinearMap.apply 𝕜 𝕜 z).continuous

中文:
定理 toWeakDual_continuous
  结论: Continuous fun x' : StrongDual 𝕜 E => StrongDual.toWeakDual x'
  证明: WeakBilin.continuous_of_continuous_eval _ fun z => (ContinuousLinearMap.apply 𝕜 𝕜 z).continuous

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.apply, WeakBilin, WeakBilin.continuous_of_continuous_eval, continuous, continuous_of_continuous_eval
-/
theorem toWeakDual_continuous : Continuous fun x' : StrongDual 𝕜 E => StrongDual.toWeakDual x' :=
  WeakBilin.continuous_of_continuous_eval _ fun z => (ContinuousLinearMap.apply 𝕜 𝕜 z).continuous

/--
Definition of `continuousLinearMapToWeakDual` / `continuousLinearMapToWeakDual` 的定义

English:
definition continuousLinearMapToWeakDual
  signature: : StrongDual 𝕜 E ->L[𝕜] WeakDual 𝕜 E
  body: { StrongDual.toWeakDual with }

中文:
定义 continuousLinearMapToWeakDual
  签名: : StrongDual 𝕜 E ->L[𝕜] WeakDual 𝕜 E
  定义体: { StrongDual.toWeakDual with }

Depends on / 依赖: StrongDual, StrongDual.toWeakDual, toWeakDual
-/
def continuousLinearMapToWeakDual : StrongDual 𝕜 E ->L[𝕜] WeakDual 𝕜 E :=
  { StrongDual.toWeakDual with }

set_option backward.isDefEq.respectTransparency false in
/--
theorem `dual_norm_topology_le_weak_dual_topology` / 定理 `dual_norm_topology_le_weak_dual_topology`

English:
theorem dual_norm_topology_le_weak_dual_topology
  proof: by
  convert! (@toWeakDual_continuous _ _ _ _ (by assumption)).le_induced
  exact induced_id.symm

中文:
定理 dual_norm_topology_le_weak_dual_topology
  证明: by
  convert! (@toWeakDual_continuous _ _ _ _ (by assumption)).le_induced
  exact induced_id.symm

Depends on / 依赖: convert, induced_id, induced_id.symm, le_induced, toWeakDual_continuous
-/
theorem dual_norm_topology_le_weak_dual_topology :
    (UniformSpace.toTopologicalSpace : TopologicalSpace (StrongDual 𝕜 E)) <=
      (instTopologicalSpaceWeakDual .. : TopologicalSpace (WeakDual 𝕜 E)) := by
  convert! (@toWeakDual_continuous _ _ _ _ (by assumption)).le_induced
  exact induced_id.symm

end Dual

end NormedSpace

namespace WeakDual

open NormedSpace

/-!
### Bornology and pointwise bounds

This section relates the inherited norm bornology (`IsBounded`) to the intrinsic
von Neumann bornology of the weak-\* topology (`IsVonNBounded`).

The following results justify using the norm bornology as the default instance: by the
Uniform Boundedness Principle, it coincides with the von Neumann bornology whenever
$E$ is a Banach space.
-/

variable (𝕜 E) in
/--
Definition of `seminormFamily` / `seminormFamily` 的定义

English:
definition seminormFamily
  signature: : SeminormFamily 𝕜 (WeakDual 𝕜 E) E
  body: (topDualPairing 𝕜 E).toSeminormFamily

@[simp]

中文:
定义 seminormFamily
  签名: : SeminormFamily 𝕜 (WeakDual 𝕜 E) E
  定义体: (topDualPairing 𝕜 E).toSeminormFamily

@[simp]

Depends on / 依赖: toSeminormFamily, topDualPairing
-/
def seminormFamily : SeminormFamily 𝕜 (WeakDual 𝕜 E) E := (topDualPairing 𝕜 E).toSeminormFamily

@[simp]
/--
lemma `seminormFamily_apply` / 引理 `seminormFamily_apply`

English:
lemma seminormFamily_apply
  given: (x : E) (f : WeakDual 𝕜 E)
  statement: seminormFamily 𝕜 E x f = ‖f x‖
  proof: rfl

中文:
引理 seminormFamily_apply
  条件: (x : E) (f : WeakDual 𝕜 E)
  结论: seminormFamily 𝕜 E x f = ‖f x‖
  证明: rfl
-/
lemma seminormFamily_apply (x : E) (f : WeakDual 𝕜 E) : seminormFamily 𝕜 E x f = ‖f x‖ := rfl

variable (𝕜 E) in
/--
lemma `withSeminorms` / 引理 `withSeminorms`

English:
lemma withSeminorms
  statement: WithSeminorms (seminormFamily 𝕜 E)
  proof: (topDualPairing 𝕜 E).weakBilin_withSeminorms

中文:
引理 withSeminorms
  结论: WithSeminorms (seminormFamily 𝕜 E)
  证明: (topDualPairing 𝕜 E).weakBilin_withSeminorms

Depends on / 依赖: topDualPairing, weakBilin_withSeminorms
-/
lemma withSeminorms : WithSeminorms (seminormFamily 𝕜 E) :=
  (topDualPairing 𝕜 E).weakBilin_withSeminorms

/--
theorem `isBounded_iff_isVonNBounded` / 定理 `isBounded_iff_isVonNBounded`

English:
theorem isBounded_iff_isVonNBounded
  given: [CompleteSpace E] {s : Set (WeakDual 𝕜 E)}
  proof: by
  constructor
  · exact fun h => ((NormedSpace.isVonNBounded_iff 𝕜).mpr h).of_topologicalSpace_le
      Dual.dual_norm_topology_le_weak_dual_topology
  · intro h_vN
    have h_ptwise := (withSeminorms 𝕜 E).isVonNBounded_iff_seminorm_bounded.mp h_vN
    obtain ⟨C, hC⟩ := banach_steinhaus (g := fun

中文:
定理 isBounded_iff_isVonNBounded
  条件: [CompleteSpace E] {s : Set (WeakDual 𝕜 E)}
  证明: by
  constructor
  · exact fun h => ((NormedSpace.isVonNBounded_iff 𝕜).mpr h).of_topologicalSpace_le
      Dual.dual_norm_topology_le_weak_dual_topology
  · intro h_vN
    have h_ptwise := (withSeminorms 𝕜 E).isVonNBounded_iff_seminorm_bounded.mp h_vN
    obtain ⟨C, hC⟩ := banach_steinhaus (g := fun

Depends on / 依赖: Dual.dual_norm_topology_le_weak_dual_topology, NormedSpace, NormedSpace.isVonNBounded_iff, WeakDual, WeakDual.toStrongDual, banach_steinhaus, dual_norm_topology_le_weak_dual_topology, h_ptwise, h_vN, i.property, i.val, isBounded_iff_forall_norm_le, isBounded_toWeakDual_preimage_iff_isBounded, isVonNBounded_iff, isVonNBounded_iff_seminorm_bounded, isVonNBounded_iff_seminorm_bounded.mp, le_of_lt, of_topologicalSpace_le, property, toStrongDual
-/
theorem isBounded_iff_isVonNBounded [CompleteSpace E] {s : Set (WeakDual 𝕜 E)} :
    IsBounded s ↔ Bornology.IsVonNBounded 𝕜 s := by
  constructor
  · exact fun h => ((NormedSpace.isVonNBounded_iff 𝕜).mpr h).of_topologicalSpace_le
      Dual.dual_norm_topology_le_weak_dual_topology
  · intro h_vN
    have h_ptwise := (withSeminorms 𝕜 E).isVonNBounded_iff_seminorm_bounded.mp h_vN
    obtain ⟨C, hC⟩ := banach_steinhaus (g := fun i : s => WeakDual.toStrongDual i.val) fun x =>
      let ⟨M, _, hM⟩ := h_ptwise x
      ⟨M, fun i => le_of_lt (hM i.val i.property)⟩
    rw [← isBounded_toWeakDual_preimage_iff_isBounded]; rw [isBounded_iff_forall_norm_le]
    exact ⟨C, fun f hf => hC ⟨StrongDual.toWeakDual f, hf⟩⟩

/-!
### Compactness of bounded closed sets

While the coercion `↑ : WeakDual 𝕜 E → (E → 𝕜)` is not a closed map, it sends *bounded*
closed sets to closed sets.
-/

/--
theorem `isClosed_image_coe_of_bounded_of_closed` / 定理 `isClosed_image_coe_of_bounded_of_closed`

English:
theorem isClosed_image_coe_of_bounded_of_closed
  statement: {s : Set (WeakDual 𝕜 E)}
  proof: ContinuousLinearMap.isClosed_image_coe_of_bounded_of_weak_closed hb (isClosed_induced_iff'.1 hc)

中文:
定理 isClosed_image_coe_of_bounded_of_closed
  结论: {s : Set (WeakDual 𝕜 E)}
  证明: ContinuousLinearMap.isClosed_image_coe_of_bounded_of_weak_closed hb (isClosed_induced_iff'.1 hc)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.isClosed_image_coe_of_bounded_of_weak_closed, isClosed_image_coe_of_bounded_of_weak_closed, isClosed_induced_iff
-/
theorem isClosed_image_coe_of_bounded_of_closed {s : Set (WeakDual 𝕜 E)}
    (hb : IsBounded s) (hc : IsClosed s) :
    IsClosed (((↑) : WeakDual 𝕜 E -> E -> 𝕜) '' s) :=
  ContinuousLinearMap.isClosed_image_coe_of_bounded_of_weak_closed hb (isClosed_induced_iff'.1 hc)

/--
theorem `isCompact_of_bounded_of_closed` / 定理 `isCompact_of_bounded_of_closed`

English:
theorem isCompact_of_bounded_of_closed
  statement: [ProperSpace 𝕜] {s : Set (WeakDual 𝕜 E)}
  proof: DFunLike.coe_injective.isEmbedding_induced.isCompact_iff.mpr
ContinuousLinearMap.isCompact_image_coe_of_bounded_of_closed_image hb
      isClosed_image_coe_of_bounded_of_closed hb hc

中文:
定理 isCompact_of_bounded_of_closed
  结论: [命题erSpace 𝕜] {s : Set (WeakDual 𝕜 E)}
  证明: DFunLike.coe_injective.isEmbedding_induced.isCompact_iff.mpr
ContinuousLinearMap.isCompact_image_coe_of_bounded_of_closed_image hb
      isClosed_image_coe_of_bounded_of_closed hb hc

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.isCompact_image_coe_of_bounded_of_closed_image, DFunLike, DFunLike.coe_injective.isEmbedding_induced.isCompact_iff.mpr, coe_injective, isClosed_image_coe_of_bounded_of_closed, isCompact_iff, isCompact_image_coe_of_bounded_of_closed_image, isEmbedding_induced
-/
theorem isCompact_of_bounded_of_closed [ProperSpace 𝕜] {s : Set (WeakDual 𝕜 E)}
    (hb : IsBounded s) (hc : IsClosed s) : IsCompact s :=
DFunLike.coe_injective.isEmbedding_induced.isCompact_iff.mpr
ContinuousLinearMap.isCompact_image_coe_of_bounded_of_closed_image hb
      isClosed_image_coe_of_bounded_of_closed hb hc

/-!
### Closed balls
-/

/--
theorem `isClosed_closedBall` / 定理 `isClosed_closedBall`

English:
theorem isClosed_closedBall
  given: (x' : StrongDual 𝕜 E) (r : Real)
  proof: isClosed_induced_iff'.2 (ContinuousLinearMap.is_weak_closed_closedBall x' r)

中文:
定理 isClosed_closedBall
  条件: (x' : StrongDual 𝕜 E) (r : 实数)
  证明: isClosed_induced_iff'.2 (ContinuousLinearMap.is_weak_closed_closedBall x' r)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.is_weak_closed_closedBall, isClosed_induced_iff, is_weak_closed_closedBall
-/
theorem isClosed_closedBall (x' : StrongDual 𝕜 E) (r : Real) :
    IsClosed (toStrongDual ⁻¹' closedBall x' r) :=
  isClosed_induced_iff'.2 (ContinuousLinearMap.is_weak_closed_closedBall x' r)

/--
theorem `isBounded_closedBall` / 定理 `isBounded_closedBall`

English:
theorem isBounded_closedBall
  given: (x' : StrongDual 𝕜 E) (r : Real)
  proof: isBounded_toStrongDual_preimage_iff_isBounded.mpr Metric.isBounded_closedBall

中文:
定理 isBounded_closedBall
  条件: (x' : StrongDual 𝕜 E) (r : 实数)
  证明: isBounded_toStrongDual_preimage_iff_isBounded.mpr Metric.isBounded_closedBall

Depends on / 依赖: Metric, Metric.isBounded_closedBall, isBounded_closedBall, isBounded_toStrongDual_preimage_iff_isBounded, isBounded_toStrongDual_preimage_iff_isBounded.mpr
-/
theorem isBounded_closedBall (x' : StrongDual 𝕜 E) (r : Real) :
    IsBounded (toStrongDual ⁻¹' closedBall x' r) :=
  isBounded_toStrongDual_preimage_iff_isBounded.mpr Metric.isBounded_closedBall

/--
theorem `isBounded_closure` / 定理 `isBounded_closure`

English:
theorem isBounded_closure
  given: {s : Set (WeakDual 𝕜 E)} (hb : IsBounded s)
  proof: by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : StrongDual 𝕜 E)).mp hb
  exact (isBounded_closedBall 0 R).subset
    (closure_minimal (fun y hy => hR (a := toStrongDual y) hy) (isClosed_closedBall 0 R))

中文:
定理 isBounded_closure
  条件: {s : Set (WeakDual 𝕜 E)} (hb : IsBounded s)
  证明: by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : StrongDual 𝕜 E)).mp hb
  exact (isBounded_closedBall 0 R).subset
    (closure_minimal (fun y hy => hR (a := toStrongDual y) hy) (isClosed_closedBall 0 R))

Depends on / 依赖: Metric, Metric.isBounded_iff_subset_closedBall, StrongDual, closure_minimal, isBounded_closedBall, isBounded_iff_subset_closedBall, isClosed_closedBall, subset, toStrongDual
-/
theorem isBounded_closure {s : Set (WeakDual 𝕜 E)} (hb : IsBounded s) :
    IsBounded (closure s) := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : StrongDual 𝕜 E)).mp hb
  exact (isBounded_closedBall 0 R).subset
    (closure_minimal (fun y hy => hR (a := toStrongDual y) hy) (isClosed_closedBall 0 R))

/--
theorem `isCompact_closedBall` / 定理 `isCompact_closedBall`

English:
theorem isCompact_closedBall
  given: [ProperSpace 𝕜] (x' : StrongDual 𝕜 E) (r : Real)
  proof: isCompact_of_bounded_of_closed (isBounded_closedBall x' r) (isClosed_closedBall x' r)

中文:
定理 isCompact_closedBall
  条件: [命题erSpace 𝕜] (x' : StrongDual 𝕜 E) (r : 实数)
  证明: isCompact_of_bounded_of_closed (isBounded_closedBall x' r) (isClosed_closedBall x' r)

Depends on / 依赖: isBounded_closedBall, isClosed_closedBall, isCompact_of_bounded_of_closed
-/
theorem isCompact_closedBall [ProperSpace 𝕜] (x' : StrongDual 𝕜 E) (r : Real) :
    IsCompact (toStrongDual ⁻¹' closedBall x' r) :=
  isCompact_of_bounded_of_closed (isBounded_closedBall x' r) (isClosed_closedBall x' r)

/-!
### Polar sets in the weak dual space
-/

section PolarSets

variable (𝕜)

/--
Definition of `polar` / `polar` 的定义

English:
definition polar
  signature: (s : Set M)
  body: toStrongDual ⁻¹' (StrongDual.polar 𝕜) s

中文:
定义 polar
  签名: (s : Set M)
  定义体: toStrongDual ⁻¹' (StrongDual.polar 𝕜) s

Depends on / 依赖: StrongDual, StrongDual.polar, toStrongDual
-/
def polar (s : Set M) : Set (WeakDual 𝕜 M) := toStrongDual ⁻¹' (StrongDual.polar 𝕜) s

/--
theorem `polar_def` / 定理 `polar_def`

English:
theorem polar_def
  given: (s : Set M)
  statement: polar 𝕜 s = { f : WeakDual 𝕜 M | forall x in s, ‖f x‖ <= 1 }
  proof: rfl

中文:
定理 polar_def
  条件: (s : Set M)
  结论: polar 𝕜 s = { f : WeakDual 𝕜 M | 对任意 x in s, ‖f x‖ <= 1 }
  证明: rfl
-/
theorem polar_def (s : Set M) : polar 𝕜 s = { f : WeakDual 𝕜 M | forall x in s, ‖f x‖ <= 1 } := rfl

/--
theorem `isClosed_polar` / 定理 `isClosed_polar`

English:
theorem isClosed_polar
  given: (s : Set M)
  statement: IsClosed (polar 𝕜 s)
  proof: by
  simp only [polar_def, ofPred_forall]
  exact isClosed_biInter fun x hx => isClosed_Iic.preimage (WeakBilin.eval_continuous _ _).norm

中文:
定理 isClosed_polar
  条件: (s : Set M)
  结论: IsClosed (polar 𝕜 s)
  证明: by
  simp only [polar_def, ofPred_forall]
  exact isClosed_biInter fun x hx => isClosed_Iic.preimage (WeakBilin.eval_continuous _ _).norm

Depends on / 依赖: WeakBilin, WeakBilin.eval_continuous, eval_continuous, isClosed_Iic, isClosed_Iic.preimage, isClosed_biInter, ofPred_forall, polar_def, preimage
-/
theorem isClosed_polar (s : Set M) : IsClosed (polar 𝕜 s) := by
  simp only [polar_def, ofPred_forall]
  exact isClosed_biInter fun x hx => isClosed_Iic.preimage (WeakBilin.eval_continuous _ _).norm

/--
theorem `isBounded_polar` / 定理 `isBounded_polar`

English:
theorem isBounded_polar
  given: {s : Set E} (s_nhds : s in 𝓝 (0 : E))
  statement: IsBounded (polar 𝕜 s)
  proof: isBounded_toStrongDual_preimage_iff_isBounded.mpr
  (NormedSpace.isBounded_polar_of_mem_nhds_zero 𝕜 s_nhds)

中文:
定理 isBounded_polar
  条件: {s : Set E} (s_nhds : s in 𝓝 (0 : E))
  结论: IsBounded (polar 𝕜 s)
  证明: isBounded_toStrongDual_preimage_iff_isBounded.mpr
  (NormedSpace.isBounded_polar_of_mem_nhds_zero 𝕜 s_nhds)

Depends on / 依赖: NormedSpace, NormedSpace.isBounded_polar_of_mem_nhds_zero, isBounded_polar_of_mem_nhds_zero, isBounded_toStrongDual_preimage_iff_isBounded, isBounded_toStrongDual_preimage_iff_isBounded.mpr, s_nhds
-/
theorem isBounded_polar {s : Set E} (s_nhds : s in 𝓝 (0 : E)) : IsBounded (polar 𝕜 s) :=
  isBounded_toStrongDual_preimage_iff_isBounded.mpr
  (NormedSpace.isBounded_polar_of_mem_nhds_zero 𝕜 s_nhds)

/--
theorem `isClosed_image_polar_of_mem_nhds` / 定理 `isClosed_image_polar_of_mem_nhds`

English:
theorem isClosed_image_polar_of_mem_nhds
  given: {s : Set E} (s_nhds : s in 𝓝 (0 : E))
  proof: isClosed_image_coe_of_bounded_of_closed (isBounded_polar 𝕜 s_nhds) (isClosed_polar _ _)

中文:
定理 isClosed_image_polar_of_mem_nhds
  条件: {s : Set E} (s_nhds : s in 𝓝 (0 : E))
  证明: isClosed_image_coe_of_bounded_of_closed (isBounded_polar 𝕜 s_nhds) (isClosed_polar _ _)

Depends on / 依赖: isBounded_polar, isClosed_image_coe_of_bounded_of_closed, isClosed_polar, s_nhds
-/
theorem isClosed_image_polar_of_mem_nhds {s : Set E} (s_nhds : s in 𝓝 (0 : E)) :
    IsClosed (((↑) : WeakDual 𝕜 E -> E -> 𝕜) '' polar 𝕜 s) :=
  isClosed_image_coe_of_bounded_of_closed (isBounded_polar 𝕜 s_nhds) (isClosed_polar _ _)

/--
theorem `_root_.NormedSpace.Dual.isClosed_image_polar_of_mem_nhds` / 定理 `_root_.NormedSpace.Dual.isClosed_image_polar_of_mem_nhds`

English:
theorem _root_.NormedSpace.Dual.isClosed_image_polar_of_mem_nhds
  statement: {s : Set E}
  proof: WeakDual.isClosed_image_polar_of_mem_nhds 𝕜 s_nhds

中文:
定理 _root_.NormedSpace.Dual.isClosed_image_polar_of_mem_nhds
  结论: {s : Set E}
  证明: WeakDual.isClosed_image_polar_of_mem_nhds 𝕜 s_nhds

Depends on / 依赖: WeakDual, WeakDual.isClosed_image_polar_of_mem_nhds, isClosed_image_polar_of_mem_nhds, s_nhds
-/
theorem _root_.NormedSpace.Dual.isClosed_image_polar_of_mem_nhds {s : Set E}
    (s_nhds : s in 𝓝 (0 : E)) :
    IsClosed (((↑) : StrongDual 𝕜 E -> E -> 𝕜) '' StrongDual.polar 𝕜 s) :=
  WeakDual.isClosed_image_polar_of_mem_nhds 𝕜 s_nhds

/--
theorem `isCompact_polar` / 定理 `isCompact_polar`

English:
theorem isCompact_polar
  given: [ProperSpace 𝕜] {s : Set E} (s_nhds : s in 𝓝 (0 : E))
  proof: isCompact_of_bounded_of_closed (isBounded_polar 𝕜 s_nhds) (isClosed_polar _ _)

中文:
定理 isCompact_polar
  条件: [命题erSpace 𝕜] {s : Set E} (s_nhds : s in 𝓝 (0 : E))
  证明: isCompact_of_bounded_of_closed (isBounded_polar 𝕜 s_nhds) (isClosed_polar _ _)

Depends on / 依赖: isBounded_polar, isClosed_polar, isCompact_of_bounded_of_closed, s_nhds
-/
theorem isCompact_polar [ProperSpace 𝕜] {s : Set E} (s_nhds : s in 𝓝 (0 : E)) :
    IsCompact (polar 𝕜 s) :=
  isCompact_of_bounded_of_closed (isBounded_polar 𝕜 s_nhds) (isClosed_polar _ _)

end PolarSets

/-!
### Sequential compactness
-/

open TopologicalSpace

variable (𝕜 E) [TopologicalSpace.SeparableSpace E] (K : Set (WeakDual 𝕜 E))

/--
lemma `exists_countable_separating` / 引理 `exists_countable_separating`

English:
lemma exists_countable_separating
  statement: exists (gs : Nat -> (WeakDual 𝕜 E) -> 𝕜),
  proof: by
  use (fun n φ => φ (denseSeq E n))
  constructor
  · exact fun _ => eval_continuous _
  · intro w y w_ne_y
    contrapose! w_ne_y
exact DFunLike.ext'_iff.mpr (map_continuous w).ext_on
      (denseRange_denseSeq E) (map_continuous y) (Set.eqOn_range.mpr (funext w_ne_y))

中文:
引理 exists_countable_separating
  结论: 存在 (gs : 自然数 -> (WeakDual 𝕜 E) -> 𝕜),
  证明: by
  use (fun n φ => φ (denseSeq E n))
  constructor
  · exact fun _ => eval_continuous _
  · intro w y w_ne_y
    contrapose! w_ne_y
exact DFunLike.ext'_iff.mpr (map_continuous w).ext_on
      (denseRange_denseSeq E) (map_continuous y) (Set.eqOn_range.mpr (funext w_ne_y))

Depends on / 依赖: DFunLike, DFunLike.ext, Set.eqOn_range.mpr, _iff, _iff.mpr, contrapose, denseRange_denseSeq, denseSeq, eqOn_range, eval_continuous, ext_on, map_continuous, w_ne_y
-/
lemma exists_countable_separating : exists (gs : Nat -> (WeakDual 𝕜 E) -> 𝕜),
    (forall n, Continuous (gs n)) ∧ (forall ⦃x y⦄, x != y -> exists n, gs n x != gs n y) := by
  use (fun n φ => φ (denseSeq E n))
  constructor
  · exact fun _ => eval_continuous _
  · intro w y w_ne_y
    contrapose! w_ne_y
exact DFunLike.ext'_iff.mpr (map_continuous w).ext_on
      (denseRange_denseSeq E) (map_continuous y) (Set.eqOn_range.mpr (funext w_ne_y))

/--
lemma `metrizable_of_isCompact` / 引理 `metrizable_of_isCompact`

English:
lemma metrizable_of_isCompact
  given: (K_cpt : IsCompact K)
  statement: TopologicalSpace.MetrizableSpace K
  proof: by
  have : CompactSpace K := isCompact_iff_compactSpace.mp K_cpt
  obtain ⟨gs, gs_cont, gs_sep⟩ := exists_countable_separating 𝕜 E
  exact Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating
    (fun n k => gs n k) (fun n => (gs_cont n).comp continuous_subtype_val)
fun x y hx

中文:
引理 metrizable_of_isCompact
  条件: (K_cpt : IsCompact K)
  结论: TopologicalSpace.MetrizableSpace K
  证明: by
  have : CompactSpace K := isCompact_iff_compactSpace.mp K_cpt
  obtain ⟨gs, gs_cont, gs_sep⟩ := exists_countable_separating 𝕜 E
  exact Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating
    (fun n k => gs n k) (fun n => (gs_cont n).comp continuous_subtype_val)
fun x y hx

Depends on / 依赖: CompactSpace, K_cpt, Metric, Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating, MetrizableSpace, PiNatEmbed, Subtype, Subtype.val_injective.ne, TopologicalSpace, continuous_subtype_val, exists_countable_separating, gs_cont, gs_sep, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mp, of_countable_separating, val_injective
-/
lemma metrizable_of_isCompact (K_cpt : IsCompact K) : TopologicalSpace.MetrizableSpace K := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp K_cpt
  obtain ⟨gs, gs_cont, gs_sep⟩ := exists_countable_separating 𝕜 E
  exact Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating
    (fun n k => gs n k) (fun n => (gs_cont n).comp continuous_subtype_val)
fun x y hxy => gs_sep Subtype.val_injective.ne hxy

variable [ProperSpace 𝕜] (K_cpt : IsCompact K)

/--
theorem `isSeqCompact_of_isBounded_of_isClosed` / 定理 `isSeqCompact_of_isBounded_of_isClosed`

English:
theorem isSeqCompact_of_isBounded_of_isClosed
  statement: {s : Set (WeakDual 𝕜 E)}
  proof: by
  have b_isCompact' : CompactSpace s :=
isCompact_iff_compactSpace.mp isCompact_of_bounded_of_closed hb hc
  have b_isMetrizable : TopologicalSpace.MetrizableSpace s :=
metrizable_of_isCompact 𝕜 E s isCompact_of_bounded_of_closed hb hc
  have seq_cont_phi : SeqContinuous (fun φ : s => (φ : WeakDu

中文:
定理 isSeqCompact_of_isBounded_of_isClosed
  结论: {s : Set (WeakDual 𝕜 E)}
  证明: by
  have b_isCompact' : CompactSpace s :=
isCompact_iff_compactSpace.mp isCompact_of_bounded_of_closed hb hc
  have b_isMetrizable : TopologicalSpace.MetrizableSpace s :=
metrizable_of_isCompact 𝕜 E s isCompact_of_bounded_of_closed hb hc
  have seq_cont_phi : SeqContinuous (fun φ : s => (φ : WeakDu

Depends on / 依赖: CompactSpace, IsSeqCompact, IsSeqCompact.range, MetrizableSpace, SeqContinuous, TopologicalSpace, TopologicalSpace.MetrizableSpace, WeakDual, b_isCompact, b_isMetrizable, continuous_iff_seqContinuous, continuous_iff_seqContinuous.mp, continuous_subtype_val, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mp, isCompact_of_bounded_of_closed, metrizable_of_isCompact, seq_cont_phi
-/
theorem isSeqCompact_of_isBounded_of_isClosed {s : Set (WeakDual 𝕜 E)}
    (hb : IsBounded s) (hc : IsClosed s) :
    IsSeqCompact s := by
  have b_isCompact' : CompactSpace s :=
isCompact_iff_compactSpace.mp isCompact_of_bounded_of_closed hb hc
  have b_isMetrizable : TopologicalSpace.MetrizableSpace s :=
metrizable_of_isCompact 𝕜 E s isCompact_of_bounded_of_closed hb hc
  have seq_cont_phi : SeqContinuous (fun φ : s => (φ : WeakDual 𝕜 E)) :=
    continuous_iff_seqContinuous.mp continuous_subtype_val
  simpa using IsSeqCompact.range seq_cont_phi

/--
theorem `isSeqCompact_polar` / 定理 `isSeqCompact_polar`

English:
theorem isSeqCompact_polar
  given: {s : Set E} (s_nhd : s in 𝓝 (0 : E))
  proof: isSeqCompact_of_isBounded_of_isClosed 𝕜 _ (isBounded_polar 𝕜 s_nhd) (isClosed_polar _ _)

中文:
定理 isSeqCompact_polar
  条件: {s : Set E} (s_nhd : s in 𝓝 (0 : E))
  证明: isSeqCompact_of_isBounded_of_isClosed 𝕜 _ (isBounded_polar 𝕜 s_nhd) (isClosed_polar _ _)

Depends on / 依赖: isBounded_polar, isClosed_polar, isSeqCompact_of_isBounded_of_isClosed, s_nhd
-/
theorem isSeqCompact_polar {s : Set E} (s_nhd : s in 𝓝 (0 : E)) :
    IsSeqCompact (polar 𝕜 s) :=
  isSeqCompact_of_isBounded_of_isClosed 𝕜 _ (isBounded_polar 𝕜 s_nhd) (isClosed_polar _ _)

/--
theorem `isSeqCompact_closedBall` / 定理 `isSeqCompact_closedBall`

English:
theorem isSeqCompact_closedBall
  given: (x' : StrongDual 𝕜 E) (r : Real)
  proof: isSeqCompact_of_isBounded_of_isClosed 𝕜 _ (isBounded_closedBall x' r) (isClosed_closedBall x' r)

中文:
定理 isSeqCompact_closedBall
  条件: (x' : StrongDual 𝕜 E) (r : 实数)
  证明: isSeqCompact_of_isBounded_of_isClosed 𝕜 _ (isBounded_closedBall x' r) (isClosed_closedBall x' r)

Depends on / 依赖: isBounded_closedBall, isClosed_closedBall, isSeqCompact_of_isBounded_of_isClosed
-/
theorem isSeqCompact_closedBall (x' : StrongDual 𝕜 E) (r : Real) :
    IsSeqCompact (toStrongDual ⁻¹' Metric.closedBall x' r) :=
  isSeqCompact_of_isBounded_of_isClosed 𝕜 _ (isBounded_closedBall x' r) (isClosed_closedBall x' r)

end WeakDual

section RCLike

open RCLike
open scoped NNReal Topology

namespace WeakDual

-- we shadow the variables for this section because they don't fit with the rest of the file.
variable {α 𝕜 E F : Type*} [TopologicalSpace α] [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/--
theorem `_root_.WeakBilin.continuous_of_continuous_eval_re` / 定理 `_root_.WeakBilin.continuous_of_continuous_eval_re`

English:
theorem _root_.WeakBilin.continuous_of_continuous_eval_re
  statement: (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜)
  proof: by
  refine WeakBilin.continuous_of_continuous_eval _ fun x => ?_
  suffices Continuous fun a => (re (B (g a) x) : 𝕜) - re (B (g a) ((I : 𝕜) • x)) * I by simpa
  fun_prop

中文:
定理 _root_.WeakBilin.continuous_of_continuous_eval_re
  结论: (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜)
  证明: by
  refine WeakBilin.continuous_of_continuous_eval _ fun x => ?_
  suffices Continuous fun a => (re (B (g a) x) : 𝕜) - re (B (g a) ((I : 𝕜) • x)) * I by simpa
  fun_prop

Depends on / 依赖: Continuous, WeakBilin, WeakBilin.continuous_of_continuous_eval, continuous_of_continuous_eval, fun_prop
-/
theorem _root_.WeakBilin.continuous_of_continuous_eval_re (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜)
    {g : α -> WeakBilin B} (h : forall y, Continuous fun a => re (B (g a) y)) :
    Continuous g := by
  refine WeakBilin.continuous_of_continuous_eval _ fun x => ?_
  suffices Continuous fun a => (re (B (g a) x) : 𝕜) - re (B (g a) ((I : 𝕜) • x)) * I by simpa
  fun_prop

variable [TopologicalSpace F]

/--
theorem `continuous_of_continuous_eval_re` / 定理 `continuous_of_continuous_eval_re`

English:
theorem continuous_of_continuous_eval_re
  statement: {g : α -> WeakDual 𝕜 F}
  proof: WeakBilin.continuous_of_continuous_eval_re _ h

中文:
定理 continuous_of_continuous_eval_re
  结论: {g : α -> WeakDual 𝕜 F}
  证明: WeakBilin.continuous_of_continuous_eval_re _ h

Depends on / 依赖: WeakBilin, WeakBilin.continuous_of_continuous_eval_re, continuous_of_continuous_eval_re
-/
theorem continuous_of_continuous_eval_re {g : α -> WeakDual 𝕜 F}
    (h : forall x, Continuous fun a => re (g a x)) :
    Continuous g :=
  WeakBilin.continuous_of_continuous_eval_re _ h

variable [ContinuousConstSMul 𝕜 F] [Module Real F] [IsScalarTower Real 𝕜 F]

open StrongDual

/-- The extension `StrongDual.extendRCLike` as a continuous linear equivalence between
the weak duals. -/
@[simps! -isSimp apply symm_apply]
/--
Definition of `extendRCLikeL` / `extendRCLikeL` 的定义

English:
definition extendRCLikeL
  signature: : WeakDual Real F ≃L[Real] WeakDual 𝕜 F where
  body: toStrongDual ≪≫ₗ extendRCLikeₗ ≪≫ₗ toWeakDual.restrictScalars Real
  continuous_toFun := continuous_of_continuous_eval_re fun x => by
    simpa [extendRCLikeₗ_apply] using eval_continuous x
  continuous_invFun :=
    continuous_of_continuous_eval fun x => RCLike.continuous_re.comp (eval_continuous x

中文:
定义 extendRCLikeL
  签名: : WeakDual 实数 F ≃L[实数] WeakDual 𝕜 F where
  定义体: toStrongDual ≪≫ₗ extendRCLikeₗ ≪≫ₗ toWeakDual.restrictScalars Real
  continuous_toFun := continuous_of_continuous_eval_re fun x => by
    simpa [extendRCLikeₗ_apply] using eval_continuous x
  continuous_invFun :=
    continuous_of_continuous_eval fun x => RCLike.continuous_re.comp (eval_continuous x

Depends on / 依赖: restrictScalars, toStrongDual, toWeakDual, toWeakDual.restrictScalars
-/
noncomputable def extendRCLikeL : WeakDual Real F ≃L[Real] WeakDual 𝕜 F where
  toLinearEquiv := toStrongDual ≪≫ₗ extendRCLikeₗ ≪≫ₗ toWeakDual.restrictScalars Real
  continuous_toFun := continuous_of_continuous_eval_re fun x => by
    simpa [extendRCLikeₗ_apply] using eval_continuous x
  continuous_invFun :=
    continuous_of_continuous_eval fun x => RCLike.continuous_re.comp (eval_continuous x)

@[simp]
/--
lemma `toLinearEquiv_extendRCLikeL` / 引理 `toLinearEquiv_extendRCLikeL`

English:
lemma toLinearEquiv_extendRCLikeL
  proof: by
  rfl

中文:
引理 toLinearEquiv_extendRCLikeL
  证明: by
  rfl

Depends on / 依赖: toLinearEquiv
-/
lemma toLinearEquiv_extendRCLikeL :
    (extendRCLikeL (𝕜 := 𝕜) (F := F)).toLinearEquiv =
      toStrongDual ≪≫ₗ extendRCLikeₗ ≪≫ₗ toWeakDual.restrictScalars Real := by
  rfl

/--
lemma `extendRCLikeL_apply_apply` / 引理 `extendRCLikeL_apply_apply`

English:
lemma extendRCLikeL_apply_apply
  given: (f : WeakDual Real F) (x : F)
  proof: by
  rfl

中文:
引理 extendRCLikeL_apply_apply
  条件: (f : WeakDual 实数 F) (x : F)
  证明: by
  rfl
-/
lemma extendRCLikeL_apply_apply (f : WeakDual Real F) (x : F) :
    extendRCLikeL (𝕜 := 𝕜) f x = f x - (I : 𝕜) • f ((I : 𝕜) • x) := by
  rfl

/--
lemma `extendRCLikeL_symm_apply_apply` / 引理 `extendRCLikeL_symm_apply_apply`

English:
lemma extendRCLikeL_symm_apply_apply
  given: (f : WeakDual 𝕜 F) (x : F)
  proof: rfl

@[simp]

中文:
引理 extendRCLikeL_symm_apply_apply
  条件: (f : WeakDual 𝕜 F) (x : F)
  证明: rfl

@[simp]
-/
lemma extendRCLikeL_symm_apply_apply (f : WeakDual 𝕜 F) (x : F) :
    extendRCLikeL.symm f x = re (f x) :=
  rfl

@[simp]
/--
lemma `re_extendRCLikeL_apply_apply` / 引理 `re_extendRCLikeL_apply_apply`

English:
lemma re_extendRCLikeL_apply_apply
  given: (f : WeakDual Real F) (x : F)
  proof: by
  simp [extendRCLikeL_apply_apply]

@[simp]

中文:
引理 re_extendRCLikeL_apply_apply
  条件: (f : WeakDual 实数 F) (x : F)
  证明: by
  simp [extendRCLikeL_apply_apply]

@[simp]

Depends on / 依赖: extendRCLikeL_apply_apply
-/
lemma re_extendRCLikeL_apply_apply (f : WeakDual Real F) (x : F) :
    re (extendRCLikeL (𝕜 := 𝕜) f x) = f x := by
  simp [extendRCLikeL_apply_apply]

@[simp]
/--
lemma `im_extendRCLikeL_apply_apply` / 引理 `im_extendRCLikeL_apply_apply`

English:
lemma im_extendRCLikeL_apply_apply
  given: (f : WeakDual Real F) (x : F)
  proof: by
  simp [extendRCLikeL_apply, extendRCLikeₗ_apply]

@[simp high]

中文:
引理 im_extendRCLikeL_apply_apply
  条件: (f : WeakDual 实数 F) (x : F)
  证明: by
  simp [extendRCLikeL_apply, extendRCLikeₗ_apply]

@[simp high]

Depends on / 依赖: extendRCLikeL_apply
-/
lemma im_extendRCLikeL_apply_apply (f : WeakDual Real F) (x : F) :
    im (extendRCLikeL (𝕜 := 𝕜) f x) = - f ((I : 𝕜) • x) := by
  simp [extendRCLikeL_apply, extendRCLikeₗ_apply]

@[simp high]
/--
lemma `toStrongDual_extendRCLikeL_apply` / 引理 `toStrongDual_extendRCLikeL_apply`

English:
lemma toStrongDual_extendRCLikeL_apply
  given: (f : WeakDual Real F)
  proof: rfl

@[simp high]

中文:
引理 toStrongDual_extendRCLikeL_apply
  条件: (f : WeakDual 实数 F)
  证明: rfl

@[simp high]

Depends on / 依赖: toStrongDual
-/
lemma toStrongDual_extendRCLikeL_apply (f : WeakDual Real F) :
    (extendRCLikeL (𝕜 := 𝕜) f).toStrongDual = extendRCLikeₗ f :=
  rfl

@[simp high]
/--
lemma `_root_.StrongDual.toWeakDual_extendRCLikeₗ_apply` / 引理 `_root_.StrongDual.toWeakDual_extendRCLikeₗ_apply`

English:
lemma _root_.StrongDual.toWeakDual_extendRCLikeₗ_apply
  given: (f : StrongDual Real F)
  proof: rfl

中文:
引理 _root_.StrongDual.toWeakDual_extendRCLikeₗ_apply
  条件: (f : StrongDual 实数 F)
  证明: rfl

Depends on / 依赖: f.toWeakDual, toWeakDual
-/
lemma _root_.StrongDual.toWeakDual_extendRCLikeₗ_apply (f : StrongDual Real F) :
    (extendRCLikeₗ f).toWeakDual = extendRCLikeL (𝕜 := 𝕜) f.toWeakDual :=
  rfl

end WeakDual

end RCLike
