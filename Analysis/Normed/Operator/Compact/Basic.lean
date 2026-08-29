/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Compact operators

In this file we define compact linear operators between two topological vector spaces (TVS).

## Main definitions

* `IsCompactOperator` : predicate for compact operators

## Main statements

* `isCompactOperator_iff_isCompact_closure_image_ball` : the usual characterization of
  compact operators from a normed space to a T2 TVS.
* `IsCompactOperator.comp_clm` : precomposing a compact operator by a continuous linear map gives
  a compact operator
* `IsCompactOperator.clm_comp` : postcomposing a compact operator by a continuous linear map
  gives a compact operator
* `IsCompactOperator.continuous` : compact operators are automatically continuous
* `isClosed_setOfPred_isCompactOperator` : the set of compact operators is closed for the operator
  norm

Note that results linking compact operators with `FiniteDimensional` are in a separate file
in order to avoid a heavy import. There, we prove :

* `isCompactOperator_id_iff_finiteDimensional` : the identity of `E` is compact if and only if
  `E` has finite dimension.

## Implementation details

We define `IsCompactOperator` as a predicate, because the space of compact operators inherits all
of its structure from the space of continuous linear maps (e.g we want to have the usual operator
norm on compact operators).

The two natural options then would be to make it a predicate over linear maps or continuous linear
maps. Instead we define it as a predicate over bare functions, although it really only makes sense
for linear functions, because Lean is really good at finding coercions to bare functions (whereas
coercing from continuous linear maps to linear maps often needs type ascriptions).

## References

* [N. Bourbaki, *Théories Spectrales*, Chapitre 3][bourbaki2023]

## Tags

Compact operator
-/

@[expose] public section


open Function Set Filter Bornology Metric Pointwise Topology

/-- A compact operator between two topological vector spaces. This definition is usually
given as "there exists a neighborhood of zero whose image is contained in a compact set",
but we choose a definition which involves fewer existential quantifiers and replaces images
with preimages.

We prove the equivalence in `isCompactOperator_iff_exists_mem_nhds_image_subset_compact`. -/
@[wikidata Q1780743]
/--
Definition of `IsCompactOperator` / `IsCompactOperator` 的定义

English:
definition IsCompactOperator
  signature: {M₁ M₂ : Type*} [Zero M₁] [TopologicalSpace M₁] [TopologicalSpace M₂]
  body: exists K, IsCompact K ∧ f ⁻¹' K in (𝓝 0 : Filter M₁)

中文:
定义 IsCompactOperator
  签名: {M₁ M₂ : 类型} [Zero M₁] [TopologicalSpace M₁] [TopologicalSpace M₂]
  定义体: exists K, IsCompact K ∧ f ⁻¹' K in (𝓝 0 : Filter M₁)

Depends on / 依赖: Filter, IsCompact
-/
def IsCompactOperator {M₁ M₂ : Type*} [Zero M₁] [TopologicalSpace M₁] [TopologicalSpace M₂]
    (f : M₁ -> M₂) : Prop :=
  exists K, IsCompact K ∧ f ⁻¹' K in (𝓝 0 : Filter M₁)

/--
theorem `isCompactOperator_zero` / 定理 `isCompactOperator_zero`

English:
theorem isCompactOperator_zero
  statement: {M₁ M₂ : Type*} [Zero M₁] [TopologicalSpace M₁]
  proof: ⟨{0}, isCompact_singleton, mem_of_superset univ_mem fun _ _ => rfl⟩

中文:
定理 isCompactOperator_zero
  结论: {M₁ M₂ : 类型} [Zero M₁] [TopologicalSpace M₁]
  证明: ⟨{0}, isCompact_singleton, mem_of_superset univ_mem fun _ _ => rfl⟩

Depends on / 依赖: isCompact_singleton, mem_of_superset, univ_mem
-/
theorem isCompactOperator_zero {M₁ M₂ : Type*} [Zero M₁] [TopologicalSpace M₁]
    [TopologicalSpace M₂] [Zero M₂] : IsCompactOperator (0 : M₁ -> M₂) :=
  ⟨{0}, isCompact_singleton, mem_of_superset univ_mem fun _ _ => rfl⟩

/--
theorem `isCompactOperator_id_iff_locallyCompactSpace` / 定理 `isCompactOperator_id_iff_locallyCompactSpace`

English:
theorem isCompactOperator_id_iff_locallyCompactSpace
  statement: {E : Type*}
  proof: ⟨fun ⟨_, hK, hK0⟩ => hK.locallyCompactSpace_of_mem_nhds_of_addGroup hK0,
    fun _ => exists_compact_mem_nhds 0⟩

alias ⟨LocallyCompactSpace.of_isCompactOperator_id, _⟩ :=
  isCompactOperator_id_iff_locallyCompactSpace

@[deprecated (since := "2026-03-04")] alias IsCompactOperator.locallyCompactSpac

中文:
定理 isCompactOperator_id_iff_locallyCompactSpace
  结论: {E : 类型}
  证明: ⟨fun ⟨_, hK, hK0⟩ => hK.locallyCompactSpace_of_mem_nhds_of_addGroup hK0,
    fun _ => exists_compact_mem_nhds 0⟩

alias ⟨LocallyCompactSpace.of_isCompactOperator_id, _⟩ :=
  isCompactOperator_id_iff_locallyCompactSpace

@[deprecated (since := "2026-03-04")] alias IsCompactOperator.locallyCompactSpac

Depends on / 依赖: exists_compact_mem_nhds, hK.locallyCompactSpace_of_mem_nhds_of_addGroup, locallyCompactSpace_of_mem_nhds_of_addGroup
-/
theorem isCompactOperator_id_iff_locallyCompactSpace {E : Type*}
    [AddGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] :
    IsCompactOperator (id : E -> E) ↔ LocallyCompactSpace E :=
  ⟨fun ⟨_, hK, hK0⟩ => hK.locallyCompactSpace_of_mem_nhds_of_addGroup hK0,
    fun _ => exists_compact_mem_nhds 0⟩

alias ⟨LocallyCompactSpace.of_isCompactOperator_id, _⟩ :=
  isCompactOperator_id_iff_locallyCompactSpace

@[deprecated (since := "2026-03-04")] alias IsCompactOperator.locallyCompactSpace :=
  LocallyCompactSpace.of_isCompactOperator_id

/--
lemma `isCompactOperator_id` / 引理 `isCompactOperator_id`

English:
lemma isCompactOperator_id
  statement: {E : Type*} [AddGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  proof: isCompactOperator_id_iff_locallyCompactSpace.2 ‹_›

中文:
引理 isCompactOperator_id
  结论: {E : 类型} [AddGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  证明: isCompactOperator_id_iff_locallyCompactSpace.2 ‹_›

Depends on / 依赖: isCompactOperator_id_iff_locallyCompactSpace
-/
lemma isCompactOperator_id {E : Type*} [AddGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [LocallyCompactSpace E] : IsCompactOperator (id : E -> E) :=
  isCompactOperator_id_iff_locallyCompactSpace.2 ‹_›

section Characterizations

section

variable {R₁ : Type*} [Semiring R₁] {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [AddCommMonoid M₁] [TopologicalSpace M₂]

/--
theorem `isCompactOperator_iff_exists_mem_nhds_image_subset_compact` / 定理 `isCompactOperator_iff_exists_mem_nhds_image_subset_compact`

English:
theorem isCompactOperator_iff_exists_mem_nhds_image_subset_compact
  given: (f : M₁ -> M₂)
  proof: ⟨fun ⟨K, hK, hKf⟩ => ⟨f ⁻¹' K, hKf, K, hK, image_preimage_subset _ _⟩, fun ⟨_, hV, K, hK, hVK⟩ =>
    ⟨K, hK, mem_of_superset hV (image_subset_iff.mp hVK)⟩⟩

中文:
定理 isCompactOperator_iff_exists_mem_nhds_image_subset_compact
  条件: (f : M₁ -> M₂)
  证明: ⟨fun ⟨K, hK, hKf⟩ => ⟨f ⁻¹' K, hKf, K, hK, image_preimage_subset _ _⟩, fun ⟨_, hV, K, hK, hVK⟩ =>
    ⟨K, hK, mem_of_superset hV (image_subset_iff.mp hVK)⟩⟩

Depends on / 依赖: image_preimage_subset, image_subset_iff, image_subset_iff.mp, mem_of_superset
-/
theorem isCompactOperator_iff_exists_mem_nhds_image_subset_compact (f : M₁ -> M₂) :
    IsCompactOperator f ↔ exists V in (𝓝 0 : Filter M₁), exists K : Set M₂, IsCompact K ∧ f '' V subseteq K :=
  ⟨fun ⟨K, hK, hKf⟩ => ⟨f ⁻¹' K, hKf, K, hK, image_preimage_subset _ _⟩, fun ⟨_, hV, K, hK, hVK⟩ =>
    ⟨K, hK, mem_of_superset hV (image_subset_iff.mp hVK)⟩⟩

/--
theorem `isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image` / 定理 `isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image`

English:
theorem isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image
  given: [T2Space M₂] (f : M₁ -> M₂)
  proof: by
  rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  exact
    ⟨fun ⟨V, hV, K, hK, hKV⟩ => ⟨V, hV, hK.closure_of_subset hKV⟩,
      fun ⟨V, hV, hVc⟩ => ⟨V, hV, closure (f '' V), hVc, subset_closure⟩⟩

中文:
定理 isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image
  条件: [T2Space M₂] (f : M₁ -> M₂)
  证明: by
  rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  exact
    ⟨fun ⟨V, hV, K, hK, hKV⟩ => ⟨V, hV, hK.closure_of_subset hKV⟩,
      fun ⟨V, hV, hVc⟩ => ⟨V, hV, closure (f '' V), hVc, subset_closure⟩⟩

Depends on / 依赖: closure, closure_of_subset, hK.closure_of_subset, isCompactOperator_iff_exists_mem_nhds_image_subset_compact, subset_closure
-/
theorem isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image [T2Space M₂] (f : M₁ -> M₂) :
    IsCompactOperator f ↔ exists V in (𝓝 0 : Filter M₁), IsCompact (closure <| f '' V) := by
  rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  exact
    ⟨fun ⟨V, hV, K, hK, hKV⟩ => ⟨V, hV, hK.closure_of_subset hKV⟩,
      fun ⟨V, hV, hVc⟩ => ⟨V, hV, closure (f '' V), hVc, subset_closure⟩⟩

end

section Bounded

variable {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁] [SeminormedRing 𝕜₂] {σ₁₂ : 𝕜₁ ->+* 𝕜₂}
  {M₁ M₂ : Type*} [TopologicalSpace M₁] [AddCommMonoid M₁] [TopologicalSpace M₂] [AddCommMonoid M₂]
  [Module 𝕜₁ M₁] [Module 𝕜₂ M₂] [ContinuousConstSMul 𝕜₂ M₂]

/--
theorem `IsCompactOperator.image_subset_compact_of_isVonNBounded` / 定理 `IsCompactOperator.image_subset_compact_of_isVonNBounded`

English:
theorem IsCompactOperator.image_subset_compact_of_isVonNBounded
  statement: {f : M₁ ->ₛₗ[σ₁₂] M₂}
  proof: let ⟨K, hK, hKf⟩ := hf
  let ⟨r, hr, hrS⟩ := (hS hKf).exists_pos
  let ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜₁ r
  let := ne_zero_of_norm_ne_zero (hr.trans hc).ne.symm
⟨σ₁₂ c • K, hK.image continuous_id.const_smul (σ₁₂ c), by
    rw [image_subset_iff]; rw [this.isUnit.preimage_smul_setₛₗ σ₁₂]; exac

中文:
定理 IsCompactOperator.image_subset_compact_of_isVonNBounded
  结论: {f : M₁ ->ₛₗ[σ₁₂] M₂}
  证明: let ⟨K, hK, hKf⟩ := hf
  let ⟨r, hr, hrS⟩ := (hS hKf).exists_pos
  let ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜₁ r
  let := ne_zero_of_norm_ne_zero (hr.trans hc).ne.symm
⟨σ₁₂ c • K, hK.image continuous_id.const_smul (σ₁₂ c), by
    rw [image_subset_iff]; rw [this.isUnit.preimage_smul_setₛₗ σ₁₂]; exac

Depends on / 依赖: NormedField, NormedField.exists_lt_norm, const_smul, continuous_id, continuous_id.const_smul, exists_lt_norm, exists_pos, hK.image, hc.le, hr.trans, image_subset_iff, isUnit, ne.symm, ne_zero_of_norm_ne_zero, this.isUnit.preimage_smul_set
-/
theorem IsCompactOperator.image_subset_compact_of_isVonNBounded {f : M₁ ->ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) {S : Set M₁} (hS : IsVonNBounded 𝕜₁ S) :
    exists K : Set M₂, IsCompact K ∧ f '' S subseteq K :=
  let ⟨K, hK, hKf⟩ := hf
  let ⟨r, hr, hrS⟩ := (hS hKf).exists_pos
  let ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜₁ r
  let := ne_zero_of_norm_ne_zero (hr.trans hc).ne.symm
⟨σ₁₂ c • K, hK.image continuous_id.const_smul (σ₁₂ c), by
    rw [image_subset_iff]; rw [this.isUnit.preimage_smul_setₛₗ σ₁₂]; exact hrS c hc.le⟩

/--
theorem `IsCompactOperator.isCompact_closure_image_of_isVonNBounded` / 定理 `IsCompactOperator.isCompact_closure_image_of_isVonNBounded`

English:
theorem IsCompactOperator.isCompact_closure_image_of_isVonNBounded
  statement: [T2Space M₂] {f : M₁ ->ₛₗ[σ₁₂] M₂}
  proof: let ⟨_, hK, hKf⟩ := hf.image_subset_compact_of_isVonNBounded hS
  hK.closure_of_subset hKf

中文:
定理 IsCompactOperator.isCompact_closure_image_of_isVonNBounded
  结论: [T2Space M₂] {f : M₁ ->ₛₗ[σ₁₂] M₂}
  证明: let ⟨_, hK, hKf⟩ := hf.image_subset_compact_of_isVonNBounded hS
  hK.closure_of_subset hKf

Depends on / 依赖: closure_of_subset, hK.closure_of_subset, hf.image_subset_compact_of_isVonNBounded, image_subset_compact_of_isVonNBounded
-/
theorem IsCompactOperator.isCompact_closure_image_of_isVonNBounded [T2Space M₂] {f : M₁ ->ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) {S : Set M₁} (hS : IsVonNBounded 𝕜₁ S) :
    IsCompact (closure <| f '' S) :=
  let ⟨_, hK, hKf⟩ := hf.image_subset_compact_of_isVonNBounded hS
  hK.closure_of_subset hKf

end Bounded

section NormedSpace

variable {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁] [SeminormedRing 𝕜₂] {σ₁₂ : 𝕜₁ ->+* 𝕜₂}
  {M₁ M₂ : Type*} [SeminormedAddCommGroup M₁] [TopologicalSpace M₂] [AddCommMonoid M₂]
  [NormedSpace 𝕜₁ M₁] [Module 𝕜₂ M₂]

/--
theorem `IsCompactOperator.image_subset_compact_of_bounded` / 定理 `IsCompactOperator.image_subset_compact_of_bounded`

English:
theorem IsCompactOperator.image_subset_compact_of_bounded
  statement: [ContinuousConstSMul 𝕜₂ M₂]
  proof: hf.image_subset_compact_of_isVonNBounded by rwa [NormedSpace.isVonNBounded_iff]

中文:
定理 IsCompactOperator.image_subset_compact_of_bounded
  结论: [ContinuousConstSMul 𝕜₂ M₂]
  证明: hf.image_subset_compact_of_isVonNBounded by rwa [NormedSpace.isVonNBounded_iff]

Depends on / 依赖: NormedSpace, NormedSpace.isVonNBounded_iff, hf.image_subset_compact_of_isVonNBounded, image_subset_compact_of_isVonNBounded, isVonNBounded_iff
-/
theorem IsCompactOperator.image_subset_compact_of_bounded [ContinuousConstSMul 𝕜₂ M₂]
    {f : M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) {S : Set M₁} (hS : Bornology.IsBounded S) :
    exists K : Set M₂, IsCompact K ∧ f '' S subseteq K :=
hf.image_subset_compact_of_isVonNBounded by rwa [NormedSpace.isVonNBounded_iff]

/--
theorem `IsCompactOperator.isCompact_closure_image_of_bounded` / 定理 `IsCompactOperator.isCompact_closure_image_of_bounded`

English:
theorem IsCompactOperator.isCompact_closure_image_of_bounded
  statement: [ContinuousConstSMul 𝕜₂ M₂]
  proof: hf.isCompact_closure_image_of_isVonNBounded by rwa [NormedSpace.isVonNBounded_iff]

中文:
定理 IsCompactOperator.isCompact_closure_image_of_bounded
  结论: [ContinuousConstSMul 𝕜₂ M₂]
  证明: hf.isCompact_closure_image_of_isVonNBounded by rwa [NormedSpace.isVonNBounded_iff]

Depends on / 依赖: NormedSpace, NormedSpace.isVonNBounded_iff, hf.isCompact_closure_image_of_isVonNBounded, isCompact_closure_image_of_isVonNBounded, isVonNBounded_iff
-/
theorem IsCompactOperator.isCompact_closure_image_of_bounded [ContinuousConstSMul 𝕜₂ M₂]
    [T2Space M₂] {f : M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) {S : Set M₁}
    (hS : Bornology.IsBounded S) : IsCompact (closure <| f '' S) :=
hf.isCompact_closure_image_of_isVonNBounded by rwa [NormedSpace.isVonNBounded_iff]

/--
theorem `IsCompactOperator.image_ball_subset_compact` / 定理 `IsCompactOperator.image_ball_subset_compact`

English:
theorem IsCompactOperator.image_ball_subset_compact
  statement: [ContinuousConstSMul 𝕜₂ M₂] {f : M₁ ->ₛₗ[σ₁₂] M₂}
  proof: hf.image_subset_compact_of_isVonNBounded (NormedSpace.isVonNBounded_ball 𝕜₁ M₁ r)

中文:
定理 IsCompactOperator.image_ball_subset_compact
  结论: [ContinuousConstSMul 𝕜₂ M₂] {f : M₁ ->ₛₗ[σ₁₂] M₂}
  证明: hf.image_subset_compact_of_isVonNBounded (NormedSpace.isVonNBounded_ball 𝕜₁ M₁ r)

Depends on / 依赖: NormedSpace, NormedSpace.isVonNBounded_ball, hf.image_subset_compact_of_isVonNBounded, image_subset_compact_of_isVonNBounded, isVonNBounded_ball
-/
theorem IsCompactOperator.image_ball_subset_compact [ContinuousConstSMul 𝕜₂ M₂] {f : M₁ ->ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) (r : Real) : exists K : Set M₂, IsCompact K ∧ f '' Metric.ball 0 r subseteq K :=
  hf.image_subset_compact_of_isVonNBounded (NormedSpace.isVonNBounded_ball 𝕜₁ M₁ r)

/--
theorem `IsCompactOperator.image_closedBall_subset_compact` / 定理 `IsCompactOperator.image_closedBall_subset_compact`

English:
theorem IsCompactOperator.image_closedBall_subset_compact
  statement: [ContinuousConstSMul 𝕜₂ M₂]
  proof: hf.image_subset_compact_of_isVonNBounded (NormedSpace.isVonNBounded_closedBall 𝕜₁ M₁ r)

中文:
定理 IsCompactOperator.image_closedBall_subset_compact
  结论: [ContinuousConstSMul 𝕜₂ M₂]
  证明: hf.image_subset_compact_of_isVonNBounded (NormedSpace.isVonNBounded_closedBall 𝕜₁ M₁ r)

Depends on / 依赖: NormedSpace, NormedSpace.isVonNBounded_closedBall, hf.image_subset_compact_of_isVonNBounded, image_subset_compact_of_isVonNBounded, isVonNBounded_closedBall
-/
theorem IsCompactOperator.image_closedBall_subset_compact [ContinuousConstSMul 𝕜₂ M₂]
    {f : M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) (r : Real) :
    exists K : Set M₂, IsCompact K ∧ f '' Metric.closedBall 0 r subseteq K :=
  hf.image_subset_compact_of_isVonNBounded (NormedSpace.isVonNBounded_closedBall 𝕜₁ M₁ r)

/--
theorem `IsCompactOperator.isCompact_closure_image_ball` / 定理 `IsCompactOperator.isCompact_closure_image_ball`

English:
theorem IsCompactOperator.isCompact_closure_image_ball
  statement: [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂]
  proof: hf.isCompact_closure_image_of_isVonNBounded (NormedSpace.isVonNBounded_ball 𝕜₁ M₁ r)

中文:
定理 IsCompactOperator.isCompact_closure_image_ball
  结论: [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂]
  证明: hf.isCompact_closure_image_of_isVonNBounded (NormedSpace.isVonNBounded_ball 𝕜₁ M₁ r)

Depends on / 依赖: NormedSpace, NormedSpace.isVonNBounded_ball, hf.isCompact_closure_image_of_isVonNBounded, isCompact_closure_image_of_isVonNBounded, isVonNBounded_ball
-/
theorem IsCompactOperator.isCompact_closure_image_ball [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂]
    {f : M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) (r : Real) :
    IsCompact (closure <| f '' Metric.ball 0 r) :=
  hf.isCompact_closure_image_of_isVonNBounded (NormedSpace.isVonNBounded_ball 𝕜₁ M₁ r)

/--
theorem `IsCompactOperator.isCompact_closure_image_closedBall` / 定理 `IsCompactOperator.isCompact_closure_image_closedBall`

English:
theorem IsCompactOperator.isCompact_closure_image_closedBall
  statement: [ContinuousConstSMul 𝕜₂ M₂]
  proof: hf.isCompact_closure_image_of_isVonNBounded (NormedSpace.isVonNBounded_closedBall 𝕜₁ M₁ r)

中文:
定理 IsCompactOperator.isCompact_closure_image_closedBall
  结论: [ContinuousConstSMul 𝕜₂ M₂]
  证明: hf.isCompact_closure_image_of_isVonNBounded (NormedSpace.isVonNBounded_closedBall 𝕜₁ M₁ r)

Depends on / 依赖: NormedSpace, NormedSpace.isVonNBounded_closedBall, hf.isCompact_closure_image_of_isVonNBounded, isCompact_closure_image_of_isVonNBounded, isVonNBounded_closedBall
-/
theorem IsCompactOperator.isCompact_closure_image_closedBall [ContinuousConstSMul 𝕜₂ M₂]
    [T2Space M₂] {f : M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) (r : Real) :
    IsCompact (closure <| f '' Metric.closedBall 0 r) :=
  hf.isCompact_closure_image_of_isVonNBounded (NormedSpace.isVonNBounded_closedBall 𝕜₁ M₁ r)

/--
theorem `isCompactOperator_iff_image_ball_subset_compact` / 定理 `isCompactOperator_iff_image_ball_subset_compact`

English:
theorem isCompactOperator_iff_image_ball_subset_compact
  statement: [ContinuousConstSMul 𝕜₂ M₂]
  proof: ⟨fun hf => hf.image_ball_subset_compact r, fun ⟨K, hK, hKr⟩ =>
    (isCompactOperator_iff_exists_mem_nhds_image_subset_compact f).mpr
      ⟨Metric.ball 0 r, ball_mem_nhds _ hr, K, hK, hKr⟩⟩

中文:
定理 isCompactOperator_iff_image_ball_subset_compact
  结论: [ContinuousConstSMul 𝕜₂ M₂]
  证明: ⟨fun hf => hf.image_ball_subset_compact r, fun ⟨K, hK, hKr⟩ =>
    (isCompactOperator_iff_exists_mem_nhds_image_subset_compact f).mpr
      ⟨Metric.ball 0 r, ball_mem_nhds _ hr, K, hK, hKr⟩⟩

Depends on / 依赖: Metric, Metric.ball, ball_mem_nhds, hf.image_ball_subset_compact, image_ball_subset_compact, isCompactOperator_iff_exists_mem_nhds_image_subset_compact
-/
theorem isCompactOperator_iff_image_ball_subset_compact [ContinuousConstSMul 𝕜₂ M₂]
    (f : M₁ ->ₛₗ[σ₁₂] M₂) {r : Real} (hr : 0 < r) :
    IsCompactOperator f ↔ exists K : Set M₂, IsCompact K ∧ f '' Metric.ball 0 r subseteq K :=
  ⟨fun hf => hf.image_ball_subset_compact r, fun ⟨K, hK, hKr⟩ =>
    (isCompactOperator_iff_exists_mem_nhds_image_subset_compact f).mpr
      ⟨Metric.ball 0 r, ball_mem_nhds _ hr, K, hK, hKr⟩⟩

/--
theorem `isCompactOperator_iff_image_closedBall_subset_compact` / 定理 `isCompactOperator_iff_image_closedBall_subset_compact`

English:
theorem isCompactOperator_iff_image_closedBall_subset_compact
  statement: [ContinuousConstSMul 𝕜₂ M₂]
  proof: ⟨fun hf => hf.image_closedBall_subset_compact r, fun ⟨K, hK, hKr⟩ =>
    (isCompactOperator_iff_exists_mem_nhds_image_subset_compact f).mpr
      ⟨Metric.closedBall 0 r, closedBall_mem_nhds _ hr, K, hK, hKr⟩⟩

中文:
定理 isCompactOperator_iff_image_closedBall_subset_compact
  结论: [ContinuousConstSMul 𝕜₂ M₂]
  证明: ⟨fun hf => hf.image_closedBall_subset_compact r, fun ⟨K, hK, hKr⟩ =>
    (isCompactOperator_iff_exists_mem_nhds_image_subset_compact f).mpr
      ⟨Metric.closedBall 0 r, closedBall_mem_nhds _ hr, K, hK, hKr⟩⟩

Depends on / 依赖: Metric, Metric.closedBall, closedBall, closedBall_mem_nhds, hf.image_closedBall_subset_compact, image_closedBall_subset_compact, isCompactOperator_iff_exists_mem_nhds_image_subset_compact
-/
theorem isCompactOperator_iff_image_closedBall_subset_compact [ContinuousConstSMul 𝕜₂ M₂]
    (f : M₁ ->ₛₗ[σ₁₂] M₂) {r : Real} (hr : 0 < r) :
    IsCompactOperator f ↔ exists K : Set M₂, IsCompact K ∧ f '' Metric.closedBall 0 r subseteq K :=
  ⟨fun hf => hf.image_closedBall_subset_compact r, fun ⟨K, hK, hKr⟩ =>
    (isCompactOperator_iff_exists_mem_nhds_image_subset_compact f).mpr
      ⟨Metric.closedBall 0 r, closedBall_mem_nhds _ hr, K, hK, hKr⟩⟩

/--
theorem `isCompactOperator_iff_isCompact_closure_image_ball` / 定理 `isCompactOperator_iff_isCompact_closure_image_ball`

English:
theorem isCompactOperator_iff_isCompact_closure_image_ball
  statement: [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂]
  proof: ⟨fun hf => hf.isCompact_closure_image_ball r, fun hf =>
    (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image f).mpr
      ⟨Metric.ball 0 r, ball_mem_nhds _ hr, hf⟩⟩

中文:
定理 isCompactOperator_iff_isCompact_closure_image_ball
  结论: [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂]
  证明: ⟨fun hf => hf.isCompact_closure_image_ball r, fun hf =>
    (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image f).mpr
      ⟨Metric.ball 0 r, ball_mem_nhds _ hr, hf⟩⟩

Depends on / 依赖: Metric, Metric.ball, ball_mem_nhds, hf.isCompact_closure_image_ball, isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image, isCompact_closure_image_ball
-/
theorem isCompactOperator_iff_isCompact_closure_image_ball [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂]
    (f : M₁ ->ₛₗ[σ₁₂] M₂) {r : Real} (hr : 0 < r) :
    IsCompactOperator f ↔ IsCompact (closure <| f '' Metric.ball 0 r) :=
  ⟨fun hf => hf.isCompact_closure_image_ball r, fun hf =>
    (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image f).mpr
      ⟨Metric.ball 0 r, ball_mem_nhds _ hr, hf⟩⟩

/--
theorem `isCompactOperator_iff_isCompact_closure_image_closedBall` / 定理 `isCompactOperator_iff_isCompact_closure_image_closedBall`

English:
theorem isCompactOperator_iff_isCompact_closure_image_closedBall
  statement: [ContinuousConstSMul 𝕜₂ M₂]
  proof: ⟨fun hf => hf.isCompact_closure_image_closedBall r, fun hf =>
    (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image f).mpr
      ⟨Metric.closedBall 0 r, closedBall_mem_nhds _ hr, hf⟩⟩

中文:
定理 isCompactOperator_iff_isCompact_closure_image_closedBall
  结论: [ContinuousConstSMul 𝕜₂ M₂]
  证明: ⟨fun hf => hf.isCompact_closure_image_closedBall r, fun hf =>
    (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image f).mpr
      ⟨Metric.closedBall 0 r, closedBall_mem_nhds _ hr, hf⟩⟩

Depends on / 依赖: Metric, Metric.closedBall, closedBall, closedBall_mem_nhds, hf.isCompact_closure_image_closedBall, isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image, isCompact_closure_image_closedBall
-/
theorem isCompactOperator_iff_isCompact_closure_image_closedBall [ContinuousConstSMul 𝕜₂ M₂]
    [T2Space M₂] (f : M₁ ->ₛₗ[σ₁₂] M₂) {r : Real} (hr : 0 < r) :
    IsCompactOperator f ↔ IsCompact (closure <| f '' Metric.closedBall 0 r) :=
  ⟨fun hf => hf.isCompact_closure_image_closedBall r, fun hf =>
    (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image f).mpr
      ⟨Metric.closedBall 0 r, closedBall_mem_nhds _ hr, hf⟩⟩

end NormedSpace

end Characterizations

section Operations

variable {R₁ R₄ : Type*} [Semiring R₁] [CommSemiring R₄]
  {σ₁₄ : R₁ ->+* R₄} {M₁ M₂ M₄ : Type*} [TopologicalSpace M₁]
  [AddCommMonoid M₁] [TopologicalSpace M₂] [AddCommMonoid M₂]
  [TopologicalSpace M₄] [AddCommGroup M₄]

/--
theorem `IsCompactOperator.smul` / 定理 `IsCompactOperator.smul`

English:
theorem IsCompactOperator.smul
  statement: {S : Type*} [Monoid S] [DistribMulAction S M₂]
  proof: let ⟨K, hK, hKf⟩ := hf
⟨c • K, hK.image continuous_id.const_smul c,
    mem_of_superset hKf fun _ hx => smul_mem_smul_set hx⟩

中文:
定理 IsCompactOperator.smul
  结论: {S : 类型} [Monoid S] [DistribMulAction S M₂]
  证明: let ⟨K, hK, hKf⟩ := hf
⟨c • K, hK.image continuous_id.const_smul c,
    mem_of_superset hKf fun _ hx => smul_mem_smul_set hx⟩

Depends on / 依赖: const_smul, continuous_id, continuous_id.const_smul, hK.image, mem_of_superset, smul_mem_smul_set
-/
theorem IsCompactOperator.smul {S : Type*} [Monoid S] [DistribMulAction S M₂]
    [ContinuousConstSMul S M₂] {f : M₁ -> M₂} (hf : IsCompactOperator f) (c : S) :
    IsCompactOperator (c • f) :=
  let ⟨K, hK, hKf⟩ := hf
⟨c • K, hK.image continuous_id.const_smul c,
    mem_of_superset hKf fun _ hx => smul_mem_smul_set hx⟩

/--
theorem `IsCompactOperator.smul_unit_iff` / 定理 `IsCompactOperator.smul_unit_iff`

English:
theorem IsCompactOperator.smul_unit_iff
  statement: {S : Type*} [Monoid S] [DistribMulAction S M₂]
  proof: ⟨fun h => by simpa using h.smul c⁻¹, fun h => h.smul c⟩

中文:
定理 IsCompactOperator.smul_unit_iff
  结论: {S : 类型} [Monoid S] [DistribMulAction S M₂]
  证明: ⟨fun h => by simpa using h.smul c⁻¹, fun h => h.smul c⟩

Depends on / 依赖: h.smul
-/
theorem IsCompactOperator.smul_unit_iff {S : Type*} [Monoid S] [DistribMulAction S M₂]
    [ContinuousConstSMul S M₂] {f : M₁ -> M₂} {c : Sˣ} :
    IsCompactOperator (c • f) ↔ IsCompactOperator f :=
  ⟨fun h => by simpa using h.smul c⁻¹, fun h => h.smul c⟩

/--
theorem `IsCompactOperator.smul_isUnit_iff` / 定理 `IsCompactOperator.smul_isUnit_iff`

English:
theorem IsCompactOperator.smul_isUnit_iff
  statement: {S : Type*} [Monoid S] [DistribMulAction S M₂]
  proof: by
  obtain ⟨c, rfl⟩ := hc
  exact smul_unit_iff

中文:
定理 IsCompactOperator.smul_isUnit_iff
  结论: {S : 类型} [Monoid S] [DistribMulAction S M₂]
  证明: by
  obtain ⟨c, rfl⟩ := hc
  exact smul_unit_iff

Depends on / 依赖: smul_unit_iff
-/
theorem IsCompactOperator.smul_isUnit_iff {S : Type*} [Monoid S] [DistribMulAction S M₂]
    [ContinuousConstSMul S M₂] {f : M₁ -> M₂} {c : S} (hc : IsUnit c) :
    IsCompactOperator (c • f) ↔ IsCompactOperator f := by
  obtain ⟨c, rfl⟩ := hc
  exact smul_unit_iff

/--
theorem `IsCompactOperator.smul_iff` / 定理 `IsCompactOperator.smul_iff`

English:
theorem IsCompactOperator.smul_iff
  statement: {S : Type*} [Group S] [DistribMulAction S M₂]
  proof: smul_isUnit_iff (Group.isUnit c)

中文:
定理 IsCompactOperator.smul_iff
  结论: {S : 类型} [Group S] [DistribMulAction S M₂]
  证明: smul_isUnit_iff (Group.isUnit c)

Depends on / 依赖: Group.isUnit, isUnit, smul_isUnit_iff
-/
theorem IsCompactOperator.smul_iff {S : Type*} [Group S] [DistribMulAction S M₂]
    [ContinuousConstSMul S M₂] {f : M₁ -> M₂} (c : S) :
    IsCompactOperator (c • f) ↔ IsCompactOperator f :=
  smul_isUnit_iff (Group.isUnit c)

/--
theorem `IsCompactOperator.smul_iff₀` / 定理 `IsCompactOperator.smul_iff₀`

English:
theorem IsCompactOperator.smul_iff₀
  statement: {S : Type*} [GroupWithZero S] [DistribMulAction S M₂]
  proof: smul_isUnit_iff hc.isUnit

中文:
定理 IsCompactOperator.smul_iff₀
  结论: {S : 类型} [GroupWithZero S] [DistribMulAction S M₂]
  证明: smul_isUnit_iff hc.isUnit

Depends on / 依赖: hc.isUnit, isUnit, smul_isUnit_iff
-/
theorem IsCompactOperator.smul_iff₀ {S : Type*} [GroupWithZero S] [DistribMulAction S M₂]
    [ContinuousConstSMul S M₂] {f : M₁ -> M₂} {c : S} (hc : c != 0) :
    IsCompactOperator (c • f) ↔ IsCompactOperator f :=
  smul_isUnit_iff hc.isUnit

/--
theorem `IsCompactOperator.add` / 定理 `IsCompactOperator.add`

English:
theorem IsCompactOperator.add
  statement: [ContinuousAdd M₂] {f g : M₁ -> M₂} (hf : IsCompactOperator f)
  proof: let ⟨A, hA, hAf⟩ := hf
  let ⟨B, hB, hBg⟩ := hg
  ⟨A + B, hA.add hB,
    mem_of_superset (inter_mem hAf hBg) fun _ ⟨hxA, hxB⟩ => Set.add_mem_add hxA hxB⟩

中文:
定理 IsCompactOperator.add
  结论: [ContinuousAdd M₂] {f g : M₁ -> M₂} (hf : IsCompactOperator f)
  证明: let ⟨A, hA, hAf⟩ := hf
  let ⟨B, hB, hBg⟩ := hg
  ⟨A + B, hA.add hB,
    mem_of_superset (inter_mem hAf hBg) fun _ ⟨hxA, hxB⟩ => Set.add_mem_add hxA hxB⟩

Depends on / 依赖: Set.add_mem_add, add_mem_add, hA.add, inter_mem, mem_of_superset
-/
theorem IsCompactOperator.add [ContinuousAdd M₂] {f g : M₁ -> M₂} (hf : IsCompactOperator f)
    (hg : IsCompactOperator g) : IsCompactOperator (f + g) :=
  let ⟨A, hA, hAf⟩ := hf
  let ⟨B, hB, hBg⟩ := hg
  ⟨A + B, hA.add hB,
    mem_of_superset (inter_mem hAf hBg) fun _ ⟨hxA, hxB⟩ => Set.add_mem_add hxA hxB⟩

/--
theorem `IsCompactOperator.neg` / 定理 `IsCompactOperator.neg`

English:
theorem IsCompactOperator.neg
  given: [ContinuousNeg M₄] {f : M₁ -> M₄} (hf : IsCompactOperator f)
  proof: let ⟨K, hK, hKf⟩ := hf
  ⟨-K, hK.neg, mem_of_superset hKf fun x (hx : f x in K) => Set.neg_mem_neg.mpr hx⟩

中文:
定理 IsCompactOperator.neg
  条件: [ContinuousNeg M₄] {f : M₁ -> M₄} (hf : IsCompactOperator f)
  证明: let ⟨K, hK, hKf⟩ := hf
  ⟨-K, hK.neg, mem_of_superset hKf fun x (hx : f x in K) => Set.neg_mem_neg.mpr hx⟩

Depends on / 依赖: Set.neg_mem_neg.mpr, hK.neg, mem_of_superset, neg_mem_neg
-/
theorem IsCompactOperator.neg [ContinuousNeg M₄] {f : M₁ -> M₄} (hf : IsCompactOperator f) :
    IsCompactOperator (-f) :=
  let ⟨K, hK, hKf⟩ := hf
  ⟨-K, hK.neg, mem_of_superset hKf fun x (hx : f x in K) => Set.neg_mem_neg.mpr hx⟩

/--
theorem `IsCompactOperator.sub` / 定理 `IsCompactOperator.sub`

English:
theorem IsCompactOperator.sub
  statement: [IsTopologicalAddGroup M₄] {f g : M₁ -> M₄} (hf : IsCompactOperator f)
  proof: by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

中文:
定理 IsCompactOperator.sub
  结论: [IsTopologicalAddGroup M₄] {f g : M₁ -> M₄} (hf : IsCompactOperator f)
  证明: by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem IsCompactOperator.sub [IsTopologicalAddGroup M₄] {f g : M₁ -> M₄} (hf : IsCompactOperator f)
    (hg : IsCompactOperator g) : IsCompactOperator (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

variable (σ₁₄ M₁ M₄)

/--
Definition of `compactOperator` / `compactOperator` 的定义

English:
definition compactOperator
  signature: [Module R₁ M₁] [Module R₄ M₄] [ContinuousConstSMul R₄ M₄]
  body: { f | IsCompactOperator f }
  add_mem' hf hg := hf.add hg
  zero_mem' := isCompactOperator_zero
  smul_mem' c _ hf := hf.smul c

中文:
定义 compactOperator
  签名: [Module R₁ M₁] [Module R₄ M₄] [ContinuousConstSMul R₄ M₄]
  定义体: { f | IsCompactOperator f }
  add_mem' hf hg := hf.add hg
  zero_mem' := isCompactOperator_zero
  smul_mem' c _ hf := hf.smul c

Depends on / 依赖: IsCompactOperator
-/
def compactOperator [Module R₁ M₁] [Module R₄ M₄] [ContinuousConstSMul R₄ M₄]
    [IsTopologicalAddGroup M₄] : Submodule R₄ (M₁ ->SL[σ₁₄] M₄) where
  carrier := { f | IsCompactOperator f }
  add_mem' hf hg := hf.add hg
  zero_mem' := isCompactOperator_zero
  smul_mem' c _ hf := hf.smul c

end Operations

section Comp

variable {R₁ R₂ R₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃] {σ₁₂ : R₁ ->+* R₂}
  {σ₂₃ : R₂ ->+* R₃} {M₁ M₂ M₃ : Type*} [TopologicalSpace M₁] [TopologicalSpace M₂]
  [TopologicalSpace M₃] [AddCommMonoid M₁] [Module R₁ M₁]

/--
theorem `IsCompactOperator.comp_clm` / 定理 `IsCompactOperator.comp_clm`

English:
theorem IsCompactOperator.comp_clm
  statement: [AddCommMonoid M₂] [Module R₂ M₂] {f : M₂ -> M₃}
  proof: by
  have := g.continuous.tendsto 0
  rw [map_zero] at this
  rcases hf with ⟨K, hK, hKf⟩
  exact ⟨K, hK, this hKf⟩

中文:
定理 IsCompactOperator.comp_clm
  结论: [AddCommMonoid M₂] [Module R₂ M₂] {f : M₂ -> M₃}
  证明: by
  have := g.continuous.tendsto 0
  rw [map_zero] at this
  rcases hf with ⟨K, hK, hKf⟩
  exact ⟨K, hK, this hKf⟩

Depends on / 依赖: continuous, g.continuous.tendsto, map_zero, tendsto
-/
theorem IsCompactOperator.comp_clm [AddCommMonoid M₂] [Module R₂ M₂] {f : M₂ -> M₃}
    (hf : IsCompactOperator f) (g : M₁ ->SL[σ₁₂] M₂) : IsCompactOperator (f ∘ g) := by
  have := g.continuous.tendsto 0
  rw [map_zero] at this
  rcases hf with ⟨K, hK, hKf⟩
  exact ⟨K, hK, this hKf⟩

/--
theorem `IsCompactOperator.continuous_comp` / 定理 `IsCompactOperator.continuous_comp`

English:
theorem IsCompactOperator.continuous_comp
  statement: {f : M₁ -> M₂} (hf : IsCompactOperator f) {g : M₂ -> M₃}
  proof: by
  rcases hf with ⟨K, hK, hKf⟩
  refine ⟨g '' K, hK.image hg, mem_of_superset hKf ?_⟩
  rw [preimage_comp]
  exact preimage_mono (subset_preimage_image _ _)

中文:
定理 IsCompactOperator.continuous_comp
  结论: {f : M₁ -> M₂} (hf : IsCompactOperator f) {g : M₂ -> M₃}
  证明: by
  rcases hf with ⟨K, hK, hKf⟩
  refine ⟨g '' K, hK.image hg, mem_of_superset hKf ?_⟩
  rw [preimage_comp]
  exact preimage_mono (subset_preimage_image _ _)

Depends on / 依赖: hK.image, mem_of_superset, preimage_comp, preimage_mono, subset_preimage_image
-/
theorem IsCompactOperator.continuous_comp {f : M₁ -> M₂} (hf : IsCompactOperator f) {g : M₂ -> M₃}
    (hg : Continuous g) : IsCompactOperator (g ∘ f) := by
  rcases hf with ⟨K, hK, hKf⟩
  refine ⟨g '' K, hK.image hg, mem_of_superset hKf ?_⟩
  rw [preimage_comp]
  exact preimage_mono (subset_preimage_image _ _)

/--
theorem `IsCompactOperator.clm_comp` / 定理 `IsCompactOperator.clm_comp`

English:
theorem IsCompactOperator.clm_comp
  statement: [AddCommMonoid M₂] [Module R₂ M₂] [AddCommMonoid M₃]
  proof: hf.continuous_comp g.continuous

中文:
定理 IsCompactOperator.clm_comp
  结论: [AddCommMonoid M₂] [Module R₂ M₂] [AddCommMonoid M₃]
  证明: hf.continuous_comp g.continuous

Depends on / 依赖: continuous, continuous_comp, g.continuous, hf.continuous_comp
-/
theorem IsCompactOperator.clm_comp [AddCommMonoid M₂] [Module R₂ M₂] [AddCommMonoid M₃]
    [Module R₃ M₃] {f : M₁ -> M₂} (hf : IsCompactOperator f) (g : M₂ ->SL[σ₂₃] M₃) :
    IsCompactOperator (g ∘ f) :=
  hf.continuous_comp g.continuous

/--
theorem `isCompactOperator_of_locallyCompactSpace_dom` / 定理 `isCompactOperator_of_locallyCompactSpace_dom`

English:
theorem isCompactOperator_of_locallyCompactSpace_dom
  statement: [AddCommGroup M₂] [Module R₂ M₂]
  proof: (isCompactOperator_id.comp_clm T :)

中文:
定理 isCompactOperator_of_locallyCompactSpace_dom
  结论: [AddCommGroup M₂] [Module R₂ M₂]
  证明: (isCompactOperator_id.comp_clm T :)

Depends on / 依赖: comp_clm, isCompactOperator_id, isCompactOperator_id.comp_clm
-/
theorem isCompactOperator_of_locallyCompactSpace_dom [AddCommGroup M₂] [Module R₂ M₂]
    [IsTopologicalAddGroup M₂] [LocallyCompactSpace M₂] (T : M₁ ->SL[σ₁₂] M₂) :
    IsCompactOperator T := (isCompactOperator_id.comp_clm T :)

/--
theorem `isCompactOperator_of_locallyCompactSpace_rng` / 定理 `isCompactOperator_of_locallyCompactSpace_rng`

English:
theorem isCompactOperator_of_locallyCompactSpace_rng
  statement: [AddCommGroup M₂] [Module R₂ M₂]
  proof: isCompactOperator_id.clm_comp T

中文:
定理 isCompactOperator_of_locallyCompactSpace_rng
  结论: [AddCommGroup M₂] [Module R₂ M₂]
  证明: isCompactOperator_id.clm_comp T

Depends on / 依赖: clm_comp, isCompactOperator_id, isCompactOperator_id.clm_comp
-/
theorem isCompactOperator_of_locallyCompactSpace_rng [AddCommGroup M₂] [Module R₂ M₂]
    [IsTopologicalAddGroup M₂] [LocallyCompactSpace M₂] [AddCommMonoid M₃] [Module R₃ M₃]
    (T : M₂ ->SL[σ₂₃] M₃) : IsCompactOperator T := isCompactOperator_id.clm_comp T

end Comp

section CodRestrict

variable {R₂ : Type*} [Semiring R₂] {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [TopologicalSpace M₂] [AddCommMonoid M₁] [AddCommMonoid M₂]
  [Module R₂ M₂]

/--
theorem `IsCompactOperator.codRestrict` / 定理 `IsCompactOperator.codRestrict`

English:
theorem IsCompactOperator.codRestrict
  statement: {f : M₁ -> M₂} (hf : IsCompactOperator f) {V : Submodule R₂ M₂}
  proof: let ⟨_, hK, hKf⟩ := hf
  ⟨_, h_closed.isClosedEmbedding_subtypeVal.isCompact_preimage hK, hKf⟩

中文:
定理 IsCompactOperator.codRestrict
  结论: {f : M₁ -> M₂} (hf : IsCompactOperator f) {V : Submodule R₂ M₂}
  证明: let ⟨_, hK, hKf⟩ := hf
  ⟨_, h_closed.isClosedEmbedding_subtypeVal.isCompact_preimage hK, hKf⟩

Depends on / 依赖: h_closed, h_closed.isClosedEmbedding_subtypeVal.isCompact_preimage, isClosedEmbedding_subtypeVal, isCompact_preimage
-/
theorem IsCompactOperator.codRestrict {f : M₁ -> M₂} (hf : IsCompactOperator f) {V : Submodule R₂ M₂}
    (hV : forall x, f x in V) (h_closed : IsClosed (V : Set M₂)) :
    IsCompactOperator (Set.codRestrict f V hV) :=
  let ⟨_, hK, hKf⟩ := hf
  ⟨_, h_closed.isClosedEmbedding_subtypeVal.isCompact_preimage hK, hKf⟩

end CodRestrict

section Restrict

variable {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂] {σ₁₂ : R₁ ->+* R₂}
  {M₁ M₂ : Type*} [TopologicalSpace M₁] [UniformSpace M₂]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R₁ M₁]
  [Module R₂ M₂]

/--
theorem `IsCompactOperator.restrict` / 定理 `IsCompactOperator.restrict`

English:
theorem IsCompactOperator.restrict
  statement: {f : M₁ ->ₗ[R₁] M₁} (hf : IsCompactOperator f)
  proof: (hf.comp_clm V.subtypeL).codRestrict (SetLike.forall.2 hV) h_closed

中文:
定理 IsCompactOperator.restrict
  结论: {f : M₁ ->ₗ[R₁] M₁} (hf : IsCompactOperator f)
  证明: (hf.comp_clm V.subtypeL).codRestrict (SetLike.forall.2 hV) h_closed

Depends on / 依赖: SetLike, SetLike.forall, V.subtypeL, codRestrict, comp_clm, h_closed, hf.comp_clm, subtypeL
-/
theorem IsCompactOperator.restrict {f : M₁ ->ₗ[R₁] M₁} (hf : IsCompactOperator f)
    {V : Submodule R₁ M₁} (hV : forall v in V, f v in V) (h_closed : IsClosed (V : Set M₁)) :
    IsCompactOperator (f.restrict hV) :=
  (hf.comp_clm V.subtypeL).codRestrict (SetLike.forall.2 hV) h_closed

/--
theorem `IsCompactOperator.restrict'` / 定理 `IsCompactOperator.restrict'`

English:
theorem IsCompactOperator.restrict'
  statement: [T0Space M₂] {f : M₂ ->ₗ[R₂] M₂}
  proof: hf.restrict hV (completeSpace_coe_iff_isComplete.mp hcomplete).isClosed

中文:
定理 IsCompactOperator.restrict'
  结论: [T0Space M₂] {f : M₂ ->ₗ[R₂] M₂}
  证明: hf.restrict hV (completeSpace_coe_iff_isComplete.mp hcomplete).isClosed

Depends on / 依赖: completeSpace_coe_iff_isComplete, completeSpace_coe_iff_isComplete.mp, hcomplete, hf.restrict, isClosed, restrict
-/
theorem IsCompactOperator.restrict' [T0Space M₂] {f : M₂ ->ₗ[R₂] M₂}
    (hf : IsCompactOperator f) {V : Submodule R₂ M₂} (hV : forall v in V, f v in V)
    [hcomplete : CompleteSpace V] : IsCompactOperator (f.restrict hV) :=
  hf.restrict hV (completeSpace_coe_iff_isComplete.mp hcomplete).isClosed

end Restrict

section Continuous

variable {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
  {σ₁₂ : 𝕜₁ ->+* 𝕜₂} [RingHomIsometric σ₁₂] {M₁ M₂ : Type*} [TopologicalSpace M₁] [AddCommGroup M₁]
  [TopologicalSpace M₂] [AddCommGroup M₂] [Module 𝕜₁ M₁] [Module 𝕜₂ M₂] [IsTopologicalAddGroup M₁]
  [ContinuousConstSMul 𝕜₁ M₁] [IsTopologicalAddGroup M₂] [ContinuousSMul 𝕜₂ M₂]

@[continuity]
/--
theorem `IsCompactOperator.continuous` / 定理 `IsCompactOperator.continuous`

English:
theorem IsCompactOperator.continuous
  given: {f : M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f)
  proof: by
  -- Since `f` is linear, we only need to show that it is continuous at zero.
  -- Let `U` be a neighborhood of `0` in `M₂`.
  refine continuous_of_continuousAt_zero f fun U hU => ?_
  rw [map_zero] at hU
  -- The compactness of `f` gives us a compact set `K : Set M₂` such that `f ⁻¹' K` is a
  -

中文:
定理 IsCompactOperator.continuous
  条件: {f : M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f)
  证明: by
  -- Since `f` is linear, we only need to show that it is continuous at zero.
  -- Let `U` be a neighborhood of `0` in `M₂`.
  refine continuous_of_continuousAt_zero f fun U hU => ?_
  rw [map_zero] at hU
  -- The compactness of `f` gives us a compact set `K : Set M₂` such that `f ⁻¹' K` is a
  -
-/
theorem IsCompactOperator.continuous {f : M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) :
    Continuous f := by
  -- Since `f` is linear, we only need to show that it is continuous at zero.
  -- Let `U` be a neighborhood of `0` in `M₂`.
  refine continuous_of_continuousAt_zero f fun U hU => ?_
  rw [map_zero] at hU
  -- The compactness of `f` gives us a compact set `K : Set M₂` such that `f ⁻¹' K` is a
  -- neighborhood of `0` in `M₁`.
  rcases hf with ⟨K, hK, hKf⟩
  -- But any compact set Von-Neumann bounded. Thus, `K` absorbs `U`.
  -- This gives `r > 0` such that `∀ a : 𝕜₂, r ≤ ‖a‖ → K ⊆ a • U`.
  rcases (hK.isVonNBounded 𝕜₂ hU).exists_pos with ⟨r, hr, hrU⟩
  -- Choose `c : 𝕜₂` with `r < ‖c‖`.
  rcases NormedField.exists_lt_norm 𝕜₁ r with ⟨c, hc⟩
  have hcnz : c != 0 := ne_zero_of_norm_ne_zero (hr.trans hc).ne.symm
  -- We have `f ⁻¹' ((σ₁₂ c⁻¹) • K) = c⁻¹ • f ⁻¹' K ∈ 𝓝 0`. Thus, showing that
  -- `(σ₁₂ c⁻¹) • K ⊆ U` is enough to deduce that `f ⁻¹' U ∈ 𝓝 0`.
  suffices (σ₁₂ <| c⁻¹) • K subseteq U by
    grw [← this]
    have : IsUnit c⁻¹ := hcnz.isUnit.inv
    rwa [mem_map, this.preimage_smul_setₛₗ σ₁₂, set_smul_mem_nhds_zero_iff (inv_ne_zero hcnz)]
  -- Since `σ₁₂ c⁻¹` = `(σ₁₂ c)⁻¹`, we have to prove that `K ⊆ σ₁₂ c • U`.
  rw [map_inv₀]; rw [← subset_smul_set_iff₀ ((map_ne_zero σ₁₂).mpr hcnz)]
  -- But `σ₁₂` is isometric, so `‖σ₁₂ c‖ = ‖c‖ > r`, which concludes the argument since
  -- `∀ a : 𝕜₂, r ≤ ‖a‖ → K ⊆ a • U`.
  refine hrU (σ₁₂ c) ?_
  rw [RingHomIsometric.norm_map]
  exact hc.le

/--
Definition of `ContinuousLinearMap.mkOfIsCompactOperator` / `ContinuousLinearMap.mkOfIsCompactOperator` 的定义

English:
definition ContinuousLinearMap.mkOfIsCompactOperator
  signature: {f : M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f)
  body: ⟨f, hf.continuous⟩

@[simp]

中文:
定义 ContinuousLinearMap.mkOfIsCompactOperator
  签名: {f : M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f)
  定义体: ⟨f, hf.continuous⟩

@[simp]

Depends on / 依赖: continuous, hf.continuous
-/
def ContinuousLinearMap.mkOfIsCompactOperator {f : M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) :
    M₁ ->SL[σ₁₂] M₂ :=
  ⟨f, hf.continuous⟩

@[simp]
/--
theorem `ContinuousLinearMap.mkOfIsCompactOperator_to_linearMap` / 定理 `ContinuousLinearMap.mkOfIsCompactOperator_to_linearMap`

English:
theorem ContinuousLinearMap.mkOfIsCompactOperator_to_linearMap
  statement: {f : M₁ ->ₛₗ[σ₁₂] M₂}
  proof: rfl

@[simp]

中文:
定理 ContinuousLinearMap.mkOfIsCompactOperator_to_linearMap
  结论: {f : M₁ ->ₛₗ[σ₁₂] M₂}
  证明: rfl

@[simp]
-/
theorem ContinuousLinearMap.mkOfIsCompactOperator_to_linearMap {f : M₁ ->ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) :
    (ContinuousLinearMap.mkOfIsCompactOperator hf : M₁ ->ₛₗ[σ₁₂] M₂) = f :=
  rfl

@[simp]
/--
theorem `ContinuousLinearMap.coe_mkOfIsCompactOperator` / 定理 `ContinuousLinearMap.coe_mkOfIsCompactOperator`

English:
theorem ContinuousLinearMap.coe_mkOfIsCompactOperator
  statement: {f : M₁ ->ₛₗ[σ₁₂] M₂}
  proof: rfl

中文:
定理 ContinuousLinearMap.coe_mkOfIsCompactOperator
  结论: {f : M₁ ->ₛₗ[σ₁₂] M₂}
  证明: rfl
-/
theorem ContinuousLinearMap.coe_mkOfIsCompactOperator {f : M₁ ->ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) : (ContinuousLinearMap.mkOfIsCompactOperator hf : M₁ -> M₂) = f :=
  rfl

/--
theorem `ContinuousLinearMap.mkOfIsCompactOperator_mem_compactOperator` / 定理 `ContinuousLinearMap.mkOfIsCompactOperator_mem_compactOperator`

English:
theorem ContinuousLinearMap.mkOfIsCompactOperator_mem_compactOperator
  statement: {f : M₁ ->ₛₗ[σ₁₂] M₂}
  proof: hf

中文:
定理 ContinuousLinearMap.mkOfIsCompactOperator_mem_compactOperator
  结论: {f : M₁ ->ₛₗ[σ₁₂] M₂}
  证明: hf
-/
theorem ContinuousLinearMap.mkOfIsCompactOperator_mem_compactOperator {f : M₁ ->ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) :
    ContinuousLinearMap.mkOfIsCompactOperator hf in compactOperator σ₁₂ M₁ M₂ :=
  hf

end Continuous

/--
theorem `isClosed_setOfPred_isCompactOperator` / 定理 `isClosed_setOfPred_isCompactOperator`

English:
theorem isClosed_setOfPred_isCompactOperator
  statement: {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁]
  proof: by
  refine isClosed_of_closure_subset ?_
  rintro u hu
  rw [mem_closure_iff_nhds_zero] at hu
  suffices TotallyBounded (u '' Metric.closedBall 0 1) by
    change IsCompactOperator (u : M₁ ->ₛₗ[σ₁₂] M₂)
    rw [isCompactOperator_iff_isCompact_closure_image_closedBall (u : M₁ ->ₛₗ[σ₁₂] M₂) zero_lt_o

中文:
定理 isClosed_setOfPred_isCompactOperator
  结论: {𝕜₁ 𝕜₂ : 类型} [NontriviallyNormedField 𝕜₁]
  证明: by
  refine isClosed_of_closure_subset ?_
  rintro u hu
  rw [mem_closure_iff_nhds_zero] at hu
  suffices TotallyBounded (u '' Metric.closedBall 0 1) by
    change IsCompactOperator (u : M₁ ->ₛₗ[σ₁₂] M₂)
    rw [isCompactOperator_iff_isCompact_closure_image_closedBall (u : M₁ ->ₛₗ[σ₁₂] M₂) zero_lt_o

Depends on / 依赖: IsCompactOperator, Metric, Metric.closedBall, TotallyBounded, closedBal, closedBall, closure, exists_nhds_zero_half, isClosed_closure, isClosed_of_closure_subset, isCompactOperator_iff_isCompact_closure_image_closedBall, isCompact_of_isClosed, mem_closure_iff_nhds_zero, this.closure.isCompact_of_isClosed, totallyBounded_iff_subset_finite_iUnion_nhds_zero, zero_lt_one
-/
theorem isClosed_setOfPred_isCompactOperator {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁]
    [NormedField 𝕜₂] {σ₁₂ : 𝕜₁ ->+* 𝕜₂} {M₁ M₂ : Type*} [SeminormedAddCommGroup M₁]
    [AddCommGroup M₂] [NormedSpace 𝕜₁ M₁] [Module 𝕜₂ M₂] [UniformSpace M₂] [IsUniformAddGroup M₂]
    [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂] [CompleteSpace M₂] :
    IsClosed { f : M₁ ->SL[σ₁₂] M₂ | IsCompactOperator f } := by
  refine isClosed_of_closure_subset ?_
  rintro u hu
  rw [mem_closure_iff_nhds_zero] at hu
  suffices TotallyBounded (u '' Metric.closedBall 0 1) by
    change IsCompactOperator (u : M₁ ->ₛₗ[σ₁₂] M₂)
    rw [isCompactOperator_iff_isCompact_closure_image_closedBall (u : M₁ ->ₛₗ[σ₁₂] M₂) zero_lt_one]
    exact this.closure.isCompact_of_isClosed isClosed_closure
  rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero]
  intro U hU
  rcases exists_nhds_zero_half hU with ⟨V, hV, hVU⟩
  let SV : Set M₁ × Set M₂ := ⟨closedBall 0 1, -V⟩
  rcases hu { f | forall x in SV.1, f x in SV.2 }
      (ContinuousLinearMap.hasBasis_nhds_zero.mem_of_mem
        ⟨NormedSpace.isVonNBounded_closedBall _ _ _, neg_mem_nhds_zero M₂ hV⟩) with
    ⟨v, hv, huv⟩
  rcases totallyBounded_iff_subset_finite_iUnion_nhds_zero.mp
      (hv.isCompact_closure_image_closedBall 1).totallyBounded V hV with
    ⟨T, hT, hTv⟩
  have hTv : v '' closedBall 0 1 subseteq _ := subset_closure.trans hTv
  refine ⟨T, hT, ?_⟩
  rw [image_subset_iff]; rw [preimage_iUnion₂] at hTv ⊢
  intro x hx
  specialize hTv hx
  rw [mem_iUnion₂] at hTv ⊢
  rcases hTv with ⟨t, ht, htx⟩
  refine ⟨t, ht, ?_⟩
  rw [mem_preimage]; rw [mem_vadd_set_iff_neg_vadd_mem]; rw [vadd_eq_add]; rw [neg_add_eq_sub] at htx ⊢
  convert! hVU _ htx _ (huv x hx) using 1
  rw [sub_apply]
  abel

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_isCompactOperator := isClosed_setOfPred_isCompactOperator

/--
theorem `compactOperator_topologicalClosure` / 定理 `compactOperator_topologicalClosure`

English:
theorem compactOperator_topologicalClosure
  statement: {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁]
  proof: SetLike.ext' isClosed_setOfPred_isCompactOperator.closure_eq

中文:
定理 compactOperator_topologicalClosure
  结论: {𝕜₁ 𝕜₂ : 类型} [NontriviallyNormedField 𝕜₁]
  证明: SetLike.ext' isClosed_setOfPred_isCompactOperator.closure_eq

Depends on / 依赖: SetLike, SetLike.ext, closure_eq, isClosed_setOfPred_isCompactOperator, isClosed_setOfPred_isCompactOperator.closure_eq
-/
theorem compactOperator_topologicalClosure {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁]
    [NormedField 𝕜₂] {σ₁₂ : 𝕜₁ ->+* 𝕜₂} {M₁ M₂ : Type*} [SeminormedAddCommGroup M₁]
    [AddCommGroup M₂] [NormedSpace 𝕜₁ M₁] [Module 𝕜₂ M₂] [UniformSpace M₂] [IsUniformAddGroup M₂]
    [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂] [CompleteSpace M₂] :
    (compactOperator σ₁₂ M₁ M₂).topologicalClosure = compactOperator σ₁₂ M₁ M₂ :=
  SetLike.ext' isClosed_setOfPred_isCompactOperator.closure_eq

/--
theorem `isCompactOperator_of_tendsto` / 定理 `isCompactOperator_of_tendsto`

English:
theorem isCompactOperator_of_tendsto
  statement: {ι 𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁]
  proof: isClosed_setOfPred_isCompactOperator.mem_of_tendsto hf hF

中文:
定理 isCompactOperator_of_tendsto
  结论: {ι 𝕜₁ 𝕜₂ : 类型} [NontriviallyNormedField 𝕜₁]
  证明: isClosed_setOfPred_isCompactOperator.mem_of_tendsto hf hF

Depends on / 依赖: isClosed_setOfPred_isCompactOperator, isClosed_setOfPred_isCompactOperator.mem_of_tendsto, mem_of_tendsto
-/
theorem isCompactOperator_of_tendsto {ι 𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁]
    [NormedField 𝕜₂] {σ₁₂ : 𝕜₁ ->+* 𝕜₂} {M₁ M₂ : Type*} [SeminormedAddCommGroup M₁]
    [AddCommGroup M₂] [NormedSpace 𝕜₁ M₁] [Module 𝕜₂ M₂] [UniformSpace M₂] [IsUniformAddGroup M₂]
    [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂] [CompleteSpace M₂] {l : Filter ι} [l.NeBot]
    {F : ι -> M₁ ->SL[σ₁₂] M₂} {f : M₁ ->SL[σ₁₂] M₂} (hf : Tendsto F l (𝓝 f))
    (hF : forallᶠ i in l, IsCompactOperator (F i)) : IsCompactOperator f :=
  isClosed_setOfPred_isCompactOperator.mem_of_tendsto hf hF
