/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Michał Świętek
-/
module

public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.Normed.Module.WeakDual

/-!
# The double dual of a normed space

In this file we define the inclusion of a normed space into its double strong dual,
prove that it is an isometry (for `𝕜 = ℝ` or `𝕜 = ℂ`), and use the corresponding weak-topology
embedding together with Banach–Alaoglu to transfer compactness from the weak-star bidual back to
the weak topology.

## Main definitions

* `NormedSpace.inclusionInDoubleDual` is the inclusion of a normed space in its double
  `StrongDual`, considered as a bounded linear map.
* `NormedSpace.inclusionInDoubleDualLi` is the same map as a linear isometry (for `𝕜 = ℝ` or
  `𝕜 = ℂ`).
* `NormedSpace.inclusionInDoubleDualWeak` is the map from the weak space into the weak-star bidual,
  as a continuous linear map.
* `NormedSpace.isEmbedding_inclusionInDoubleDualWeak` shows that `inclusionInDoubleDualWeak` is
  a topological embedding.
* `NormedSpace.isCompact_closure_of_isBounded` transfers compactness from the weak-star topology
  on the bidual back to the weak topology on `X`.

## References

* [Conway, John B., A course in functional analysis][conway1990]

## Tags

double dual, inclusion, isometry, embedding, weak-star topology
-/

@[expose] public section

noncomputable section

open Topology Bornology WeakDual

universe u v

namespace NormedSpace

section inclusionInDoubleDual

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable (E : Type*) [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/--
Definition of `inclusionInDoubleDual` / `inclusionInDoubleDual` 的定义

English:
definition inclusionInDoubleDual
  signature: : E ->L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)
  body: ContinuousLinearMap.apply 𝕜 𝕜

@[simp]

中文:
定义 inclusionInDoubleDual
  签名: : E ->L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)
  定义体: ContinuousLinearMap.apply 𝕜 𝕜

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.apply
-/
def inclusionInDoubleDual : E ->L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
  ContinuousLinearMap.apply 𝕜 𝕜

@[simp]
/--
theorem `dual_def` / 定理 `dual_def`

English:
theorem dual_def
  given: (x : E) (f : StrongDual 𝕜 E)
  statement: inclusionInDoubleDual 𝕜 E x f = f x
  proof: rfl

中文:
定理 dual_def
  条件: (x : E) (f : StrongDual 𝕜 E)
  结论: inclusionInDoubleDual 𝕜 E x f = f x
  证明: rfl
-/
theorem dual_def (x : E) (f : StrongDual 𝕜 E) : inclusionInDoubleDual 𝕜 E x f = f x :=
  rfl

/--
theorem `inclusionInDoubleDual_norm_eq` / 定理 `inclusionInDoubleDual_norm_eq`

English:
theorem inclusionInDoubleDual_norm_eq
  proof: ContinuousLinearMap.opNorm_flip _

中文:
定理 inclusionInDoubleDual_norm_eq
  证明: ContinuousLinearMap.opNorm_flip _

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.opNorm_flip, opNorm_flip
-/
theorem inclusionInDoubleDual_norm_eq :
    ‖inclusionInDoubleDual 𝕜 E‖ = ‖ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 E)‖ :=
  ContinuousLinearMap.opNorm_flip _

/--
theorem `inclusionInDoubleDual_norm_le` / 定理 `inclusionInDoubleDual_norm_le`

English:
theorem inclusionInDoubleDual_norm_le
  statement: ‖inclusionInDoubleDual 𝕜 E‖ <= 1
  proof: by
  rw [inclusionInDoubleDual_norm_eq]
  exact ContinuousLinearMap.norm_id_le

中文:
定理 inclusionInDoubleDual_norm_le
  结论: ‖inclusionInDoubleDual 𝕜 E‖ <= 1
  证明: by
  rw [inclusionInDoubleDual_norm_eq]
  exact ContinuousLinearMap.norm_id_le

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.norm_id_le, inclusionInDoubleDual_norm_eq, norm_id_le
-/
theorem inclusionInDoubleDual_norm_le : ‖inclusionInDoubleDual 𝕜 E‖ <= 1 := by
  rw [inclusionInDoubleDual_norm_eq]
  exact ContinuousLinearMap.norm_id_le

/--
theorem `double_dual_bound` / 定理 `double_dual_bound`

English:
theorem double_dual_bound
  given: (x : E)
  statement: ‖(inclusionInDoubleDual 𝕜 E) x‖ <= ‖x‖
  proof: by
  simpa using ContinuousLinearMap.le_of_opNorm_le _ (inclusionInDoubleDual_norm_le 𝕜 E) x

中文:
定理 double_dual_bound
  条件: (x : E)
  结论: ‖(inclusionInDoubleDual 𝕜 E) x‖ <= ‖x‖
  证明: by
  simpa using ContinuousLinearMap.le_of_opNorm_le _ (inclusionInDoubleDual_norm_le 𝕜 E) x

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.le_of_opNorm_le, inclusionInDoubleDual_norm_le, le_of_opNorm_le
-/
theorem double_dual_bound (x : E) : ‖(inclusionInDoubleDual 𝕜 E) x‖ <= ‖x‖ := by
  simpa using ContinuousLinearMap.le_of_opNorm_le _ (inclusionInDoubleDual_norm_le 𝕜 E) x

end inclusionInDoubleDual

section BidualIsometry

variable (𝕜 : Type v) [RCLike 𝕜] {E : Type u}

section Seminormed

variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/--
Definition of `inclusionInDoubleDualLi` / `inclusionInDoubleDualLi` 的定义

English:
definition inclusionInDoubleDualLi
  signature: : E ->ₗᵢ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)
  body: { inclusionInDoubleDual 𝕜 E with
    norm_map' x := by
      apply le_antisymm (double_dual_bound 𝕜 E x)
      obtain ⟨g, hg⟩ := exists_dual_vector'' 𝕜 x
      grw [← (inclusionInDoubleDual 𝕜 E x).unit_le_opNorm g hg.left]
      simp [hg.right] }

中文:
定义 inclusionInDoubleDualLi
  签名: : E ->ₗᵢ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)
  定义体: { inclusionInDoubleDual 𝕜 E with
    norm_map' x := by
      apply le_antisymm (double_dual_bound 𝕜 E x)
      obtain ⟨g, hg⟩ := exists_dual_vector'' 𝕜 x
      grw [← (inclusionInDoubleDual 𝕜 E x).unit_le_opNorm g hg.left]
      simp [hg.right] }

Depends on / 依赖: double_dual_bound, exists_dual_vector, hg.left, hg.right, inclusionInDoubleDual, le_antisymm, norm_map, unit_le_opNorm
-/
def inclusionInDoubleDualLi : E ->ₗᵢ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
  { inclusionInDoubleDual 𝕜 E with
    norm_map' x := by
      apply le_antisymm (double_dual_bound 𝕜 E x)
      obtain ⟨g, hg⟩ := exists_dual_vector'' 𝕜 x
      grw [← (inclusionInDoubleDual 𝕜 E x).unit_le_opNorm g hg.left]
      simp [hg.right] }

/--
theorem `norm_le_dual_bound` / 定理 `norm_le_dual_bound`

English:
theorem norm_le_dual_bound
  statement: (x : E) {M : Real} (hMp : 0 <= M)
  proof: by
  rw [← (inclusionInDoubleDualLi (E := E) 𝕜).norm_map x]
  exact ContinuousLinearMap.opNorm_le_bound _ hMp hM

中文:
定理 norm_le_dual_bound
  结论: (x : E) {M : 实数} (hMp : 0 <= M)
  证明: by
  rw [← (inclusionInDoubleDualLi (E := E) 𝕜).norm_map x]
  exact ContinuousLinearMap.opNorm_le_bound _ hMp hM

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.opNorm_le_bound, inclusionInDoubleDualLi, norm_map, opNorm_le_bound
-/
theorem norm_le_dual_bound (x : E) {M : Real} (hMp : 0 <= M)
    (hM : forall f : StrongDual 𝕜 E, ‖f x‖ <= M * ‖f‖) : ‖x‖ <= M := by
  rw [← (inclusionInDoubleDualLi (E := E) 𝕜).norm_map x]
  exact ContinuousLinearMap.opNorm_le_bound _ hMp hM

end Seminormed

end BidualIsometry

section Embedding

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable (X : Type*) [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The map from a normed space with the weak topology into the weak-star bidual, as a continuous
linear map. Built using `LinearEquiv.arrowCongr` to properly bundle the topology changes via
`toWeakSpace` and `StrongDual.toWeakDual`. -/
@[simps! -isSimp apply apply_apply]
/--
Definition of `inclusionInDoubleDualWeak` / `inclusionInDoubleDualWeak` 的定义

English:
definition inclusionInDoubleDualWeak
  signature: : WeakSpace 𝕜 X ->L[𝕜] WeakDual 𝕜 (StrongDual 𝕜 X) where
  body: (toWeakSpace 𝕜 X).arrowCongr StrongDual.toWeakDual
    (inclusionInDoubleDual 𝕜 X).toLinearMap
  cont := Topology.IsInducing.continuous ⟨Eq.symm induced_compose⟩

中文:
定义 inclusionInDoubleDualWeak
  签名: : WeakSpace 𝕜 X ->L[𝕜] WeakDual 𝕜 (StrongDual 𝕜 X) where
  定义体: (toWeakSpace 𝕜 X).arrowCongr StrongDual.toWeakDual
    (inclusionInDoubleDual 𝕜 X).toLinearMap
  cont := Topology.IsInducing.continuous ⟨Eq.symm induced_compose⟩

Depends on / 依赖: StrongDual, StrongDual.toWeakDual, arrowCongr, toWeakDual, toWeakSpace
-/
def inclusionInDoubleDualWeak : WeakSpace 𝕜 X ->L[𝕜] WeakDual 𝕜 (StrongDual 𝕜 X) where
  toLinearMap := (toWeakSpace 𝕜 X).arrowCongr StrongDual.toWeakDual
    (inclusionInDoubleDual 𝕜 X).toLinearMap
  cont := Topology.IsInducing.continuous ⟨Eq.symm induced_compose⟩

attribute [simp] inclusionInDoubleDualWeak_apply_apply

@[simp]
/--
lemma `toLinearMap_inclusionInDoubleDualWeak` / 引理 `toLinearMap_inclusionInDoubleDualWeak`

English:
lemma toLinearMap_inclusionInDoubleDualWeak
  proof: rfl

中文:
引理 toLinearMap_inclusionInDoubleDualWeak
  证明: rfl
-/
lemma toLinearMap_inclusionInDoubleDualWeak :
    (inclusionInDoubleDualWeak 𝕜 X).toLinearMap =
      (toWeakSpace 𝕜 X).arrowCongr StrongDual.toWeakDual (inclusionInDoubleDual 𝕜 X).toLinearMap :=
  rfl

variable (𝕜 : Type*) [RCLike 𝕜] (X : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/--
theorem `isEmbedding_inclusionInDoubleDualWeak` / 定理 `isEmbedding_inclusionInDoubleDualWeak`

English:
theorem isEmbedding_inclusionInDoubleDualWeak
  proof: Eq.symm induced_compose
  injective := StrongDual.toWeakDual.injective.comp
    (inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).injective

中文:
定理 isEmbedding_inclusionInDoubleDualWeak
  证明: Eq.symm induced_compose
  injective := StrongDual.toWeakDual.injective.comp
    (inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).injective

Depends on / 依赖: Eq.symm, induced_compose
-/
theorem isEmbedding_inclusionInDoubleDualWeak :
    IsEmbedding (inclusionInDoubleDualWeak 𝕜 X) where
  eq_induced := Eq.symm induced_compose
  injective := StrongDual.toWeakDual.injective.comp
    (inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).injective

/--
theorem `isCompact_closure_of_isBounded` / 定理 `isCompact_closure_of_isBounded`

English:
theorem isCompact_closure_of_isBounded
  statement: (S : Set (WeakSpace 𝕜 X))
  proof: by
  rw [(isEmbedding_inclusionInDoubleDualWeak 𝕜 X).closure_eq_preimage_closure_image]
  apply (isEmbedding_inclusionInDoubleDualWeak 𝕜 X).isCompact_preimage' _ hrange
  exact WeakDual.isCompact_of_bounded_of_closed
    (WeakDual.isBounded_closure ((inclusionInDoubleDual 𝕜 X).lipschitz.isBounded_im

中文:
定理 isCompact_closure_of_isBounded
  结论: (S : Set (WeakSpace 𝕜 X))
  证明: by
  rw [(isEmbedding_inclusionInDoubleDualWeak 𝕜 X).closure_eq_preimage_closure_image]
  apply (isEmbedding_inclusionInDoubleDualWeak 𝕜 X).isCompact_preimage' _ hrange
  exact WeakDual.isCompact_of_bounded_of_closed
    (WeakDual.isBounded_closure ((inclusionInDoubleDual 𝕜 X).lipschitz.isBounded_im

Depends on / 依赖: WeakDual, WeakDual.isBounded_closure, WeakDual.isCompact_of_bounded_of_closed, closure_eq_preimage_closure_image, hrange, inclusionInDoubleDual, isBounded_closure, isBounded_image, isClosed_closure, isCompact_of_bounded_of_closed, isCompact_preimage, isEmbedding_inclusionInDoubleDualWeak, lipschitz, lipschitz.isBounded_image
-/
theorem isCompact_closure_of_isBounded (S : Set (WeakSpace 𝕜 X))
    (hb : IsBounded ((toWeakSpace 𝕜 X) ⁻¹' S))
    (hrange : closure (inclusionInDoubleDualWeak 𝕜 X '' S) subseteq
      Set.range (inclusionInDoubleDualWeak 𝕜 X)) :
    IsCompact (closure S) := by
  rw [(isEmbedding_inclusionInDoubleDualWeak 𝕜 X).closure_eq_preimage_closure_image]
  apply (isEmbedding_inclusionInDoubleDualWeak 𝕜 X).isCompact_preimage' _ hrange
  exact WeakDual.isCompact_of_bounded_of_closed
    (WeakDual.isBounded_closure ((inclusionInDoubleDual 𝕜 X).lipschitz.isBounded_image hb))
    isClosed_closure

end Embedding

end NormedSpace
