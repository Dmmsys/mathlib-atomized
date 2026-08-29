/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Floris van Doorn
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Algebra.ContinuousAffineEquiv

/-!
# Ample subsets of real vector spaces

In this file we study ample sets in real vector spaces. A set is ample if all its connected
component have full convex hull. Ample sets are an important ingredient for defining ample
differential relations.

## Main results
- `ampleSet_empty` and `ampleSet_univ`: the empty set and `univ` are ample
- `AmpleSet.union`: the union of two ample sets is ample
- `AmpleSet.{pre}image`: being ample is invariant under continuous affine equivalences;
  `AmpleSet.{pre}image_iff` are "iff" versions of these
- `AmpleSet.vadd`: in particular, ample-ness is invariant under affine translations
- `AmpleSet.of_one_lt_codim`: a linear subspace of codimension at least two has an ample complement.
  This is the crucial geometric ingredient which allows to apply convex integration
  to the theory of immersions in positive codimension.

## Implementation notes

A priori, the definition of ample subset asks for a vector space structure and a topology on the
ambient type without any link between those structures. In practice, we care most about using these
for finite-dimensional vector spaces with their natural topology.

All vector spaces in the file are real vector spaces. While the definition generalises to other
connected fields, that is not useful in practice.

## Tags
ample set
-/

@[expose] public section

/-! ## Definition and invariance -/

open Set

variable {F : Type*} [AddCommGroup F] [Module Real F] [TopologicalSpace F]

/--
Definition of `AmpleSet` / `AmpleSet` 的定义

English:
definition AmpleSet
  signature: (s : Set F)
  body: forall x in s, convexHull Real (connectedComponentIn s x) = univ

中文:
定义 AmpleSet
  签名: (s : 集合 F)
  定义体: forall x in s, convexHull Real (connectedComponentIn s x) = univ

Depends on / 依赖: connectedComponentIn, convexHull
-/
def AmpleSet (s : Set F) : Prop :=
  forall x in s, convexHull Real (connectedComponentIn s x) = univ

/-- A whole vector space is ample. -/
@[simp]
/--
theorem `ampleSet_univ` / 定理 `ampleSet_univ`

English:
theorem ampleSet_univ
  given: {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  proof: by
  intro x _
  rw [connectedComponentIn_univ]; rw [PreconnectedSpace.connectedComponent_eq_univ]; rw [convexHull_univ]

中文:
定理 ampleSet_univ
  条件: {F : 类型} [赋范交换加群 F] [赋范空间 实数 F]
  证明: by
  intro x _
  rw [connectedComponentIn_univ]; rw [PreconnectedSpace.connectedComponent_eq_univ]; rw [convexHull_univ]

Depends on / 依赖: PreconnectedSpace, PreconnectedSpace.connectedComponent_eq_univ, connectedComponentIn_univ, connectedComponent_eq_univ, convexHull_univ
-/
theorem ampleSet_univ {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] :
    AmpleSet (univ : Set F) := by
  intro x _
  rw [connectedComponentIn_univ]; rw [PreconnectedSpace.connectedComponent_eq_univ]; rw [convexHull_univ]

/-- The empty set in a vector space is ample. -/
@[simp]
/--
theorem `ampleSet_empty` / 定理 `ampleSet_empty`

English:
theorem ampleSet_empty
  statement: AmpleSet (∅ : Set F)
  proof: fun _ => False.elim

中文:
定理 ampleSet_empty
  结论: AmpleSet (∅ : 集合 F)
  证明: fun _ => False.elim

Depends on / 依赖: False.elim
-/
theorem ampleSet_empty : AmpleSet (∅ : Set F) := fun _ => False.elim

namespace AmpleSet

/--
theorem `union` / 定理 `union`

English:
theorem union
  given: {s t : Set F} (hs : AmpleSet s) (ht : AmpleSet t)
  statement: AmpleSet (s union t)
  proof: by
  intro x hx
  rcases hx with (h | h) <;>
  -- The connected component of `x ∈ s` in `s ∪ t` contains the connected component of `x` in `s`,
  -- hence is also full; similarly for `t`.
  [have hx := hs x h; have hx := ht x h] <;>
  rw [← Set.univ_subset_iff]; rw [← hx] <;>
  apply convexHull_mono

中文:
定理 union
  条件: {s t : 集合 F} (hs : AmpleSet s) (ht : AmpleSet t)
  结论: AmpleSet (s union t)
  证明: by
  intro x hx
  rcases hx with (h | h) <;>
  -- The connected component of `x ∈ s` in `s ∪ t` contains the connected component of `x` in `s`,
  -- hence is also full; similarly for `t`.
  [have hx := hs x h; have hx := ht x h] <;>
  rw [← Set.univ_subset_iff]; rw [← hx] <;>
  apply convexHull_mono
-/
theorem union {s t : Set F} (hs : AmpleSet s) (ht : AmpleSet t) : AmpleSet (s union t) := by
  intro x hx
  rcases hx with (h | h) <;>
  -- The connected component of `x ∈ s` in `s ∪ t` contains the connected component of `x` in `s`,
  -- hence is also full; similarly for `t`.
  [have hx := hs x h; have hx := ht x h] <;>
  rw [← Set.univ_subset_iff]; rw [← hx] <;>
  apply convexHull_mono <;>
  apply connectedComponentIn_mono <;>
  [apply subset_union_left; apply subset_union_right]

variable {E : Type*} [AddCommGroup E] [Module Real E] [TopologicalSpace E]

/--
theorem `image` / 定理 `image`

English:
theorem image
  given: {s : Set E} (h : AmpleSet s) (L : E ≃ᴬ[Real] F)
  proof: forall_mem_image.mpr fun x hx =>
  calc (convexHull Real) (connectedComponentIn (L '' s) (L x))
    _ = (convexHull Real) (L '' (connectedComponentIn s x)) :=
.symm congrArg _ L.toHomeomorph.image_connectedComponentIn hx
    _ = L '' (convexHull Real (connectedComponentIn s x)) :=
.symm L.toAffineMa

中文:
定理 像
  条件: {s : 集合 E} (h : AmpleSet s) (L : E ≃ᴬ[实数] F)
  证明: forall_mem_image.mpr fun x hx =>
  calc (convexHull Real) (connectedComponentIn (L '' s) (L x))
    _ = (convexHull Real) (L '' (connectedComponentIn s x)) :=
.symm congrArg _ L.toHomeomorph.image_connectedComponentIn hx
    _ = L '' (convexHull Real (connectedComponentIn s x)) :=
.symm L.toAffineMa

Depends on / 依赖: forall_mem_image, forall_mem_image.mpr
-/
theorem image {s : Set E} (h : AmpleSet s) (L : E ≃ᴬ[Real] F) :
    AmpleSet (L '' s) := forall_mem_image.mpr fun x hx =>
  calc (convexHull Real) (connectedComponentIn (L '' s) (L x))
    _ = (convexHull Real) (L '' (connectedComponentIn s x)) :=
.symm congrArg _ L.toHomeomorph.image_connectedComponentIn hx
    _ = L '' (convexHull Real (connectedComponentIn s x)) :=
.symm L.toAffineMap.image_convexHull _
    _ = univ := by rw [h x hx, image_univ, L.surjective.range_eq]

/--
theorem `image_iff` / 定理 `image_iff`

English:
theorem image_iff
  given: {s : Set E} (L : E ≃ᴬ[Real] F)
  proof: ⟨fun h => (L.symm_image_image s) ▸ h.image L.symm, fun h => h.image L⟩

中文:
定理 image_iff
  条件: {s : 集合 E} (L : E ≃ᴬ[实数] F)
  证明: ⟨fun h => (L.symm_image_image s) ▸ h.image L.symm, fun h => h.image L⟩

Depends on / 依赖: L.symm, L.symm_image_image, h.image, symm_image_image
-/
theorem image_iff {s : Set E} (L : E ≃ᴬ[Real] F) :
    AmpleSet (L '' s) ↔ AmpleSet s :=
  ⟨fun h => (L.symm_image_image s) ▸ h.image L.symm, fun h => h.image L⟩

/--
theorem `preimage` / 定理 `preimage`

English:
theorem preimage
  given: {s : Set F} (h : AmpleSet s) (L : E ≃ᴬ[Real] F)
  statement: AmpleSet (L ⁻¹' s)
  proof: by
  rw [← L.image_symm_eq_preimage]
  exact h.image L.symm

中文:
定理 原像
  条件: {s : 集合 F} (h : AmpleSet s) (L : E ≃ᴬ[实数] F)
  结论: AmpleSet (L ⁻¹' s)
  证明: by
  rw [← L.image_symm_eq_preimage]
  exact h.image L.symm

Depends on / 依赖: L.image_symm_eq_preimage, L.symm, h.image, image_symm_eq_preimage
-/
theorem preimage {s : Set F} (h : AmpleSet s) (L : E ≃ᴬ[Real] F) : AmpleSet (L ⁻¹' s) := by
  rw [← L.image_symm_eq_preimage]
  exact h.image L.symm

/--
theorem `preimage_iff` / 定理 `preimage_iff`

English:
theorem preimage_iff
  given: {s : Set F} (L : E ≃ᴬ[Real] F)
  proof: ⟨fun h => L.image_preimage s ▸ h.image L, fun h => h.preimage L⟩

中文:
定理 preimage_iff
  条件: {s : 集合 F} (L : E ≃ᴬ[实数] F)
  证明: ⟨fun h => L.image_preimage s ▸ h.image L, fun h => h.preimage L⟩

Depends on / 依赖: L.image_preimage, h.image, h.preimage, image_preimage, preimage
-/
theorem preimage_iff {s : Set F} (L : E ≃ᴬ[Real] F) :
    AmpleSet (L ⁻¹' s) ↔ AmpleSet s :=
  ⟨fun h => L.image_preimage s ▸ h.image L, fun h => h.preimage L⟩

open scoped Pointwise

/--
theorem `vadd` / 定理 `vadd`

English:
theorem vadd
  given: [ContinuousAdd E] {s : Set E} (h : AmpleSet s) {y : E}
  proof: h.image (ContinuousAffineEquiv.constVAdd Real E y)

中文:
定理 vadd
  条件: [连续加法 E] {s : 集合 E} (h : AmpleSet s) {y : E}
  证明: h.image (ContinuousAffineEquiv.constVAdd Real E y)

Depends on / 依赖: ContinuousAffineEquiv, ContinuousAffineEquiv.constVAdd, constVAdd, h.image
-/
theorem vadd [ContinuousAdd E] {s : Set E} (h : AmpleSet s) {y : E} :
    AmpleSet (y +ᵥ s) :=
  h.image (ContinuousAffineEquiv.constVAdd Real E y)

/--
theorem `vadd_iff` / 定理 `vadd_iff`

English:
theorem vadd_iff
  given: [ContinuousAdd E] {s : Set E} {y : E}
  proof: AmpleSet.image_iff (ContinuousAffineEquiv.constVAdd Real E y)

中文:
定理 vadd_iff
  条件: [连续加法 E] {s : 集合 E} {y : E}
  证明: AmpleSet.image_iff (ContinuousAffineEquiv.constVAdd Real E y)

Depends on / 依赖: AmpleSet, AmpleSet.image_iff, ContinuousAffineEquiv, ContinuousAffineEquiv.constVAdd, constVAdd, image_iff
-/
theorem vadd_iff [ContinuousAdd E] {s : Set E} {y : E} :
    AmpleSet (y +ᵥ s) ↔ AmpleSet s :=
  AmpleSet.image_iff (ContinuousAffineEquiv.constVAdd Real E y)

/-! ## Subspaces of codimension at least two have ample complement -/
section Codimension

/--
theorem `of_one_lt_codim` / 定理 `of_one_lt_codim`

English:
theorem of_one_lt_codim
  statement: [IsTopologicalAddGroup F] [ContinuousSMul Real F] {E : Submodule Real F}
  proof: fun x hx => by
  rw [E.connectedComponentIn_eq_self_of_one_lt_codim hcodim hx]; rw [eq_univ_iff_forall]
  intro y
  by_cases h : y in E
  · obtain ⟨z, hz⟩ : exists z, z ∉ E := by
      rw [← not_forall]; rw [← Submodule.eq_top_iff']
      rintro rfl
      simp at hcodim
    refine segment_subset_con

中文:
定理 of_one_lt_codim
  结论: [是拓扑加群 F] [连续标量乘法 实数 F] {E : 子模 实数 F}
  证明: fun x hx => by
  rw [E.connectedComponentIn_eq_self_of_one_lt_codim hcodim hx]; rw [eq_univ_iff_forall]
  intro y
  by_cases h : y in E
  · obtain ⟨z, hz⟩ : exists z, z ∉ E := by
      rw [← not_forall]; rw [← Submodule.eq_top_iff']
      rintro rfl
      simp at hcodim
    refine segment_subset_con

Depends on / 依赖: E.connectedComponentIn_eq_self_of_one_lt_codim, Submodule, Submodule.add_mem_iff_right, Submodule.eq_top_iff, add_mem_iff_right, connectedComponentIn_eq_self_of_one_lt_codim, eq_top_iff, eq_univ_iff_forall, hcodim, mem_segment_sub_add, not_forall, segment_subset_convexHull, sub_eq_add_neg, subset_convexHull
-/
theorem of_one_lt_codim [IsTopologicalAddGroup F] [ContinuousSMul Real F] {E : Submodule Real F}
    (hcodim : 1 < Module.rank Real (F ⧸ E)) :
    AmpleSet (Eᶜ : Set F) := fun x hx => by
  rw [E.connectedComponentIn_eq_self_of_one_lt_codim hcodim hx]; rw [eq_univ_iff_forall]
  intro y
  by_cases h : y in E
  · obtain ⟨z, hz⟩ : exists z, z ∉ E := by
      rw [← not_forall]; rw [← Submodule.eq_top_iff']
      rintro rfl
      simp at hcodim
    refine segment_subset_convexHull ?_ ?_ (mem_segment_sub_add y z) <;>
      simpa [sub_eq_add_neg, Submodule.add_mem_iff_right _ h]
  · exact subset_convexHull Real (Eᶜ : Set F) h

end Codimension

end AmpleSet
