/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Orthogonal projection in affine spaces

This file defines orthogonal projection onto an affine subspace,
and reflection of a point in an affine subspace.

## Main definitions

* `EuclideanGeometry.orthogonalProjection` is the orthogonal
  projection of a point onto an affine subspace.

* `EuclideanGeometry.reflection` is the reflection of a point in an
  affine subspace.

-/

@[expose] public section

noncomputable section

namespace EuclideanGeometry

variable {𝕜 : Type*} {V : Type*} {P : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
variable {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace 𝕜 V₂]

open AffineSubspace

variable [MetricSpace P] [NormedAddTorsor V P]

/--
Definition of `orthogonalProjection` / `orthogonalProjection` 的定义

English:
definition orthogonalProjection
  signature: (s : AffineSubspace 𝕜 P) [Nonempty s]
  body: letI x := Classical.arbitrary s
  AffineIsometryEquiv.vaddConst 𝕜 x
.toContinuousAffineEquiv.toContinuousAffineMap.comp
      s.direction.orthogonalProjectionOnto.toContinuousAffineMap
.comp .symm AffineIsometryEquiv.vaddConst 𝕜 (x : P)

中文:
定义 orthogonalProjection
  签名: (s : AffineSubspace 𝕜 P) [Nonempty s]
  定义体: letI x := Classical.arbitrary s
  AffineIsometryEquiv.vaddConst 𝕜 x
.toContinuousAffineEquiv.toContinuousAffineMap.comp
      s.direction.orthogonalProjectionOnto.toContinuousAffineMap
.comp .symm AffineIsometryEquiv.vaddConst 𝕜 (x : P)

Depends on / 依赖: AffineIsometryEquiv, AffineIsometryEquiv.vaddConst, Classical, Classical.arbitrary, arbitrary, direction, orthogonalProjectionOnto, s.direction.orthogonalProjectionOnto.toContinuousAffineMap, toContinuousAffineEquiv, toContinuousAffineEquiv.toContinuousAffineMap.comp, toContinuousAffineMap, vaddConst
-/
def orthogonalProjection (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] : P ->ᴬ[𝕜] s :=
  letI x := Classical.arbitrary s
  AffineIsometryEquiv.vaddConst 𝕜 x
.toContinuousAffineEquiv.toContinuousAffineMap.comp
      s.direction.orthogonalProjectionOnto.toContinuousAffineMap
.comp .symm AffineIsometryEquiv.vaddConst 𝕜 (x : P)

/--
theorem `orthogonalProjection_apply` / 定理 `orthogonalProjection_apply`

English:
theorem orthogonalProjection_apply
  statement: (s : AffineSubspace 𝕜 P) [Nonempty s]
  proof: rfl

中文:
定理 orthogonalProjection_apply
  结论: (s : AffineSubspace 𝕜 P) [Nonempty s]
  证明: rfl
-/
theorem orthogonalProjection_apply (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p} :
    orthogonalProjection s p = s.direction.orthogonalProjectionOnto (p -ᵥ Classical.arbitrary s)
      +ᵥ Classical.arbitrary s :=
  rfl

/--
theorem `orthogonalProjection_apply'` / 定理 `orthogonalProjection_apply'`

English:
theorem orthogonalProjection_apply'
  statement: (s : AffineSubspace 𝕜 P) [Nonempty s]
  proof: rfl

中文:
定理 orthogonalProjection_apply'
  结论: (s : AffineSubspace 𝕜 P) [Nonempty s]
  证明: rfl
-/
theorem orthogonalProjection_apply' (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p} :
    (orthogonalProjection s p : P) =
      (s.direction.orthogonalProjectionOnto (p -ᵥ Classical.arbitrary s) : V) +ᵥ
      (Classical.arbitrary s : P) :=
  rfl

/--
theorem `orthogonalProjection_apply_mem` / 定理 `orthogonalProjection_apply_mem`

English:
theorem orthogonalProjection_apply_mem
  statement: (s : AffineSubspace 𝕜 P) [Nonempty s]
  proof: by
  rw [orthogonalProjection_apply]; rw [coe_vadd]; rw [vadd_eq_vadd_iff_sub_eq_vsub]; rw [← Submodule.coe_sub]; rw [← map_sub]; rw [vsub_sub_vsub_cancel_left]; rw [Submodule.coe_orthogonalProjectionOnto_apply]; rw [Submodule.starProjection_eq_self_iff]
  exact s.vsub_mem_direction (SetLike.coe_mem

中文:
定理 orthogonalProjection_apply_mem
  结论: (s : AffineSubspace 𝕜 P) [Nonempty s]
  证明: by
  rw [orthogonalProjection_apply]; rw [coe_vadd]; rw [vadd_eq_vadd_iff_sub_eq_vsub]; rw [← Submodule.coe_sub]; rw [← map_sub]; rw [vsub_sub_vsub_cancel_left]; rw [Submodule.coe_orthogonalProjectionOnto_apply]; rw [Submodule.starProjection_eq_self_iff]
  exact s.vsub_mem_direction (SetLike.coe_mem

Depends on / 依赖: SetLike, SetLike.coe_mem, Submodule, Submodule.coe_orthogonalProjectionOnto_apply, Submodule.coe_sub, Submodule.starProjection_eq_self_iff, coe_mem, coe_orthogonalProjectionOnto_apply, coe_sub, coe_vadd, map_sub, orthogonalProjection_apply, s.vsub_mem_direction, starProjection_eq_self_iff, vadd_eq_vadd_iff_sub_eq_vsub, vsub_mem_direction, vsub_sub_vsub_cancel_left
-/
theorem orthogonalProjection_apply_mem (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p x} (hx : x in s) :
    orthogonalProjection s p = (s.direction.orthogonalProjectionOnto (p -ᵥ x) : V) +ᵥ x := by
  rw [orthogonalProjection_apply]; rw [coe_vadd]; rw [vadd_eq_vadd_iff_sub_eq_vsub]; rw [← Submodule.coe_sub]; rw [← map_sub]; rw [vsub_sub_vsub_cancel_left]; rw [Submodule.coe_orthogonalProjectionOnto_apply]; rw [Submodule.starProjection_eq_self_iff]
  exact s.vsub_mem_direction (SetLike.coe_mem _) hx

/-- Since both instance arguments are propositions, allow `simp` to rewrite them
alongside the `s` argument.

Note that without the coercion to `P`, the LHS and RHS would have different types. -/
@[congr]
/--
theorem `orthogonalProjection_congr` / 定理 `orthogonalProjection_congr`

English:
theorem orthogonalProjection_congr
  statement: {s₁ s₂ : AffineSubspace 𝕜 P} {p₁ p₂ : P}
  proof: h ▸ ‹_›
    letI : s₂.direction.HasOrthogonalProjection := h ▸ ‹_›
    (orthogonalProjection s₁ p₁ : P) = (orthogonalProjection s₂ p₂ : P) := by
  subst h hp
  rfl

中文:
定理 orthogonalProjection_congr
  结论: {s₁ s₂ : AffineSubspace 𝕜 P} {p₁ p₂ : P}
  证明: h ▸ ‹_›
    letI : s₂.direction.HasOrthogonalProjection := h ▸ ‹_›
    (orthogonalProjection s₁ p₁ : P) = (orthogonalProjection s₂ p₂ : P) := by
  subst h hp
  rfl
-/
theorem orthogonalProjection_congr {s₁ s₂ : AffineSubspace 𝕜 P} {p₁ p₂ : P}
    [Nonempty s₁] [s₁.direction.HasOrthogonalProjection]
    (h : s₁ = s₂) (hp : p₁ = p₂) :
    letI : Nonempty s₂ := h ▸ ‹_›
    letI : s₂.direction.HasOrthogonalProjection := h ▸ ‹_›
    (orthogonalProjection s₁ p₁ : P) = (orthogonalProjection s₂ p₂ : P) := by
  subst h hp
  rfl

/-- The linear map corresponding to `orthogonalProjection`. -/
@[simp]
/--
theorem `orthogonalProjection_linear` / 定理 `orthogonalProjection_linear`

English:
theorem orthogonalProjection_linear
  statement: {s : AffineSubspace 𝕜 P} [Nonempty s]
  proof: rfl

中文:
定理 orthogonalProjection_linear
  结论: {s : AffineSubspace 𝕜 P} [Nonempty s]
  证明: rfl
-/
theorem orthogonalProjection_linear {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] :
    (orthogonalProjection s).linear = s.direction.orthogonalProjectionOnto :=
  rfl

/-- The continuous linear map corresponding to `orthogonalProjection`. -/
@[simp]
/--
theorem `orthogonalProjection_contLinear` / 定理 `orthogonalProjection_contLinear`

English:
theorem orthogonalProjection_contLinear
  statement: {s : AffineSubspace 𝕜 P} [Nonempty s]
  proof: rfl

中文:
定理 orthogonalProjection_contLinear
  结论: {s : AffineSubspace 𝕜 P} [Nonempty s]
  证明: rfl
-/
theorem orthogonalProjection_contLinear {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] :
    (orthogonalProjection s).contLinear = s.direction.orthogonalProjectionOnto :=
  rfl

/--
theorem `orthogonalProjection_mem` / 定理 `orthogonalProjection_mem`

English:
theorem orthogonalProjection_mem
  statement: {s : AffineSubspace 𝕜 P} [Nonempty s]
  proof: (orthogonalProjection s p).2

中文:
定理 orthogonalProjection_mem
  结论: {s : AffineSubspace 𝕜 P} [Nonempty s]
  证明: (orthogonalProjection s p).2

Depends on / 依赖: orthogonalProjection
-/
theorem orthogonalProjection_mem {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) : ↑(orthogonalProjection s p) in s :=
  (orthogonalProjection s p).2

/--
theorem `orthogonalProjection_mem_orthogonal` / 定理 `orthogonalProjection_mem_orthogonal`

English:
theorem orthogonalProjection_mem_orthogonal
  statement: (s : AffineSubspace 𝕜 P) [Nonempty s]
  proof: by
  rw [mem_mk']; rw [orthogonalProjection_apply]; rw [coe_vadd]; rw [vadd_vsub_eq_sub_vsub]; rw [← Submodule.neg_mem_iff]; rw [neg_sub]
  apply Submodule.sub_starProjection_mem_orthogonal

中文:
定理 orthogonalProjection_mem_orthogonal
  结论: (s : AffineSubspace 𝕜 P) [Nonempty s]
  证明: by
  rw [mem_mk']; rw [orthogonalProjection_apply]; rw [coe_vadd]; rw [vadd_vsub_eq_sub_vsub]; rw [← Submodule.neg_mem_iff]; rw [neg_sub]
  apply Submodule.sub_starProjection_mem_orthogonal

Depends on / 依赖: Submodule, Submodule.neg_mem_iff, Submodule.sub_starProjection_mem_orthogonal, coe_vadd, mem_mk, neg_mem_iff, neg_sub, orthogonalProjection_apply, sub_starProjection_mem_orthogonal, vadd_vsub_eq_sub_vsub
-/
theorem orthogonalProjection_mem_orthogonal (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    ↑(orthogonalProjection s p) in mk' p s.directionᗮ := by
  rw [mem_mk']; rw [orthogonalProjection_apply]; rw [coe_vadd]; rw [vadd_vsub_eq_sub_vsub]; rw [← Submodule.neg_mem_iff]; rw [neg_sub]
  apply Submodule.sub_starProjection_mem_orthogonal

/--
theorem `inter_eq_singleton_orthogonalProjection` / 定理 `inter_eq_singleton_orthogonalProjection`

English:
theorem inter_eq_singleton_orthogonalProjection
  statement: {s : AffineSubspace 𝕜 P} [Nonempty s]
  proof: by
  obtain ⟨q, hq⟩ := inter_eq_singleton_of_nonempty_of_isCompl (nonempty_subtype.mp ‹_›)
    (mk'_nonempty p s.directionᗮ)
    (by
      rw [direction_mk' p s.directionᗮ]
      exact s.direction.isCompl_orthogonal)
  rwa [Set.eq_singleton_iff_nonempty_unique_mem.1 hq |>.2 _
    ⟨orthogonalProjecti

中文:
定理 inter_eq_singleton_orthogonalProjection
  结论: {s : AffineSubspace 𝕜 P} [Nonempty s]
  证明: by
  obtain ⟨q, hq⟩ := inter_eq_singleton_of_nonempty_of_isCompl (nonempty_subtype.mp ‹_›)
    (mk'_nonempty p s.directionᗮ)
    (by
      rw [direction_mk' p s.directionᗮ]
      exact s.direction.isCompl_orthogonal)
  rwa [Set.eq_singleton_iff_nonempty_unique_mem.1 hq |>.2 _
    ⟨orthogonalProjecti

Depends on / 依赖: Set.eq_singleton_iff_nonempty_unique_mem, _nonempty, direction, direction_mk, eq_singleton_iff_nonempty_unique_mem, inter_eq_singleton_of_nonempty_of_isCompl, isCompl_orthogonal, nonempty_subtype, nonempty_subtype.mp, orthogonalProjection_mem, orthogonalProjection_mem_orthogonal, s.direction, s.direction.isCompl_orthogonal
-/
theorem inter_eq_singleton_orthogonalProjection {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    (s : Set P) inter mk' p s.directionᗮ = {↑(orthogonalProjection s p)} := by
  obtain ⟨q, hq⟩ := inter_eq_singleton_of_nonempty_of_isCompl (nonempty_subtype.mp ‹_›)
    (mk'_nonempty p s.directionᗮ)
    (by
      rw [direction_mk' p s.directionᗮ]
      exact s.direction.isCompl_orthogonal)
  rwa [Set.eq_singleton_iff_nonempty_unique_mem.1 hq |>.2 _
    ⟨orthogonalProjection_mem _, orthogonalProjection_mem_orthogonal _ _⟩]

/--
theorem `orthogonalProjection_vsub_mem_direction` / 定理 `orthogonalProjection_vsub_mem_direction`

English:
theorem orthogonalProjection_vsub_mem_direction
  statement: {s : AffineSubspace 𝕜 P} [Nonempty s]
  proof: (orthogonalProjection s p₂ -ᵥ ⟨p₁, hp₁⟩ : s.direction).2

中文:
定理 orthogonalProjection_vsub_mem_direction
  结论: {s : AffineSubspace 𝕜 P} [Nonempty s]
  证明: (orthogonalProjection s p₂ -ᵥ ⟨p₁, hp₁⟩ : s.direction).2

Depends on / 依赖: direction, orthogonalProjection, s.direction
-/
theorem orthogonalProjection_vsub_mem_direction {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p₁ : P} (p₂ : P) (hp₁ : p₁ in s) :
    ↑(orthogonalProjection s p₂ -ᵥ ⟨p₁, hp₁⟩ : s.direction) in s.direction :=
  (orthogonalProjection s p₂ -ᵥ ⟨p₁, hp₁⟩ : s.direction).2

/--
theorem `vsub_orthogonalProjection_mem_direction` / 定理 `vsub_orthogonalProjection_mem_direction`

English:
theorem vsub_orthogonalProjection_mem_direction
  statement: {s : AffineSubspace 𝕜 P} [Nonempty s]
  proof: ((⟨p₁, hp₁⟩ : s) -ᵥ orthogonalProjection s p₂ : s.direction).2

中文:
定理 vsub_orthogonalProjection_mem_direction
  结论: {s : AffineSubspace 𝕜 P} [Nonempty s]
  证明: ((⟨p₁, hp₁⟩ : s) -ᵥ orthogonalProjection s p₂ : s.direction).2

Depends on / 依赖: direction, orthogonalProjection, s.direction
-/
theorem vsub_orthogonalProjection_mem_direction {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p₁ : P} (p₂ : P) (hp₁ : p₁ in s) :
    ↑((⟨p₁, hp₁⟩ : s) -ᵥ orthogonalProjection s p₂ : s.direction) in s.direction :=
  ((⟨p₁, hp₁⟩ : s) -ᵥ orthogonalProjection s p₂ : s.direction).2

/--
theorem `orthogonalProjection_eq_self_iff` / 定理 `orthogonalProjection_eq_self_iff`

English:
theorem orthogonalProjection_eq_self_iff
  statement: {s : AffineSubspace 𝕜 P} [Nonempty s]
  proof: by
  constructor
  · exact fun h => h ▸ orthogonalProjection_mem p
  · intro h
    have hp : p in (s : Set P) inter mk' p s.directionᗮ := ⟨h, self_mem_mk' p _⟩
    rw [inter_eq_singleton_orthogonalProjection p] at hp
    symm
    exact hp

@[simp]

中文:
定理 orthogonalProjection_eq_self_iff
  结论: {s : AffineSubspace 𝕜 P} [Nonempty s]
  证明: by
  constructor
  · exact fun h => h ▸ orthogonalProjection_mem p
  · intro h
    have hp : p in (s : Set P) inter mk' p s.directionᗮ := ⟨h, self_mem_mk' p _⟩
    rw [inter_eq_singleton_orthogonalProjection p] at hp
    symm
    exact hp

@[simp]

Depends on / 依赖: inter_eq_singleton_orthogonalProjection, orthogonalProjection_mem, s.direction, self_mem_mk
-/
theorem orthogonalProjection_eq_self_iff {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p : P} : ↑(orthogonalProjection s p) = p ↔ p in s := by
  constructor
  · exact fun h => h ▸ orthogonalProjection_mem p
  · intro h
    have hp : p in (s : Set P) inter mk' p s.directionᗮ := ⟨h, self_mem_mk' p _⟩
    rw [inter_eq_singleton_orthogonalProjection p] at hp
    symm
    exact hp

@[simp]
/--
theorem `orthogonalProjection_mem_subspace_eq_self` / 定理 `orthogonalProjection_mem_subspace_eq_self`

English:
theorem orthogonalProjection_mem_subspace_eq_self
  statement: {s : AffineSubspace 𝕜 P} [Nonempty s]
  proof: by
  ext
  rw [orthogonalProjection_eq_self_iff]
  exact p.2

中文:
定理 orthogonalProjection_mem_subspace_eq_self
  结论: {s : AffineSubspace 𝕜 P} [Nonempty s]
  证明: by
  ext
  rw [orthogonalProjection_eq_self_iff]
  exact p.2

Depends on / 依赖: orthogonalProjection_eq_self_iff
-/
theorem orthogonalProjection_mem_subspace_eq_self {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : s) : orthogonalProjection s p = p := by
  ext
  rw [orthogonalProjection_eq_self_iff]
  exact p.2

/--
theorem `orthogonalProjection_orthogonalProjection` / 定理 `orthogonalProjection_orthogonalProjection`

English:
theorem orthogonalProjection_orthogonalProjection
  statement: (s : AffineSubspace 𝕜 P) [Nonempty s]
  proof: orthogonalProjection_mem_subspace_eq_self ((orthogonalProjection s) p)

中文:
定理 orthogonalProjection_orthogonalProjection
  结论: (s : AffineSubspace 𝕜 P) [Nonempty s]
  证明: orthogonalProjection_mem_subspace_eq_self ((orthogonalProjection s) p)

Depends on / 依赖: orthogonalProjection, orthogonalProjection_mem_subspace_eq_self
-/
theorem orthogonalProjection_orthogonalProjection (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    orthogonalProjection s (orthogonalProjection s p) = orthogonalProjection s p :=
  orthogonalProjection_mem_subspace_eq_self ((orthogonalProjection s) p)

/--
theorem `eq_orthogonalProjection_of_eq_subspace` / 定理 `eq_orthogonalProjection_of_eq_subspace`

English:
theorem eq_orthogonalProjection_of_eq_subspace
  statement: {s s' : AffineSubspace 𝕜 P} [Nonempty s]
  proof: by
  subst h
  rfl

中文:
定理 eq_orthogonalProjection_of_eq_subspace
  结论: {s s' : AffineSubspace 𝕜 P} [Nonempty s]
  证明: by
  subst h
  rfl
-/
theorem eq_orthogonalProjection_of_eq_subspace {s s' : AffineSubspace 𝕜 P} [Nonempty s]
    [Nonempty s'] [s.direction.HasOrthogonalProjection] [s'.direction.HasOrthogonalProjection]
    (h : s = s') (p : P) : (orthogonalProjection s p : P) = (orthogonalProjection s' p : P) := by
  subst h
  rfl

/--
lemma `orthogonalProjection_affineSpan_singleton` / 引理 `orthogonalProjection_affineSpan_singleton`

English:
lemma orthogonalProjection_affineSpan_singleton
  given: (p₁ p₂ : P)
  proof: by
  have h := SetLike.coe_mem (orthogonalProjection (affineSpan 𝕜 {p₁}) p₂)
  rwa [mem_affineSpan_singleton] at h

中文:
引理 orthogonalProjection_affineSpan_singleton
  条件: (p₁ p₂ : P)
  证明: by
  have h := SetLike.coe_mem (orthogonalProjection (affineSpan 𝕜 {p₁}) p₂)
  rwa [mem_affineSpan_singleton] at h
-/
@[simp] lemma orthogonalProjection_affineSpan_singleton (p₁ p₂ : P) :
    orthogonalProjection (affineSpan 𝕜 {p₁}) p₂ = p₁ := by
  have h := SetLike.coe_mem (orthogonalProjection (affineSpan 𝕜 {p₁}) p₂)
  rwa [mem_affineSpan_singleton] at h

/--
theorem `dist_orthogonalProjection_eq_zero_iff` / 定理 `dist_orthogonalProjection_eq_zero_iff`

English:
theorem dist_orthogonalProjection_eq_zero_iff
  statement: {s : AffineSubspace 𝕜 P} [Nonempty s]
  proof: by
  rw [dist_comm]; rw [dist_eq_zero]; rw [orthogonalProjection_eq_self_iff]

中文:
定理 dist_orthogonalProjection_eq_zero_iff
  结论: {s : AffineSubspace 𝕜 P} [Nonempty s]
  证明: by
  rw [dist_comm]; rw [dist_eq_zero]; rw [orthogonalProjection_eq_self_iff]

Depends on / 依赖: dist_comm, dist_eq_zero, orthogonalProjection_eq_self_iff
-/
theorem dist_orthogonalProjection_eq_zero_iff {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p : P} :
    dist p (orthogonalProjection s p) = 0 ↔ p in s := by
  rw [dist_comm]; rw [dist_eq_zero]; rw [orthogonalProjection_eq_self_iff]

/--
theorem `dist_orthogonalProjection_ne_zero_of_notMem` / 定理 `dist_orthogonalProjection_ne_zero_of_notMem`

English:
theorem dist_orthogonalProjection_ne_zero_of_notMem
  statement: {s : AffineSubspace 𝕜 P} [Nonempty s]
  proof: mt dist_orthogonalProjection_eq_zero_iff.mp hp

中文:
定理 dist_orthogonalProjection_ne_zero_of_notMem
  结论: {s : AffineSubspace 𝕜 P} [Nonempty s]
  证明: mt dist_orthogonalProjection_eq_zero_iff.mp hp

Depends on / 依赖: dist_orthogonalProjection_eq_zero_iff, dist_orthogonalProjection_eq_zero_iff.mp
-/
theorem dist_orthogonalProjection_ne_zero_of_notMem {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p : P} (hp : p ∉ s) :
    dist p (orthogonalProjection s p) != 0 :=
  mt dist_orthogonalProjection_eq_zero_iff.mp hp

/--
theorem `orthogonalProjection_vsub_mem_direction_orthogonal` / 定理 `orthogonalProjection_vsub_mem_direction_orthogonal`

English:
theorem orthogonalProjection_vsub_mem_direction_orthogonal
  statement: (s : AffineSubspace 𝕜 P) [Nonempty s]
  proof: by
  rw [← mem_mk']
  apply orthogonalProjection_mem_orthogonal

中文:
定理 orthogonalProjection_vsub_mem_direction_orthogonal
  结论: (s : AffineSubspace 𝕜 P) [Nonempty s]
  证明: by
  rw [← mem_mk']
  apply orthogonalProjection_mem_orthogonal

Depends on / 依赖: mem_mk, orthogonalProjection_mem_orthogonal
-/
theorem orthogonalProjection_vsub_mem_direction_orthogonal (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    (orthogonalProjection s p : P) -ᵥ p in s.directionᗮ := by
  rw [← mem_mk']
  apply orthogonalProjection_mem_orthogonal

/--
theorem `vsub_orthogonalProjection_mem_direction_orthogonal` / 定理 `vsub_orthogonalProjection_mem_direction_orthogonal`

English:
theorem vsub_orthogonalProjection_mem_direction_orthogonal
  statement: (s : AffineSubspace 𝕜 P) [Nonempty s]
  proof: direction_mk' p s.directionᗮ ▸
    vsub_mem_direction (self_mem_mk' _ _) (orthogonalProjection_mem_orthogonal s p)

中文:
定理 vsub_orthogonalProjection_mem_direction_orthogonal
  结论: (s : AffineSubspace 𝕜 P) [Nonempty s]
  证明: direction_mk' p s.directionᗮ ▸
    vsub_mem_direction (self_mem_mk' _ _) (orthogonalProjection_mem_orthogonal s p)

Depends on / 依赖: direction_mk, orthogonalProjection_mem_orthogonal, s.direction, self_mem_mk, vsub_mem_direction
-/
theorem vsub_orthogonalProjection_mem_direction_orthogonal (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) : p -ᵥ orthogonalProjection s p in s.directionᗮ :=
  direction_mk' p s.directionᗮ ▸
    vsub_mem_direction (self_mem_mk' _ _) (orthogonalProjection_mem_orthogonal s p)

/--
theorem `orthogonalProjection_vsub_orthogonalProjection` / 定理 `orthogonalProjection_vsub_orthogonalProjection`

English:
theorem orthogonalProjection_vsub_orthogonalProjection
  statement: (s : AffineSubspace 𝕜 P) [Nonempty s]
  proof: by
  simpa using vsub_orthogonalProjection_mem_direction_orthogonal _ _

中文:
定理 orthogonalProjection_vsub_orthogonalProjection
  结论: (s : AffineSubspace 𝕜 P) [Nonempty s]
  证明: by
  simpa using vsub_orthogonalProjection_mem_direction_orthogonal _ _

Depends on / 依赖: vsub_orthogonalProjection_mem_direction_orthogonal
-/
theorem orthogonalProjection_vsub_orthogonalProjection (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    s.direction.orthogonalProjectionOnto (p -ᵥ orthogonalProjection s p) = 0 := by
  simpa using vsub_orthogonalProjection_mem_direction_orthogonal _ _

/--
lemma `coe_orthogonalProjection_eq_iff_mem` / 引理 `coe_orthogonalProjection_eq_iff_mem`

English:
lemma coe_orthogonalProjection_eq_iff_mem
  statement: {s : AffineSubspace 𝕜 P} [Nonempty s]
  proof: by
  constructor
  · rintro rfl
    exact ⟨orthogonalProjection_mem _, vsub_orthogonalProjection_mem_direction_orthogonal _ _⟩
  · rintro ⟨hqs, hpq⟩
    have hq : q in mk' p s.directionᗮ := by
      rwa [mem_mk', ← neg_mem_iff, neg_vsub_eq_vsub_rev]
    suffices q in ({(orthogonalProjection s p : P)

中文:
引理 coe_orthogonalProjection_eq_iff_mem
  结论: {s : AffineSubspace 𝕜 P} [Nonempty s]
  证明: by
  constructor
  · rintro rfl
    exact ⟨orthogonalProjection_mem _, vsub_orthogonalProjection_mem_direction_orthogonal _ _⟩
  · rintro ⟨hqs, hpq⟩
    have hq : q in mk' p s.directionᗮ := by
      rwa [mem_mk', ← neg_mem_iff, neg_vsub_eq_vsub_rev]
    suffices q in ({(orthogonalProjection s p : P)

Depends on / 依赖: Set.mem_inter_iff, SetLike, SetLike.mem_coe, eq_comm, inter_eq_singleton_orthogonalProjection, mem_coe, mem_inter_iff, mem_mk, neg_mem_iff, neg_vsub_eq_vsub_rev, orthogonalProjection, orthogonalProjection_mem, s.direction, vsub_orthogonalProjection_mem_direction_orthogonal
-/
lemma coe_orthogonalProjection_eq_iff_mem {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p q : P} :
    orthogonalProjection s p = q ↔ q in s ∧ p -ᵥ q in s.directionᗮ := by
  constructor
  · rintro rfl
    exact ⟨orthogonalProjection_mem _, vsub_orthogonalProjection_mem_direction_orthogonal _ _⟩
  · rintro ⟨hqs, hpq⟩
    have hq : q in mk' p s.directionᗮ := by
      rwa [mem_mk', ← neg_mem_iff, neg_vsub_eq_vsub_rev]
    suffices q in ({(orthogonalProjection s p : P)} : Set P) by
      simpa [eq_comm] using this
    rw [← inter_eq_singleton_orthogonalProjection]
    simp only [Set.mem_inter_iff, SetLike.mem_coe]
    exact ⟨hqs, hq⟩

/--
lemma `orthogonalProjection_eq_iff_mem` / 引理 `orthogonalProjection_eq_iff_mem`

English:
lemma orthogonalProjection_eq_iff_mem
  statement: {s : AffineSubspace 𝕜 P} [Nonempty s]
  proof: by
  simpa using coe_orthogonalProjection_eq_iff_mem (s := s) (p := p) (q := (q : P))

中文:
引理 orthogonalProjection_eq_iff_mem
  结论: {s : AffineSubspace 𝕜 P} [Nonempty s]
  证明: by
  simpa using coe_orthogonalProjection_eq_iff_mem (s := s) (p := p) (q := (q : P))

Depends on / 依赖: coe_orthogonalProjection_eq_iff_mem
-/
lemma orthogonalProjection_eq_iff_mem {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p : P} {q : s} :
    orthogonalProjection s p = q ↔ p -ᵥ q in s.directionᗮ := by
  simpa using coe_orthogonalProjection_eq_iff_mem (s := s) (p := p) (q := (q : P))

/--
lemma `orthogonalProjection_eq_orthogonalProjection_iff_vsub_mem` / 引理 `orthogonalProjection_eq_orthogonalProjection_iff_vsub_mem`

English:
lemma orthogonalProjection_eq_orthogonalProjection_iff_vsub_mem
  statement: {s : AffineSubspace 𝕜 P}
  proof: by
  rw [orthogonalProjection_eq_iff_mem]; rw [← s.directionᗮ.add_mem_iff_left (x := p -ᵥ q)
    (vsub_orthogonalProjection_mem_direction_orthogonal s q)]
  simp

中文:
引理 orthogonalProjection_eq_orthogonalProjection_iff_vsub_mem
  结论: {s : AffineSubspace 𝕜 P}
  证明: by
  rw [orthogonalProjection_eq_iff_mem]; rw [← s.directionᗮ.add_mem_iff_left (x := p -ᵥ q)
    (vsub_orthogonalProjection_mem_direction_orthogonal s q)]
  simp

Depends on / 依赖: add_mem_iff_left, orthogonalProjection_eq_iff_mem, s.direction, vsub_orthogonalProjection_mem_direction_orthogonal
-/
lemma orthogonalProjection_eq_orthogonalProjection_iff_vsub_mem {s : AffineSubspace 𝕜 P}
    [Nonempty s] [s.direction.HasOrthogonalProjection] {p q : P} :
    orthogonalProjection s p = orthogonalProjection s q ↔ p -ᵥ q in s.directionᗮ := by
  rw [orthogonalProjection_eq_iff_mem]; rw [← s.directionᗮ.add_mem_iff_left (x := p -ᵥ q)
    (vsub_orthogonalProjection_mem_direction_orthogonal s q)]
  simp

/--
lemma `orthogonalProjection_sup_of_orthogonalProjection_eq` / 引理 `orthogonalProjection_sup_of_orthogonalProjection_eq`

English:
lemma orthogonalProjection_sup_of_orthogonalProjection_eq
  statement: {s₁ s₂ : AffineSubspace 𝕜 P} [Nonempty s₁]
  proof: by
  rw [coe_orthogonalProjection_eq_iff_mem]
  refine ⟨SetLike.le_def.1 le_sup_left (orthogonalProjection_mem _), ?_⟩
  rw [direction_sup_eq_sup_direction (orthogonalProjection_mem p) (h ▸ orthogonalProjection_mem p)]; rw [← Submodule.inf_orthogonal]
  exact ⟨vsub_orthogonalProjection_mem_direction

中文:
引理 orthogonalProjection_sup_of_orthogonalProjection_eq
  结论: {s₁ s₂ : AffineSubspace 𝕜 P} [Nonempty s₁]
  证明: by
  rw [coe_orthogonalProjection_eq_iff_mem]
  refine ⟨SetLike.le_def.1 le_sup_left (orthogonalProjection_mem _), ?_⟩
  rw [direction_sup_eq_sup_direction (orthogonalProjection_mem p) (h ▸ orthogonalProjection_mem p)]; rw [← Submodule.inf_orthogonal]
  exact ⟨vsub_orthogonalProjection_mem_direction

Depends on / 依赖: SetLike, SetLike.le_def, Submodule, Submodule.inf_orthogonal, coe_orthogonalProjection_eq_iff_mem, direction_sup_eq_sup_direction, inf_orthogonal, le_def, le_sup_left, orthogonalProjection_mem, vsub_orthogonalProjection_mem_direction_orthogonal
-/
lemma orthogonalProjection_sup_of_orthogonalProjection_eq {s₁ s₂ : AffineSubspace 𝕜 P} [Nonempty s₁]
    [Nonempty s₂] [s₁.direction.HasOrthogonalProjection] [s₂.direction.HasOrthogonalProjection]
    {p : P} (h : (orthogonalProjection s₁ p : P) = orthogonalProjection s₂ p)
    [(s₁ ⊔ s₂).direction.HasOrthogonalProjection] :
    (orthogonalProjection (s₁ ⊔ s₂) p : P) = orthogonalProjection s₁ p := by
  rw [coe_orthogonalProjection_eq_iff_mem]
  refine ⟨SetLike.le_def.1 le_sup_left (orthogonalProjection_mem _), ?_⟩
  rw [direction_sup_eq_sup_direction (orthogonalProjection_mem p) (h ▸ orthogonalProjection_mem p)]; rw [← Submodule.inf_orthogonal]
  exact ⟨vsub_orthogonalProjection_mem_direction_orthogonal _ _,
    h ▸ vsub_orthogonalProjection_mem_direction_orthogonal _ _⟩

/--
theorem `orthogonalProjection_vadd_eq_self` / 定理 `orthogonalProjection_vadd_eq_self`

English:
theorem orthogonalProjection_vadd_eq_self
  statement: {s : AffineSubspace 𝕜 P} [Nonempty s]
  proof: by
  ext
  exact coe_orthogonalProjection_eq_iff_mem.mpr (by simp [*])

中文:
定理 orthogonalProjection_vadd_eq_self
  结论: {s : AffineSubspace 𝕜 P} [Nonempty s]
  证明: by
  ext
  exact coe_orthogonalProjection_eq_iff_mem.mpr (by simp [*])

Depends on / 依赖: coe_orthogonalProjection_eq_iff_mem, coe_orthogonalProjection_eq_iff_mem.mpr
-/
theorem orthogonalProjection_vadd_eq_self {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p : P} (hp : p in s) {v : V} (hv : v in s.directionᗮ) :
    orthogonalProjection s (v +ᵥ p) = ⟨p, hp⟩ := by
  ext
  exact coe_orthogonalProjection_eq_iff_mem.mpr (by simp [*])

/--
theorem `orthogonalProjection_vadd_smul_vsub_orthogonalProjection` / 定理 `orthogonalProjection_vadd_smul_vsub_orthogonalProjection`

English:
theorem orthogonalProjection_vadd_smul_vsub_orthogonalProjection
  statement: {s : AffineSubspace 𝕜 P}
  proof: orthogonalProjection_vadd_eq_self hp
    (Submodule.smul_mem _ _ (vsub_orthogonalProjection_mem_direction_orthogonal s _))

中文:
定理 orthogonalProjection_vadd_smul_vsub_orthogonalProjection
  结论: {s : AffineSubspace 𝕜 P}
  证明: orthogonalProjection_vadd_eq_self hp
    (Submodule.smul_mem _ _ (vsub_orthogonalProjection_mem_direction_orthogonal s _))

Depends on / 依赖: Submodule, Submodule.smul_mem, orthogonalProjection_vadd_eq_self, smul_mem, vsub_orthogonalProjection_mem_direction_orthogonal
-/
theorem orthogonalProjection_vadd_smul_vsub_orthogonalProjection {s : AffineSubspace 𝕜 P}
    [Nonempty s] [s.direction.HasOrthogonalProjection] {p₁ : P} (p₂ : P) (r : 𝕜) (hp : p₁ in s) :
    orthogonalProjection s (r • (p₂ -ᵥ orthogonalProjection s p₂ : V) +ᵥ p₁) = ⟨p₁, hp⟩ :=
  orthogonalProjection_vadd_eq_self hp
    (Submodule.smul_mem _ _ (vsub_orthogonalProjection_mem_direction_orthogonal s _))

/--
lemma `orthogonalProjection_orthogonalProjection_of_le` / 引理 `orthogonalProjection_orthogonalProjection_of_le`

English:
lemma orthogonalProjection_orthogonalProjection_of_le
  statement: {s₁ s₂ : AffineSubspace 𝕜 P} [Nonempty s₁]
  proof: by
  rw [orthogonalProjection_eq_orthogonalProjection_iff_vsub_mem]
  exact SetLike.le_def.1 (Submodule.orthogonal_le (direction_le h))
    (orthogonalProjection_vsub_mem_direction_orthogonal _ _)

中文:
引理 orthogonalProjection_orthogonalProjection_of_le
  结论: {s₁ s₂ : AffineSubspace 𝕜 P} [Nonempty s₁]
  证明: by
  rw [orthogonalProjection_eq_orthogonalProjection_iff_vsub_mem]
  exact SetLike.le_def.1 (Submodule.orthogonal_le (direction_le h))
    (orthogonalProjection_vsub_mem_direction_orthogonal _ _)

Depends on / 依赖: SetLike, SetLike.le_def, Submodule, Submodule.orthogonal_le, direction_le, le_def, orthogonalProjection_eq_orthogonalProjection_iff_vsub_mem, orthogonalProjection_vsub_mem_direction_orthogonal, orthogonal_le
-/
lemma orthogonalProjection_orthogonalProjection_of_le {s₁ s₂ : AffineSubspace 𝕜 P} [Nonempty s₁]
    [Nonempty s₂] [s₁.direction.HasOrthogonalProjection] [s₂.direction.HasOrthogonalProjection]
    (h : s₁ <= s₂) (p : P) :
    orthogonalProjection s₁ (orthogonalProjection s₂ p) = orthogonalProjection s₁ p := by
  rw [orthogonalProjection_eq_orthogonalProjection_iff_vsub_mem]
  exact SetLike.le_def.1 (Submodule.orthogonal_le (direction_le h))
    (orthogonalProjection_vsub_mem_direction_orthogonal _ _)

/--
theorem `dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq` / 定理 `dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq`

English:
theorem dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
  proof: by
  rw [dist_comm p₂ _]; rw [dist_eq_norm_vsub V p₁ _]; rw [dist_eq_norm_vsub V p₁ _]; rw [dist_eq_norm_vsub V _ p₂]; rw [← vsub_add_vsub_cancel p₁ (orthogonalProjection s p₂) p₂]; rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜)]
  exact Submodule.inner_right_of_mem_orthogonal (vsu

中文:
定理 dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
  证明: by
  rw [dist_comm p₂ _]; rw [dist_eq_norm_vsub V p₁ _]; rw [dist_eq_norm_vsub V p₁ _]; rw [dist_eq_norm_vsub V _ p₂]; rw [← vsub_add_vsub_cancel p₁ (orthogonalProjection s p₂) p₂]; rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜)]
  exact Submodule.inner_right_of_mem_orthogonal (vsu

Depends on / 依赖: Submodule, Submodule.inner_right_of_mem_orthogonal, dist_comm, dist_eq_norm_vsub, inner_right_of_mem_orthogonal, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero, orthogonalProjection, orthogonalProjection_vsub_mem_direction_orthogonal, vsub_add_vsub_cancel, vsub_orthogonalProjection_mem_direction
-/
theorem dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
    {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] {p₁ : P} (p₂ : P)
    (hp₁ : p₁ in s) :
    dist p₁ p₂ * dist p₁ p₂ =
      dist p₁ (orthogonalProjection s p₂) * dist p₁ (orthogonalProjection s p₂) +
        dist p₂ (orthogonalProjection s p₂) * dist p₂ (orthogonalProjection s p₂) := by
  rw [dist_comm p₂ _]; rw [dist_eq_norm_vsub V p₁ _]; rw [dist_eq_norm_vsub V p₁ _]; rw [dist_eq_norm_vsub V _ p₂]; rw [← vsub_add_vsub_cancel p₁ (orthogonalProjection s p₂) p₂]; rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜)]
  exact Submodule.inner_right_of_mem_orthogonal (vsub_orthogonalProjection_mem_direction p₂ hp₁)
    (orthogonalProjection_vsub_mem_direction_orthogonal s p₂)

/--
lemma `dist_orthogonalProjection_eq_dist_iff_eq_of_mem` / 引理 `dist_orthogonalProjection_eq_dist_iff_eq_of_mem`

English:
lemma dist_orthogonalProjection_eq_dist_iff_eq_of_mem
  statement: {s : AffineSubspace 𝕜 P}
  proof: ⟨p₂, hp₂⟩
    dist p₁ (orthogonalProjection s p₁) = dist p₁ p₂ ↔ orthogonalProjection s p₁ = p₂ := by
  have : Nonempty s := ⟨p₂, hp₂⟩
  constructor
  · intro h
    rwa [← sq_eq_sq₀ dist_nonneg dist_nonneg, pow_two, pow_two, dist_comm _ p₂,
      dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orth

中文:
引理 dist_orthogonalProjection_eq_dist_iff_eq_of_mem
  结论: {s : AffineSubspace 𝕜 P}
  证明: ⟨p₂, hp₂⟩
    dist p₁ (orthogonalProjection s p₁) = dist p₁ p₂ ↔ orthogonalProjection s p₁ = p₂ := by
  have : Nonempty s := ⟨p₂, hp₂⟩
  constructor
  · intro h
    rwa [← sq_eq_sq₀ dist_nonneg dist_nonneg, pow_two, pow_two, dist_comm _ p₂,
      dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orth
-/
lemma dist_orthogonalProjection_eq_dist_iff_eq_of_mem {s : AffineSubspace 𝕜 P}
    [s.direction.HasOrthogonalProjection] {p₁ p₂ : P} (hp₂ : p₂ in s) :
    haveI : Nonempty s := ⟨p₂, hp₂⟩
    dist p₁ (orthogonalProjection s p₁) = dist p₁ p₂ ↔ orthogonalProjection s p₁ = p₂ := by
  have : Nonempty s := ⟨p₂, hp₂⟩
  constructor
  · intro h
    rwa [← sq_eq_sq₀ dist_nonneg dist_nonneg, pow_two, pow_two, dist_comm _ p₂,
      dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq _ hp₂,
      right_eq_add, mul_eq_zero, dist_eq_zero, or_self, eq_comm] at h
  · intro h
    nth_rw 4 [← h]

/--
lemma `dist_orthogonalProjection_eq_infDist` / 引理 `dist_orthogonalProjection_eq_infDist`

English:
lemma dist_orthogonalProjection_eq_infDist
  statement: (s : AffineSubspace 𝕜 P) [Nonempty s]
  proof: by
  refine le_antisymm ?_ (Metric.infDist_le_dist_of_mem (orthogonalProjection_mem _))
  rw [Metric.infDist_eq_iInf]
  refine le_ciInf fun x => le_of_sq_le_sq ?_ dist_nonneg
  rw [dist_comm _ (x : P)]
  simp_rw [pow_two,
    dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p

中文:
引理 dist_orthogonalProjection_eq_infDist
  结论: (s : AffineSubspace 𝕜 P) [Nonempty s]
  证明: by
  refine le_antisymm ?_ (Metric.infDist_le_dist_of_mem (orthogonalProjection_mem _))
  rw [Metric.infDist_eq_iInf]
  refine le_ciInf fun x => le_of_sq_le_sq ?_ dist_nonneg
  rw [dist_comm _ (x : P)]
  simp_rw [pow_two,
    dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p

Depends on / 依赖: Metric, Metric.infDist_eq_iInf, Metric.infDist_le_dist_of_mem, dist_comm, dist_nonneg, dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq, infDist_eq_iInf, infDist_le_dist_of_mem, le_antisymm, le_ciInf, le_of_sq_le_sq, mul_self_nonneg, orthogonalProjection_mem, pow_two, property, simp_rw, x.property
-/
lemma dist_orthogonalProjection_eq_infDist (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    dist p (orthogonalProjection s p) = Metric.infDist p s := by
  refine le_antisymm ?_ (Metric.infDist_le_dist_of_mem (orthogonalProjection_mem _))
  rw [Metric.infDist_eq_iInf]
  refine le_ciInf fun x => le_of_sq_le_sq ?_ dist_nonneg
  rw [dist_comm _ (x : P)]
  simp_rw [pow_two,
    dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p x.property]
  simp [mul_self_nonneg]

/--
lemma `dist_orthogonalProjection_eq_infNndist` / 引理 `dist_orthogonalProjection_eq_infNndist`

English:
lemma dist_orthogonalProjection_eq_infNndist
  statement: (s : AffineSubspace 𝕜 P) [Nonempty s]
  proof: by
  rw [← NNReal.coe_inj]
  simp [dist_orthogonalProjection_eq_infDist]

中文:
引理 dist_orthogonalProjection_eq_infNndist
  结论: (s : AffineSubspace 𝕜 P) [Nonempty s]
  证明: by
  rw [← NNReal.coe_inj]
  simp [dist_orthogonalProjection_eq_infDist]

Depends on / 依赖: NNReal, NNReal.coe_inj, coe_inj, dist_orthogonalProjection_eq_infDist
-/
lemma dist_orthogonalProjection_eq_infNndist (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    nndist p (orthogonalProjection s p) = Metric.infNndist p s := by
  rw [← NNReal.coe_inj]
  simp [dist_orthogonalProjection_eq_infDist]

/--
theorem `dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd` / 定理 `dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd`

English:
theorem dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd
  statement: {s : AffineSubspace 𝕜 P} {p₁ p₂ : P}
  proof: calc
    dist (r₁ • v +ᵥ p₁) (r₂ • v +ᵥ p₂) * dist (r₁ • v +ᵥ p₁) (r₂ • v +ᵥ p₂) =
        ‖p₁ -ᵥ p₂ + (r₁ - r₂) • v‖ * ‖p₁ -ᵥ p₂ + (r₁ - r₂) • v‖ := by
      rw [dist_eq_norm_vsub V (r₁ • v +ᵥ p₁)]; rw [vsub_vadd_eq_vsub_sub]; rw [vadd_vsub_assoc]; rw [sub_smul]; rw [add_comm]; rw [add_sub_assoc]
 

中文:
定理 dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd
  结论: {s : AffineSubspace 𝕜 P} {p₁ p₂ : P}
  证明: calc
    dist (r₁ • v +ᵥ p₁) (r₂ • v +ᵥ p₂) * dist (r₁ • v +ᵥ p₁) (r₂ • v +ᵥ p₂) =
        ‖p₁ -ᵥ p₂ + (r₁ - r₂) • v‖ * ‖p₁ -ᵥ p₂ + (r₁ - r₂) • v‖ := by
      rw [dist_eq_norm_vsub V (r₁ • v +ᵥ p₁)]; rw [vsub_vadd_eq_vsub_sub]; rw [vadd_vsub_assoc]; rw [sub_smul]; rw [add_comm]; rw [add_sub_assoc]
 

Depends on / 依赖: Submodule, Submodule.inner_right_of_mem_orthogonal, Submodule.smul_mem, add_comm, add_sub_assoc, dist_eq_norm_vsub, inner_right_of_mem_orthogonal, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero, smul_mem, sub_smul, vadd_vsub_assoc, vsub_mem_direction, vsub_vadd_eq_vsub_sub
-/
theorem dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd {s : AffineSubspace 𝕜 P} {p₁ p₂ : P}
    (hp₁ : p₁ in s) (hp₂ : p₂ in s) (r₁ r₂ : 𝕜) {v : V} (hv : v in s.directionᗮ) :
    dist (r₁ • v +ᵥ p₁) (r₂ • v +ᵥ p₂) * dist (r₁ • v +ᵥ p₁) (r₂ • v +ᵥ p₂) =
      dist p₁ p₂ * dist p₁ p₂ + ‖r₁ - r₂‖ * ‖r₁ - r₂‖ * (‖v‖ * ‖v‖) :=
  calc
    dist (r₁ • v +ᵥ p₁) (r₂ • v +ᵥ p₂) * dist (r₁ • v +ᵥ p₁) (r₂ • v +ᵥ p₂) =
        ‖p₁ -ᵥ p₂ + (r₁ - r₂) • v‖ * ‖p₁ -ᵥ p₂ + (r₁ - r₂) • v‖ := by
      rw [dist_eq_norm_vsub V (r₁ • v +ᵥ p₁)]; rw [vsub_vadd_eq_vsub_sub]; rw [vadd_vsub_assoc]; rw [sub_smul]; rw [add_comm]; rw [add_sub_assoc]
    _ = ‖p₁ -ᵥ p₂‖ * ‖p₁ -ᵥ p₂‖ + ‖(r₁ - r₂) • v‖ * ‖(r₁ - r₂) • v‖ :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
        (Submodule.inner_right_of_mem_orthogonal (vsub_mem_direction hp₁ hp₂)
          (Submodule.smul_mem _ _ hv))
    _ = dist p₁ p₂ * dist p₁ p₂ + ‖r₁ - r₂‖ * ‖r₁ - r₂‖ * (‖v‖ * ‖v‖) := by
      rw [norm_smul]; rw [dist_eq_norm_vsub V p₁]
      ring

/--
theorem `dist_eq_iff_dist_orthogonalProjection_eq` / 定理 `dist_eq_iff_dist_orthogonalProjection_eq`

English:
theorem dist_eq_iff_dist_orthogonalProjection_eq
  statement: {s : AffineSubspace 𝕜 P} [Nonempty s]
  proof: by
  rw [← mul_self_inj_of_nonneg dist_nonneg dist_nonneg]; rw [←
    mul_self_inj_of_nonneg dist_nonneg dist_nonneg]; rw [dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p₃ hp₁]; rw [dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p₃ hp₂]
  simp

中文:
定理 dist_eq_iff_dist_orthogonalProjection_eq
  结论: {s : AffineSubspace 𝕜 P} [Nonempty s]
  证明: by
  rw [← mul_self_inj_of_nonneg dist_nonneg dist_nonneg]; rw [←
    mul_self_inj_of_nonneg dist_nonneg dist_nonneg]; rw [dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p₃ hp₁]; rw [dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p₃ hp₂]
  simp

Depends on / 依赖: dist_nonneg, dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq, mul_self_inj_of_nonneg
-/
theorem dist_eq_iff_dist_orthogonalProjection_eq {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p₁ p₂ : P} (p₃ : P) (hp₁ : p₁ in s) (hp₂ : p₂ in s) :
    dist p₁ p₃ = dist p₂ p₃ ↔
      dist p₁ (orthogonalProjection s p₃) = dist p₂ (orthogonalProjection s p₃) := by
  rw [← mul_self_inj_of_nonneg dist_nonneg dist_nonneg]; rw [←
    mul_self_inj_of_nonneg dist_nonneg dist_nonneg]; rw [dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p₃ hp₁]; rw [dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p₃ hp₂]
  simp

/--
theorem `dist_set_eq_iff_dist_orthogonalProjection_eq` / 定理 `dist_set_eq_iff_dist_orthogonalProjection_eq`

English:
theorem dist_set_eq_iff_dist_orthogonalProjection_eq
  statement: {s : AffineSubspace 𝕜 P} [Nonempty s]
  proof: ⟨fun h _ hp₁ _ hp₂ hne =>
    (dist_eq_iff_dist_orthogonalProjection_eq p (hps hp₁) (hps hp₂)).1 (h hp₁ hp₂ hne),
    fun h _ hp₁ _ hp₂ hne =>
    (dist_eq_iff_dist_orthogonalProjection_eq p (hps hp₁) (hps hp₂)).2 (h hp₁ hp₂ hne)⟩

中文:
定理 dist_set_eq_iff_dist_orthogonalProjection_eq
  结论: {s : AffineSubspace 𝕜 P} [Nonempty s]
  证明: ⟨fun h _ hp₁ _ hp₂ hne =>
    (dist_eq_iff_dist_orthogonalProjection_eq p (hps hp₁) (hps hp₂)).1 (h hp₁ hp₂ hne),
    fun h _ hp₁ _ hp₂ hne =>
    (dist_eq_iff_dist_orthogonalProjection_eq p (hps hp₁) (hps hp₂)).2 (h hp₁ hp₂ hne)⟩

Depends on / 依赖: dist_eq_iff_dist_orthogonalProjection_eq
-/
theorem dist_set_eq_iff_dist_orthogonalProjection_eq {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {ps : Set P} (hps : ps subseteq s) (p : P) :
    (Set.Pairwise ps fun p₁ p₂ => dist p₁ p = dist p₂ p) ↔
      Set.Pairwise ps fun p₁ p₂ =>
        dist p₁ (orthogonalProjection s p) = dist p₂ (orthogonalProjection s p) :=
  ⟨fun h _ hp₁ _ hp₂ hne =>
    (dist_eq_iff_dist_orthogonalProjection_eq p (hps hp₁) (hps hp₂)).1 (h hp₁ hp₂ hne),
    fun h _ hp₁ _ hp₂ hne =>
    (dist_eq_iff_dist_orthogonalProjection_eq p (hps hp₁) (hps hp₂)).2 (h hp₁ hp₂ hne)⟩

/--
theorem `exists_dist_eq_iff_exists_dist_orthogonalProjection_eq` / 定理 `exists_dist_eq_iff_exists_dist_orthogonalProjection_eq`

English:
theorem exists_dist_eq_iff_exists_dist_orthogonalProjection_eq
  statement: {s : AffineSubspace 𝕜 P} [Nonempty s]
  proof: by
  have h := dist_set_eq_iff_dist_orthogonalProjection_eq hps p
  simp_rw [Set.pairwise_eq_iff_exists_eq] at h
  exact h

中文:
定理 exists_dist_eq_iff_exists_dist_orthogonalProjection_eq
  结论: {s : AffineSubspace 𝕜 P} [Nonempty s]
  证明: by
  have h := dist_set_eq_iff_dist_orthogonalProjection_eq hps p
  simp_rw [Set.pairwise_eq_iff_exists_eq] at h
  exact h

Depends on / 依赖: Set.pairwise_eq_iff_exists_eq, dist_set_eq_iff_dist_orthogonalProjection_eq, pairwise_eq_iff_exists_eq, simp_rw
-/
theorem exists_dist_eq_iff_exists_dist_orthogonalProjection_eq {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {ps : Set P} (hps : ps subseteq s) (p : P) :
    (exists r, forall p₁ in ps, dist p₁ p = r) ↔ exists r, forall p₁ in ps, dist p₁ ↑(orthogonalProjection s p) = r := by
  have h := dist_set_eq_iff_dist_orthogonalProjection_eq hps p
  simp_rw [Set.pairwise_eq_iff_exists_eq] at h
  exact h

/--
Definition of `reflection` / `reflection` 的定义

English:
definition reflection
  signature: (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection]
  body: letI x : P := Classical.arbitrary s
  AffineIsometryEquiv.vaddConst 𝕜 x
.symm.trans s.direction.reflection.toAffineIsometryEquiv
.trans AffineIsometryEquiv.vaddConst 𝕜 x

中文:
定义 reflection
  签名: (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection]
  定义体: letI x : P := Classical.arbitrary s
  AffineIsometryEquiv.vaddConst 𝕜 x
.symm.trans s.direction.reflection.toAffineIsometryEquiv
.trans AffineIsometryEquiv.vaddConst 𝕜 x

Depends on / 依赖: AffineIsometryEquiv, AffineIsometryEquiv.vaddConst, Classical, Classical.arbitrary, arbitrary, direction, reflection, s.direction.reflection.toAffineIsometryEquiv, symm.trans, toAffineIsometryEquiv, vaddConst
-/
def reflection (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection] :
    P ≃ᵃⁱ[𝕜] P :=
  letI x : P := Classical.arbitrary s
  AffineIsometryEquiv.vaddConst 𝕜 x
.symm.trans s.direction.reflection.toAffineIsometryEquiv
.trans AffineIsometryEquiv.vaddConst 𝕜 x

/--
theorem `reflection_apply` / 定理 `reflection_apply`

English:
theorem reflection_apply
  statement: (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection]
  proof: rfl

中文:
定理 reflection_apply
  结论: (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection]
  证明: rfl
-/
theorem reflection_apply (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection]
    (p : P) :
    reflection s p = s.direction.reflection (p -ᵥ Classical.arbitrary s)
      +ᵥ (Classical.arbitrary s : P) :=
  rfl

/--
theorem `reflection_apply_of_mem` / 定理 `reflection_apply_of_mem`

English:
theorem reflection_apply_of_mem
  statement: (s : AffineSubspace 𝕜 P) [Nonempty s]
  proof: by
  rw [reflection_apply]; rw [vadd_eq_vadd_iff_sub_eq_vsub]; rw [← map_sub]; rw [vsub_sub_vsub_cancel_left]; rw [s.direction.reflection_eq_self_iff]
  exact s.vsub_mem_direction (SetLike.coe_mem _) hx

中文:
定理 reflection_apply_of_mem
  结论: (s : AffineSubspace 𝕜 P) [Nonempty s]
  证明: by
  rw [reflection_apply]; rw [vadd_eq_vadd_iff_sub_eq_vsub]; rw [← map_sub]; rw [vsub_sub_vsub_cancel_left]; rw [s.direction.reflection_eq_self_iff]
  exact s.vsub_mem_direction (SetLike.coe_mem _) hx

Depends on / 依赖: SetLike, SetLike.coe_mem, coe_mem, direction, map_sub, reflection_apply, reflection_eq_self_iff, s.direction.reflection_eq_self_iff, s.vsub_mem_direction, vadd_eq_vadd_iff_sub_eq_vsub, vsub_mem_direction, vsub_sub_vsub_cancel_left
-/
theorem reflection_apply_of_mem (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) {x} (hx : x in s) :
    reflection s p = s.direction.reflection (p -ᵥ x) +ᵥ x := by
  rw [reflection_apply]; rw [vadd_eq_vadd_iff_sub_eq_vsub]; rw [← map_sub]; rw [vsub_sub_vsub_cancel_left]; rw [s.direction.reflection_eq_self_iff]
  exact s.vsub_mem_direction (SetLike.coe_mem _) hx

/--
theorem `reflection_apply'` / 定理 `reflection_apply'`

English:
theorem reflection_apply'
  statement: (s : AffineSubspace 𝕜 P) [Nonempty s]
  proof: by
  rw [reflection_apply]; rw [orthogonalProjection_apply']; rw [Submodule.coe_orthogonalProjectionOnto_apply]
  set x : P := ↑(Classical.arbitrary s)
  set v : V := s.direction.starProjection (p -ᵥ x)
  rw [Submodule.reflection_apply]; rw [two_smul]; rw [sub_eq_add_neg]; rw [neg_vsub_eq_vsub_rev];

中文:
定理 reflection_apply'
  结论: (s : AffineSubspace 𝕜 P) [Nonempty s]
  证明: by
  rw [reflection_apply]; rw [orthogonalProjection_apply']; rw [Submodule.coe_orthogonalProjectionOnto_apply]
  set x : P := ↑(Classical.arbitrary s)
  set v : V := s.direction.starProjection (p -ᵥ x)
  rw [Submodule.reflection_apply]; rw [two_smul]; rw [sub_eq_add_neg]; rw [neg_vsub_eq_vsub_rev];

Depends on / 依赖: Classical, Classical.arbitrary, Submodule, Submodule.coe_orthogonalProjectionOnto_apply, Submodule.reflection_apply, add_assoc, add_comm, add_vadd, arbitrary, coe_orthogonalProjectionOnto_apply, direction, neg_vsub_eq_vsub_rev, orthogonalProjection_apply, reflection_apply, s.direction.starProjection, starProjection, sub_eq_add_neg, two_smul, vadd_vsub_assoc
-/
theorem reflection_apply' (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    reflection s p = (↑(orthogonalProjection s p) -ᵥ p) +ᵥ (orthogonalProjection s p : P) := by
  rw [reflection_apply]; rw [orthogonalProjection_apply']; rw [Submodule.coe_orthogonalProjectionOnto_apply]
  set x : P := ↑(Classical.arbitrary s)
  set v : V := s.direction.starProjection (p -ᵥ x)
  rw [Submodule.reflection_apply]; rw [two_smul]; rw [sub_eq_add_neg]; rw [neg_vsub_eq_vsub_rev]; rw [add_assoc]; rw [add_comm v]; rw [add_vadd]; rw [vadd_vsub_assoc]

/--
theorem `eq_reflection_of_eq_subspace` / 定理 `eq_reflection_of_eq_subspace`

English:
theorem eq_reflection_of_eq_subspace
  statement: {s s' : AffineSubspace 𝕜 P} [Nonempty s] [Nonempty s']
  proof: by
  subst h
  rfl

中文:
定理 eq_reflection_of_eq_subspace
  结论: {s s' : AffineSubspace 𝕜 P} [Nonempty s] [Nonempty s']
  证明: by
  subst h
  rfl
-/
theorem eq_reflection_of_eq_subspace {s s' : AffineSubspace 𝕜 P} [Nonempty s] [Nonempty s']
    [s.direction.HasOrthogonalProjection] [s'.direction.HasOrthogonalProjection] (h : s = s')
    (p : P) : (reflection s p : P) = (reflection s' p : P) := by
  subst h
  rfl

/-- Reflecting twice in the same subspace. -/
@[simp]
/--
theorem `reflection_reflection` / 定理 `reflection_reflection`

English:
theorem reflection_reflection
  statement: (s : AffineSubspace 𝕜 P) [Nonempty s]
  proof: by
  simp [reflection, -AffineIsometryEquiv.map_vadd]

中文:
定理 reflection_reflection
  结论: (s : AffineSubspace 𝕜 P) [Nonempty s]
  证明: by
  simp [reflection, -AffineIsometryEquiv.map_vadd]

Depends on / 依赖: AffineIsometryEquiv, AffineIsometryEquiv.map_vadd, map_vadd, reflection
-/
theorem reflection_reflection (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) : reflection s (reflection s p) = p := by
  simp [reflection, -AffineIsometryEquiv.map_vadd]

/-- Reflection is its own inverse. -/
@[simp]
/--
theorem `reflection_symm` / 定理 `reflection_symm`

English:
theorem reflection_symm
  statement: (s : AffineSubspace 𝕜 P) [Nonempty s]
  proof: by
  ext
  rw [← (reflection s).injective.eq_iff]
  simp

中文:
定理 reflection_symm
  结论: (s : AffineSubspace 𝕜 P) [Nonempty s]
  证明: by
  ext
  rw [← (reflection s).injective.eq_iff]
  simp

Depends on / 依赖: eq_iff, injective, injective.eq_iff, reflection
-/
theorem reflection_symm (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] : (reflection s).symm = reflection s := by
  ext
  rw [← (reflection s).injective.eq_iff]
  simp

/--
theorem `reflection_involutive` / 定理 `reflection_involutive`

English:
theorem reflection_involutive
  statement: (s : AffineSubspace 𝕜 P) [Nonempty s]
  proof: reflection_reflection s

中文:
定理 reflection_involutive
  结论: (s : AffineSubspace 𝕜 P) [Nonempty s]
  证明: reflection_reflection s

Depends on / 依赖: reflection_reflection
-/
theorem reflection_involutive (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] : Function.Involutive (reflection s) :=
  reflection_reflection s

/--
theorem `reflection_eq_self_iff` / 定理 `reflection_eq_self_iff`

English:
theorem reflection_eq_self_iff
  statement: {s : AffineSubspace 𝕜 P} [Nonempty s]
  proof: by
  rw [reflection_apply]; rw [Eq.comm]; rw [eq_vadd_iff_vsub_eq]; rw [Eq.comm]; rw [s.direction.reflection_eq_self_iff]; rw [s.mem_direction_iff_eq_vsub_right (SetLike.coe_mem (Classical.arbitrary s))]
  simp

中文:
定理 reflection_eq_self_iff
  结论: {s : AffineSubspace 𝕜 P} [Nonempty s]
  证明: by
  rw [reflection_apply]; rw [Eq.comm]; rw [eq_vadd_iff_vsub_eq]; rw [Eq.comm]; rw [s.direction.reflection_eq_self_iff]; rw [s.mem_direction_iff_eq_vsub_right (SetLike.coe_mem (Classical.arbitrary s))]
  simp

Depends on / 依赖: Classical, Classical.arbitrary, Eq.comm, SetLike, SetLike.coe_mem, arbitrary, coe_mem, direction, eq_vadd_iff_vsub_eq, mem_direction_iff_eq_vsub_right, reflection_apply, reflection_eq_self_iff, s.direction.reflection_eq_self_iff, s.mem_direction_iff_eq_vsub_right
-/
theorem reflection_eq_self_iff {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) : reflection s p = p ↔ p in s := by
  rw [reflection_apply]; rw [Eq.comm]; rw [eq_vadd_iff_vsub_eq]; rw [Eq.comm]; rw [s.direction.reflection_eq_self_iff]; rw [s.mem_direction_iff_eq_vsub_right (SetLike.coe_mem (Classical.arbitrary s))]
  simp

/--
theorem `reflection_eq_iff_orthogonalProjection_eq` / 定理 `reflection_eq_iff_orthogonalProjection_eq`

English:
theorem reflection_eq_iff_orthogonalProjection_eq
  statement: (s₁ s₂ : AffineSubspace 𝕜 P) [Nonempty s₁]
  proof: by
  rw [reflection_apply']; rw [reflection_apply']
  constructor
  · intro h
    rw [← @vsub_eq_zero_iff_eq V]; rw [vsub_vadd_eq_vsub_sub]; rw [vadd_vsub_assoc]; rw [add_comm]; rw [add_sub_assoc]; rw [vsub_sub_vsub_cancel_right]; rw [←
      two_smul 𝕜 ((orthogonalProjection s₁ p : P) -ᵥ orthogonal

中文:
定理 reflection_eq_iff_orthogonalProjection_eq
  结论: (s₁ s₂ : AffineSubspace 𝕜 P) [Nonempty s₁]
  证明: by
  rw [reflection_apply']; rw [reflection_apply']
  constructor
  · intro h
    rw [← @vsub_eq_zero_iff_eq V]; rw [vsub_vadd_eq_vsub_sub]; rw [vadd_vsub_assoc]; rw [add_comm]; rw [add_sub_assoc]; rw [vsub_sub_vsub_cancel_right]; rw [←
      two_smul 𝕜 ((orthogonalProjection s₁ p : P) -ᵥ orthogonal

Depends on / 依赖: add_comm, add_sub_assoc, orthogonalProjection, reflection_apply, smul_eq_zero, two_smul, vadd_vsub_assoc, vsub_eq_zero_iff_eq, vsub_sub_vsub_cancel_right, vsub_vadd_eq_vsub_sub
-/
theorem reflection_eq_iff_orthogonalProjection_eq (s₁ s₂ : AffineSubspace 𝕜 P) [Nonempty s₁]
    [Nonempty s₂] [s₁.direction.HasOrthogonalProjection] [s₂.direction.HasOrthogonalProjection]
    (p : P) :
    reflection s₁ p = reflection s₂ p ↔
      (orthogonalProjection s₁ p : P) = orthogonalProjection s₂ p := by
  rw [reflection_apply']; rw [reflection_apply']
  constructor
  · intro h
    rw [← @vsub_eq_zero_iff_eq V]; rw [vsub_vadd_eq_vsub_sub]; rw [vadd_vsub_assoc]; rw [add_comm]; rw [add_sub_assoc]; rw [vsub_sub_vsub_cancel_right]; rw [←
      two_smul 𝕜 ((orthogonalProjection s₁ p : P) -ᵥ orthogonalProjection s₂ p)]; rw [smul_eq_zero] at h
    simpa using h
  · intro h
    rw [h]

/--
theorem `dist_reflection` / 定理 `dist_reflection`

English:
theorem dist_reflection
  statement: (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection]
  proof: by
  conv_lhs => rw [← reflection_reflection s p₁]
  exact (reflection s).dist_map _ _

中文:
定理 dist_reflection
  结论: (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection]
  证明: by
  conv_lhs => rw [← reflection_reflection s p₁]
  exact (reflection s).dist_map _ _

Depends on / 依赖: conv_lhs, dist_map, reflection, reflection_reflection
-/
theorem dist_reflection (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection]
    (p₁ p₂ : P) : dist p₁ (reflection s p₂) = dist (reflection s p₁) p₂ := by
  conv_lhs => rw [← reflection_reflection s p₁]
  exact (reflection s).dist_map _ _

/--
theorem `dist_reflection_eq_of_mem` / 定理 `dist_reflection_eq_of_mem`

English:
theorem dist_reflection_eq_of_mem
  statement: (s : AffineSubspace 𝕜 P) [Nonempty s]
  proof: by
  rw [← reflection_eq_self_iff p₁] at hp₁
  convert! (reflection s).dist_map p₁ p₂
  rw [hp₁]

中文:
定理 dist_reflection_eq_of_mem
  结论: (s : AffineSubspace 𝕜 P) [Nonempty s]
  证明: by
  rw [← reflection_eq_self_iff p₁] at hp₁
  convert! (reflection s).dist_map p₁ p₂
  rw [hp₁]

Depends on / 依赖: convert, dist_map, reflection, reflection_eq_self_iff
-/
theorem dist_reflection_eq_of_mem (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p₁ : P} (hp₁ : p₁ in s) (p₂ : P) :
    dist p₁ (reflection s p₂) = dist p₁ p₂ := by
  rw [← reflection_eq_self_iff p₁] at hp₁
  convert! (reflection s).dist_map p₁ p₂
  rw [hp₁]

/--
theorem `reflection_mem_of_le_of_mem` / 定理 `reflection_mem_of_le_of_mem`

English:
theorem reflection_mem_of_le_of_mem
  statement: {s₁ s₂ : AffineSubspace 𝕜 P} [Nonempty s₁]
  proof: by
  rw [reflection_apply']
  have ho : ↑(orthogonalProjection s₁ p) in s₂ := hle (orthogonalProjection_mem p)
  exact vadd_mem_of_mem_direction (vsub_mem_direction ho hp) ho

中文:
定理 reflection_mem_of_le_of_mem
  结论: {s₁ s₂ : AffineSubspace 𝕜 P} [Nonempty s₁]
  证明: by
  rw [reflection_apply']
  have ho : ↑(orthogonalProjection s₁ p) in s₂ := hle (orthogonalProjection_mem p)
  exact vadd_mem_of_mem_direction (vsub_mem_direction ho hp) ho

Depends on / 依赖: orthogonalProjection, orthogonalProjection_mem, reflection_apply, vadd_mem_of_mem_direction, vsub_mem_direction
-/
theorem reflection_mem_of_le_of_mem {s₁ s₂ : AffineSubspace 𝕜 P} [Nonempty s₁]
    [s₁.direction.HasOrthogonalProjection] (hle : s₁ <= s₂) {p : P} (hp : p in s₂) :
    reflection s₁ p in s₂ := by
  rw [reflection_apply']
  have ho : ↑(orthogonalProjection s₁ p) in s₂ := hle (orthogonalProjection_mem p)
  exact vadd_mem_of_mem_direction (vsub_mem_direction ho hp) ho

/--
theorem `reflection_orthogonal_vadd` / 定理 `reflection_orthogonal_vadd`

English:
theorem reflection_orthogonal_vadd
  statement: {s : AffineSubspace 𝕜 P} [Nonempty s]
  proof: by
  rw [reflection_apply']; rw [orthogonalProjection_vadd_eq_self hp hv]; rw [vsub_vadd_eq_vsub_sub]
  simp

中文:
定理 reflection_orthogonal_vadd
  结论: {s : AffineSubspace 𝕜 P} [Nonempty s]
  证明: by
  rw [reflection_apply']; rw [orthogonalProjection_vadd_eq_self hp hv]; rw [vsub_vadd_eq_vsub_sub]
  simp

Depends on / 依赖: orthogonalProjection_vadd_eq_self, reflection_apply, vsub_vadd_eq_vsub_sub
-/
theorem reflection_orthogonal_vadd {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p : P} (hp : p in s) {v : V} (hv : v in s.directionᗮ) :
    reflection s (v +ᵥ p) = -v +ᵥ p := by
  rw [reflection_apply']; rw [orthogonalProjection_vadd_eq_self hp hv]; rw [vsub_vadd_eq_vsub_sub]
  simp

/--
theorem `reflection_vadd_smul_vsub_orthogonalProjection` / 定理 `reflection_vadd_smul_vsub_orthogonalProjection`

English:
theorem reflection_vadd_smul_vsub_orthogonalProjection
  statement: {s : AffineSubspace 𝕜 P} [Nonempty s]
  proof: reflection_orthogonal_vadd hp₁
    (Submodule.smul_mem _ _ (vsub_orthogonalProjection_mem_direction_orthogonal s _))

中文:
定理 reflection_vadd_smul_vsub_orthogonalProjection
  结论: {s : AffineSubspace 𝕜 P} [Nonempty s]
  证明: reflection_orthogonal_vadd hp₁
    (Submodule.smul_mem _ _ (vsub_orthogonalProjection_mem_direction_orthogonal s _))

Depends on / 依赖: Submodule, Submodule.smul_mem, reflection_orthogonal_vadd, smul_mem, vsub_orthogonalProjection_mem_direction_orthogonal
-/
theorem reflection_vadd_smul_vsub_orthogonalProjection {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p₁ : P} (p₂ : P) (r : 𝕜) (hp₁ : p₁ in s) :
    reflection s (r • (p₂ -ᵥ orthogonalProjection s p₂) +ᵥ p₁) =
      -(r • (p₂ -ᵥ orthogonalProjection s p₂)) +ᵥ p₁ :=
  reflection_orthogonal_vadd hp₁
    (Submodule.smul_mem _ _ (vsub_orthogonalProjection_mem_direction_orthogonal s _))

variable [MetricSpace P₂] [NormedAddTorsor V₂ P₂]

/--
lemma `orthogonalProjection_map` / 引理 `orthogonalProjection_map`

English:
lemma orthogonalProjection_map
  statement: (s : AffineSubspace 𝕜 P) [Nonempty s]
  proof: by
  rw [coe_orthogonalProjection_eq_iff_mem]
  simp only [mem_map, AffineIsometry.coe_toAffineMap, AffineIsometry.map_eq_iff, exists_eq_right,
    SetLike.coe_mem, map_direction, AffineIsometry.linear_eq_linearIsometry, true_and]
  rw [← AffineIsometry.coe_toAffineMap]; rw [← AffineMap.linearMap_vs

中文:
引理 orthogonalProjection_map
  结论: (s : AffineSubspace 𝕜 P) [Nonempty s]
  证明: by
  rw [coe_orthogonalProjection_eq_iff_mem]
  simp only [mem_map, AffineIsometry.coe_toAffineMap, AffineIsometry.map_eq_iff, exists_eq_right,
    SetLike.coe_mem, map_direction, AffineIsometry.linear_eq_linearIsometry, true_and]
  rw [← AffineIsometry.coe_toAffineMap]; rw [← AffineMap.linearMap_vs
-/
@[simp] lemma orthogonalProjection_map (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (f : P ->ᵃⁱ[𝕜] P₂)
    [(s.map f.toAffineMap).direction.HasOrthogonalProjection] (p : P) :
    orthogonalProjection (s.map f.toAffineMap) (f p) = f (orthogonalProjection s p) := by
  rw [coe_orthogonalProjection_eq_iff_mem]
  simp only [mem_map, AffineIsometry.coe_toAffineMap, AffineIsometry.map_eq_iff, exists_eq_right,
    SetLike.coe_mem, map_direction, AffineIsometry.linear_eq_linearIsometry, true_and]
  rw [← AffineIsometry.coe_toAffineMap]; rw [← AffineMap.linearMap_vsub]; rw [Submodule.mem_orthogonal]
  intro u hu
  rw [Submodule.mem_map] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  rw [AffineIsometry.linear_eq_linearIsometry]; rw [LinearIsometry.coe_toLinearMap]; rw [LinearIsometry.inner_map_map]; rw [Submodule.inner_right_of_mem_orthogonal hv
      (vsub_orthogonalProjection_mem_direction_orthogonal _ _)]

/--
lemma `orthogonalProjection_subtype` / 引理 `orthogonalProjection_subtype`

English:
lemma orthogonalProjection_subtype
  statement: (s : AffineSubspace 𝕜 P) [Nonempty s] (s' : AffineSubspace 𝕜 s)
  proof: by
  rw [eq_comm]
  have : (s'.map s.subtypeₐᵢ.toAffineMap).direction.HasOrthogonalProjection := by
    rw [subtypeₐᵢ_toAffineMap]
    infer_instance
  convert! orthogonalProjection_map s' s.subtypeₐᵢ p

中文:
引理 orthogonalProjection_subtype
  结论: (s : AffineSubspace 𝕜 P) [Nonempty s] (s' : AffineSubspace 𝕜 s)
  证明: by
  rw [eq_comm]
  have : (s'.map s.subtypeₐᵢ.toAffineMap).direction.HasOrthogonalProjection := by
    rw [subtypeₐᵢ_toAffineMap]
    infer_instance
  convert! orthogonalProjection_map s' s.subtypeₐᵢ p

Depends on / 依赖: HasOrthogonalProjection, convert, direction, direction.HasOrthogonalProjection, eq_comm, infer_instance, orthogonalProjection_map, s.subtype, toAffineMap
-/
lemma orthogonalProjection_subtype (s : AffineSubspace 𝕜 P) [Nonempty s] (s' : AffineSubspace 𝕜 s)
    [Nonempty s'] [s'.direction.HasOrthogonalProjection]
    [(s'.map s.subtype).direction.HasOrthogonalProjection] (p : s) :
    (orthogonalProjection s' p : P) = orthogonalProjection (s'.map s.subtype) p := by
  rw [eq_comm]
  have : (s'.map s.subtypeₐᵢ.toAffineMap).direction.HasOrthogonalProjection := by
    rw [subtypeₐᵢ_toAffineMap]
    infer_instance
  convert! orthogonalProjection_map s' s.subtypeₐᵢ p

/--
lemma `reflection_map` / 引理 `reflection_map`

English:
lemma reflection_map
  statement: (s : AffineSubspace 𝕜 P) [Nonempty s]
  proof: by
  simp [reflection_apply']

中文:
引理 reflection_map
  结论: (s : AffineSubspace 𝕜 P) [Nonempty s]
  证明: by
  simp [reflection_apply']
-/
@[simp] lemma reflection_map (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (f : P ->ᵃⁱ[𝕜] P₂)
    [(s.map f.toAffineMap).direction.HasOrthogonalProjection] (p : P) :
    reflection (s.map f.toAffineMap) (f p) = f (reflection s p) := by
  simp [reflection_apply']

/--
lemma `reflection_subtype` / 引理 `reflection_subtype`

English:
lemma reflection_subtype
  statement: (s : AffineSubspace 𝕜 P) [Nonempty s] (s' : AffineSubspace 𝕜 s)
  proof: by
  simp [reflection_apply', orthogonalProjection_subtype]

中文:
引理 reflection_subtype
  结论: (s : AffineSubspace 𝕜 P) [Nonempty s] (s' : AffineSubspace 𝕜 s)
  证明: by
  simp [reflection_apply', orthogonalProjection_subtype]

Depends on / 依赖: orthogonalProjection_subtype, reflection_apply
-/
lemma reflection_subtype (s : AffineSubspace 𝕜 P) [Nonempty s] (s' : AffineSubspace 𝕜 s)
    [Nonempty s'] [s'.direction.HasOrthogonalProjection]
    [(s'.map s.subtype).direction.HasOrthogonalProjection] (p : s) :
    (reflection s' p : P) = reflection (s'.map s.subtype) p := by
  simp [reflection_apply', orthogonalProjection_subtype]

end EuclideanGeometry

namespace Affine

namespace Simplex

open EuclideanGeometry

variable {𝕜 : Type*} {V : Type*} {P : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
variable {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace 𝕜 V₂]

variable [MetricSpace P] [NormedAddTorsor V P]

/--
Definition of `orthogonalProjectionSpan` / `orthogonalProjectionSpan` 的定义

English:
definition orthogonalProjectionSpan
  signature: {n : Nat} (s : Simplex 𝕜 P n)
  body: orthogonalProjection (affineSpan 𝕜 (Set.range s.points))

中文:
定义 orthogonalProjectionSpan
  签名: {n : 自然数} (s : Simplex 𝕜 P n)
  定义体: orthogonalProjection (affineSpan 𝕜 (Set.range s.points))

Depends on / 依赖: Set.range, affineSpan, orthogonalProjection, points, s.points
-/
def orthogonalProjectionSpan {n : Nat} (s : Simplex 𝕜 P n) :
    P ->ᴬ[𝕜] affineSpan 𝕜 (Set.range s.points) :=
  orthogonalProjection (affineSpan 𝕜 (Set.range s.points))

/--
lemma `orthogonalProjectionSpan_congr` / 引理 `orthogonalProjectionSpan_congr`

English:
lemma orthogonalProjectionSpan_congr
  statement: {m n : Nat} {s₁ : Simplex 𝕜 P m} {s₂ : Simplex 𝕜 P n}
  proof: orthogonalProjection_congr (by rw [h]) hp

中文:
引理 orthogonalProjectionSpan_congr
  结论: {m n : 自然数} {s₁ : Simplex 𝕜 P m} {s₂ : Simplex 𝕜 P n}
  证明: orthogonalProjection_congr (by rw [h]) hp

Depends on / 依赖: orthogonalProjection_congr
-/
lemma orthogonalProjectionSpan_congr {m n : Nat} {s₁ : Simplex 𝕜 P m} {s₂ : Simplex 𝕜 P n}
    {p₁ p₂ : P} (h : Set.range s₁.points = Set.range s₂.points) (hp : p₁ = p₂) :
    (s₁.orthogonalProjectionSpan p₁ : P) = s₂.orthogonalProjectionSpan p₂ :=
  orthogonalProjection_congr (by rw [h]) hp

/--
lemma `orthogonalProjectionSpan_reindex` / 引理 `orthogonalProjectionSpan_reindex`

English:
lemma orthogonalProjectionSpan_reindex
  statement: {m n : Nat} (s : Simplex 𝕜 P m)
  proof: orthogonalProjectionSpan_congr (s.reindex_range_points e) rfl

中文:
引理 orthogonalProjectionSpan_reindex
  结论: {m n : 自然数} (s : Simplex 𝕜 P m)
  证明: orthogonalProjectionSpan_congr (s.reindex_range_points e) rfl
-/
@[simp] lemma orthogonalProjectionSpan_reindex {m n : Nat} (s : Simplex 𝕜 P m)
    (e : Fin (m + 1) ≃ Fin (n + 1)) (p : P) :
    ((s.reindex e).orthogonalProjectionSpan p : P) = s.orthogonalProjectionSpan p :=
  orthogonalProjectionSpan_congr (s.reindex_range_points e) rfl

/--
theorem `orthogonalProjection_vadd_smul_vsub_orthogonalProjection` / 定理 `orthogonalProjection_vadd_smul_vsub_orthogonalProjection`

English:
theorem orthogonalProjection_vadd_smul_vsub_orthogonalProjection
  statement: {n : Nat} (s : Simplex 𝕜 P n)
  proof: EuclideanGeometry.orthogonalProjection_vadd_smul_vsub_orthogonalProjection _ _ _

中文:
定理 orthogonalProjection_vadd_smul_vsub_orthogonalProjection
  结论: {n : 自然数} (s : Simplex 𝕜 P n)
  证明: EuclideanGeometry.orthogonalProjection_vadd_smul_vsub_orthogonalProjection _ _ _

Depends on / 依赖: EuclideanGeometry, EuclideanGeometry.orthogonalProjection_vadd_smul_vsub_orthogonalProjection, orthogonalProjection_vadd_smul_vsub_orthogonalProjection
-/
theorem orthogonalProjection_vadd_smul_vsub_orthogonalProjection {n : Nat} (s : Simplex 𝕜 P n)
    {p₁ : P} (p₂ : P) (r : 𝕜) (hp : p₁ in affineSpan 𝕜 (Set.range s.points)) :
    s.orthogonalProjectionSpan (r • (p₂ -ᵥ s.orthogonalProjectionSpan p₂ : V) +ᵥ p₁) = ⟨p₁, hp⟩ :=
  EuclideanGeometry.orthogonalProjection_vadd_smul_vsub_orthogonalProjection _ _ _

/--
theorem `coe_orthogonalProjection_vadd_smul_vsub_orthogonalProjection` / 定理 `coe_orthogonalProjection_vadd_smul_vsub_orthogonalProjection`

English:
theorem coe_orthogonalProjection_vadd_smul_vsub_orthogonalProjection
  statement: {n : Nat} {r₁ : 𝕜}
  proof: congrArg ((↑) : _ -> P) (orthogonalProjection_vadd_smul_vsub_orthogonalProjection _ _ _ hp₁o)

中文:
定理 coe_orthogonalProjection_vadd_smul_vsub_orthogonalProjection
  结论: {n : 自然数} {r₁ : 𝕜}
  证明: congrArg ((↑) : _ -> P) (orthogonalProjection_vadd_smul_vsub_orthogonalProjection _ _ _ hp₁o)

Depends on / 依赖: orthogonalProjection_vadd_smul_vsub_orthogonalProjection
-/
theorem coe_orthogonalProjection_vadd_smul_vsub_orthogonalProjection {n : Nat} {r₁ : 𝕜}
    (s : Simplex 𝕜 P n) {p p₁o : P} (hp₁o : p₁o in affineSpan 𝕜 (Set.range s.points)) :
    ↑(s.orthogonalProjectionSpan (r₁ • (p -ᵥ ↑(s.orthogonalProjectionSpan p)) +ᵥ p₁o)) = p₁o :=
  congrArg ((↑) : _ -> P) (orthogonalProjection_vadd_smul_vsub_orthogonalProjection _ _ _ hp₁o)

/--
theorem `dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq` / 定理 `dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq`

English:
theorem dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
  statement: {n : Nat}
  proof: EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq _ hp₁

@[simp]

中文:
定理 dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
  结论: {n : 自然数}
  证明: EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq _ hp₁

@[simp]

Depends on / 依赖: EuclideanGeometry, EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq, dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
-/
theorem dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq {n : Nat}
    (s : Simplex 𝕜 P n) {p₁ : P} (p₂ : P) (hp₁ : p₁ in affineSpan 𝕜 (Set.range s.points)) :
    dist p₁ p₂ * dist p₁ p₂ =
      dist p₁ (s.orthogonalProjectionSpan p₂) * dist p₁ (s.orthogonalProjectionSpan p₂) +
        dist p₂ (s.orthogonalProjectionSpan p₂) * dist p₂ (s.orthogonalProjectionSpan p₂) :=
  EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq _ hp₁

@[simp]
/--
lemma `orthogonalProjectionSpan_eq_point` / 引理 `orthogonalProjectionSpan_eq_point`

English:
lemma orthogonalProjectionSpan_eq_point
  given: (s : Simplex 𝕜 P 0) (p : P)
  proof: by
  rw [orthogonalProjectionSpan]
  convert! orthogonalProjection_affineSpan_singleton _ _
  simp [Fin.fin_one_eq_zero]

中文:
引理 orthogonalProjectionSpan_eq_point
  条件: (s : Simplex 𝕜 P 0) (p : P)
  证明: by
  rw [orthogonalProjectionSpan]
  convert! orthogonalProjection_affineSpan_singleton _ _
  simp [Fin.fin_one_eq_zero]

Depends on / 依赖: Fin.fin_one_eq_zero, convert, fin_one_eq_zero, orthogonalProjectionSpan, orthogonalProjection_affineSpan_singleton
-/
lemma orthogonalProjectionSpan_eq_point (s : Simplex 𝕜 P 0) (p : P) :
    s.orthogonalProjectionSpan p = s.points 0 := by
  rw [orthogonalProjectionSpan]
  convert! orthogonalProjection_affineSpan_singleton _ _
  simp [Fin.fin_one_eq_zero]

/--
lemma `orthogonalProjectionSpan_faceOpposite_eq_point_rev` / 引理 `orthogonalProjectionSpan_faceOpposite_eq_point_rev`

English:
lemma orthogonalProjectionSpan_faceOpposite_eq_point_rev
  statement: (s : Simplex 𝕜 P 1) (i : Fin 2)
  proof: by
  simp [faceOpposite_point_eq_point_rev]

中文:
引理 orthogonalProjectionSpan_faceOpposite_eq_point_rev
  结论: (s : Simplex 𝕜 P 1) (i : Fin 2)
  证明: by
  simp [faceOpposite_point_eq_point_rev]

Depends on / 依赖: faceOpposite_point_eq_point_rev
-/
lemma orthogonalProjectionSpan_faceOpposite_eq_point_rev (s : Simplex 𝕜 P 1) (i : Fin 2)
    (p : P) : (s.faceOpposite i).orthogonalProjectionSpan p = s.points i.rev := by
  simp [faceOpposite_point_eq_point_rev]

variable [MetricSpace P₂] [NormedAddTorsor V₂ P₂]

/--
lemma `orthogonalProjectionSpan_map` / 引理 `orthogonalProjectionSpan_map`

English:
lemma orthogonalProjectionSpan_map
  given: {n : Nat} (s : Simplex 𝕜 P n) (f : P ->ᵃⁱ[𝕜] P₂) (p : P)
  proof: by
  simp_rw [orthogonalProjectionSpan]
  convert! orthogonalProjection_map (affineSpan 𝕜 (Set.range s.points)) f p
  simp [AffineSubspace.map_span, Set.range_comp]

中文:
引理 orthogonalProjectionSpan_map
  条件: {n : 自然数} (s : Simplex 𝕜 P n) (f : P ->ᵃⁱ[𝕜] P₂) (p : P)
  证明: by
  simp_rw [orthogonalProjectionSpan]
  convert! orthogonalProjection_map (affineSpan 𝕜 (Set.range s.points)) f p
  simp [AffineSubspace.map_span, Set.range_comp]

Depends on / 依赖: AffineSubspace, AffineSubspace.map_span, Set.range, Set.range_comp, affineSpan, convert, map_span, orthogonalProjectionSpan, orthogonalProjection_map, points, range_comp, s.points, simp_rw
-/
lemma orthogonalProjectionSpan_map {n : Nat} (s : Simplex 𝕜 P n) (f : P ->ᵃⁱ[𝕜] P₂) (p : P) :
    (s.map f.toAffineMap f.injective).orthogonalProjectionSpan (f p) =
      f (s.orthogonalProjectionSpan p) := by
  simp_rw [orthogonalProjectionSpan]
  convert! orthogonalProjection_map (affineSpan 𝕜 (Set.range s.points)) f p
  simp [AffineSubspace.map_span, Set.range_comp]

/--
lemma `orthogonalProjectionSpan_restrict` / 引理 `orthogonalProjectionSpan_restrict`

English:
lemma orthogonalProjectionSpan_restrict
  statement: {n : Nat} (s : Simplex 𝕜 P n)
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    ((s.restrict S hS).orthogonalProjectionSpan p : P) = s.orthogonalProjectionSpan p := by
  rw [eq_comm]
  convert! (s.restrict S hS).orthogonalProjectionSpan_map S.subtypeₐᵢ p

中文:
引理 orthogonalProjectionSpan_restrict
  结论: {n : 自然数} (s : Simplex 𝕜 P n)
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    ((s.restrict S hS).orthogonalProjectionSpan p : P) = s.orthogonalProjectionSpan p := by
  rw [eq_comm]
  convert! (s.restrict S hS).orthogonalProjectionSpan_map S.subtypeₐᵢ p
-/
@[simp] lemma orthogonalProjectionSpan_restrict {n : Nat} (s : Simplex 𝕜 P n)
    (S : AffineSubspace 𝕜 P) (hS : affineSpan 𝕜 (Set.range s.points) <= S) (p : S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    ((s.restrict S hS).orthogonalProjectionSpan p : P) = s.orthogonalProjectionSpan p := by
  rw [eq_comm]
  convert! (s.restrict S hS).orthogonalProjectionSpan_map S.subtypeₐᵢ p

end Simplex

end Affine
