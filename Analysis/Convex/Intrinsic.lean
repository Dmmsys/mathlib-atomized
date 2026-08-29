/-
Copyright (c) 2023 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-!
# Intrinsic frontier and interior

This file defines the intrinsic frontier, interior and closure of a set in a normed additive torsor.
These are also known as relative frontier, interior, closure.

The intrinsic frontier/interior/closure of a set `s` is the frontier/interior/closure of `s`
considered as a set in its affine span.

The intrinsic interior is in general greater than the topological interior, the intrinsic frontier
in general less than the topological frontier, and the intrinsic closure in cases of interest the
same as the topological closure.

## Definitions

* `intrinsicInterior`: Intrinsic interior
* `intrinsicFrontier`: Intrinsic frontier
* `intrinsicClosure`: Intrinsic closure

## Results

The main results are:
* `AffineIsometry.intrinsicInterior_image`/`AffineIsometry.intrinsicFrontier_image`/
  `AffineIsometry.intrinsicClosure_image`: Intrinsic interiors/frontiers/closures commute with
  taking the image under an affine isometry.
* `Set.Nonempty.intrinsicInterior`: The intrinsic interior of a nonempty convex set is nonempty.

## References

* Chapter 8 of [Barry Simon, *Convexity*][simon2011]
* Chapter 1 of [Rolf Schneider, *Convex Bodies: The Brunn-Minkowski theory*][schneider2013].

## TODO

* `IsClosed s → IsExtreme 𝕜 s (intrinsicFrontier 𝕜 s)`
* `x ∈ s → y ∈ intrinsicInterior 𝕜 s → openSegment 𝕜 x y ⊆ intrinsicInterior 𝕜 s`
-/

@[expose] public section

open AffineSubspace Set Topology
open scoped Pointwise

variable {𝕜 V W Q P : Type*}

section AddTorsor

variable (𝕜) [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace P] [AddTorsor V P]
  {s t : Set P} {x : P}

/--
Definition of `intrinsicInterior` / `intrinsicInterior` 的定义

English:
definition intrinsicInterior
  signature: (s : Set P)
  body: (↑) '' interior ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)

中文:
定义 intrinsic整数erior
  签名: (s : 集合 P)
  定义体: (↑) '' interior ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)

Depends on / 依赖: affineSpan, interior
-/
def intrinsicInterior (s : Set P) : Set P :=
  (↑) '' interior ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)

/--
Definition of `intrinsicFrontier` / `intrinsicFrontier` 的定义

English:
definition intrinsicFrontier
  signature: (s : Set P)
  body: (↑) '' frontier ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)

中文:
定义 intrinsicFrontier
  签名: (s : 集合 P)
  定义体: (↑) '' frontier ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)

Depends on / 依赖: affineSpan, frontier
-/
def intrinsicFrontier (s : Set P) : Set P :=
  (↑) '' frontier ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)

/--
Definition of `intrinsicClosure` / `intrinsicClosure` 的定义

English:
definition intrinsicClosure
  signature: (s : Set P)
  body: (↑) '' closure ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)

中文:
定义 intrinsicClosure
  签名: (s : 集合 P)
  定义体: (↑) '' closure ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)

Depends on / 依赖: affineSpan, closure
-/
def intrinsicClosure (s : Set P) : Set P :=
  (↑) '' closure ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)

variable {𝕜}

@[simp]
/--
theorem `mem_intrinsicInterior` / 定理 `mem_intrinsicInterior`

English:
theorem mem_intrinsicInterior
  proof: mem_image _ _ _

@[simp]

中文:
定理 mem_intrinsic整数erior
  证明: mem_image _ _ _

@[simp]

Depends on / 依赖: mem_image
-/
theorem mem_intrinsicInterior :
    x in intrinsicInterior 𝕜 s ↔ exists y, y in interior ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s) ∧ ↑y = x :=
  mem_image _ _ _

@[simp]
/--
theorem `mem_intrinsicFrontier` / 定理 `mem_intrinsicFrontier`

English:
theorem mem_intrinsicFrontier
  proof: mem_image _ _ _

@[simp]

中文:
定理 mem_intrinsicFrontier
  证明: mem_image _ _ _

@[simp]

Depends on / 依赖: mem_image
-/
theorem mem_intrinsicFrontier :
    x in intrinsicFrontier 𝕜 s ↔ exists y, y in frontier ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s) ∧ ↑y = x :=
  mem_image _ _ _

@[simp]
/--
theorem `mem_intrinsicClosure` / 定理 `mem_intrinsicClosure`

English:
theorem mem_intrinsicClosure
  proof: mem_image _ _ _

中文:
定理 mem_intrinsicClosure
  证明: mem_image _ _ _

Depends on / 依赖: mem_image
-/
theorem mem_intrinsicClosure :
    x in intrinsicClosure 𝕜 s ↔ exists y, y in closure ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s) ∧ ↑y = x :=
  mem_image _ _ _

/--
theorem `intrinsicInterior_subset` / 定理 `intrinsicInterior_subset`

English:
theorem intrinsicInterior_subset
  statement: intrinsicInterior 𝕜 s subseteq s
  proof: image_subset_iff.2 interior_subset

中文:
定理 intrinsic整数erior_subset
  结论: intrinsic整数erior 𝕜 s subseteq s
  证明: image_subset_iff.2 interior_subset

Depends on / 依赖: image_subset_iff, interior_subset
-/
theorem intrinsicInterior_subset : intrinsicInterior 𝕜 s subseteq s :=
  image_subset_iff.2 interior_subset

/--
theorem `intrinsicFrontier_subset` / 定理 `intrinsicFrontier_subset`

English:
theorem intrinsicFrontier_subset
  given: (hs : IsClosed s)
  statement: intrinsicFrontier 𝕜 s subseteq s
  proof: image_subset_iff.2 (hs.preimage continuous_induced_dom).frontier_subset

中文:
定理 intrinsicFrontier_subset
  条件: (hs : 是闭集 s)
  结论: intrinsicFrontier 𝕜 s subseteq s
  证明: image_subset_iff.2 (hs.preimage continuous_induced_dom).frontier_subset

Depends on / 依赖: continuous_induced_dom, frontier_subset, hs.preimage, image_subset_iff, preimage
-/
theorem intrinsicFrontier_subset (hs : IsClosed s) : intrinsicFrontier 𝕜 s subseteq s :=
  image_subset_iff.2 (hs.preimage continuous_induced_dom).frontier_subset

/--
theorem `intrinsicFrontier_subset_intrinsicClosure` / 定理 `intrinsicFrontier_subset_intrinsicClosure`

English:
theorem intrinsicFrontier_subset_intrinsicClosure
  statement: intrinsicFrontier 𝕜 s subseteq intrinsicClosure 𝕜 s
  proof: image_mono frontier_subset_closure

中文:
定理 intrinsicFrontier_subset_intrinsicClosure
  结论: intrinsicFrontier 𝕜 s subseteq intrinsicClosure 𝕜 s
  证明: image_mono frontier_subset_closure

Depends on / 依赖: frontier_subset_closure, image_mono
-/
theorem intrinsicFrontier_subset_intrinsicClosure : intrinsicFrontier 𝕜 s subseteq intrinsicClosure 𝕜 s :=
  image_mono frontier_subset_closure

/--
theorem `subset_intrinsicClosure` / 定理 `subset_intrinsicClosure`

English:
theorem subset_intrinsicClosure
  statement: s subseteq intrinsicClosure 𝕜 s
  proof: fun x hx => ⟨⟨x, subset_affineSpan _ _ hx⟩, subset_closure hx, rfl⟩

@[simp]

中文:
定理 subset_intrinsicClosure
  结论: s subseteq intrinsicClosure 𝕜 s
  证明: fun x hx => ⟨⟨x, subset_affineSpan _ _ hx⟩, subset_closure hx, rfl⟩

@[simp]

Depends on / 依赖: subset_affineSpan, subset_closure
-/
theorem subset_intrinsicClosure : s subseteq intrinsicClosure 𝕜 s :=
  fun x hx => ⟨⟨x, subset_affineSpan _ _ hx⟩, subset_closure hx, rfl⟩

@[simp]
/--
theorem `intrinsicInterior_empty` / 定理 `intrinsicInterior_empty`

English:
theorem intrinsicInterior_empty
  statement: intrinsicInterior 𝕜 (∅ : Set P) = ∅
  proof: by simp [intrinsicInterior]

@[simp]

中文:
定理 intrinsic整数erior_empty
  结论: intrinsic整数erior 𝕜 (∅ : 集合 P) = ∅
  证明: by simp [intrinsicInterior]

@[simp]

Depends on / 依赖: intrinsicInterior
-/
theorem intrinsicInterior_empty : intrinsicInterior 𝕜 (∅ : Set P) = ∅ := by simp [intrinsicInterior]

@[simp]
/--
theorem `intrinsicFrontier_empty` / 定理 `intrinsicFrontier_empty`

English:
theorem intrinsicFrontier_empty
  statement: intrinsicFrontier 𝕜 (∅ : Set P) = ∅
  proof: by simp [intrinsicFrontier]

@[simp]

中文:
定理 intrinsicFrontier_empty
  结论: intrinsicFrontier 𝕜 (∅ : 集合 P) = ∅
  证明: by simp [intrinsicFrontier]

@[simp]

Depends on / 依赖: intrinsicFrontier
-/
theorem intrinsicFrontier_empty : intrinsicFrontier 𝕜 (∅ : Set P) = ∅ := by simp [intrinsicFrontier]

@[simp]
/--
theorem `intrinsicClosure_empty` / 定理 `intrinsicClosure_empty`

English:
theorem intrinsicClosure_empty
  statement: intrinsicClosure 𝕜 (∅ : Set P) = ∅
  proof: by simp [intrinsicClosure]

@[simp]

中文:
定理 intrinsicClosure_empty
  结论: intrinsicClosure 𝕜 (∅ : 集合 P) = ∅
  证明: by simp [intrinsicClosure]

@[simp]

Depends on / 依赖: intrinsicClosure
-/
theorem intrinsicClosure_empty : intrinsicClosure 𝕜 (∅ : Set P) = ∅ := by simp [intrinsicClosure]

@[simp]
/--
theorem `intrinsicClosure_nonempty` / 定理 `intrinsicClosure_nonempty`

English:
theorem intrinsicClosure_nonempty
  statement: (intrinsicClosure 𝕜 s).Nonempty ↔ s.Nonempty
  proof: ⟨by simp_rw [nonempty_iff_ne_empty]; rintro h rfl; exact h intrinsicClosure_empty,
    Nonempty.mono subset_intrinsicClosure⟩

alias ⟨Set.Nonempty.ofIntrinsicClosure, Set.Nonempty.intrinsicClosure⟩ := intrinsicClosure_nonempty

@[simp]

中文:
定理 intrinsicClosure_nonempty
  结论: (intrinsicClosure 𝕜 s).非空 ↔ s.非空
  证明: ⟨by simp_rw [nonempty_iff_ne_empty]; rintro h rfl; exact h intrinsicClosure_empty,
    Nonempty.mono subset_intrinsicClosure⟩

alias ⟨Set.Nonempty.ofIntrinsicClosure, Set.Nonempty.intrinsicClosure⟩ := intrinsicClosure_nonempty

@[simp]

Depends on / 依赖: Nonempty, Nonempty.mono, intrinsicClosure_empty, nonempty_iff_ne_empty, simp_rw, subset_intrinsicClosure
-/
theorem intrinsicClosure_nonempty : (intrinsicClosure 𝕜 s).Nonempty ↔ s.Nonempty :=
  ⟨by simp_rw [nonempty_iff_ne_empty]; rintro h rfl; exact h intrinsicClosure_empty,
    Nonempty.mono subset_intrinsicClosure⟩

alias ⟨Set.Nonempty.ofIntrinsicClosure, Set.Nonempty.intrinsicClosure⟩ := intrinsicClosure_nonempty

@[simp]
/--
theorem `intrinsicInterior_singleton` / 定理 `intrinsicInterior_singleton`

English:
theorem intrinsicInterior_singleton
  given: (x : P)
  statement: intrinsicInterior 𝕜 ({x} : Set P) = {x}
  proof: by
  simp only [intrinsicInterior, preimage_coe_affineSpan_singleton, interior_univ, image_univ,
    Subtype.range_coe_subtype, mem_affineSpan_singleton, ofPred_eq_eq_singleton]

@[simp]

中文:
定理 intrinsic整数erior_singleton
  条件: (x : P)
  结论: intrinsic整数erior 𝕜 ({x} : 集合 P) = {x}
  证明: by
  simp only [intrinsicInterior, preimage_coe_affineSpan_singleton, interior_univ, image_univ,
    Subtype.range_coe_subtype, mem_affineSpan_singleton, ofPred_eq_eq_singleton]

@[simp]

Depends on / 依赖: Subtype, Subtype.range_coe_subtype, image_univ, interior_univ, intrinsicInterior, mem_affineSpan_singleton, ofPred_eq_eq_singleton, preimage_coe_affineSpan_singleton, range_coe_subtype
-/
theorem intrinsicInterior_singleton (x : P) : intrinsicInterior 𝕜 ({x} : Set P) = {x} := by
  simp only [intrinsicInterior, preimage_coe_affineSpan_singleton, interior_univ, image_univ,
    Subtype.range_coe_subtype, mem_affineSpan_singleton, ofPred_eq_eq_singleton]

@[simp]
/--
theorem `intrinsicFrontier_singleton` / 定理 `intrinsicFrontier_singleton`

English:
theorem intrinsicFrontier_singleton
  given: (x : P)
  statement: intrinsicFrontier 𝕜 ({x} : Set P) = ∅
  proof: by
  rw [intrinsicFrontier]; rw [preimage_coe_affineSpan_singleton]; rw [frontier_univ]; rw [image_empty]

@[simp]

中文:
定理 intrinsicFrontier_singleton
  条件: (x : P)
  结论: intrinsicFrontier 𝕜 ({x} : 集合 P) = ∅
  证明: by
  rw [intrinsicFrontier]; rw [preimage_coe_affineSpan_singleton]; rw [frontier_univ]; rw [image_empty]

@[simp]

Depends on / 依赖: frontier_univ, image_empty, intrinsicFrontier, preimage_coe_affineSpan_singleton
-/
theorem intrinsicFrontier_singleton (x : P) : intrinsicFrontier 𝕜 ({x} : Set P) = ∅ := by
  rw [intrinsicFrontier]; rw [preimage_coe_affineSpan_singleton]; rw [frontier_univ]; rw [image_empty]

@[simp]
/--
theorem `intrinsicClosure_singleton` / 定理 `intrinsicClosure_singleton`

English:
theorem intrinsicClosure_singleton
  given: (x : P)
  statement: intrinsicClosure 𝕜 ({x} : Set P) = {x}
  proof: by
  simp only [intrinsicClosure, preimage_coe_affineSpan_singleton, closure_univ, image_univ,
    Subtype.range_coe_subtype, mem_affineSpan_singleton, ofPred_eq_eq_singleton]

中文:
定理 intrinsicClosure_singleton
  条件: (x : P)
  结论: intrinsicClosure 𝕜 ({x} : 集合 P) = {x}
  证明: by
  simp only [intrinsicClosure, preimage_coe_affineSpan_singleton, closure_univ, image_univ,
    Subtype.range_coe_subtype, mem_affineSpan_singleton, ofPred_eq_eq_singleton]

Depends on / 依赖: Subtype, Subtype.range_coe_subtype, closure_univ, image_univ, intrinsicClosure, mem_affineSpan_singleton, ofPred_eq_eq_singleton, preimage_coe_affineSpan_singleton, range_coe_subtype
-/
theorem intrinsicClosure_singleton (x : P) : intrinsicClosure 𝕜 ({x} : Set P) = {x} := by
  simp only [intrinsicClosure, preimage_coe_affineSpan_singleton, closure_univ, image_univ,
    Subtype.range_coe_subtype, mem_affineSpan_singleton, ofPred_eq_eq_singleton]



/--
theorem `intrinsicClosure_mono` / 定理 `intrinsicClosure_mono`

English:
theorem intrinsicClosure_mono
  given: (h : s subseteq t)
  statement: intrinsicClosure 𝕜 s subseteq intrinsicClosure 𝕜 t
  proof: by
  refine image_subset_iff.2 fun x hx => ?_
  refine ⟨Set.inclusion (affineSpan_mono _ h) x, ?_, rfl⟩
  refine (continuous_inclusion (affineSpan_mono _ h)).closure_preimage_subset _ (closure_mono ?_ hx)
  exact fun y hy => h hy

中文:
定理 intrinsicClosure_mono
  条件: (h : s subseteq t)
  结论: intrinsicClosure 𝕜 s subseteq intrinsicClosure 𝕜 t
  证明: by
  refine image_subset_iff.2 fun x hx => ?_
  refine ⟨Set.inclusion (affineSpan_mono _ h) x, ?_, rfl⟩
  refine (continuous_inclusion (affineSpan_mono _ h)).closure_preimage_subset _ (closure_mono ?_ hx)
  exact fun y hy => h hy

Depends on / 依赖: Set.inclusion, affineSpan_mono, closure_mono, closure_preimage_subset, continuous_inclusion, image_subset_iff, inclusion
-/
theorem intrinsicClosure_mono (h : s subseteq t) : intrinsicClosure 𝕜 s subseteq intrinsicClosure 𝕜 t := by
  refine image_subset_iff.2 fun x hx => ?_
  refine ⟨Set.inclusion (affineSpan_mono _ h) x, ?_, rfl⟩
  refine (continuous_inclusion (affineSpan_mono _ h)).closure_preimage_subset _ (closure_mono ?_ hx)
  exact fun y hy => h hy

/--
theorem `interior_subset_intrinsicInterior` / 定理 `interior_subset_intrinsicInterior`

English:
theorem interior_subset_intrinsicInterior
  statement: interior s subseteq intrinsicInterior 𝕜 s
  proof: fun x hx => ⟨⟨x, subset_affineSpan _ _ interior_subset hx⟩,
    preimage_interior_subset_interior_preimage continuous_subtype_val hx, rfl⟩

中文:
定理 interior_subset_intrinsic整数erior
  结论: interior s subseteq intrinsic整数erior 𝕜 s
  证明: fun x hx => ⟨⟨x, subset_affineSpan _ _ interior_subset hx⟩,
    preimage_interior_subset_interior_preimage continuous_subtype_val hx, rfl⟩

Depends on / 依赖: continuous_subtype_val, interior_subset, preimage_interior_subset_interior_preimage, subset_affineSpan
-/
theorem interior_subset_intrinsicInterior : interior s subseteq intrinsicInterior 𝕜 s :=
fun x hx => ⟨⟨x, subset_affineSpan _ _ interior_subset hx⟩,
    preimage_interior_subset_interior_preimage continuous_subtype_val hx, rfl⟩

/--
theorem `intrinsicClosure_subset_closure` / 定理 `intrinsicClosure_subset_closure`

English:
theorem intrinsicClosure_subset_closure
  statement: intrinsicClosure 𝕜 s subseteq closure s
  proof: image_subset_iff.2 continuous_subtype_val.closure_preimage_subset _

中文:
定理 intrinsicClosure_subset_closure
  结论: intrinsicClosure 𝕜 s subseteq closure s
  证明: image_subset_iff.2 continuous_subtype_val.closure_preimage_subset _

Depends on / 依赖: closure_preimage_subset, continuous_subtype_val, continuous_subtype_val.closure_preimage_subset, image_subset_iff
-/
theorem intrinsicClosure_subset_closure : intrinsicClosure 𝕜 s subseteq closure s :=
image_subset_iff.2 continuous_subtype_val.closure_preimage_subset _

/--
theorem `intrinsicFrontier_subset_frontier` / 定理 `intrinsicFrontier_subset_frontier`

English:
theorem intrinsicFrontier_subset_frontier
  statement: intrinsicFrontier 𝕜 s subseteq frontier s
  proof: image_subset_iff.2 continuous_subtype_val.frontier_preimage_subset _

中文:
定理 intrinsicFrontier_subset_frontier
  结论: intrinsicFrontier 𝕜 s subseteq frontier s
  证明: image_subset_iff.2 continuous_subtype_val.frontier_preimage_subset _

Depends on / 依赖: continuous_subtype_val, continuous_subtype_val.frontier_preimage_subset, frontier_preimage_subset, image_subset_iff
-/
theorem intrinsicFrontier_subset_frontier : intrinsicFrontier 𝕜 s subseteq frontier s :=
image_subset_iff.2 continuous_subtype_val.frontier_preimage_subset _

/--
theorem `intrinsicClosure_subset_affineSpan` / 定理 `intrinsicClosure_subset_affineSpan`

English:
theorem intrinsicClosure_subset_affineSpan
  statement: intrinsicClosure 𝕜 s subseteq affineSpan 𝕜 s
  proof: (image_subset_range _ _).trans Subtype.range_coe.subset

@[simp]

中文:
定理 intrinsicClosure_subset_affineSpan
  结论: intrinsicClosure 𝕜 s subseteq affineSpan 𝕜 s
  证明: (image_subset_range _ _).trans Subtype.range_coe.subset

@[simp]

Depends on / 依赖: Subtype, Subtype.range_coe.subset, image_subset_range, range_coe, subset
-/
theorem intrinsicClosure_subset_affineSpan : intrinsicClosure 𝕜 s subseteq affineSpan 𝕜 s :=
  (image_subset_range _ _).trans Subtype.range_coe.subset

@[simp]
/--
theorem `intrinsicClosure_sdiff_intrinsicFrontier` / 定理 `intrinsicClosure_sdiff_intrinsicFrontier`

English:
theorem intrinsicClosure_sdiff_intrinsicFrontier
  given: (s : Set P)
  proof: (image_sdiff Subtype.coe_injective _ _).symm.trans by
    rw [closure_sdiff_frontier]; rw [intrinsicInterior]

@[deprecated (since := "2026-06-03")]
alias intrinsicClosure_diff_intrinsicFrontier := intrinsicClosure_sdiff_intrinsicFrontier

@[simp]

中文:
定理 intrinsicClosure_sdiff_intrinsicFrontier
  条件: (s : 集合 P)
  证明: (image_sdiff Subtype.coe_injective _ _).symm.trans by
    rw [closure_sdiff_frontier]; rw [intrinsicInterior]

@[deprecated (since := "2026-06-03")]
alias intrinsicClosure_diff_intrinsicFrontier := intrinsicClosure_sdiff_intrinsicFrontier

@[simp]

Depends on / 依赖: Subtype, Subtype.coe_injective, closure_sdiff_frontier, coe_injective, image_sdiff, intrinsicInterior, symm.trans
-/
theorem intrinsicClosure_sdiff_intrinsicFrontier (s : Set P) :
    intrinsicClosure 𝕜 s \ intrinsicFrontier 𝕜 s = intrinsicInterior 𝕜 s :=
(image_sdiff Subtype.coe_injective _ _).symm.trans by
    rw [closure_sdiff_frontier]; rw [intrinsicInterior]

@[deprecated (since := "2026-06-03")]
alias intrinsicClosure_diff_intrinsicFrontier := intrinsicClosure_sdiff_intrinsicFrontier

@[simp]
/--
theorem `intrinsicClosure_sdiff_intrinsicInterior` / 定理 `intrinsicClosure_sdiff_intrinsicInterior`

English:
theorem intrinsicClosure_sdiff_intrinsicInterior
  given: (s : Set P)
  proof: (image_sdiff Subtype.coe_injective _ _).symm

@[deprecated (since := "2026-06-03")]
alias intrinsicClosure_diff_intrinsicInterior := intrinsicClosure_sdiff_intrinsicInterior

@[simp]

中文:
定理 intrinsicClosure_sdiff_intrinsic整数erior
  条件: (s : 集合 P)
  证明: (image_sdiff Subtype.coe_injective _ _).symm

@[deprecated (since := "2026-06-03")]
alias intrinsicClosure_diff_intrinsicInterior := intrinsicClosure_sdiff_intrinsicInterior

@[simp]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective, image_sdiff
-/
theorem intrinsicClosure_sdiff_intrinsicInterior (s : Set P) :
    intrinsicClosure 𝕜 s \ intrinsicInterior 𝕜 s = intrinsicFrontier 𝕜 s :=
  (image_sdiff Subtype.coe_injective _ _).symm

@[deprecated (since := "2026-06-03")]
alias intrinsicClosure_diff_intrinsicInterior := intrinsicClosure_sdiff_intrinsicInterior

@[simp]
/--
theorem `intrinsicInterior_union_intrinsicFrontier` / 定理 `intrinsicInterior_union_intrinsicFrontier`

English:
theorem intrinsicInterior_union_intrinsicFrontier
  given: (s : Set P)
  proof: by
  simp [intrinsicClosure, intrinsicInterior, intrinsicFrontier, closure_eq_interior_union_frontier,
    image_union]

@[simp]

中文:
定理 intrinsic整数erior_union_intrinsicFrontier
  条件: (s : 集合 P)
  证明: by
  simp [intrinsicClosure, intrinsicInterior, intrinsicFrontier, closure_eq_interior_union_frontier,
    image_union]

@[simp]

Depends on / 依赖: closure_eq_interior_union_frontier, image_union, intrinsicClosure, intrinsicFrontier, intrinsicInterior
-/
theorem intrinsicInterior_union_intrinsicFrontier (s : Set P) :
    intrinsicInterior 𝕜 s union intrinsicFrontier 𝕜 s = intrinsicClosure 𝕜 s := by
  simp [intrinsicClosure, intrinsicInterior, intrinsicFrontier, closure_eq_interior_union_frontier,
    image_union]

@[simp]
/--
theorem `intrinsicFrontier_union_intrinsicInterior` / 定理 `intrinsicFrontier_union_intrinsicInterior`

English:
theorem intrinsicFrontier_union_intrinsicInterior
  given: (s : Set P)
  proof: by
  rw [union_comm]; rw [intrinsicInterior_union_intrinsicFrontier]

中文:
定理 intrinsicFrontier_union_intrinsic整数erior
  条件: (s : 集合 P)
  证明: by
  rw [union_comm]; rw [intrinsicInterior_union_intrinsicFrontier]

Depends on / 依赖: intrinsicInterior_union_intrinsicFrontier, union_comm
-/
theorem intrinsicFrontier_union_intrinsicInterior (s : Set P) :
    intrinsicFrontier 𝕜 s union intrinsicInterior 𝕜 s = intrinsicClosure 𝕜 s := by
  rw [union_comm]; rw [intrinsicInterior_union_intrinsicFrontier]

/--
theorem `isClosed_intrinsicClosure` / 定理 `isClosed_intrinsicClosure`

English:
theorem isClosed_intrinsicClosure
  given: (hs : IsClosed (affineSpan 𝕜 s : Set P))
  proof: hs.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_closure

中文:
定理 isClosed_intrinsicClosure
  条件: (hs : 是闭集 (affineSpan 𝕜 s : 集合 P))
  证明: hs.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_closure

Depends on / 依赖: hs.isClosedEmbedding_subtypeVal.isClosedMap, isClosedEmbedding_subtypeVal, isClosedMap, isClosed_closure
-/
theorem isClosed_intrinsicClosure (hs : IsClosed (affineSpan 𝕜 s : Set P)) :
    IsClosed (intrinsicClosure 𝕜 s) :=
  hs.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_closure

/--
theorem `isClosed_intrinsicFrontier` / 定理 `isClosed_intrinsicFrontier`

English:
theorem isClosed_intrinsicFrontier
  given: (hs : IsClosed (affineSpan 𝕜 s : Set P))
  proof: hs.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_frontier

@[simp]

中文:
定理 isClosed_intrinsicFrontier
  条件: (hs : 是闭集 (affineSpan 𝕜 s : 集合 P))
  证明: hs.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_frontier

@[simp]

Depends on / 依赖: hs.isClosedEmbedding_subtypeVal.isClosedMap, isClosedEmbedding_subtypeVal, isClosedMap, isClosed_frontier
-/
theorem isClosed_intrinsicFrontier (hs : IsClosed (affineSpan 𝕜 s : Set P)) :
    IsClosed (intrinsicFrontier 𝕜 s) :=
  hs.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_frontier

@[simp]
/--
theorem `affineSpan_intrinsicClosure` / 定理 `affineSpan_intrinsicClosure`

English:
theorem affineSpan_intrinsicClosure
  given: (s : Set P)
  proof: (affineSpan_le.2 intrinsicClosure_subset_affineSpan).antisymm
    affineSpan_mono _ subset_intrinsicClosure

中文:
定理 affineSpan_intrinsicClosure
  条件: (s : 集合 P)
  证明: (affineSpan_le.2 intrinsicClosure_subset_affineSpan).antisymm
    affineSpan_mono _ subset_intrinsicClosure

Depends on / 依赖: affineSpan_le, affineSpan_mono, antisymm, intrinsicClosure_subset_affineSpan, subset_intrinsicClosure
-/
theorem affineSpan_intrinsicClosure (s : Set P) :
    affineSpan 𝕜 (intrinsicClosure 𝕜 s) = affineSpan 𝕜 s :=
(affineSpan_le.2 intrinsicClosure_subset_affineSpan).antisymm
    affineSpan_mono _ subset_intrinsicClosure

/--
theorem `IsClosed.intrinsicClosure` / 定理 `IsClosed.intrinsicClosure`

English:
theorem IsClosed.intrinsicClosure
  given: (hs : IsClosed ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s))
  proof: by
  rw [intrinsicClosure]; rw [hs.closure_eq]; rw [image_preimage_eq_of_subset]
  exact (subset_affineSpan _ _).trans Subtype.range_coe.superset

@[simp]

中文:
定理 是闭集.intrinsicClosure
  条件: (hs : 是闭集 ((↑) ⁻¹' s : 集合 <| affineSpan 𝕜 s))
  证明: by
  rw [intrinsicClosure]; rw [hs.closure_eq]; rw [image_preimage_eq_of_subset]
  exact (subset_affineSpan _ _).trans Subtype.range_coe.superset

@[simp]
-/
protected theorem IsClosed.intrinsicClosure (hs : IsClosed ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)) :
    intrinsicClosure 𝕜 s = s := by
  rw [intrinsicClosure]; rw [hs.closure_eq]; rw [image_preimage_eq_of_subset]
  exact (subset_affineSpan _ _).trans Subtype.range_coe.superset

@[simp]
/--
theorem `intrinsicClosure_idem` / 定理 `intrinsicClosure_idem`

English:
theorem intrinsicClosure_idem
  given: (s : Set P)
  proof: by
  refine IsClosed.intrinsicClosure ?_
  set t := affineSpan 𝕜 (intrinsicClosure 𝕜 s) with ht
  clear_value t
  obtain rfl := ht.trans (affineSpan_intrinsicClosure _)
  rw [intrinsicClosure]; rw [preimage_image_eq _ Subtype.coe_injective]
  exact isClosed_closure

中文:
定理 intrinsicClosure_idem
  条件: (s : 集合 P)
  证明: by
  refine IsClosed.intrinsicClosure ?_
  set t := affineSpan 𝕜 (intrinsicClosure 𝕜 s) with ht
  clear_value t
  obtain rfl := ht.trans (affineSpan_intrinsicClosure _)
  rw [intrinsicClosure]; rw [preimage_image_eq _ Subtype.coe_injective]
  exact isClosed_closure

Depends on / 依赖: IsClosed, IsClosed.intrinsicClosure, Subtype, Subtype.coe_injective, affineSpan, affineSpan_intrinsicClosure, clear_value, coe_injective, ht.trans, intrinsicClosure, isClosed_closure, preimage_image_eq
-/
theorem intrinsicClosure_idem (s : Set P) :
    intrinsicClosure 𝕜 (intrinsicClosure 𝕜 s) = intrinsicClosure 𝕜 s := by
  refine IsClosed.intrinsicClosure ?_
  set t := affineSpan 𝕜 (intrinsicClosure 𝕜 s) with ht
  clear_value t
  obtain rfl := ht.trans (affineSpan_intrinsicClosure _)
  rw [intrinsicClosure]; rw [preimage_image_eq _ Subtype.coe_injective]
  exact isClosed_closure

/--
theorem `intrinsicClosure_eq_closure_inter_affineSpan` / 定理 `intrinsicClosure_eq_closure_inter_affineSpan`

English:
theorem intrinsicClosure_eq_closure_inter_affineSpan
  given: (s : Set P)
  proof: by
  have h : Topology.IsInducing ((↑) : affineSpan 𝕜 s -> P) := .subtypeVal
  rw [intrinsicClosure]; rw [h.closure_eq_preimage_closure_image]; rw [Set.image_preimage_eq_inter_range]; rw [Set.image_preimage_eq_of_subset ?_]; rw [Subtype.range_coe]
  rw [Subtype.range_coe]
  apply subset_affineSpan

中文:
定理 intrinsicClosure_eq_closure_inter_affineSpan
  条件: (s : 集合 P)
  证明: by
  have h : Topology.IsInducing ((↑) : affineSpan 𝕜 s -> P) := .subtypeVal
  rw [intrinsicClosure]; rw [h.closure_eq_preimage_closure_image]; rw [Set.image_preimage_eq_inter_range]; rw [Set.image_preimage_eq_of_subset ?_]; rw [Subtype.range_coe]
  rw [Subtype.range_coe]
  apply subset_affineSpan

Depends on / 依赖: IsInducing, Set.image_preimage_eq_inter_range, Set.image_preimage_eq_of_subset, Subtype, Subtype.range_coe, Topology, Topology.IsInducing, affineSpan, closure_eq_preimage_closure_image, h.closure_eq_preimage_closure_image, image_preimage_eq_inter_range, image_preimage_eq_of_subset, intrinsicClosure, range_coe, subset_affineSpan, subtypeVal
-/
theorem intrinsicClosure_eq_closure_inter_affineSpan (s : Set P) :
    intrinsicClosure 𝕜 s = closure s inter affineSpan 𝕜 s := by
  have h : Topology.IsInducing ((↑) : affineSpan 𝕜 s -> P) := .subtypeVal
  rw [intrinsicClosure]; rw [h.closure_eq_preimage_closure_image]; rw [Set.image_preimage_eq_inter_range]; rw [Set.image_preimage_eq_of_subset ?_]; rw [Subtype.range_coe]
  rw [Subtype.range_coe]
  apply subset_affineSpan

/--
theorem `intrinsicInterior_prod_eq` / 定理 `intrinsicInterior_prod_eq`

English:
theorem intrinsicInterior_prod_eq
  statement: [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace Q]
  proof: by
  let e : affineSpan 𝕜 (s ×ˢ t) ≃ₜ affineSpan 𝕜 s × affineSpan 𝕜 t :=
    (Homeomorph.setCongr (by simp [affineSpan_prod_eq])).trans (Homeomorph.Set.prod _ _)
  have : Subtype.val ∘ e.symm = fun p => (p.1, p.2) := rfl
  have h : ((↑) ⁻¹' (s ×ˢ t) : Set _) = e ⁻¹' (((↑) ⁻¹' s) ×ˢ ((↑) ⁻¹' t)) := rfl
  simp_rw [intrinsicInterior, h, ← e.preimage_interior, interior_prod_eq, ← e.image_symm,
    ← image_comp, prod_image_image_eq, this]

中文:
定理 intrinsic整数erior_prod_eq
  结论: [加法交换群 W] [模 𝕜 W] [拓扑空间 Q]
  证明: by
  let e : affineSpan 𝕜 (s ×ˢ t) ≃ₜ affineSpan 𝕜 s × affineSpan 𝕜 t :=
    (Homeomorph.setCongr (by simp [affineSpan_prod_eq])).trans (Homeomorph.Set.prod _ _)
  have : Subtype.val ∘ e.symm = fun p => (p.1, p.2) := rfl
  have h : ((↑) ⁻¹' (s ×ˢ t) : Set _) = e ⁻¹' (((↑) ⁻¹' s) ×ˢ ((↑) ⁻¹' t)) := rfl
  simp_rw [intrinsicInterior, h, ← e.preimage_interior, interior_prod_eq, ← e.image_symm,
    ← image_comp, prod_image_image_eq, this]

Depends on / 依赖: Homeomorph, Homeomorph.Set.prod, Homeomorph.setCongr, Subtype, Subtype.val, affineSpan, affineSpan_prod_eq, e.image_symm, e.preimage_interior, e.symm, image_comp, image_symm, interior_prod_eq, intrinsicInterior, preimage_interior, prod_image_image_eq, setCongr, simp_rw
-/
theorem intrinsicInterior_prod_eq [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace Q]
    [AddTorsor W Q] (s : Set P) (t : Set Q) :
    intrinsicInterior 𝕜 (s ×ˢ t) = intrinsicInterior 𝕜 s ×ˢ intrinsicInterior 𝕜 t := by
  let e : affineSpan 𝕜 (s ×ˢ t) ≃ₜ affineSpan 𝕜 s × affineSpan 𝕜 t :=
    (Homeomorph.setCongr (by simp [affineSpan_prod_eq])).trans (Homeomorph.Set.prod _ _)
  have : Subtype.val ∘ e.symm = fun p => (p.1, p.2) := rfl
  have h : ((↑) ⁻¹' (s ×ˢ t) : Set _) = e ⁻¹' (((↑) ⁻¹' s) ×ˢ ((↑) ⁻¹' t)) := rfl
  simp_rw [intrinsicInterior, h, ← e.preimage_interior, interior_prod_eq, ← e.image_symm,
    ← image_comp, prod_image_image_eq, this]

section ImageOfHomeomorphAffineSpan

variable [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace Q] [AddTorsor W Q]
  {f : P -> Q} {s : Set P}

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `preimage_image_eq_of_homeomorph_affineSpan` / 定理 `preimage_image_eq_of_homeomorph_affineSpan`

English:
theorem preimage_image_eq_of_homeomorph_affineSpan
  proof: by
  ext x
  refine ⟨fun ⟨_, hy, hfy⟩ => ?_ , fun hx => ⟨_, hx, rfl⟩⟩
  change (x : P) in s
  rwa [exists_eq_subtype_mk_iff.mp ⟨subset_affineSpan 𝕜 s hy, he_homeo.injective <| Subtype.ext <|
      by simpa [he] using hfy.symm⟩]

中文:
定理 preimage_image_eq_of_homeomorph_affineSpan
  证明: by
  ext x
  refine ⟨fun ⟨_, hy, hfy⟩ => ?_ , fun hx => ⟨_, hx, rfl⟩⟩
  change (x : P) in s
  rwa [exists_eq_subtype_mk_iff.mp ⟨subset_affineSpan 𝕜 s hy, he_homeo.injective <| Subtype.ext <|
      by simpa [he] using hfy.symm⟩]
-/
private theorem preimage_image_eq_of_homeomorph_affineSpan
    (e : affineSpan 𝕜 s -> affineSpan 𝕜 (f '' s)) (he_homeo : IsHomeomorph e)
    (he : forall x, (e x : Q) = f x) :
    (f ∘ (↑)) ⁻¹' (f '' s) = ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s) := by
  ext x
  refine ⟨fun ⟨_, hy, hfy⟩ => ?_ , fun hx => ⟨_, hx, rfl⟩⟩
  change (x : P) in s
  rwa [exists_eq_subtype_mk_iff.mp ⟨subset_affineSpan 𝕜 s hy, he_homeo.injective <| Subtype.ext <|
      by simpa [he] using hfy.symm⟩]

variable (e : [Nonempty s] -> affineSpan 𝕜 s -> affineSpan 𝕜 (f '' s))
  (he_homeo : [Nonempty s] -> IsHomeomorph e) (he : [Nonempty s] -> forall x, e x = f x)

include e he_homeo he

/--
theorem `intrinsicInterior_image_of_homeomorph_affineSpan` / 定理 `intrinsicInterior_image_of_homeomorph_affineSpan`

English:
theorem intrinsicInterior_image_of_homeomorph_affineSpan
  proof: by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · have : Nonempty s := hs.to_subtype
    rw [intrinsicInterior]; rw [← image_interior_preimage_comp e he_homeo]; rw [(funext he : (↑) ∘ e = f ∘ (↑))]; rw [preimage_image_eq_of_homeomorph_affineSpan e he_homeo he]; rw [image_comp]; rfl

中文:
定理 intrinsic整数erior_image_of_homeomorph_affineSpan
  证明: by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · have : Nonempty s := hs.to_subtype
    rw [intrinsicInterior]; rw [← image_interior_preimage_comp e he_homeo]; rw [(funext he : (↑) ∘ e = f ∘ (↑))]; rw [preimage_image_eq_of_homeomorph_affineSpan e he_homeo he]; rw [image_comp]; rfl
-/
private theorem intrinsicInterior_image_of_homeomorph_affineSpan :
    intrinsicInterior 𝕜 (f '' s) = f '' intrinsicInterior 𝕜 s := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · have : Nonempty s := hs.to_subtype
    rw [intrinsicInterior]; rw [← image_interior_preimage_comp e he_homeo]; rw [(funext he : (↑) ∘ e = f ∘ (↑))]; rw [preimage_image_eq_of_homeomorph_affineSpan e he_homeo he]; rw [image_comp]; rfl

/--
theorem `intrinsicFrontier_image_of_homeomorph_affineSpan` / 定理 `intrinsicFrontier_image_of_homeomorph_affineSpan`

English:
theorem intrinsicFrontier_image_of_homeomorph_affineSpan
  proof: by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · have : Nonempty s := hs.to_subtype
    rw [intrinsicFrontier]; rw [← image_frontier_preimage_comp e he_homeo]; rw [(funext he : (↑) ∘ e = f ∘ (↑))]; rw [preimage_image_eq_of_homeomorph_affineSpan e he_homeo he]; rw [image_comp]; rfl

中文:
定理 intrinsicFrontier_image_of_homeomorph_affineSpan
  证明: by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · have : Nonempty s := hs.to_subtype
    rw [intrinsicFrontier]; rw [← image_frontier_preimage_comp e he_homeo]; rw [(funext he : (↑) ∘ e = f ∘ (↑))]; rw [preimage_image_eq_of_homeomorph_affineSpan e he_homeo he]; rw [image_comp]; rfl
-/
private theorem intrinsicFrontier_image_of_homeomorph_affineSpan :
    intrinsicFrontier 𝕜 (f '' s) = f '' intrinsicFrontier 𝕜 s := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · have : Nonempty s := hs.to_subtype
    rw [intrinsicFrontier]; rw [← image_frontier_preimage_comp e he_homeo]; rw [(funext he : (↑) ∘ e = f ∘ (↑))]; rw [preimage_image_eq_of_homeomorph_affineSpan e he_homeo he]; rw [image_comp]; rfl

/--
theorem `intrinsicClosure_image_of_homeomorph_affineSpan` / 定理 `intrinsicClosure_image_of_homeomorph_affineSpan`

English:
theorem intrinsicClosure_image_of_homeomorph_affineSpan
  proof: by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · have : Nonempty s := hs.to_subtype
    rw [intrinsicClosure]; rw [← image_closure_preimage_comp e he_homeo]; rw [(funext he : (↑) ∘ e = f ∘ (↑))]; rw [preimage_image_eq_of_homeomorph_affineSpan e he_homeo he]; rw [image_comp]; rfl

中文:
定理 intrinsicClosure_image_of_homeomorph_affineSpan
  证明: by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · have : Nonempty s := hs.to_subtype
    rw [intrinsicClosure]; rw [← image_closure_preimage_comp e he_homeo]; rw [(funext he : (↑) ∘ e = f ∘ (↑))]; rw [preimage_image_eq_of_homeomorph_affineSpan e he_homeo he]; rw [image_comp]; rfl
-/
private theorem intrinsicClosure_image_of_homeomorph_affineSpan :
    intrinsicClosure 𝕜 (f '' s) = f '' intrinsicClosure 𝕜 s := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · have : Nonempty s := hs.to_subtype
    rw [intrinsicClosure]; rw [← image_closure_preimage_comp e he_homeo]; rw [(funext he : (↑) ∘ e = f ∘ (↑))]; rw [preimage_image_eq_of_homeomorph_affineSpan e he_homeo he]; rw [image_comp]; rfl

end ImageOfHomeomorphAffineSpan

end AddTorsor

namespace ContinuousAffineEquiv

variable [Ring 𝕜] [AddCommGroup V] [AddCommGroup W] [Module 𝕜 V] [Module 𝕜 W]
  [TopologicalSpace P] [TopologicalSpace Q] [AddTorsor V P] [AddTorsor W Q]

@[simp]
/--
theorem `intrinsicInterior_image` / 定理 `intrinsicInterior_image`

English:
theorem intrinsicInterior_image
  given: (φ : P ≃ᴬ[𝕜] Q) (s : Set P)
  proof: let e : [Nonempty s] -> (affineSpan 𝕜 s) ≃ᴬ[𝕜] (affineSpan 𝕜 (φ '' s)) := fun [_] =>
(φ.affineSubspaceMap (affineSpan 𝕜 s)).trans ofEq (map_span φ.toAffineMap s)
  intrinsicInterior_image_of_homeomorph_affineSpan
    (fun [_] => e.toHomeomorph) (fun [_] => e.toHomeomorph.isHomeomorph) (fun [_] _ => rfl)

@[simp]

中文:
定理 intrinsic整数erior_image
  条件: (φ : P ≃ᴬ[𝕜] Q) (s : 集合 P)
  证明: let e : [Nonempty s] -> (affineSpan 𝕜 s) ≃ᴬ[𝕜] (affineSpan 𝕜 (φ '' s)) := fun [_] =>
(φ.affineSubspaceMap (affineSpan 𝕜 s)).trans ofEq (map_span φ.toAffineMap s)
  intrinsicInterior_image_of_homeomorph_affineSpan
    (fun [_] => e.toHomeomorph) (fun [_] => e.toHomeomorph.isHomeomorph) (fun [_] _ => rfl)

@[simp]

Depends on / 依赖: Nonempty, affineSpan, affineSubspaceMap, e.toHomeomorph, e.toHomeomorph.isHomeomorph, intrinsicInterior_image_of_homeomorph_affineSpan, isHomeomorph, map_span, toAffineMap, toHomeomorph
-/
theorem intrinsicInterior_image (φ : P ≃ᴬ[𝕜] Q) (s : Set P) :
    intrinsicInterior 𝕜 (φ '' s) = φ '' intrinsicInterior 𝕜 s :=
  let e : [Nonempty s] -> (affineSpan 𝕜 s) ≃ᴬ[𝕜] (affineSpan 𝕜 (φ '' s)) := fun [_] =>
(φ.affineSubspaceMap (affineSpan 𝕜 s)).trans ofEq (map_span φ.toAffineMap s)
  intrinsicInterior_image_of_homeomorph_affineSpan
    (fun [_] => e.toHomeomorph) (fun [_] => e.toHomeomorph.isHomeomorph) (fun [_] _ => rfl)

@[simp]
/--
theorem `intrinsicFrontier_image` / 定理 `intrinsicFrontier_image`

English:
theorem intrinsicFrontier_image
  given: (φ : P ≃ᴬ[𝕜] Q) (s : Set P)
  proof: let e : [Nonempty s] -> (affineSpan 𝕜 s) ≃ᴬ[𝕜] (affineSpan 𝕜 (φ '' s)) := fun [_] =>
(φ.affineSubspaceMap (affineSpan 𝕜 s)).trans ofEq (map_span φ.toAffineMap s)
  intrinsicFrontier_image_of_homeomorph_affineSpan
    (fun [_] => e.toHomeomorph) (fun [_] => e.toHomeomorph.isHomeomorph) (fun [_] _ => rfl)

@[simp]

中文:
定理 intrinsicFrontier_image
  条件: (φ : P ≃ᴬ[𝕜] Q) (s : 集合 P)
  证明: let e : [Nonempty s] -> (affineSpan 𝕜 s) ≃ᴬ[𝕜] (affineSpan 𝕜 (φ '' s)) := fun [_] =>
(φ.affineSubspaceMap (affineSpan 𝕜 s)).trans ofEq (map_span φ.toAffineMap s)
  intrinsicFrontier_image_of_homeomorph_affineSpan
    (fun [_] => e.toHomeomorph) (fun [_] => e.toHomeomorph.isHomeomorph) (fun [_] _ => rfl)

@[simp]

Depends on / 依赖: Nonempty, affineSpan, affineSubspaceMap, e.toHomeomorph, e.toHomeomorph.isHomeomorph, intrinsicFrontier_image_of_homeomorph_affineSpan, isHomeomorph, map_span, toAffineMap, toHomeomorph
-/
theorem intrinsicFrontier_image (φ : P ≃ᴬ[𝕜] Q) (s : Set P) :
    intrinsicFrontier 𝕜 (φ '' s) = φ '' intrinsicFrontier 𝕜 s :=
  let e : [Nonempty s] -> (affineSpan 𝕜 s) ≃ᴬ[𝕜] (affineSpan 𝕜 (φ '' s)) := fun [_] =>
(φ.affineSubspaceMap (affineSpan 𝕜 s)).trans ofEq (map_span φ.toAffineMap s)
  intrinsicFrontier_image_of_homeomorph_affineSpan
    (fun [_] => e.toHomeomorph) (fun [_] => e.toHomeomorph.isHomeomorph) (fun [_] _ => rfl)

@[simp]
/--
theorem `intrinsicClosure_image` / 定理 `intrinsicClosure_image`

English:
theorem intrinsicClosure_image
  given: (φ : P ≃ᴬ[𝕜] Q) (s : Set P)
  proof: let e : [Nonempty s] -> (affineSpan 𝕜 s) ≃ᴬ[𝕜] (affineSpan 𝕜 (φ '' s)) := fun [_] =>
(φ.affineSubspaceMap (affineSpan 𝕜 s)).trans ofEq (map_span φ.toAffineMap s)
  intrinsicClosure_image_of_homeomorph_affineSpan
    (fun [_] => e.toHomeomorph) (fun [_] => e.toHomeomorph.isHomeomorph) (fun [_] _ => rfl)

中文:
定理 intrinsicClosure_image
  条件: (φ : P ≃ᴬ[𝕜] Q) (s : 集合 P)
  证明: let e : [Nonempty s] -> (affineSpan 𝕜 s) ≃ᴬ[𝕜] (affineSpan 𝕜 (φ '' s)) := fun [_] =>
(φ.affineSubspaceMap (affineSpan 𝕜 s)).trans ofEq (map_span φ.toAffineMap s)
  intrinsicClosure_image_of_homeomorph_affineSpan
    (fun [_] => e.toHomeomorph) (fun [_] => e.toHomeomorph.isHomeomorph) (fun [_] _ => rfl)

Depends on / 依赖: Nonempty, affineSpan, affineSubspaceMap, e.toHomeomorph, e.toHomeomorph.isHomeomorph, intrinsicClosure_image_of_homeomorph_affineSpan, isHomeomorph, map_span, toAffineMap, toHomeomorph
-/
theorem intrinsicClosure_image (φ : P ≃ᴬ[𝕜] Q) (s : Set P) :
    intrinsicClosure 𝕜 (φ '' s) = φ '' intrinsicClosure 𝕜 s :=
  let e : [Nonempty s] -> (affineSpan 𝕜 s) ≃ᴬ[𝕜] (affineSpan 𝕜 (φ '' s)) := fun [_] =>
(φ.affineSubspaceMap (affineSpan 𝕜 s)).trans ofEq (map_span φ.toAffineMap s)
  intrinsicClosure_image_of_homeomorph_affineSpan
    (fun [_] => e.toHomeomorph) (fun [_] => e.toHomeomorph.isHomeomorph) (fun [_] _ => rfl)

end ContinuousAffineEquiv

namespace AffineIsometry

variable [NormedField 𝕜] [SeminormedAddCommGroup V] [SeminormedAddCommGroup W] [NormedSpace 𝕜 V]
  [NormedSpace 𝕜 W] [MetricSpace P] [PseudoMetricSpace Q] [NormedAddTorsor V P]
  [NormedAddTorsor W Q]

@[simp]
/--
theorem `intrinsicInterior_image` / 定理 `intrinsicInterior_image`

English:
theorem intrinsicInterior_image
  given: (φ : P ->ᵃⁱ[𝕜] Q) (s : Set P)
  proof: let e : [Nonempty s] -> (affineSpan 𝕜 s) ≃ᴬ[𝕜] (affineSpan 𝕜 (φ '' s)) := fun [_] =>
((affineSpan 𝕜 s).isometryEquivMap φ).toContinuousAffineEquiv.trans ofEq
(map_span φ.toAffineMap s).trans congrArg _ congrArg (· '' s) φ.coe_toAffineMap
  intrinsicInterior_image_of_homeomorph_affineSpan
    (fun [_] => e.toHomeomorph) (fun [_] => e.toHomeomorph.isHomeomorph) (fun [_] _ => rfl)

@[simp]

中文:
定理 intrinsic整数erior_image
  条件: (φ : P ->ᵃⁱ[𝕜] Q) (s : 集合 P)
  证明: let e : [Nonempty s] -> (affineSpan 𝕜 s) ≃ᴬ[𝕜] (affineSpan 𝕜 (φ '' s)) := fun [_] =>
((affineSpan 𝕜 s).isometryEquivMap φ).toContinuousAffineEquiv.trans ofEq
(map_span φ.toAffineMap s).trans congrArg _ congrArg (· '' s) φ.coe_toAffineMap
  intrinsicInterior_image_of_homeomorph_affineSpan
    (fun [_] => e.toHomeomorph) (fun [_] => e.toHomeomorph.isHomeomorph) (fun [_] _ => rfl)

@[simp]

Depends on / 依赖: Nonempty, affineSpan, coe_toAffineMap, e.toHomeomorph, e.toHomeomorph.isHomeomorph, intrinsicInterior_image_of_homeomorph_affineSpan, isHomeomorph, isometryEquivMap, map_span, toAffineMap, toContinuousAffineEquiv, toContinuousAffineEquiv.trans, toHomeomorph
-/
theorem intrinsicInterior_image (φ : P ->ᵃⁱ[𝕜] Q) (s : Set P) :
    intrinsicInterior 𝕜 (φ '' s) = φ '' intrinsicInterior 𝕜 s :=
  let e : [Nonempty s] -> (affineSpan 𝕜 s) ≃ᴬ[𝕜] (affineSpan 𝕜 (φ '' s)) := fun [_] =>
((affineSpan 𝕜 s).isometryEquivMap φ).toContinuousAffineEquiv.trans ofEq
(map_span φ.toAffineMap s).trans congrArg _ congrArg (· '' s) φ.coe_toAffineMap
  intrinsicInterior_image_of_homeomorph_affineSpan
    (fun [_] => e.toHomeomorph) (fun [_] => e.toHomeomorph.isHomeomorph) (fun [_] _ => rfl)

@[simp]
/--
theorem `intrinsicFrontier_image` / 定理 `intrinsicFrontier_image`

English:
theorem intrinsicFrontier_image
  given: (φ : P ->ᵃⁱ[𝕜] Q) (s : Set P)
  proof: let e : [Nonempty s] -> (affineSpan 𝕜 s) ≃ᴬ[𝕜] (affineSpan 𝕜 (φ '' s)) := fun [_] =>
((affineSpan 𝕜 s).isometryEquivMap φ).toContinuousAffineEquiv.trans ofEq
(map_span φ.toAffineMap s).trans congrArg _ congrArg (· '' s) φ.coe_toAffineMap
  intrinsicFrontier_image_of_homeomorph_affineSpan
    (fun [_] => e.toHomeomorph) (fun [_] => e.toHomeomorph.isHomeomorph) (fun [_] _ => rfl)

@[simp]

中文:
定理 intrinsicFrontier_image
  条件: (φ : P ->ᵃⁱ[𝕜] Q) (s : 集合 P)
  证明: let e : [Nonempty s] -> (affineSpan 𝕜 s) ≃ᴬ[𝕜] (affineSpan 𝕜 (φ '' s)) := fun [_] =>
((affineSpan 𝕜 s).isometryEquivMap φ).toContinuousAffineEquiv.trans ofEq
(map_span φ.toAffineMap s).trans congrArg _ congrArg (· '' s) φ.coe_toAffineMap
  intrinsicFrontier_image_of_homeomorph_affineSpan
    (fun [_] => e.toHomeomorph) (fun [_] => e.toHomeomorph.isHomeomorph) (fun [_] _ => rfl)

@[simp]

Depends on / 依赖: Nonempty, affineSpan, coe_toAffineMap, e.toHomeomorph, e.toHomeomorph.isHomeomorph, intrinsicFrontier_image_of_homeomorph_affineSpan, isHomeomorph, isometryEquivMap, map_span, toAffineMap, toContinuousAffineEquiv, toContinuousAffineEquiv.trans, toHomeomorph
-/
theorem intrinsicFrontier_image (φ : P ->ᵃⁱ[𝕜] Q) (s : Set P) :
    intrinsicFrontier 𝕜 (φ '' s) = φ '' intrinsicFrontier 𝕜 s :=
  let e : [Nonempty s] -> (affineSpan 𝕜 s) ≃ᴬ[𝕜] (affineSpan 𝕜 (φ '' s)) := fun [_] =>
((affineSpan 𝕜 s).isometryEquivMap φ).toContinuousAffineEquiv.trans ofEq
(map_span φ.toAffineMap s).trans congrArg _ congrArg (· '' s) φ.coe_toAffineMap
  intrinsicFrontier_image_of_homeomorph_affineSpan
    (fun [_] => e.toHomeomorph) (fun [_] => e.toHomeomorph.isHomeomorph) (fun [_] _ => rfl)

@[simp]
/--
theorem `intrinsicClosure_image` / 定理 `intrinsicClosure_image`

English:
theorem intrinsicClosure_image
  given: (φ : P ->ᵃⁱ[𝕜] Q) (s : Set P)
  proof: let e : [Nonempty s] -> (affineSpan 𝕜 s) ≃ᴬ[𝕜] (affineSpan 𝕜 (φ '' s)) := fun [_] =>
((affineSpan 𝕜 s).isometryEquivMap φ).toContinuousAffineEquiv.trans ofEq
(map_span φ.toAffineMap s).trans congrArg _ congrArg (· '' s) φ.coe_toAffineMap
  intrinsicClosure_image_of_homeomorph_affineSpan
    (fun [_] => e.toHomeomorph) (fun [_] => e.toHomeomorph.isHomeomorph) (fun [_] _ => rfl)

@[deprecated intrinsicInterior_image (since := "2026-05-08")]
alias image_intrinsicInterior := intrinsicInterior_image

@[deprecated intrinsicFrontier_image (since := "2026-05-08")]
alias image_intrinsicFrontier := intrinsicFrontier_image

@[deprecated intrinsicClosure_image (since := "2026-05-08")]
alias image_intrinsicClosure := intrinsicClosure_image

中文:
定理 intrinsicClosure_image
  条件: (φ : P ->ᵃⁱ[𝕜] Q) (s : 集合 P)
  证明: let e : [Nonempty s] -> (affineSpan 𝕜 s) ≃ᴬ[𝕜] (affineSpan 𝕜 (φ '' s)) := fun [_] =>
((affineSpan 𝕜 s).isometryEquivMap φ).toContinuousAffineEquiv.trans ofEq
(map_span φ.toAffineMap s).trans congrArg _ congrArg (· '' s) φ.coe_toAffineMap
  intrinsicClosure_image_of_homeomorph_affineSpan
    (fun [_] => e.toHomeomorph) (fun [_] => e.toHomeomorph.isHomeomorph) (fun [_] _ => rfl)

@[deprecated intrinsicInterior_image (since := "2026-05-08")]
alias image_intrinsicInterior := intrinsicInterior_image

@[deprecated intrinsicFrontier_image (since := "2026-05-08")]
alias image_intrinsicFrontier := intrinsicFrontier_image

@[deprecated intrinsicClosure_image (since := "2026-05-08")]
alias image_intrinsicClosure := intrinsicClosure_image

Depends on / 依赖: Nonempty, affineSpan, coe_toAffineMap, e.toHomeomorph, e.toHomeomorph.isHomeomorph, intrinsicClosure_image_of_homeomorph_affineSpan, isHomeomorph, isometryEquivMap, map_span, toAffineMap, toContinuousAffineEquiv, toContinuousAffineEquiv.trans, toHomeomorph
-/
theorem intrinsicClosure_image (φ : P ->ᵃⁱ[𝕜] Q) (s : Set P) :
    intrinsicClosure 𝕜 (φ '' s) = φ '' intrinsicClosure 𝕜 s :=
  let e : [Nonempty s] -> (affineSpan 𝕜 s) ≃ᴬ[𝕜] (affineSpan 𝕜 (φ '' s)) := fun [_] =>
((affineSpan 𝕜 s).isometryEquivMap φ).toContinuousAffineEquiv.trans ofEq
(map_span φ.toAffineMap s).trans congrArg _ congrArg (· '' s) φ.coe_toAffineMap
  intrinsicClosure_image_of_homeomorph_affineSpan
    (fun [_] => e.toHomeomorph) (fun [_] => e.toHomeomorph.isHomeomorph) (fun [_] _ => rfl)

@[deprecated intrinsicInterior_image (since := "2026-05-08")]
alias image_intrinsicInterior := intrinsicInterior_image

@[deprecated intrinsicFrontier_image (since := "2026-05-08")]
alias image_intrinsicFrontier := intrinsicFrontier_image

@[deprecated intrinsicClosure_image (since := "2026-05-08")]
alias image_intrinsicClosure := intrinsicClosure_image

end AffineIsometry

namespace AffineEquiv

variable [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  [MetricSpace P] [NormedAddTorsor V P]
  [MetricSpace Q] [NormedAddTorsor W Q]

@[simp]
/--
theorem `intrinsicInterior_image` / 定理 `intrinsicInterior_image`

English:
theorem intrinsicInterior_image
  given: (φ : P ≃ᵃ[𝕜] Q) (s : Set P)
  proof: φ.toContinuousAffineEquiv.intrinsicInterior_image s

@[simp]

中文:
定理 intrinsic整数erior_image
  条件: (φ : P ≃ᵃ[𝕜] Q) (s : 集合 P)
  证明: φ.toContinuousAffineEquiv.intrinsicInterior_image s

@[simp]

Depends on / 依赖: intrinsicInterior_image, toContinuousAffineEquiv, toContinuousAffineEquiv.intrinsicInterior_image
-/
theorem intrinsicInterior_image (φ : P ≃ᵃ[𝕜] Q) (s : Set P) :
    intrinsicInterior 𝕜 (φ '' s) = φ '' intrinsicInterior 𝕜 s :=
  φ.toContinuousAffineEquiv.intrinsicInterior_image s

@[simp]
/--
theorem `intrinsicFrontier_image` / 定理 `intrinsicFrontier_image`

English:
theorem intrinsicFrontier_image
  given: (φ : P ≃ᵃ[𝕜] Q) (s : Set P)
  proof: φ.toContinuousAffineEquiv.intrinsicFrontier_image s

@[simp]

中文:
定理 intrinsicFrontier_image
  条件: (φ : P ≃ᵃ[𝕜] Q) (s : 集合 P)
  证明: φ.toContinuousAffineEquiv.intrinsicFrontier_image s

@[simp]

Depends on / 依赖: intrinsicFrontier_image, toContinuousAffineEquiv, toContinuousAffineEquiv.intrinsicFrontier_image
-/
theorem intrinsicFrontier_image (φ : P ≃ᵃ[𝕜] Q) (s : Set P) :
    intrinsicFrontier 𝕜 (φ '' s) = φ '' intrinsicFrontier 𝕜 s :=
  φ.toContinuousAffineEquiv.intrinsicFrontier_image s

@[simp]
/--
theorem `intrinsicClosure_image` / 定理 `intrinsicClosure_image`

English:
theorem intrinsicClosure_image
  given: (φ : P ≃ᵃ[𝕜] Q) (s : Set P)
  proof: φ.toContinuousAffineEquiv.intrinsicClosure_image s

中文:
定理 intrinsicClosure_image
  条件: (φ : P ≃ᵃ[𝕜] Q) (s : 集合 P)
  证明: φ.toContinuousAffineEquiv.intrinsicClosure_image s

Depends on / 依赖: intrinsicClosure_image, toContinuousAffineEquiv, toContinuousAffineEquiv.intrinsicClosure_image
-/
theorem intrinsicClosure_image (φ : P ≃ᵃ[𝕜] Q) (s : Set P) :
    intrinsicClosure 𝕜 (φ '' s) = φ '' intrinsicClosure 𝕜 s :=
  φ.toContinuousAffineEquiv.intrinsicClosure_image s

end AffineEquiv

section NormedAddTorsor

variable (𝕜) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [FiniteDimensional 𝕜 V] [MetricSpace P] [NormedAddTorsor V P] (s : Set P)

@[simp]
/--
theorem `intrinsicClosure_eq_closure` / 定理 `intrinsicClosure_eq_closure`

English:
theorem intrinsicClosure_eq_closure
  statement: intrinsicClosure 𝕜 s = closure s
  proof: by
  ext x
  simp only [mem_closure_iff, mem_intrinsicClosure]
  refine ⟨?_, fun h => ⟨⟨x, _⟩, ?_, Subtype.coe_mk _ ?_⟩⟩
  · rintro ⟨x, h, rfl⟩ t ht hx
    obtain ⟨z, hz₁, hz₂⟩ := h _ (continuous_induced_dom.isOpen_preimage t ht) hx
    exact ⟨z, hz₁, hz₂⟩
  · rintro _ ⟨t, ht, rfl⟩ hx
    obtain ⟨y, hyt, hys⟩ := h _ ht hx
    exact ⟨⟨_, subset_affineSpan 𝕜 s hys⟩, hyt, hys⟩
  · by_contra hc
    obtain ⟨z, hz₁, hz₂⟩ := h _ (affineSpan 𝕜 s).closed_of_finiteDimensional.isOpen_compl hc
    exact hz₁ (subset_affineSpan 𝕜 s hz₂)

中文:
定理 intrinsicClosure_eq_closure
  结论: intrinsicClosure 𝕜 s = closure s
  证明: by
  ext x
  simp only [mem_closure_iff, mem_intrinsicClosure]
  refine ⟨?_, fun h => ⟨⟨x, _⟩, ?_, Subtype.coe_mk _ ?_⟩⟩
  · rintro ⟨x, h, rfl⟩ t ht hx
    obtain ⟨z, hz₁, hz₂⟩ := h _ (continuous_induced_dom.isOpen_preimage t ht) hx
    exact ⟨z, hz₁, hz₂⟩
  · rintro _ ⟨t, ht, rfl⟩ hx
    obtain ⟨y, hyt, hys⟩ := h _ ht hx
    exact ⟨⟨_, subset_affineSpan 𝕜 s hys⟩, hyt, hys⟩
  · by_contra hc
    obtain ⟨z, hz₁, hz₂⟩ := h _ (affineSpan 𝕜 s).closed_of_finiteDimensional.isOpen_compl hc
    exact hz₁ (subset_affineSpan 𝕜 s hz₂)

Depends on / 依赖: Subtype, Subtype.coe_mk, affineSpan, closed_of_finiteDimensional, closed_of_finiteDimensional.isOpen_compl, coe_mk, continuous_induced_dom, continuous_induced_dom.isOpen_preimage, isOpen_compl, isOpen_preimage, mem_closure_iff, mem_intrinsicClosure, subset_affineSpan
-/
theorem intrinsicClosure_eq_closure : intrinsicClosure 𝕜 s = closure s := by
  ext x
  simp only [mem_closure_iff, mem_intrinsicClosure]
  refine ⟨?_, fun h => ⟨⟨x, _⟩, ?_, Subtype.coe_mk _ ?_⟩⟩
  · rintro ⟨x, h, rfl⟩ t ht hx
    obtain ⟨z, hz₁, hz₂⟩ := h _ (continuous_induced_dom.isOpen_preimage t ht) hx
    exact ⟨z, hz₁, hz₂⟩
  · rintro _ ⟨t, ht, rfl⟩ hx
    obtain ⟨y, hyt, hys⟩ := h _ ht hx
    exact ⟨⟨_, subset_affineSpan 𝕜 s hys⟩, hyt, hys⟩
  · by_contra hc
    obtain ⟨z, hz₁, hz₂⟩ := h _ (affineSpan 𝕜 s).closed_of_finiteDimensional.isOpen_compl hc
    exact hz₁ (subset_affineSpan 𝕜 s hz₂)

variable {𝕜}

@[simp]
/--
theorem `closure_sdiff_intrinsicInterior` / 定理 `closure_sdiff_intrinsicInterior`

English:
theorem closure_sdiff_intrinsicInterior
  given: (s : Set P)
  proof: intrinsicClosure_eq_closure 𝕜 s ▸ intrinsicClosure_sdiff_intrinsicInterior s

@[deprecated (since := "2026-06-03")]
alias closure_diff_intrinsicInterior := closure_sdiff_intrinsicInterior

@[simp]

中文:
定理 closure_sdiff_intrinsic整数erior
  条件: (s : 集合 P)
  证明: intrinsicClosure_eq_closure 𝕜 s ▸ intrinsicClosure_sdiff_intrinsicInterior s

@[deprecated (since := "2026-06-03")]
alias closure_diff_intrinsicInterior := closure_sdiff_intrinsicInterior

@[simp]

Depends on / 依赖: intrinsicClosure_eq_closure, intrinsicClosure_sdiff_intrinsicInterior
-/
theorem closure_sdiff_intrinsicInterior (s : Set P) :
    closure s \ intrinsicInterior 𝕜 s = intrinsicFrontier 𝕜 s :=
  intrinsicClosure_eq_closure 𝕜 s ▸ intrinsicClosure_sdiff_intrinsicInterior s

@[deprecated (since := "2026-06-03")]
alias closure_diff_intrinsicInterior := closure_sdiff_intrinsicInterior

@[simp]
/--
theorem `closure_sdiff_intrinsicFrontier` / 定理 `closure_sdiff_intrinsicFrontier`

English:
theorem closure_sdiff_intrinsicFrontier
  given: (s : Set P)
  proof: intrinsicClosure_eq_closure 𝕜 s ▸ intrinsicClosure_sdiff_intrinsicFrontier s

@[deprecated (since := "2026-06-03")]
alias closure_diff_intrinsicFrontier := closure_sdiff_intrinsicFrontier

中文:
定理 closure_sdiff_intrinsicFrontier
  条件: (s : 集合 P)
  证明: intrinsicClosure_eq_closure 𝕜 s ▸ intrinsicClosure_sdiff_intrinsicFrontier s

@[deprecated (since := "2026-06-03")]
alias closure_diff_intrinsicFrontier := closure_sdiff_intrinsicFrontier

Depends on / 依赖: intrinsicClosure_eq_closure, intrinsicClosure_sdiff_intrinsicFrontier
-/
theorem closure_sdiff_intrinsicFrontier (s : Set P) :
    closure s \ intrinsicFrontier 𝕜 s = intrinsicInterior 𝕜 s :=
  intrinsicClosure_eq_closure 𝕜 s ▸ intrinsicClosure_sdiff_intrinsicFrontier s

@[deprecated (since := "2026-06-03")]
alias closure_diff_intrinsicFrontier := closure_sdiff_intrinsicFrontier

end NormedAddTorsor

section Convex

variable [Field 𝕜] [LinearOrder 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousConstSMul 𝕜 V] {s : Set V}

/--
theorem `Convex.intrinsicClosure` / 定理 `Convex.intrinsicClosure`

English:
theorem Convex.intrinsicClosure
  given: (hs : Convex 𝕜 s)
  statement: Convex 𝕜 (intrinsicClosure 𝕜 s)
  proof: by
  rw [intrinsicClosure_eq_closure_inter_affineSpan]
  exact hs.closure.inter (affineSpan 𝕜 s).convex

中文:
定理 凸.intrinsicClosure
  条件: (hs : 凸 𝕜 s)
  结论: 凸 𝕜 (intrinsicClosure 𝕜 s)
  证明: by
  rw [intrinsicClosure_eq_closure_inter_affineSpan]
  exact hs.closure.inter (affineSpan 𝕜 s).convex
-/
protected theorem Convex.intrinsicClosure (hs : Convex 𝕜 s) : Convex 𝕜 (intrinsicClosure 𝕜 s) := by
  rw [intrinsicClosure_eq_closure_inter_affineSpan]
  exact hs.closure.inter (affineSpan 𝕜 s).convex

end Convex

/--
theorem `aux` / 定理 `aux`

English:
theorem aux
  statement: {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] (φ : α ≃ₜ β)
  proof: by
  rw [← φ.image_symm]; rw [← φ.symm.image_interior]; rw [image_nonempty]

中文:
定理 aux
  结论: {α β : 类型} [拓扑空间 α] [拓扑空间 β] (φ : α ≃ₜ β)
  证明: by
  rw [← φ.image_symm]; rw [← φ.symm.image_interior]; rw [image_nonempty]
-/
private theorem aux {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] (φ : α ≃ₜ β)
    (s : Set β) : (interior s).Nonempty ↔ (interior (φ ⁻¹' s)).Nonempty := by
  rw [← φ.image_symm]; rw [← φ.symm.image_interior]; rw [image_nonempty]

variable [NormedAddCommGroup V] [NormedSpace Real V] [FiniteDimensional Real V] {s : Set V}

/--
theorem `Set.Nonempty.intrinsicInterior` / 定理 `Set.Nonempty.intrinsicInterior`

English:
theorem Set.Nonempty.intrinsicInterior
  given: (hscv : Convex Real s) (hsne : s.Nonempty)
  proof: by
  have := hsne.coe_sort
  obtain ⟨p, hp⟩ := hsne
  let p' : _root_.affineSpan Real s := ⟨p, subset_affineSpan _ _ hp⟩
  rw [intrinsicInterior]; rw [image_nonempty]; rw [aux (AffineIsometryEquiv.constVSub Real p').symm.toHomeomorph]; rw [Convex.interior_nonempty_iff_affineSpan_eq_top]; rw [AffineIsometryEquiv.coe_toHomeomorph]; rw [←
    AffineIsometryEquiv.coe_toAffineEquiv]; rw [← comap_span]; rw [affineSpan_coe_preimage_eq_top]; rw [comap_top]
  exact hscv.affine_preimage
    ((_root_.affineSpan Real s).subtype.comp
      (AffineIsometryEquiv.constVSub Real p').symm.toAffineEquiv.toAffineMap)

中文:
定理 集合.非空.intrinsic整数erior
  条件: (hscv : 凸 实数 s) (hsne : s.非空)
  证明: by
  have := hsne.coe_sort
  obtain ⟨p, hp⟩ := hsne
  let p' : _root_.affineSpan Real s := ⟨p, subset_affineSpan _ _ hp⟩
  rw [intrinsicInterior]; rw [image_nonempty]; rw [aux (AffineIsometryEquiv.constVSub Real p').symm.toHomeomorph]; rw [Convex.interior_nonempty_iff_affineSpan_eq_top]; rw [AffineIsometryEquiv.coe_toHomeomorph]; rw [←
    AffineIsometryEquiv.coe_toAffineEquiv]; rw [← comap_span]; rw [affineSpan_coe_preimage_eq_top]; rw [comap_top]
  exact hscv.affine_preimage
    ((_root_.affineSpan Real s).subtype.comp
      (AffineIsometryEquiv.constVSub Real p').symm.toAffineEquiv.toAffineMap)
-/
protected theorem Set.Nonempty.intrinsicInterior (hscv : Convex Real s) (hsne : s.Nonempty) :
    (intrinsicInterior Real s).Nonempty := by
  have := hsne.coe_sort
  obtain ⟨p, hp⟩ := hsne
  let p' : _root_.affineSpan Real s := ⟨p, subset_affineSpan _ _ hp⟩
  rw [intrinsicInterior]; rw [image_nonempty]; rw [aux (AffineIsometryEquiv.constVSub Real p').symm.toHomeomorph]; rw [Convex.interior_nonempty_iff_affineSpan_eq_top]; rw [AffineIsometryEquiv.coe_toHomeomorph]; rw [←
    AffineIsometryEquiv.coe_toAffineEquiv]; rw [← comap_span]; rw [affineSpan_coe_preimage_eq_top]; rw [comap_top]
  exact hscv.affine_preimage
    ((_root_.affineSpan Real s).subtype.comp
      (AffineIsometryEquiv.constVSub Real p').symm.toAffineEquiv.toAffineMap)

/--
theorem `intrinsicInterior_nonempty` / 定理 `intrinsicInterior_nonempty`

English:
theorem intrinsicInterior_nonempty
  given: (hs : Convex Real s)
  proof: ⟨by simp_rw [nonempty_iff_ne_empty]; rintro h rfl; exact h intrinsicInterior_empty,
    Set.Nonempty.intrinsicInterior hs⟩

中文:
定理 intrinsic整数erior_nonempty
  条件: (hs : 凸 实数 s)
  证明: ⟨by simp_rw [nonempty_iff_ne_empty]; rintro h rfl; exact h intrinsicInterior_empty,
    Set.Nonempty.intrinsicInterior hs⟩

Depends on / 依赖: Nonempty, Set.Nonempty.intrinsicInterior, intrinsicInterior, intrinsicInterior_empty, nonempty_iff_ne_empty, simp_rw
-/
theorem intrinsicInterior_nonempty (hs : Convex Real s) :
    (intrinsicInterior Real s).Nonempty ↔ s.Nonempty :=
  ⟨by simp_rw [nonempty_iff_ne_empty]; rintro h rfl; exact h intrinsicInterior_empty,
    Set.Nonempty.intrinsicInterior hs⟩
