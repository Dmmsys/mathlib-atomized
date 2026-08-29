/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Extreme

/-!
# Convex independence

This file defines convex independent families of points.

Convex independence is closely related to affine independence. In both cases, no point can be
written as a combination of others. When the combination is affine (that is, any coefficients), this
yields affine independence. When the combination is convex (that is, all coefficients are
nonnegative), then this yields convex independence. In particular, affine independence implies
convex independence.

## Main declarations

* `ConvexIndependent p`: Convex independence of the indexed family `p : ι → E`. Every point of the
  family only belongs to convex hulls of sets of the family containing it.
* `convexIndependent_iff_finset`: Carathéodory's theorem allows us to only check finsets to
  conclude convex independence.
* `Convex.convexIndependent_extremePoints`: Extreme points of a convex set are convex independent.

## References

* https://en.wikipedia.org/wiki/Convex_position

## TODO

Prove `AffineIndependent.convexIndependent`. This requires some glue between `affineCombination`
and `Finset.centerMass`.

## Tags

independence, convex position
-/

@[expose] public section


open Affine Finset Function

variable {𝕜 E ι : Type*}

section OrderedSemiring

variable (𝕜) [Semiring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]

/--
Definition of `ConvexIndependent` / `ConvexIndependent` 的定义

English:
definition ConvexIndependent
  signature: (p : ι -> E)
  body: forall (s : Set ι) (x : ι), p x in convexHull 𝕜 (p '' s) -> x in s

中文:
定义 ConvexIndependent
  签名: (p : ι -> E)
  定义体: forall (s : Set ι) (x : ι), p x in convexHull 𝕜 (p '' s) -> x in s

Depends on / 依赖: convexHull
-/
def ConvexIndependent (p : ι -> E) : Prop :=
  forall (s : Set ι) (x : ι), p x in convexHull 𝕜 (p '' s) -> x in s

variable {𝕜}

/--
theorem `Subsingleton.convexIndependent` / 定理 `Subsingleton.convexIndependent`

English:
theorem Subsingleton.convexIndependent
  given: [Subsingleton ι] (p : ι -> E)
  statement: ConvexIndependent 𝕜 p
  proof: by
  intro s x hx
  have : (convexHull 𝕜 (p '' s)).Nonempty := ⟨p x, hx⟩
  rw [convexHull_nonempty_iff]; rw [Set.image_nonempty] at this
  rwa [Subsingleton.mem_iff_nonempty]

中文:
定理 Subsingleton.convexIndependent
  条件: [Subsingleton ι] (p : ι -> E)
  结论: ConvexIndependent 𝕜 p
  证明: by
  intro s x hx
  have : (convexHull 𝕜 (p '' s)).Nonempty := ⟨p x, hx⟩
  rw [convexHull_nonempty_iff]; rw [Set.image_nonempty] at this
  rwa [Subsingleton.mem_iff_nonempty]

Depends on / 依赖: Nonempty, Set.image_nonempty, Subsingleton, Subsingleton.mem_iff_nonempty, convexHull, convexHull_nonempty_iff, image_nonempty, mem_iff_nonempty
-/
theorem Subsingleton.convexIndependent [Subsingleton ι] (p : ι -> E) : ConvexIndependent 𝕜 p := by
  intro s x hx
  have : (convexHull 𝕜 (p '' s)).Nonempty := ⟨p x, hx⟩
  rw [convexHull_nonempty_iff]; rw [Set.image_nonempty] at this
  rwa [Subsingleton.mem_iff_nonempty]

/--
theorem `ConvexIndependent.injective` / 定理 `ConvexIndependent.injective`

English:
theorem ConvexIndependent.injective
  given: {p : ι -> E} (hc : ConvexIndependent 𝕜 p)
  proof: by
  refine fun i j hij => hc {j} i ?_
  rw [hij]; rw [Set.image_singleton]; rw [convexHull_singleton]
  exact Set.mem_singleton _

中文:
定理 ConvexIndependent.injective
  条件: {p : ι -> E} (hc : ConvexIndependent 𝕜 p)
  证明: by
  refine fun i j hij => hc {j} i ?_
  rw [hij]; rw [Set.image_singleton]; rw [convexHull_singleton]
  exact Set.mem_singleton _
-/
protected theorem ConvexIndependent.injective {p : ι -> E} (hc : ConvexIndependent 𝕜 p) :
    Function.Injective p := by
  refine fun i j hij => hc {j} i ?_
  rw [hij]; rw [Set.image_singleton]; rw [convexHull_singleton]
  exact Set.mem_singleton _

/--
theorem `ConvexIndependent.comp_embedding` / 定理 `ConvexIndependent.comp_embedding`

English:
theorem ConvexIndependent.comp_embedding
  statement: {ι' : Type*} (f : ι' ↪ ι) {p : ι -> E}
  proof: by
  intro s x hx
  rw [← f.injective.mem_set_image]
  exact hc _ _ (by rwa [Set.image_image])

中文:
定理 ConvexIndependent.comp_embedding
  结论: {ι' : 类型} (f : ι' ↪ ι) {p : ι -> E}
  证明: by
  intro s x hx
  rw [← f.injective.mem_set_image]
  exact hc _ _ (by rwa [Set.image_image])

Depends on / 依赖: Set.image_image, f.injective.mem_set_image, image_image, injective, mem_set_image
-/
theorem ConvexIndependent.comp_embedding {ι' : Type*} (f : ι' ↪ ι) {p : ι -> E}
    (hc : ConvexIndependent 𝕜 p) : ConvexIndependent 𝕜 (p ∘ f) := by
  intro s x hx
  rw [← f.injective.mem_set_image]
  exact hc _ _ (by rwa [Set.image_image])

/--
theorem `ConvexIndependent.subtype` / 定理 `ConvexIndependent.subtype`

English:
theorem ConvexIndependent.subtype
  given: {p : ι -> E} (hc : ConvexIndependent 𝕜 p) (s : Set ι)
  proof: hc.comp_embedding (Embedding.subtype _)

中文:
定理 ConvexIndependent.subtype
  条件: {p : ι -> E} (hc : ConvexIndependent 𝕜 p) (s : Set ι)
  证明: hc.comp_embedding (Embedding.subtype _)
-/
protected theorem ConvexIndependent.subtype {p : ι -> E} (hc : ConvexIndependent 𝕜 p) (s : Set ι) :
    ConvexIndependent 𝕜 fun i : s => p i :=
  hc.comp_embedding (Embedding.subtype _)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ConvexIndependent.range` / 定理 `ConvexIndependent.range`

English:
theorem ConvexIndependent.range
  given: {p : ι -> E} (hc : ConvexIndependent 𝕜 p)
  proof: by
  let f : Set.range p -> ι := fun x => x.property.choose
  have hf : forall x, p (f x) = x := fun x => x.property.choose_spec
  let fe : Set.range p ↪ ι := ⟨f, fun x₁ x₂ he => Subtype.ext (hf x₁ ▸ hf x₂ ▸ he ▸ rfl)⟩
  convert! hc.comp_embedding fe
  ext
  rw [Embedding.coeFn_mk]; rw [comp_apply];

中文:
定理 ConvexIndependent.range
  条件: {p : ι -> E} (hc : ConvexIndependent 𝕜 p)
  证明: by
  let f : Set.range p -> ι := fun x => x.property.choose
  have hf : forall x, p (f x) = x := fun x => x.property.choose_spec
  let fe : Set.range p ↪ ι := ⟨f, fun x₁ x₂ he => Subtype.ext (hf x₁ ▸ hf x₂ ▸ he ▸ rfl)⟩
  convert! hc.comp_embedding fe
  ext
  rw [Embedding.coeFn_mk]; rw [comp_apply];
-/
protected theorem ConvexIndependent.range {p : ι -> E} (hc : ConvexIndependent 𝕜 p) :
    ConvexIndependent 𝕜 ((↑) : Set.range p -> E) := by
  let f : Set.range p -> ι := fun x => x.property.choose
  have hf : forall x, p (f x) = x := fun x => x.property.choose_spec
  let fe : Set.range p ↪ ι := ⟨f, fun x₁ x₂ he => Subtype.ext (hf x₁ ▸ hf x₂ ▸ he ▸ rfl)⟩
  convert! hc.comp_embedding fe
  ext
  rw [Embedding.coeFn_mk]; rw [comp_apply]; rw [hf]

/--
theorem `ConvexIndependent.mono` / 定理 `ConvexIndependent.mono`

English:
theorem ConvexIndependent.mono
  statement: {s t : Set E} (hc : ConvexIndependent 𝕜 ((↑) : t -> E))
  proof: hc.comp_embedding (s.embeddingOfSubset t hs)

中文:
定理 ConvexIndependent.mono
  结论: {s t : Set E} (hc : ConvexIndependent 𝕜 ((↑) : t -> E))
  证明: hc.comp_embedding (s.embeddingOfSubset t hs)
-/
protected theorem ConvexIndependent.mono {s t : Set E} (hc : ConvexIndependent 𝕜 ((↑) : t -> E))
    (hs : s subseteq t) : ConvexIndependent 𝕜 ((↑) : s -> E) :=
  hc.comp_embedding (s.embeddingOfSubset t hs)

/--
theorem `Function.Injective.convexIndependent_iff_set` / 定理 `Function.Injective.convexIndependent_iff_set`

English:
theorem Function.Injective.convexIndependent_iff_set
  given: {p : ι -> E} (hi : Function.Injective p)
  proof: ⟨fun hc =>
    hc.comp_embedding
      (⟨fun i => ⟨p i, Set.mem_range_self _⟩, fun _ _ h => hi (Subtype.mk_eq_mk.1 h)⟩ :
        ι ↪ Set.range p),
    ConvexIndependent.range⟩

中文:
定理 Function.Injective.convexIndependent_iff_set
  条件: {p : ι -> E} (hi : Function.Injective p)
  证明: ⟨fun hc =>
    hc.comp_embedding
      (⟨fun i => ⟨p i, Set.mem_range_self _⟩, fun _ _ h => hi (Subtype.mk_eq_mk.1 h)⟩ :
        ι ↪ Set.range p),
    ConvexIndependent.range⟩

Depends on / 依赖: ConvexIndependent, ConvexIndependent.range, Set.mem_range_self, Set.range, Subtype, Subtype.mk_eq_mk, comp_embedding, hc.comp_embedding, mem_range_self, mk_eq_mk
-/
theorem Function.Injective.convexIndependent_iff_set {p : ι -> E} (hi : Function.Injective p) :
    ConvexIndependent 𝕜 ((↑) : Set.range p -> E) ↔ ConvexIndependent 𝕜 p :=
  ⟨fun hc =>
    hc.comp_embedding
      (⟨fun i => ⟨p i, Set.mem_range_self _⟩, fun _ _ h => hi (Subtype.mk_eq_mk.1 h)⟩ :
        ι ↪ Set.range p),
    ConvexIndependent.range⟩

/-- If a family is convex independent, a point in the family is in the convex hull of some of the
points given by a subset of the index type if and only if the point's index is in this subset. -/
@[simp]
/--
theorem `ConvexIndependent.mem_convexHull_iff` / 定理 `ConvexIndependent.mem_convexHull_iff`

English:
theorem ConvexIndependent.mem_convexHull_iff
  statement: {p : ι -> E} (hc : ConvexIndependent 𝕜 p)
  proof: ⟨hc _ _, fun hi => subset_convexHull 𝕜 _ (Set.mem_image_of_mem p hi)⟩

中文:
定理 ConvexIndependent.mem_convexHull_iff
  结论: {p : ι -> E} (hc : ConvexIndependent 𝕜 p)
  证明: ⟨hc _ _, fun hi => subset_convexHull 𝕜 _ (Set.mem_image_of_mem p hi)⟩
-/
protected theorem ConvexIndependent.mem_convexHull_iff {p : ι -> E} (hc : ConvexIndependent 𝕜 p)
    (s : Set ι) (i : ι) : p i in convexHull 𝕜 (p '' s) ↔ i in s :=
  ⟨hc _ _, fun hi => subset_convexHull 𝕜 _ (Set.mem_image_of_mem p hi)⟩

/--
theorem `convexIndependent_iff_notMem_convexHull_sdiff` / 定理 `convexIndependent_iff_notMem_convexHull_sdiff`

English:
theorem convexIndependent_iff_notMem_convexHull_sdiff
  given: {p : ι -> E}
  proof: by
  refine ⟨fun hc i s h => ?_, fun h s i hi => ?_⟩
  · rw [hc.mem_convexHull_iff] at h
    exact h.2 (Set.mem_singleton _)
  · by_contra H
    refine h i s ?_
    rw [Set.sdiff_singleton_eq_self H]
    exact hi

@[deprecated (since := "2026-06-03")]
alias convexIndependent_iff_notMem_convexHull_di

中文:
定理 convexIndependent_iff_notMem_convexHull_sdiff
  条件: {p : ι -> E}
  证明: by
  refine ⟨fun hc i s h => ?_, fun h s i hi => ?_⟩
  · rw [hc.mem_convexHull_iff] at h
    exact h.2 (Set.mem_singleton _)
  · by_contra H
    refine h i s ?_
    rw [Set.sdiff_singleton_eq_self H]
    exact hi

@[deprecated (since := "2026-06-03")]
alias convexIndependent_iff_notMem_convexHull_di

Depends on / 依赖: Set.mem_singleton, Set.sdiff_singleton_eq_self, hc.mem_convexHull_iff, mem_convexHull_iff, mem_singleton, sdiff_singleton_eq_self
-/
theorem convexIndependent_iff_notMem_convexHull_sdiff {p : ι -> E} :
    ConvexIndependent 𝕜 p ↔ forall i s, p i ∉ convexHull 𝕜 (p '' (s \ {i})) := by
  refine ⟨fun hc i s h => ?_, fun h s i hi => ?_⟩
  · rw [hc.mem_convexHull_iff] at h
    exact h.2 (Set.mem_singleton _)
  · by_contra H
    refine h i s ?_
    rw [Set.sdiff_singleton_eq_self H]
    exact hi

@[deprecated (since := "2026-06-03")]
alias convexIndependent_iff_notMem_convexHull_diff := convexIndependent_iff_notMem_convexHull_sdiff

/--
theorem `convexIndependent_set_iff_inter_convexHull_subset` / 定理 `convexIndependent_set_iff_inter_convexHull_subset`

English:
theorem convexIndependent_set_iff_inter_convexHull_subset
  given: {s : Set E}
  proof: by
  constructor
  · rintro hc t h x ⟨hxs, hxt⟩
    refine hc { x | ↑x in t } ⟨x, hxs⟩ ?_
    rw [Subtype.coe_image_of_subset h]
    exact hxt
  · intro hc t x h
    rw [← Subtype.coe_injective.mem_set_image]
    exact hc (t.image ((↑) : s -> E)) (Subtype.coe_image_subset s t) ⟨x.prop, h⟩

中文:
定理 convexIndependent_set_iff_inter_convexHull_subset
  条件: {s : Set E}
  证明: by
  constructor
  · rintro hc t h x ⟨hxs, hxt⟩
    refine hc { x | ↑x in t } ⟨x, hxs⟩ ?_
    rw [Subtype.coe_image_of_subset h]
    exact hxt
  · intro hc t x h
    rw [← Subtype.coe_injective.mem_set_image]
    exact hc (t.image ((↑) : s -> E)) (Subtype.coe_image_subset s t) ⟨x.prop, h⟩

Depends on / 依赖: Subtype, Subtype.coe_image_of_subset, Subtype.coe_image_subset, Subtype.coe_injective.mem_set_image, coe_image_of_subset, coe_image_subset, coe_injective, mem_set_image, t.image, x.prop
-/
theorem convexIndependent_set_iff_inter_convexHull_subset {s : Set E} :
    ConvexIndependent 𝕜 ((↑) : s -> E) ↔ forall t, t subseteq s -> s inter convexHull 𝕜 t subseteq t := by
  constructor
  · rintro hc t h x ⟨hxs, hxt⟩
    refine hc { x | ↑x in t } ⟨x, hxs⟩ ?_
    rw [Subtype.coe_image_of_subset h]
    exact hxt
  · intro hc t x h
    rw [← Subtype.coe_injective.mem_set_image]
    exact hc (t.image ((↑) : s -> E)) (Subtype.coe_image_subset s t) ⟨x.prop, h⟩

/--
theorem `convexIndependent_set_iff_notMem_convexHull_sdiff` / 定理 `convexIndependent_set_iff_notMem_convexHull_sdiff`

English:
theorem convexIndependent_set_iff_notMem_convexHull_sdiff
  given: {s : Set E}
  proof: by
  rw [convexIndependent_set_iff_inter_convexHull_subset]
  constructor
  · rintro hs x hxs hx
    exact (hs _ Set.sdiff_subset ⟨hxs, hx⟩).2 (Set.mem_singleton _)
  · rintro hs t ht x ⟨hxs, hxt⟩
    by_contra h
    exact hs _ hxs (convexHull_mono (Set.subset_sdiff_singleton ht h) hxt)

@[deprecate

中文:
定理 convexIndependent_set_iff_notMem_convexHull_sdiff
  条件: {s : Set E}
  证明: by
  rw [convexIndependent_set_iff_inter_convexHull_subset]
  constructor
  · rintro hs x hxs hx
    exact (hs _ Set.sdiff_subset ⟨hxs, hx⟩).2 (Set.mem_singleton _)
  · rintro hs t ht x ⟨hxs, hxt⟩
    by_contra h
    exact hs _ hxs (convexHull_mono (Set.subset_sdiff_singleton ht h) hxt)

@[deprecate

Depends on / 依赖: Set.mem_singleton, Set.sdiff_subset, Set.subset_sdiff_singleton, convexHull_mono, convexIndependent_set_iff_inter_convexHull_subset, mem_singleton, sdiff_subset, subset_sdiff_singleton
-/
theorem convexIndependent_set_iff_notMem_convexHull_sdiff {s : Set E} :
    ConvexIndependent 𝕜 ((↑) : s -> E) ↔ forall x in s, x ∉ convexHull 𝕜 (s \ {x}) := by
  rw [convexIndependent_set_iff_inter_convexHull_subset]
  constructor
  · rintro hs x hxs hx
    exact (hs _ Set.sdiff_subset ⟨hxs, hx⟩).2 (Set.mem_singleton _)
  · rintro hs t ht x ⟨hxs, hxt⟩
    by_contra h
    exact hs _ hxs (convexHull_mono (Set.subset_sdiff_singleton ht h) hxt)

@[deprecated (since := "2026-06-03")]
alias convexIndependent_set_iff_notMem_convexHull_diff :=
  convexIndependent_set_iff_notMem_convexHull_sdiff

end OrderedSemiring

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {s : Set E}

open scoped Classical in
/--
theorem `convexIndependent_iff_finset` / 定理 `convexIndependent_iff_finset`

English:
theorem convexIndependent_iff_finset
  given: {p : ι -> E}
  proof: by
  refine ⟨fun hc s x hx => hc s x ?_, fun h s x hx => ?_⟩
  · rwa [Finset.coe_image] at hx
  have hp : Injective p := by
    rintro a b hab
    rw [← mem_singleton]
    refine h {b} a ?_
    rw [hab]; rw [image_singleton]; rw [coe_singleton]; rw [convexHull_singleton]
    exact Set.mem_singleton 

中文:
定理 convexIndependent_iff_finset
  条件: {p : ι -> E}
  证明: by
  refine ⟨fun hc s x hx => hc s x ?_, fun h s x hx => ?_⟩
  · rwa [Finset.coe_image] at hx
  have hp : Injective p := by
    rintro a b hab
    rw [← mem_singleton]
    refine h {b} a ?_
    rw [hab]; rw [image_singleton]; rw [coe_singleton]; rw [convexHull_singleton]
    exact Set.mem_singleton 

Depends on / 依赖: Finset, Finset.coe_image, Injective, Set.mem_iUnion, Set.mem_singleton, coe_image, coe_singleton, convexHull_eq_union_convexHull_finite_subsets, convexHull_singleton, hp.injOn, hp.mem_set_image, image_singleton, mem_coe, mem_iUnion, mem_preimage, mem_set_image, mem_singleton, preimage, simp_rw, t.preimage
-/
theorem convexIndependent_iff_finset {p : ι -> E} :
    ConvexIndependent 𝕜 p ↔
      forall (s : Finset ι) (x : ι), p x in convexHull 𝕜 (s.image p : Set E) -> x in s := by
  refine ⟨fun hc s x hx => hc s x ?_, fun h s x hx => ?_⟩
  · rwa [Finset.coe_image] at hx
  have hp : Injective p := by
    rintro a b hab
    rw [← mem_singleton]
    refine h {b} a ?_
    rw [hab]; rw [image_singleton]; rw [coe_singleton]; rw [convexHull_singleton]
    exact Set.mem_singleton _
  rw [convexHull_eq_union_convexHull_finite_subsets] at hx
  simp_rw [Set.mem_iUnion] at hx
  obtain ⟨t, ht, hx⟩ := hx
  rw [← hp.mem_set_image]
  refine ht ?_
  suffices x in t.preimage p hp.injOn by rwa [mem_preimage, ← mem_coe] at this
  refine h _ x ?_
  rwa [t.image_preimage p hp.injOn, filter_true_of_mem]
  exact fun y hy => s.image_subset_range p (ht <| mem_coe.2 hy)



/--
theorem `Convex.convexIndependent_extremePoints` / 定理 `Convex.convexIndependent_extremePoints`

English:
theorem Convex.convexIndependent_extremePoints
  given: (hs : Convex 𝕜 s)
  proof: convexIndependent_set_iff_notMem_convexHull_sdiff.2 fun _ hx h =>
    (extremePoints_convexHull_subset
          (inter_extremePoints_subset_extremePoints_of_subset
            (convexHull_min (Set.sdiff_subset.trans extremePoints_subset) hs) ⟨h, hx⟩)).2
      (Set.mem_singleton _)

中文:
定理 Convex.convexIndependent_extremePoints
  条件: (hs : Convex 𝕜 s)
  证明: convexIndependent_set_iff_notMem_convexHull_sdiff.2 fun _ hx h =>
    (extremePoints_convexHull_subset
          (inter_extremePoints_subset_extremePoints_of_subset
            (convexHull_min (Set.sdiff_subset.trans extremePoints_subset) hs) ⟨h, hx⟩)).2
      (Set.mem_singleton _)

Depends on / 依赖: Set.mem_singleton, Set.sdiff_subset.trans, convexHull_min, convexIndependent_set_iff_notMem_convexHull_sdiff, extremePoints_convexHull_subset, extremePoints_subset, inter_extremePoints_subset_extremePoints_of_subset, mem_singleton, sdiff_subset
-/
theorem Convex.convexIndependent_extremePoints (hs : Convex 𝕜 s) :
    ConvexIndependent 𝕜 ((↑) : s.extremePoints 𝕜 -> E) :=
  convexIndependent_set_iff_notMem_convexHull_sdiff.2 fun _ hx h =>
    (extremePoints_convexHull_subset
          (inter_extremePoints_subset_extremePoints_of_subset
            (convexHull_min (Set.sdiff_subset.trans extremePoints_subset) hs) ⟨h, hx⟩)).2
      (Set.mem_singleton _)

end LinearOrderedField
