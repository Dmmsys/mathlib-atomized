/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import Mathlib.Topology.SeparatedMap

/-!
# Local homeomorphisms

This file defines local homeomorphisms.

## Main definitions

For a function `f : X → Y ` between topological spaces, we say
* `IsLocalHomeomorphOn f s` if `f` is a local homeomorphism around each point of `s`: for each
  `x : X`, the restriction of `f` to some open neighborhood `U` of `x` gives a homeomorphism
  between `U` and an open subset of `Y`.
* `IsLocalHomeomorph f`: `f` is a local homeomorphism, i.e. it's a local homeomorphism on `univ`.

Note that `IsLocalHomeomorph` is a global condition. This is in contrast to
`OpenPartialHomeomorph`, which is a homeomorphism between specific open subsets.

## Main results
* local homeomorphisms are locally injective open maps
* more!

-/

@[expose] public section


open Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (g : Y -> Z)
  (f : X -> Y) (s : Set X) (t : Set Y)

/--
Definition of `IsLocalHomeomorphOn` / `IsLocalHomeomorphOn` 的定义

English:
definition IsLocalHomeomorphOn
  body: forall x in s, exists e : OpenPartialHomeomorph X Y, x in e.source ∧ f = e

中文:
定义 IsLocalHomeomorphOn
  定义体: forall x in s, exists e : OpenPartialHomeomorph X Y, x in e.source ∧ f = e

Depends on / 依赖: OpenPartialHomeomorph, e.source, source
-/
def IsLocalHomeomorphOn :=
  forall x in s, exists e : OpenPartialHomeomorph X Y, x in e.source ∧ f = e

/--
theorem `isLocalHomeomorphOn_iff_isOpenEmbedding_restrict` / 定理 `isLocalHomeomorphOn_iff_isOpenEmbedding_restrict`

English:
theorem isLocalHomeomorphOn_iff_isOpenEmbedding_restrict
  given: {f : X -> Y}
  proof: by
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · obtain ⟨e, hxe, rfl⟩ := h x hx
    exact ⟨e.source, e.open_source.mem_nhds hxe, e.isOpenEmbedding_restrict⟩
  · obtain ⟨U, hU, emb⟩ := h x hx
    have : IsOpenEmbedding ((interior U).domRestrict f) := by
      refine emb.comp ⟨.inclusion interior_

中文:
定理 isLocalHomeomorphOn_iff_isOpenEmbedding_restrict
  条件: {f : X -> Y}
  证明: by
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · obtain ⟨e, hxe, rfl⟩ := h x hx
    exact ⟨e.source, e.open_source.mem_nhds hxe, e.isOpenEmbedding_restrict⟩
  · obtain ⟨U, hU, emb⟩ := h x hx
    have : IsOpenEmbedding ((interior U).domRestrict f) := by
      refine emb.comp ⟨.inclusion interior_

Depends on / 依赖: IsOpenEmbedding, Nonempty, OpenPartialHomeomorph, OpenPartialHomeomorph.o, Set.range_inclusion, domRestrict, e.isOpenEmbedding_restrict, e.open_source.mem_nhds, e.source, emb.comp, inclusion, interior, interior_subset, isOpenEmbedding_iff_continuous_injective_isOpenMap, isOpenEmbedding_iff_continuous_injective_isOpenMap.mp, isOpenEmbedding_restrict, isOpen_induced, isOpen_interior, mem_nhds, openMap
-/
theorem isLocalHomeomorphOn_iff_isOpenEmbedding_restrict {f : X -> Y} :
    IsLocalHomeomorphOn f s ↔ forall x in s, exists U in 𝓝 x, IsOpenEmbedding (U.domRestrict f) := by
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · obtain ⟨e, hxe, rfl⟩ := h x hx
    exact ⟨e.source, e.open_source.mem_nhds hxe, e.isOpenEmbedding_restrict⟩
  · obtain ⟨U, hU, emb⟩ := h x hx
    have : IsOpenEmbedding ((interior U).domRestrict f) := by
      refine emb.comp ⟨.inclusion interior_subset, ?_⟩
      rw [Set.range_inclusion]; exact isOpen_induced isOpen_interior
    obtain ⟨cont, inj, openMap⟩ := isOpenEmbedding_iff_continuous_injective_isOpenMap.mp this
    have : Nonempty X := ⟨x⟩
    exact ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict
      (Set.injOn_iff_injective.mpr inj).toPartialEquiv
      (continuousOn_iff_continuous_domRestrict.mpr cont) openMap isOpen_interior,
      mem_interior_iff_mem_nhds.mpr hU, rfl⟩

namespace IsLocalHomeomorphOn

variable {f s}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `discreteTopology_of_image` / 定理 `discreteTopology_of_image`

English:
theorem discreteTopology_of_image
  statement: (h : IsLocalHomeomorphOn f s)
  proof: discreteTopology_iff_isOpen_singleton.mpr fun x => by
    obtain ⟨e, hx, rfl⟩ := h x x.2
    have ⟨U, hU, eq⟩ := isOpen_discrete {(⟨_, _, x.2, rfl⟩ : e '' s)}
    refine ⟨e.source inter e ⁻¹' U, e.continuousOn_toFun.isOpen_inter_preimage e.open_source hU,
      subset_antisymm (fun x' mem => Subtype

中文:
定理 discreteTopology_of_image
  结论: (h : IsLocalHomeomorphOn f s)
  证明: discreteTopology_iff_isOpen_singleton.mpr fun x => by
    obtain ⟨e, hx, rfl⟩ := h x x.2
    have ⟨U, hU, eq⟩ := isOpen_discrete {(⟨_, _, x.2, rfl⟩ : e '' s)}
    refine ⟨e.source inter e ⁻¹' U, e.continuousOn_toFun.isOpen_inter_preimage e.open_source hU,
      subset_antisymm (fun x' mem => Subtype

Depends on / 依赖: Set.subset_singleton_iff, Subtype, Subtype.ext, continuousOn_toFun, discreteTopology_iff_isOpen_singleton, discreteTopology_iff_isOpen_singleton.mpr, e.continuousOn_toFun.isOpen_inter_preimage, e.injOn, e.open_source, e.source, eq.subset, eq.superset, isOpen_discrete, isOpen_inter_preimage, open_source, source, subset, subset_antisymm, subset_singleton_iff, superset
-/
theorem discreteTopology_of_image (h : IsLocalHomeomorphOn f s)
    [DiscreteTopology (f '' s)] : DiscreteTopology s :=
  discreteTopology_iff_isOpen_singleton.mpr fun x => by
    obtain ⟨e, hx, rfl⟩ := h x x.2
    have ⟨U, hU, eq⟩ := isOpen_discrete {(⟨_, _, x.2, rfl⟩ : e '' s)}
    refine ⟨e.source inter e ⁻¹' U, e.continuousOn_toFun.isOpen_inter_preimage e.open_source hU,
      subset_antisymm (fun x' mem => Subtype.ext <| e.injOn mem.1 hx ?_) ?_⟩
    · simpa using Set.subset_singleton_iff.1 eq.subset ⟨_, x', x'.2, rfl⟩ mem.2
    · rintro x rfl; exact ⟨hx, eq.superset rfl⟩

/--
lemma `isDiscrete_of_image` / 引理 `isDiscrete_of_image`

English:
lemma isDiscrete_of_image
  statement: (h : IsLocalHomeomorphOn f s)
  proof: have := hs.1; ⟨discreteTopology_of_image h⟩

中文:
引理 isDiscrete_of_image
  结论: (h : IsLocalHomeomorphOn f s)
  证明: have := hs.1; ⟨discreteTopology_of_image h⟩

Depends on / 依赖: discreteTopology_of_image
-/
lemma isDiscrete_of_image (h : IsLocalHomeomorphOn f s)
    (hs : IsDiscrete (f '' s)) : IsDiscrete s :=
  have := hs.1; ⟨discreteTopology_of_image h⟩

/--
theorem `discreteTopology_image_iff` / 定理 `discreteTopology_image_iff`

English:
theorem discreteTopology_image_iff
  given: (h : IsLocalHomeomorphOn f s) (hs : IsOpen s)
  proof: by
  refine ⟨fun _ => h.discreteTopology_of_image, ?_⟩
  simp_rw [discreteTopology_iff_isOpen_singleton]
  rintro hX ⟨_, x, hx, rfl⟩
  obtain ⟨e, hxe, rfl⟩ := h x hx
  refine ⟨e '' {x}, e.isOpen_image_of_subset_source ?_ (Set.singleton_subset_iff.mpr hxe), ?_⟩
  · simpa using hs.isOpenMap_subtype_va

中文:
定理 discreteTopology_image_iff
  条件: (h : IsLocalHomeomorphOn f s) (hs : IsOpen s)
  证明: by
  refine ⟨fun _ => h.discreteTopology_of_image, ?_⟩
  simp_rw [discreteTopology_iff_isOpen_singleton]
  rintro hX ⟨_, x, hx, rfl⟩
  obtain ⟨e, hxe, rfl⟩ := h x hx
  refine ⟨e '' {x}, e.isOpen_image_of_subset_source ?_ (Set.singleton_subset_iff.mpr hxe), ?_⟩
  · simpa using hs.isOpenMap_subtype_va

Depends on / 依赖: Set.singleton_subset_iff.mpr, Subtype, Subtype.ext_iff, discreteTopology_iff_isOpen_singleton, discreteTopology_of_image, e.isOpen_image_of_subset_source, ext_iff, h.discreteTopology_of_image, hs.isOpenMap_subtype_val, isOpenMap_subtype_val, isOpen_image_of_subset_source, simp_rw, singleton_subset_iff
-/
theorem discreteTopology_image_iff (h : IsLocalHomeomorphOn f s) (hs : IsOpen s) :
    DiscreteTopology (f '' s) ↔ DiscreteTopology s := by
  refine ⟨fun _ => h.discreteTopology_of_image, ?_⟩
  simp_rw [discreteTopology_iff_isOpen_singleton]
  rintro hX ⟨_, x, hx, rfl⟩
  obtain ⟨e, hxe, rfl⟩ := h x hx
  refine ⟨e '' {x}, e.isOpen_image_of_subset_source ?_ (Set.singleton_subset_iff.mpr hxe), ?_⟩
  · simpa using hs.isOpenMap_subtype_val _ (hX ⟨x, hx⟩)
  · ext; simp [Subtype.ext_iff]

/--
lemma `isDiscrete_image_iff` / 引理 `isDiscrete_image_iff`

English:
lemma isDiscrete_image_iff
  given: (h : IsLocalHomeomorphOn f s) (hs : IsOpen s)
  proof: .mpr hs'.to_subtype⟩⟩ ⟨h.isDiscrete_of_image, fun hs' => ⟨h.discreteTopology_image_iff hs

中文:
引理 isDiscrete_image_iff
  条件: (h : IsLocalHomeomorphOn f s) (hs : IsOpen s)
  证明: .mpr hs'.to_subtype⟩⟩ ⟨h.isDiscrete_of_image, fun hs' => ⟨h.discreteTopology_image_iff hs

Depends on / 依赖: discreteTopology_image_iff, h.discreteTopology_image_iff, h.isDiscrete_of_image, isDiscrete_of_image, to_subtype
-/
lemma isDiscrete_image_iff (h : IsLocalHomeomorphOn f s) (hs : IsOpen s) :
    IsDiscrete (f '' s) ↔ IsDiscrete s :=
.mpr hs'.to_subtype⟩⟩ ⟨h.isDiscrete_of_image, fun hs' => ⟨h.discreteTopology_image_iff hs

variable (f s) in
/--
theorem `mk` / 定理 `mk`

English:
theorem mk
  given: (h : forall x in s, exists e : OpenPartialHomeomorph X Y, x in e.source ∧ Set.EqOn f e e.source)
  proof: by
  intro x hx
  obtain ⟨e, hx, he⟩ := h x hx
  exact
    ⟨{ e with
        toFun := f
        map_source' := fun _x hx => by rw [he hx]; exact e.map_source' hx
        left_inv' := fun _x hx => by rw [he hx]; exact e.left_inv' hx
        right_inv' := fun _y hy => by rw [he (e.map_target' hy)]; ex

中文:
定理 mk
  条件: (h : 对任意 x in s, 存在 e : OpenPartialHomeomorph X Y, x in e.source ∧ Set.EqOn f e e.source)
  证明: by
  intro x hx
  obtain ⟨e, hx, he⟩ := h x hx
  exact
    ⟨{ e with
        toFun := f
        map_source' := fun _x hx => by rw [he hx]; exact e.map_source' hx
        left_inv' := fun _x hx => by rw [he hx]; exact e.left_inv' hx
        right_inv' := fun _y hy => by rw [he (e.map_target' hy)]; ex

Depends on / 依赖: continuousOn_congr, continuousOn_toFun, e.continuousOn_toFun, e.left_inv, e.map_source, e.map_target, e.right_inv, left_inv, map_source, map_target, right_inv
-/
theorem mk (h : forall x in s, exists e : OpenPartialHomeomorph X Y, x in e.source ∧ Set.EqOn f e e.source) :
    IsLocalHomeomorphOn f s := by
  intro x hx
  obtain ⟨e, hx, he⟩ := h x hx
  exact
    ⟨{ e with
        toFun := f
        map_source' := fun _x hx => by rw [he hx]; exact e.map_source' hx
        left_inv' := fun _x hx => by rw [he hx]; exact e.left_inv' hx
        right_inv' := fun _y hy => by rw [he (e.map_target' hy)]; exact e.right_inv' hy
        continuousOn_toFun := (continuousOn_congr he).mpr e.continuousOn_toFun },
      hx, rfl⟩

/--
lemma `OpenPartialHomeomorph.isLocalHomeomorphOn` / 引理 `OpenPartialHomeomorph.isLocalHomeomorphOn`

English:
lemma OpenPartialHomeomorph.isLocalHomeomorphOn
  given: (e : OpenPartialHomeomorph X Y)
  proof: fun _ hx => ⟨e, hx, rfl⟩

中文:
引理 OpenPartialHomeomorph.isLocalHomeomorphOn
  条件: (e : OpenPartialHomeomorph X Y)
  证明: fun _ hx => ⟨e, hx, rfl⟩
-/
lemma OpenPartialHomeomorph.isLocalHomeomorphOn (e : OpenPartialHomeomorph X Y) :
    IsLocalHomeomorphOn e e.source :=
  fun _ hx => ⟨e, hx, rfl⟩

variable {g t}

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: {t : Set X} (hf : IsLocalHomeomorphOn f t) (hst : s subseteq t)
  statement: IsLocalHomeomorphOn f s
  proof: fun x hx => hf x (hst hx)

中文:
定理 mono
  条件: {t : Set X} (hf : IsLocalHomeomorphOn f t) (hst : s subseteq t)
  结论: IsLocalHomeomorphOn f s
  证明: fun x hx => hf x (hst hx)
-/
theorem mono {t : Set X} (hf : IsLocalHomeomorphOn f t) (hst : s subseteq t) : IsLocalHomeomorphOn f s :=
  fun x hx => hf x (hst hx)

/--
theorem `of_comp_left` / 定理 `of_comp_left`

English:
theorem of_comp_left
  statement: (hgf : IsLocalHomeomorphOn (g ∘ f) s) (hg : IsLocalHomeomorphOn g (f '' s))
  proof: mk f s fun x hx => by
  obtain ⟨g, hxg, rfl⟩ := hg (f x) ⟨x, hx, rfl⟩
  obtain ⟨gf, hgf, he⟩ := hgf x hx
  refine ⟨(gf.restr <| f ⁻¹' g.source).trans g.symm, ⟨⟨hgf, mem_interior_iff_mem_nhds.mpr
    ((cont x hx).preimage_mem_nhds <| g.open_source.mem_nhds hxg)⟩, he ▸ g.map_source hxg⟩,
    fun y hy 

中文:
定理 of_comp_left
  结论: (hgf : IsLocalHomeomorphOn (g ∘ f) s) (hg : IsLocalHomeomorphOn g (f '' s))
  证明: mk f s fun x hx => by
  obtain ⟨g, hxg, rfl⟩ := hg (f x) ⟨x, hx, rfl⟩
  obtain ⟨gf, hgf, he⟩ := hgf x hx
  refine ⟨(gf.restr <| f ⁻¹' g.source).trans g.symm, ⟨⟨hgf, mem_interior_iff_mem_nhds.mpr
    ((cont x hx).preimage_mem_nhds <| g.open_source.mem_nhds hxg)⟩, he ▸ g.map_source hxg⟩,
    fun y hy 

Depends on / 依赖: Function, Function.comp_apply, comp_apply, eq_symm_apply, g.eq_symm_apply, g.map_source, g.open_source.mem_nhds, g.source, g.symm, gf.restr, interior_subset, map_source, mem_interior_iff_mem_nhds, mem_interior_iff_mem_nhds.mpr, mem_nhds, open_source, preimage_mem_nhds, source
-/
theorem of_comp_left (hgf : IsLocalHomeomorphOn (g ∘ f) s) (hg : IsLocalHomeomorphOn g (f '' s))
    (cont : forall x in s, ContinuousAt f x) : IsLocalHomeomorphOn f s := mk f s fun x hx => by
  obtain ⟨g, hxg, rfl⟩ := hg (f x) ⟨x, hx, rfl⟩
  obtain ⟨gf, hgf, he⟩ := hgf x hx
  refine ⟨(gf.restr <| f ⁻¹' g.source).trans g.symm, ⟨⟨hgf, mem_interior_iff_mem_nhds.mpr
    ((cont x hx).preimage_mem_nhds <| g.open_source.mem_nhds hxg)⟩, he ▸ g.map_source hxg⟩,
    fun y hy => ?_⟩
  change f y = g.symm (gf y)
  have : f y in g.source := by apply interior_subset hy.1.2
  rw [← he]; rw [g.eq_symm_apply this (by apply g.map_source this)]; rw [Function.comp_apply]

/--
theorem `of_comp_right` / 定理 `of_comp_right`

English:
theorem of_comp_right
  given: (hgf : IsLocalHomeomorphOn (g ∘ f) s) (hf : IsLocalHomeomorphOn f s)
  proof: mk g _ by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨f, hxf, rfl⟩ := hf x hx
  obtain ⟨gf, hgf, he⟩ := hgf x hx
  refine ⟨f.symm.trans gf, ⟨f.map_source hxf, ?_⟩, fun y hy => ?_⟩
  · apply (f.left_inv hxf).symm ▸ hgf
  · change g y = gf (f.symm y)
    rw [← he]; rw [Function.comp_apply]; rw [f.right_inv hy.1

中文:
定理 of_comp_right
  条件: (hgf : IsLocalHomeomorphOn (g ∘ f) s) (hf : IsLocalHomeomorphOn f s)
  证明: mk g _ by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨f, hxf, rfl⟩ := hf x hx
  obtain ⟨gf, hgf, he⟩ := hgf x hx
  refine ⟨f.symm.trans gf, ⟨f.map_source hxf, ?_⟩, fun y hy => ?_⟩
  · apply (f.left_inv hxf).symm ▸ hgf
  · change g y = gf (f.symm y)
    rw [← he]; rw [Function.comp_apply]; rw [f.right_inv hy.1

Depends on / 依赖: Function, Function.comp_apply, comp_apply, f.left_inv, f.map_source, f.right_inv, f.symm, f.symm.trans, left_inv, map_source, right_inv
-/
theorem of_comp_right (hgf : IsLocalHomeomorphOn (g ∘ f) s) (hf : IsLocalHomeomorphOn f s) :
IsLocalHomeomorphOn g (f '' s) := mk g _ by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨f, hxf, rfl⟩ := hf x hx
  obtain ⟨gf, hgf, he⟩ := hgf x hx
  refine ⟨f.symm.trans gf, ⟨f.map_source hxf, ?_⟩, fun y hy => ?_⟩
  · apply (f.left_inv hxf).symm ▸ hgf
  · change g y = gf (f.symm y)
    rw [← he]; rw [Function.comp_apply]; rw [f.right_inv hy.1]

/--
theorem `map_nhds_eq` / 定理 `map_nhds_eq`

English:
theorem map_nhds_eq
  given: (hf : IsLocalHomeomorphOn f s) {x : X} (hx : x in s)
  statement: (𝓝 x).map f = 𝓝 (f x)
  proof: let ⟨e, hx, he⟩ := hf x hx
  he.symm ▸ e.map_nhds_eq hx

中文:
定理 map_nhds_eq
  条件: (hf : IsLocalHomeomorphOn f s) {x : X} (hx : x in s)
  结论: (𝓝 x).map f = 𝓝 (f x)
  证明: let ⟨e, hx, he⟩ := hf x hx
  he.symm ▸ e.map_nhds_eq hx

Depends on / 依赖: e.map_nhds_eq, he.symm, map_nhds_eq
-/
theorem map_nhds_eq (hf : IsLocalHomeomorphOn f s) {x : X} (hx : x in s) : (𝓝 x).map f = 𝓝 (f x) :=
  let ⟨e, hx, he⟩ := hf x hx
  he.symm ▸ e.map_nhds_eq hx

/--
theorem `continuousAt` / 定理 `continuousAt`

English:
theorem continuousAt
  given: (hf : IsLocalHomeomorphOn f s) {x : X} (hx : x in s)
  proof: (hf.map_nhds_eq hx).le

中文:
定理 continuousAt
  条件: (hf : IsLocalHomeomorphOn f s) {x : X} (hx : x in s)
  证明: (hf.map_nhds_eq hx).le
-/
protected theorem continuousAt (hf : IsLocalHomeomorphOn f s) {x : X} (hx : x in s) :
    ContinuousAt f x :=
  (hf.map_nhds_eq hx).le

/--
theorem `continuousOn` / 定理 `continuousOn`

English:
theorem continuousOn
  given: (hf : IsLocalHomeomorphOn f s)
  statement: ContinuousOn f s
  proof: continuousOn_of_forall_continuousAt fun _x => hf.continuousAt

中文:
定理 continuousOn
  条件: (hf : IsLocalHomeomorphOn f s)
  结论: ContinuousOn f s
  证明: continuousOn_of_forall_continuousAt fun _x => hf.continuousAt
-/
protected theorem continuousOn (hf : IsLocalHomeomorphOn f s) : ContinuousOn f s :=
  continuousOn_of_forall_continuousAt fun _x => hf.continuousAt

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  statement: (hg : IsLocalHomeomorphOn g t) (hf : IsLocalHomeomorphOn f s)
  proof: by
  intro x hx
  obtain ⟨eg, hxg, rfl⟩ := hg (f x) (h hx)
  obtain ⟨ef, hxf, rfl⟩ := hf x hx
  exact ⟨ef.trans eg, ⟨hxf, hxg⟩, rfl⟩

中文:
定理 comp
  结论: (hg : IsLocalHomeomorphOn g t) (hf : IsLocalHomeomorphOn f s)
  证明: by
  intro x hx
  obtain ⟨eg, hxg, rfl⟩ := hg (f x) (h hx)
  obtain ⟨ef, hxf, rfl⟩ := hf x hx
  exact ⟨ef.trans eg, ⟨hxf, hxg⟩, rfl⟩
-/
protected theorem comp (hg : IsLocalHomeomorphOn g t) (hf : IsLocalHomeomorphOn f s)
    (h : Set.MapsTo f s t) : IsLocalHomeomorphOn (g ∘ f) s := by
  intro x hx
  obtain ⟨eg, hxg, rfl⟩ := hg (f x) (h hx)
  obtain ⟨ef, hxf, rfl⟩ := hf x hx
  exact ⟨ef.trans eg, ⟨hxf, hxg⟩, rfl⟩

end IsLocalHomeomorphOn

/--
Definition of `IsLocalHomeomorph` / `IsLocalHomeomorph` 的定义

English:
definition IsLocalHomeomorph
  body: forall x : X, exists e : OpenPartialHomeomorph X Y, x in e.source ∧ f = e

中文:
定义 IsLocalHomeomorph
  定义体: forall x : X, exists e : OpenPartialHomeomorph X Y, x in e.source ∧ f = e

Depends on / 依赖: OpenPartialHomeomorph, e.source, source
-/
def IsLocalHomeomorph :=
  forall x : X, exists e : OpenPartialHomeomorph X Y, x in e.source ∧ f = e

/--
theorem `Homeomorph.isLocalHomeomorph` / 定理 `Homeomorph.isLocalHomeomorph`

English:
theorem Homeomorph.isLocalHomeomorph
  given: (f : X ≃ₜ Y)
  statement: IsLocalHomeomorph f
  proof: fun _ => ⟨f.toOpenPartialHomeomorph, trivial, rfl⟩

中文:
定理 Homeomorph.isLocalHomeomorph
  条件: (f : X ≃ₜ Y)
  结论: IsLocalHomeomorph f
  证明: fun _ => ⟨f.toOpenPartialHomeomorph, trivial, rfl⟩

Depends on / 依赖: f.toOpenPartialHomeomorph, toOpenPartialHomeomorph
-/
theorem Homeomorph.isLocalHomeomorph (f : X ≃ₜ Y) : IsLocalHomeomorph f :=
  fun _ => ⟨f.toOpenPartialHomeomorph, trivial, rfl⟩

variable {f s}

/--
theorem `isLocalHomeomorph_iff_isLocalHomeomorphOn_univ` / 定理 `isLocalHomeomorph_iff_isLocalHomeomorphOn_univ`

English:
theorem isLocalHomeomorph_iff_isLocalHomeomorphOn_univ
  proof: ⟨fun h x _ => h x, fun h x => h x trivial⟩

中文:
定理 isLocalHomeomorph_iff_isLocalHomeomorphOn_univ
  证明: ⟨fun h x _ => h x, fun h x => h x trivial⟩
-/
theorem isLocalHomeomorph_iff_isLocalHomeomorphOn_univ :
    IsLocalHomeomorph f ↔ IsLocalHomeomorphOn f Set.univ :=
  ⟨fun h x _ => h x, fun h x => h x trivial⟩

/--
theorem `IsLocalHomeomorph.isLocalHomeomorphOn` / 定理 `IsLocalHomeomorph.isLocalHomeomorphOn`

English:
theorem IsLocalHomeomorph.isLocalHomeomorphOn
  given: (hf : IsLocalHomeomorph f)
  proof: fun x _ => hf x

中文:
定理 IsLocalHomeomorph.isLocalHomeomorphOn
  条件: (hf : IsLocalHomeomorph f)
  证明: fun x _ => hf x
-/
protected theorem IsLocalHomeomorph.isLocalHomeomorphOn (hf : IsLocalHomeomorph f) :
    IsLocalHomeomorphOn f s := fun x _ => hf x

/--
theorem `isLocalHomeomorph_iff_isOpenEmbedding_restrict` / 定理 `isLocalHomeomorph_iff_isOpenEmbedding_restrict`

English:
theorem isLocalHomeomorph_iff_isOpenEmbedding_restrict
  given: {f : X -> Y}
  proof: by
  simp_rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ,
    isLocalHomeomorphOn_iff_isOpenEmbedding_restrict, imp_iff_right (Set.mem_univ _)]

中文:
定理 isLocalHomeomorph_iff_isOpenEmbedding_restrict
  条件: {f : X -> Y}
  证明: by
  simp_rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ,
    isLocalHomeomorphOn_iff_isOpenEmbedding_restrict, imp_iff_right (Set.mem_univ _)]

Depends on / 依赖: Set.mem_univ, imp_iff_right, isLocalHomeomorphOn_iff_isOpenEmbedding_restrict, isLocalHomeomorph_iff_isLocalHomeomorphOn_univ, mem_univ, simp_rw
-/
theorem isLocalHomeomorph_iff_isOpenEmbedding_restrict {f : X -> Y} :
    IsLocalHomeomorph f ↔ forall x : X, exists U in 𝓝 x, IsOpenEmbedding (U.domRestrict f) := by
  simp_rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ,
    isLocalHomeomorphOn_iff_isOpenEmbedding_restrict, imp_iff_right (Set.mem_univ _)]

/--
theorem `Topology.IsOpenEmbedding.isLocalHomeomorph` / 定理 `Topology.IsOpenEmbedding.isLocalHomeomorph`

English:
theorem Topology.IsOpenEmbedding.isLocalHomeomorph
  given: (hf : IsOpenEmbedding f)
  statement: IsLocalHomeomorph f
  proof: isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr fun _ =>
    ⟨_, Filter.univ_mem, hf.comp (Homeomorph.Set.univ X).isOpenEmbedding⟩

中文:
定理 Topology.IsOpenEmbedding.isLocalHomeomorph
  条件: (hf : IsOpenEmbedding f)
  结论: IsLocalHomeomorph f
  证明: isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr fun _ =>
    ⟨_, Filter.univ_mem, hf.comp (Homeomorph.Set.univ X).isOpenEmbedding⟩

Depends on / 依赖: Filter, Filter.univ_mem, Homeomorph, Homeomorph.Set.univ, hf.comp, isLocalHomeomorph_iff_isOpenEmbedding_restrict, isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr, isOpenEmbedding, univ_mem
-/
theorem Topology.IsOpenEmbedding.isLocalHomeomorph (hf : IsOpenEmbedding f) : IsLocalHomeomorph f :=
  isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr fun _ =>
    ⟨_, Filter.univ_mem, hf.comp (Homeomorph.Set.univ X).isOpenEmbedding⟩

namespace IsLocalHomeomorph

/--
theorem `comap_discreteTopology` / 定理 `comap_discreteTopology`

English:
theorem comap_discreteTopology
  statement: (h : IsLocalHomeomorph f)
  proof: (Homeomorph.Set.univ X).discreteTopology_iff.mp h.isLocalHomeomorphOn.discreteTopology_of_image

中文:
定理 comap_discreteTopology
  结论: (h : IsLocalHomeomorph f)
  证明: (Homeomorph.Set.univ X).discreteTopology_iff.mp h.isLocalHomeomorphOn.discreteTopology_of_image

Depends on / 依赖: Homeomorph, Homeomorph.Set.univ, discreteTopology_iff, discreteTopology_iff.mp, discreteTopology_of_image, h.isLocalHomeomorphOn.discreteTopology_of_image, isLocalHomeomorphOn
-/
theorem comap_discreteTopology (h : IsLocalHomeomorph f)
    [DiscreteTopology Y] : DiscreteTopology X :=
  (Homeomorph.Set.univ X).discreteTopology_iff.mp h.isLocalHomeomorphOn.discreteTopology_of_image

/--
theorem `discreteTopology_range_iff` / 定理 `discreteTopology_range_iff`

English:
theorem discreteTopology_range_iff
  given: (h : IsLocalHomeomorph f)
  proof: by
  rw [← Set.image_univ]; rw [← (Homeomorph.Set.univ X).discreteTopology_iff]
  exact h.isLocalHomeomorphOn.discreteTopology_image_iff isOpen_univ

中文:
定理 discreteTopology_range_iff
  条件: (h : IsLocalHomeomorph f)
  证明: by
  rw [← Set.image_univ]; rw [← (Homeomorph.Set.univ X).discreteTopology_iff]
  exact h.isLocalHomeomorphOn.discreteTopology_image_iff isOpen_univ

Depends on / 依赖: Homeomorph, Homeomorph.Set.univ, Set.image_univ, discreteTopology_iff, discreteTopology_image_iff, h.isLocalHomeomorphOn.discreteTopology_image_iff, image_univ, isLocalHomeomorphOn, isOpen_univ
-/
theorem discreteTopology_range_iff (h : IsLocalHomeomorph f) :
    DiscreteTopology (Set.range f) ↔ DiscreteTopology X := by
  rw [← Set.image_univ]; rw [← (Homeomorph.Set.univ X).discreteTopology_iff]
  exact h.isLocalHomeomorphOn.discreteTopology_image_iff isOpen_univ

/--
theorem `discreteTopology_iff_of_surjective` / 定理 `discreteTopology_iff_of_surjective`

English:
theorem discreteTopology_iff_of_surjective
  given: (h : IsLocalHomeomorph f) (hs : Function.Surjective f)
  proof: by
  rw [← (Homeomorph.Set.univ Y).discreteTopology_iff]; rw [← hs.range_eq]; rw [h.discreteTopology_range_iff]

中文:
定理 discreteTopology_iff_of_surjective
  条件: (h : IsLocalHomeomorph f) (hs : Function.Surjective f)
  证明: by
  rw [← (Homeomorph.Set.univ Y).discreteTopology_iff]; rw [← hs.range_eq]; rw [h.discreteTopology_range_iff]

Depends on / 依赖: Homeomorph, Homeomorph.Set.univ, discreteTopology_iff, discreteTopology_range_iff, h.discreteTopology_range_iff, hs.range_eq, range_eq
-/
theorem discreteTopology_iff_of_surjective (h : IsLocalHomeomorph f) (hs : Function.Surjective f) :
    DiscreteTopology X ↔ DiscreteTopology Y := by
  rw [← (Homeomorph.Set.univ Y).discreteTopology_iff]; rw [← hs.range_eq]; rw [h.discreteTopology_range_iff]

variable (f)

/--
theorem `mk` / 定理 `mk`

English:
theorem mk
  given: (h : forall x : X, exists e : OpenPartialHomeomorph X Y, x in e.source ∧ Set.EqOn f e e.source)
  proof: isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    (IsLocalHomeomorphOn.mk f Set.univ fun x _hx => h x)

@[deprecated (since := "2026-06-06")]
alias Homeomorph.isLocalHomeomorph := _root_.Homeomorph.isLocalHomeomorph

中文:
定理 mk
  条件: (h : 对任意 x : X, 存在 e : OpenPartialHomeomorph X Y, x in e.source ∧ Set.EqOn f e e.source)
  证明: isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    (IsLocalHomeomorphOn.mk f Set.univ fun x _hx => h x)

@[deprecated (since := "2026-06-06")]
alias Homeomorph.isLocalHomeomorph := _root_.Homeomorph.isLocalHomeomorph

Depends on / 依赖: IsLocalHomeomorphOn, IsLocalHomeomorphOn.mk, Set.univ, isLocalHomeomorph_iff_isLocalHomeomorphOn_univ, isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
-/
theorem mk (h : forall x : X, exists e : OpenPartialHomeomorph X Y, x in e.source ∧ Set.EqOn f e e.source) :
    IsLocalHomeomorph f :=
  isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    (IsLocalHomeomorphOn.mk f Set.univ fun x _hx => h x)

@[deprecated (since := "2026-06-06")]
alias Homeomorph.isLocalHomeomorph := _root_.Homeomorph.isLocalHomeomorph

variable {g f}

/--
lemma `isLocallyInjective` / 引理 `isLocallyInjective`

English:
lemma isLocallyInjective
  given: (hf : IsLocalHomeomorph f)
  statement: IsLocallyInjective f
  proof: fun x => by obtain ⟨f, hx, rfl⟩ := hf x; exact ⟨f.source, f.open_source, hx, f.injOn⟩

中文:
引理 isLocallyInjective
  条件: (hf : IsLocalHomeomorph f)
  结论: IsLocallyInjective f
  证明: fun x => by obtain ⟨f, hx, rfl⟩ := hf x; exact ⟨f.source, f.open_source, hx, f.injOn⟩

Depends on / 依赖: f.injOn, f.open_source, f.source, open_source, source
-/
lemma isLocallyInjective (hf : IsLocalHomeomorph f) : IsLocallyInjective f :=
  fun x => by obtain ⟨f, hx, rfl⟩ := hf x; exact ⟨f.source, f.open_source, hx, f.injOn⟩

/--
theorem `of_comp` / 定理 `of_comp`

English:
theorem of_comp
  statement: (hgf : IsLocalHomeomorph (g ∘ f)) (hg : IsLocalHomeomorph g)
  proof: isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    hgf.isLocalHomeomorphOn.of_comp_left hg.isLocalHomeomorphOn fun _ _ => cont.continuousAt

中文:
定理 of_comp
  结论: (hgf : IsLocalHomeomorph (g ∘ f)) (hg : IsLocalHomeomorph g)
  证明: isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    hgf.isLocalHomeomorphOn.of_comp_left hg.isLocalHomeomorphOn fun _ _ => cont.continuousAt

Depends on / 依赖: cont.continuousAt, continuousAt, hg.isLocalHomeomorphOn, hgf.isLocalHomeomorphOn.of_comp_left, isLocalHomeomorphOn, isLocalHomeomorph_iff_isLocalHomeomorphOn_univ, isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr, of_comp_left
-/
theorem of_comp (hgf : IsLocalHomeomorph (g ∘ f)) (hg : IsLocalHomeomorph g)
    (cont : Continuous f) : IsLocalHomeomorph f :=
isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    hgf.isLocalHomeomorphOn.of_comp_left hg.isLocalHomeomorphOn fun _ _ => cont.continuousAt

/--
theorem `map_nhds_eq` / 定理 `map_nhds_eq`

English:
theorem map_nhds_eq
  given: (hf : IsLocalHomeomorph f) (x : X)
  statement: (𝓝 x).map f = 𝓝 (f x)
  proof: hf.isLocalHomeomorphOn.map_nhds_eq (Set.mem_univ x)

中文:
定理 map_nhds_eq
  条件: (hf : IsLocalHomeomorph f) (x : X)
  结论: (𝓝 x).map f = 𝓝 (f x)
  证明: hf.isLocalHomeomorphOn.map_nhds_eq (Set.mem_univ x)

Depends on / 依赖: Set.mem_univ, hf.isLocalHomeomorphOn.map_nhds_eq, isLocalHomeomorphOn, map_nhds_eq, mem_univ
-/
theorem map_nhds_eq (hf : IsLocalHomeomorph f) (x : X) : (𝓝 x).map f = 𝓝 (f x) :=
  hf.isLocalHomeomorphOn.map_nhds_eq (Set.mem_univ x)

/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (hf : IsLocalHomeomorph f)
  statement: Continuous f
  proof: continuousOn_univ.mp hf.isLocalHomeomorphOn.continuousOn

中文:
定理 continuous
  条件: (hf : IsLocalHomeomorph f)
  结论: Continuous f
  证明: continuousOn_univ.mp hf.isLocalHomeomorphOn.continuousOn
-/
protected theorem continuous (hf : IsLocalHomeomorph f) : Continuous f :=
  continuousOn_univ.mp hf.isLocalHomeomorphOn.continuousOn

/--
theorem `isOpenMap` / 定理 `isOpenMap`

English:
theorem isOpenMap
  given: (hf : IsLocalHomeomorph f)
  statement: IsOpenMap f
  proof: IsOpenMap.of_nhds_le fun x => ge_of_eq (hf.map_nhds_eq x)

中文:
定理 isOpenMap
  条件: (hf : IsLocalHomeomorph f)
  结论: IsOpenMap f
  证明: IsOpenMap.of_nhds_le fun x => ge_of_eq (hf.map_nhds_eq x)
-/
protected theorem isOpenMap (hf : IsLocalHomeomorph f) : IsOpenMap f :=
  IsOpenMap.of_nhds_le fun x => ge_of_eq (hf.map_nhds_eq x)

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: (hg : IsLocalHomeomorph g) (hf : IsLocalHomeomorph f)
  proof: isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    (hg.isLocalHomeomorphOn.comp hf.isLocalHomeomorphOn (Set.univ.mapsTo_univ f))

中文:
定理 comp
  条件: (hg : IsLocalHomeomorph g) (hf : IsLocalHomeomorph f)
  证明: isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    (hg.isLocalHomeomorphOn.comp hf.isLocalHomeomorphOn (Set.univ.mapsTo_univ f))
-/
protected theorem comp (hg : IsLocalHomeomorph g) (hf : IsLocalHomeomorph f) :
    IsLocalHomeomorph (g ∘ f) :=
  isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    (hg.isLocalHomeomorphOn.comp hf.isLocalHomeomorphOn (Set.univ.mapsTo_univ f))

/--
theorem `isOpenEmbedding_of_injective` / 定理 `isOpenEmbedding_of_injective`

English:
theorem isOpenEmbedding_of_injective
  given: (hf : IsLocalHomeomorph f) (hi : f.Injective)
  proof: .of_continuous_injective_isOpenMap hf.continuous hi hf.isOpenMap

中文:
定理 isOpenEmbedding_of_injective
  条件: (hf : IsLocalHomeomorph f) (hi : f.Injective)
  证明: .of_continuous_injective_isOpenMap hf.continuous hi hf.isOpenMap

Depends on / 依赖: continuous, hf.continuous, hf.isOpenMap, isOpenMap, of_continuous_injective_isOpenMap
-/
theorem isOpenEmbedding_of_injective (hf : IsLocalHomeomorph f) (hi : f.Injective) :
    IsOpenEmbedding f :=
  .of_continuous_injective_isOpenMap hf.continuous hi hf.isOpenMap

/--
Definition of `toHomeomorphOfBijective` / `toHomeomorphOfBijective` 的定义

English:
definition toHomeomorphOfBijective
  signature: (hf : IsLocalHomeomorph f) (hb : f.Bijective)
  body: (Equiv.ofBijective f hb).toHomeomorphOfContinuousOpen hf.continuous hf.isOpenMap

中文:
定义 toHomeomorphOfBijective
  签名: (hf : IsLocalHomeomorph f) (hb : f.Bijective)
  定义体: (Equiv.ofBijective f hb).toHomeomorphOfContinuousOpen hf.continuous hf.isOpenMap

Depends on / 依赖: Equiv.ofBijective, continuous, hf.continuous, hf.isOpenMap, isOpenMap, ofBijective, toHomeomorphOfContinuousOpen
-/
noncomputable def toHomeomorphOfBijective (hf : IsLocalHomeomorph f) (hb : f.Bijective) :
    X ≃ₜ Y :=
  (Equiv.ofBijective f hb).toHomeomorphOfContinuousOpen hf.continuous hf.isOpenMap

/--
theorem `isOpenEmbedding_of_comp` / 定理 `isOpenEmbedding_of_comp`

English:
theorem isOpenEmbedding_of_comp
  statement: (hf : IsLocalHomeomorph g) (hgf : IsOpenEmbedding (g ∘ f))
  proof: (hgf.isLocalHomeomorph.of_comp hf cont).isOpenEmbedding_of_injective hgf.injective.of_comp

中文:
定理 isOpenEmbedding_of_comp
  结论: (hf : IsLocalHomeomorph g) (hgf : IsOpenEmbedding (g ∘ f))
  证明: (hgf.isLocalHomeomorph.of_comp hf cont).isOpenEmbedding_of_injective hgf.injective.of_comp

Depends on / 依赖: hgf.injective.of_comp, hgf.isLocalHomeomorph.of_comp, injective, isLocalHomeomorph, isOpenEmbedding_of_injective, of_comp
-/
theorem isOpenEmbedding_of_comp (hf : IsLocalHomeomorph g) (hgf : IsOpenEmbedding (g ∘ f))
    (cont : Continuous f) : IsOpenEmbedding f :=
  (hgf.isLocalHomeomorph.of_comp hf cont).isOpenEmbedding_of_injective hgf.injective.of_comp

open TopologicalSpace in
/--
theorem `isTopologicalBasis` / 定理 `isTopologicalBasis`

English:
theorem isTopologicalBasis
  given: (hf : IsLocalHomeomorph f)
  statement: IsTopologicalBasis
  proof: by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ fun x U hx hU => ?_
  · rintro _ ⟨U, hU, s, hs, rfl⟩
    refine (isOpenEmbedding_of_comp hf (hs ▸ ⟨IsEmbedding.subtypeVal, ?_⟩)
      s.continuous).isOpen_range
    rwa [Subtype.range_val]
  · obtain ⟨f, hxf, rfl⟩ := hf x
    refine ⟨f.source inter

中文:
定理 isTopologicalBasis
  条件: (hf : IsLocalHomeomorph f)
  结论: IsTopologicalBasis
  证明: by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ fun x U hx hU => ?_
  · rintro _ ⟨U, hU, s, hs, rfl⟩
    refine (isOpenEmbedding_of_comp hf (hs ▸ ⟨IsEmbedding.subtypeVal, ?_⟩)
      s.continuous).isOpen_range
    rwa [Subtype.range_val]
  · obtain ⟨f, hxf, rfl⟩ := hf x
    refine ⟨f.source inter

Depends on / 依赖: IsEmbedding, IsEmbedding.subtypeVal, Set.range_domRestrict, Subtype, Subtype.range_val, continuous, continuousOn_iff_continuous_domRestrict, continuousOn_iff_continuous_domRestrict.mp, continuousOn_invFun, f.continuousOn_invFun.mono, f.source, f.symm, f.symm.isOpen_inter_preimage, f.target, isOpenEmbedding_of_comp, isOpen_inter_preimage, isOpen_range, isTopologicalBasis_of_isOpen_of_nhds, range_domRestrict, range_val
-/
theorem isTopologicalBasis (hf : IsLocalHomeomorph f) : IsTopologicalBasis
    {U : Set X | exists V : Set Y, IsOpen V ∧ exists s : C(V,X), f ∘ s = (↑) ∧ Set.range s = U} := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ fun x U hx hU => ?_
  · rintro _ ⟨U, hU, s, hs, rfl⟩
    refine (isOpenEmbedding_of_comp hf (hs ▸ ⟨IsEmbedding.subtypeVal, ?_⟩)
      s.continuous).isOpen_range
    rwa [Subtype.range_val]
  · obtain ⟨f, hxf, rfl⟩ := hf x
    refine ⟨f.source inter U, ⟨f.target inter f.symm ⁻¹' U, f.symm.isOpen_inter_preimage hU,
      ⟨_, continuousOn_iff_continuous_domRestrict.mp (f.continuousOn_invFun.mono fun _ h => h.1)⟩,
      ?_, (Set.range_domRestrict _ _).trans ?_⟩, ⟨hxf, hx⟩, fun _ h => h.2⟩
    · ext y; exact f.right_inv y.2.1
    · apply (f.symm_image_target_inter_eq _).trans
      rw [Set.preimage_inter]; rw [← Set.inter_assoc]; rw [Set.inter_eq_self_of_subset_left
        f.source_preimage_target]; rw [f.source_inter_preimage_inv_preimage]

variable (hf : IsLocalHomeomorph f) {x : X}

variable (x) in
/--
Definition of `localInverseAt` / `localInverseAt` 的定义

English:
definition localInverseAt
  signature: : OpenPartialHomeomorph Y X
  body: (hf x).choose.symm

中文:
定义 localInverseAt
  签名: : OpenPartialHomeomorph Y X
  定义体: (hf x).choose.symm

Depends on / 依赖: choose.symm
-/
noncomputable def localInverseAt : OpenPartialHomeomorph Y X := (hf x).choose.symm

/--
lemma `self_mem_localInverseAt_target` / 引理 `self_mem_localInverseAt_target`

English:
lemma self_mem_localInverseAt_target
  statement: x in (hf.localInverseAt x).target
  proof: (hf x).choose_spec.1

中文:
引理 self_mem_localInverseAt_target
  结论: x in (hf.localInverseAt x).target
  证明: (hf x).choose_spec.1
-/
@[grind =>, simp] lemma self_mem_localInverseAt_target : x in (hf.localInverseAt x).target :=
  (hf x).choose_spec.1

variable (x) in
/--
lemma `localInverseAt_symm` / 引理 `localInverseAt_symm`

English:
lemma localInverseAt_symm
  statement: (hf.localInverseAt x).symm = f
  proof: (hf x).choose_spec.2.symm

中文:
引理 localInverseAt_symm
  结论: (hf.localInverseAt x).symm = f
  证明: (hf x).choose_spec.2.symm
-/
@[simp] lemma localInverseAt_symm : (hf.localInverseAt x).symm = f :=
  (hf x).choose_spec.2.symm

/--
lemma `apply_self_mem_localInverseAt_source` / 引理 `apply_self_mem_localInverseAt_source`

English:
lemma apply_self_mem_localInverseAt_source
  proof: by
  rw [← congrFun (hf.localInverseAt_symm x)]
  exact (hf.localInverseAt x).map_target hf.self_mem_localInverseAt_target

中文:
引理 apply_self_mem_localInverseAt_source
  证明: by
  rw [← congrFun (hf.localInverseAt_symm x)]
  exact (hf.localInverseAt x).map_target hf.self_mem_localInverseAt_target
-/
@[grind =>, simp] lemma apply_self_mem_localInverseAt_source :
    f x in (hf.localInverseAt x).source := by
  rw [← congrFun (hf.localInverseAt_symm x)]
  exact (hf.localInverseAt x).map_target hf.self_mem_localInverseAt_target

/--
lemma `injOn_localInverseAt_target` / 引理 `injOn_localInverseAt_target`

English:
lemma injOn_localInverseAt_target
  statement: (hf.localInverseAt x).target.InjOn f
  proof: by
  rw [Set.EqOn.injOn_iff (f₂ := (hf.localInverseAt x).symm) (fun y _ => by simp)]
  exact (hf.localInverseAt x).symm.injOn

中文:
引理 injOn_localInverseAt_target
  结论: (hf.localInverseAt x).target.InjOn f
  证明: by
  rw [Set.EqOn.injOn_iff (f₂ := (hf.localInverseAt x).symm) (fun y _ => by simp)]
  exact (hf.localInverseAt x).symm.injOn

Depends on / 依赖: Set.EqOn.injOn_iff, hf.localInverseAt, injOn_iff, localInverseAt, symm.injOn
-/
lemma injOn_localInverseAt_target : (hf.localInverseAt x).target.InjOn f := by
  rw [Set.EqOn.injOn_iff (f₂ := (hf.localInverseAt x).symm) (fun y _ => by simp)]
  exact (hf.localInverseAt x).symm.injOn

/--
lemma `apply_localInverseAt_of_mem` / 引理 `apply_localInverseAt_of_mem`

English:
lemma apply_localInverseAt_of_mem
  given: {y : Y} (hx : y in (hf.localInverseAt x).source)
  proof: by
  rw [← congrFun (hf.localInverseAt_symm x)]
  exact (hf.localInverseAt x).left_inv hx

中文:
引理 apply_localInverseAt_of_mem
  条件: {y : Y} (hx : y in (hf.localInverseAt x).source)
  证明: by
  rw [← congrFun (hf.localInverseAt_symm x)]
  exact (hf.localInverseAt x).left_inv hx
-/
@[grind .] lemma apply_localInverseAt_of_mem {y : Y} (hx : y in (hf.localInverseAt x).source) :
    f (hf.localInverseAt x y) = y := by
  rw [← congrFun (hf.localInverseAt_symm x)]
  exact (hf.localInverseAt x).left_inv hx

/--
lemma `localInverseAt_apply_self` / 引理 `localInverseAt_apply_self`

English:
lemma localInverseAt_apply_self
  statement: hf.localInverseAt x (f x) = x
  proof: hf.injOn_localInverseAt_target (by simp) hf.self_mem_localInverseAt_target
    hf.apply_localInverseAt_of_mem hf.apply_self_mem_localInverseAt_source

中文:
引理 localInverseAt_apply_self
  结论: hf.localInverseAt x (f x) = x
  证明: hf.injOn_localInverseAt_target (by simp) hf.self_mem_localInverseAt_target
    hf.apply_localInverseAt_of_mem hf.apply_self_mem_localInverseAt_source
-/
@[simp] lemma localInverseAt_apply_self : hf.localInverseAt x (f x) = x :=
hf.injOn_localInverseAt_target (by simp) hf.self_mem_localInverseAt_target
    hf.apply_localInverseAt_of_mem hf.apply_self_mem_localInverseAt_source

end IsLocalHomeomorph
