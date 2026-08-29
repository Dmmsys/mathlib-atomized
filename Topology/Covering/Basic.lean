/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.FiberBundle.Basic
public import Mathlib.Topology.IsLocalHomeomorph

/-!
# Covering Maps

This file defines covering maps.

## Main definitions

* `IsEvenlyCovered f x I`: A point `x` is evenly covered by `f : E → X` with fiber `I` if `I` is
  discrete and there is a homeomorphism `f ⁻¹' U ≃ₜ U × I` for some open set `U` containing `x`
  with `f ⁻¹' U` open, such that the induced map `f ⁻¹' U → U` coincides with `f`.
* `IsCoveringMap f`: A function `f : E → X` is a covering map if every point `x` is evenly
  covered by `f` with fiber `f ⁻¹' {x}`. The fibers `f ⁻¹' {x}` must be discrete, but if `X` is
  not connected, then the fibers `f ⁻¹' {x}` are not necessarily isomorphic. Also, `f` is not
  assumed to be surjective, so the fibers are even allowed to be empty.
-/

@[expose] public section

open Bundle Topology

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] (f : E -> X) (s : Set X)

/--
Definition of `IsEvenlyCovered` / `IsEvenlyCovered` 的定义

English:
definition IsEvenlyCovered
  signature: (x : X) (I : Type*) [TopologicalSpace I]
  body: DiscreteTopology I ∧ exists U : Set X, x in U ∧ IsOpen U ∧ IsOpen (f ⁻¹' U) ∧
    exists H : f ⁻¹' U ≃ₜ U × I, forall x, (H x).1.1 = f x

中文:
定义 IsEvenlyCovered
  签名: (x : X) (I : 类型) [TopologicalSpace I]
  定义体: DiscreteTopology I ∧ exists U : Set X, x in U ∧ IsOpen U ∧ IsOpen (f ⁻¹' U) ∧
    exists H : f ⁻¹' U ≃ₜ U × I, forall x, (H x).1.1 = f x

Depends on / 依赖: DiscreteTopology, IsOpen
-/
def IsEvenlyCovered (x : X) (I : Type*) [TopologicalSpace I] :=
  DiscreteTopology I ∧ exists U : Set X, x in U ∧ IsOpen U ∧ IsOpen (f ⁻¹' U) ∧
    exists H : f ⁻¹' U ≃ₜ U × I, forall x, (H x).1.1 = f x

namespace IsEvenlyCovered

variable {f} {I : Type*} [TopologicalSpace I]

/--
Definition of `fiberHomeomorph` / `fiberHomeomorph` 的定义

English:
definition fiberHomeomorph
  signature: {x : X} (h : IsEvenlyCovered f x I)
  body: by
  choose _ U hxU hU hfU H hH using h
  exact
  { toFun i := ⟨H.symm (⟨x, hxU⟩, i), by simp [← hH]⟩
    invFun e := (H ⟨e, by rwa [Set.mem_preimage, (e.2 : f e = x)]⟩).2
    left_inv _ := by simp
right_inv e := Set.inclusion_injective (Set.preimage_mono (Set.singleton_subset_iff.mpr hxU))
H.inject

中文:
定义 fiberHomeomorph
  签名: {x : X} (h : IsEvenlyCovered f x I)
  定义体: by
  choose _ U hxU hU hfU H hH using h
  exact
  { toFun i := ⟨H.symm (⟨x, hxU⟩, i), by simp [← hH]⟩
    invFun e := (H ⟨e, by rwa [Set.mem_preimage, (e.2 : f e = x)]⟩).2
    left_inv _ := by simp
right_inv e := Set.inclusion_injective (Set.preimage_mono (Set.singleton_subset_iff.mpr hxU))
H.inject

Depends on / 依赖: H.injective, H.symm, Prod.ext, Set.inclusion_injective, Set.mem_preimage, Set.preimage_mono, Set.singleton_subset_iff.mpr, Subtype, Subtype.ext, continuous_invFun, continuous_toFun, fun_prop, inclusion_injective, injective, invFun, left_inv, mem_preimage, preimage_mono, right_inv, singleton_subset_iff
-/
noncomputable def fiberHomeomorph {x : X} (h : IsEvenlyCovered f x I) : I ≃ₜ f ⁻¹' {x} := by
  choose _ U hxU hU hfU H hH using h
  exact
  { toFun i := ⟨H.symm (⟨x, hxU⟩, i), by simp [← hH]⟩
    invFun e := (H ⟨e, by rwa [Set.mem_preimage, (e.2 : f e = x)]⟩).2
    left_inv _ := by simp
right_inv e := Set.inclusion_injective (Set.preimage_mono (Set.singleton_subset_iff.mpr hxU))
H.injective Prod.ext (Subtype.ext <| by simpa [hH] using e.2.symm) (by simp)
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

/--
theorem `discreteTopology_fiber` / 定理 `discreteTopology_fiber`

English:
theorem discreteTopology_fiber
  given: {x : X} (h : IsEvenlyCovered f x I)
  statement: DiscreteTopology (f ⁻¹' {x})
  proof: have := h.1; h.fiberHomeomorph.discreteTopology

中文:
定理 discreteTopology_fiber
  条件: {x : X} (h : IsEvenlyCovered f x I)
  结论: DiscreteTopology (f ⁻¹' {x})
  证明: have := h.1; h.fiberHomeomorph.discreteTopology

Depends on / 依赖: discreteTopology, fiberHomeomorph, h.fiberHomeomorph.discreteTopology
-/
theorem discreteTopology_fiber {x : X} (h : IsEvenlyCovered f x I) : DiscreteTopology (f ⁻¹' {x}) :=
  have := h.1; h.fiberHomeomorph.discreteTopology

/--
Definition of `toTrivialization'` / `toTrivialization'` 的定义

English:
definition toTrivialization'
  signature: {x : X} [Nonempty I] (h : IsEvenlyCovered f x I)
  body: by
  choose _ U hxU hU hfU H hH using h
  classical exact
  { toFun e := if he : f e in U then ⟨(H ⟨e, he⟩).1, (H ⟨e, he⟩).2⟩ else ⟨x, Classical.arbitrary I⟩
    invFun xi := H.symm (if hx : xi.1 in U then ⟨xi.1, hx⟩ else ⟨x, hxU⟩, xi.2)
    source := f ⁻¹' U
    target := U ×ˢ Set.univ
    map_sour

中文:
定义 toTrivialization'
  签名: {x : X} [Nonempty I] (h : IsEvenlyCovered f x I)
  定义体: by
  choose _ U hxU hU hfU H hH using h
  classical exact
  { toFun e := if he : f e in U then ⟨(H ⟨e, he⟩).1, (H ⟨e, he⟩).2⟩ else ⟨x, Classical.arbitrary I⟩
    invFun xi := H.symm (if hx : xi.1 in U then ⟨xi.1, hx⟩ else ⟨x, hxU⟩, xi.2)
    source := f ⁻¹' U
    target := U ×ˢ Set.univ
    map_sour

Depends on / 依赖: Classical, Classical.arbitrary, H.symm, Set.univ, Subtype, Subtype.coe_prop, arbitrary, classical, coe_prop, invFun, left_inv, map_source, map_target, open_source, right_inv, source, target
-/
noncomputable def toTrivialization' {x : X} [Nonempty I] (h : IsEvenlyCovered f x I) :
    Trivialization I f := by
  choose _ U hxU hU hfU H hH using h
  classical exact
  { toFun e := if he : f e in U then ⟨(H ⟨e, he⟩).1, (H ⟨e, he⟩).2⟩ else ⟨x, Classical.arbitrary I⟩
    invFun xi := H.symm (if hx : xi.1 in U then ⟨xi.1, hx⟩ else ⟨x, hxU⟩, xi.2)
    source := f ⁻¹' U
    target := U ×ˢ Set.univ
    map_source' e (he : f e in U) := by simp [he]
    map_target' _ _ := Subtype.coe_prop _
    left_inv' e (he : f e in U) := by simp [he]
    right_inv' xi := by rintro ⟨hx, -⟩; simpa [hx] using fun h => (h (H.symm _).2).elim
    open_source := hfU
    open_target := hU.prod isOpen_univ
continuousOn_toFun := continuousOn_iff_continuous_domRestrict.mpr
      ((continuous_subtype_val.prodMap continuous_id).comp H.continuous).congr
      fun ⟨e, (he : f e in U)⟩ => by simp [Prod.map, he]
continuousOn_invFun := continuousOn_iff_continuous_domRestrict.mpr
      ((continuous_subtype_val.comp H.symm.continuous).comp (by fun_prop :
        Continuous fun ui => ⟨⟨_, ui.2.1⟩, ui.1.2⟩)).congr fun ⟨⟨x, i⟩, ⟨hx, _⟩⟩ => by simp [hx]
    baseSet := U
    open_baseSet := hU
    source_eq := rfl
    target_eq := rfl
    proj_toFun e (he : f e in U) := by simp [he, hH] }

/--
Definition of `toTrivialization` / `toTrivialization` 的定义

English:
definition toTrivialization
  signature: {x : X} [Nonempty I] (h : IsEvenlyCovered f x I)
  body: h.toTrivialization'.transFiberHomeomorph h.fiberHomeomorph

中文:
定义 toTrivialization
  签名: {x : X} [Nonempty I] (h : IsEvenlyCovered f x I)
  定义体: h.toTrivialization'.transFiberHomeomorph h.fiberHomeomorph

Depends on / 依赖: fiberHomeomorph, h.fiberHomeomorph, h.toTrivialization, toTrivialization, transFiberHomeomorph
-/
noncomputable def toTrivialization {x : X} [Nonempty I] (h : IsEvenlyCovered f x I) :
    Trivialization (f ⁻¹' {x}) f :=
  h.toTrivialization'.transFiberHomeomorph h.fiberHomeomorph

/--
theorem `mem_toTrivialization_baseSet` / 定理 `mem_toTrivialization_baseSet`

English:
theorem mem_toTrivialization_baseSet
  given: {x : X} [Nonempty I] (h : IsEvenlyCovered f x I)
  proof: h.2.choose_spec.1

中文:
定理 mem_toTrivialization_baseSet
  条件: {x : X} [Nonempty I] (h : IsEvenlyCovered f x I)
  证明: h.2.choose_spec.1

Depends on / 依赖: choose_spec
-/
theorem mem_toTrivialization_baseSet {x : X} [Nonempty I] (h : IsEvenlyCovered f x I) :
    x in h.toTrivialization.baseSet := h.2.choose_spec.1

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `toTrivialization_apply` / 定理 `toTrivialization_apply`

English:
theorem toTrivialization_apply
  given: {x : E} [Nonempty I] (h : IsEvenlyCovered f (f x) I)
  proof: h.fiberHomeomorph.symm.injective by
    simp [toTrivialization, toTrivialization', dif_pos h.2.choose_spec.1, fiberHomeomorph]

中文:
定理 toTrivialization_apply
  条件: {x : E} [Nonempty I] (h : IsEvenlyCovered f (f x) I)
  证明: h.fiberHomeomorph.symm.injective by
    simp [toTrivialization, toTrivialization', dif_pos h.2.choose_spec.1, fiberHomeomorph]

Depends on / 依赖: choose_spec, dif_pos, fiberHomeomorph, h.fiberHomeomorph.symm.injective, injective, toTrivialization
-/
theorem toTrivialization_apply {x : E} [Nonempty I] (h : IsEvenlyCovered f (f x) I) :
    (h.toTrivialization x).2 = ⟨x, rfl⟩ :=
h.fiberHomeomorph.symm.injective by
    simp [toTrivialization, toTrivialization', dif_pos h.2.choose_spec.1, fiberHomeomorph]

/--
theorem `continuousAt` / 定理 `continuousAt`

English:
theorem continuousAt
  given: {x : E} (h : IsEvenlyCovered f (f x) I)
  statement: ContinuousAt f x
  proof: have ⟨_, _, hxU, _, _, H, _⟩ := h
  have : Nonempty I := ⟨(H ⟨x, hxU⟩).2⟩
  let e := h.toTrivialization
  e.continuousAt_proj (e.mem_source.mpr (mem_toTrivialization_baseSet h))

中文:
定理 continuousAt
  条件: {x : E} (h : IsEvenlyCovered f (f x) I)
  结论: ContinuousAt f x
  证明: have ⟨_, _, hxU, _, _, H, _⟩ := h
  have : Nonempty I := ⟨(H ⟨x, hxU⟩).2⟩
  let e := h.toTrivialization
  e.continuousAt_proj (e.mem_source.mpr (mem_toTrivialization_baseSet h))
-/
protected theorem continuousAt {x : E} (h : IsEvenlyCovered f (f x) I) : ContinuousAt f x :=
  have ⟨_, _, hxU, _, _, H, _⟩ := h
  have : Nonempty I := ⟨(H ⟨x, hxU⟩).2⟩
  let e := h.toTrivialization
  e.continuousAt_proj (e.mem_source.mpr (mem_toTrivialization_baseSet h))

/--
theorem `of_fiber_homeomorph` / 定理 `of_fiber_homeomorph`

English:
theorem of_fiber_homeomorph
  statement: {J} [TopologicalSpace J] (g : I ≃ₜ J) {x : X}
  proof: have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  ⟨g.discreteTopology, U, hxU, hU, hfU, H.trans (.prodCongr (.refl U) g), fun _ => by simp [hH]⟩

中文:
定理 of_fiber_homeomorph
  结论: {J} [TopologicalSpace J] (g : I ≃ₜ J) {x : X}
  证明: have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  ⟨g.discreteTopology, U, hxU, hU, hfU, H.trans (.prodCongr (.refl U) g), fun _ => by simp [hH]⟩

Depends on / 依赖: H.trans, discreteTopology, g.discreteTopology, prodCongr
-/
theorem of_fiber_homeomorph {J} [TopologicalSpace J] (g : I ≃ₜ J) {x : X}
    (h : IsEvenlyCovered f x I) : IsEvenlyCovered f x J :=
  have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  ⟨g.discreteTopology, U, hxU, hU, hfU, H.trans (.prodCongr (.refl U) g), fun _ => by simp [hH]⟩

/--
theorem `to_isEvenlyCovered_preimage` / 定理 `to_isEvenlyCovered_preimage`

English:
theorem to_isEvenlyCovered_preimage
  given: {x : X} (h : IsEvenlyCovered f x I)
  proof: h.of_fiber_homeomorph h.fiberHomeomorph

中文:
定理 to_isEvenlyCovered_preimage
  条件: {x : X} (h : IsEvenlyCovered f x I)
  证明: h.of_fiber_homeomorph h.fiberHomeomorph

Depends on / 依赖: fiberHomeomorph, h.fiberHomeomorph, h.of_fiber_homeomorph, of_fiber_homeomorph
-/
theorem to_isEvenlyCovered_preimage {x : X} (h : IsEvenlyCovered f x I) :
    IsEvenlyCovered f x (f ⁻¹' {x}) :=
  h.of_fiber_homeomorph h.fiberHomeomorph

/--
theorem `of_trivialization` / 定理 `of_trivialization`

English:
theorem of_trivialization
  statement: [DiscreteTopology I] {x : X} {t : Trivialization I f}
  proof: ⟨‹_›, _, hx, t.open_baseSet, t.source_eq ▸ t.open_source,
  { toFun e := ⟨⟨f e, e.2⟩, (t e).2⟩
    invFun xi := ⟨t.invFun (xi.1, xi.2), by
      rw [Set.mem_preimage]; rw [← t.mem_source]; exact t.map_target (t.target_eq ▸ ⟨xi.1.2, ⟨⟩⟩)⟩
left_inv e := Subtype.ext t.symm_apply_mk_proj (t.mem_source.m

中文:
定理 of_trivialization
  结论: [DiscreteTopology I] {x : X} {t : Trivialization I f}
  证明: ⟨‹_›, _, hx, t.open_baseSet, t.source_eq ▸ t.open_source,
  { toFun e := ⟨⟨f e, e.2⟩, (t e).2⟩
    invFun xi := ⟨t.invFun (xi.1, xi.2), by
      rw [Set.mem_preimage]; rw [← t.mem_source]; exact t.map_target (t.target_eq ▸ ⟨xi.1.2, ⟨⟩⟩)⟩
left_inv e := Subtype.ext t.symm_apply_mk_proj (t.mem_source.m

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.prodMap, Set.mem_preimage, Subtype, Subtype.ext, apply_symm_apply, continuousOn_iff_continuous_domRestrict, continuousOn_iff_continuous_domRestrict.mp, continuousOn_t, continuous_iff, continuous_iff.mpr, continuous_toFun, invFun, left_inv, map_target, mem_preimage, mem_source, open_baseSet, open_source, prodMap
-/
theorem of_trivialization [DiscreteTopology I] {x : X} {t : Trivialization I f}
    (hx : x in t.baseSet) : IsEvenlyCovered f x I :=
  ⟨‹_›, _, hx, t.open_baseSet, t.source_eq ▸ t.open_source,
  { toFun e := ⟨⟨f e, e.2⟩, (t e).2⟩
    invFun xi := ⟨t.invFun (xi.1, xi.2), by
      rw [Set.mem_preimage]; rw [← t.mem_source]; exact t.map_target (t.target_eq ▸ ⟨xi.1.2, ⟨⟩⟩)⟩
left_inv e := Subtype.ext t.symm_apply_mk_proj (t.mem_source.mpr e.2)
    right_inv xi := by simp [t.proj_symm_apply', t.apply_symm_apply']
continuous_toFun := (IsInducing.subtypeVal.prodMap .id).continuous_iff.mpr
      (continuousOn_iff_continuous_domRestrict.mp <| t.continuousOn_toFun.mono t.source_eq.ge).congr
      fun e => by simp [t.mk_proj_snd' e.2]
continuous_invFun := IsInducing.subtypeVal.continuous_iff.mpr
      t.continuousOn_invFun.comp_continuous (continuous_subtype_val.prodMap continuous_id)
      fun ⟨x, _⟩ => t.target_eq ▸ ⟨x.2, ⟨⟩⟩ }, fun _ => by simp⟩

variable (I) in
/--
theorem `of_preimage_eq_empty` / 定理 `of_preimage_eq_empty`

English:
theorem of_preimage_eq_empty
  given: [IsEmpty I] {x : X} {U : Set X} (hUx : U in 𝓝 x) (hfU : f ⁻¹' U = ∅)
  proof: have ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hUx
  have hfV : f ⁻¹' V = ∅ := Set.eq_empty_of_subset_empty ((Set.preimage_mono hVU).trans hfU.le)
  have := Set.isEmpty_coe_sort.mpr hfV
  ⟨inferInstance, _, hxV, hV, hfV ▸ isOpen_empty, .empty, isEmptyElim⟩

中文:
定理 of_preimage_eq_empty
  条件: [IsEmpty I] {x : X} {U : Set X} (hUx : U in 𝓝 x) (hfU : f ⁻¹' U = ∅)
  证明: have ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hUx
  have hfV : f ⁻¹' V = ∅ := Set.eq_empty_of_subset_empty ((Set.preimage_mono hVU).trans hfU.le)
  have := Set.isEmpty_coe_sort.mpr hfV
  ⟨inferInstance, _, hxV, hV, hfV ▸ isOpen_empty, .empty, isEmptyElim⟩

Depends on / 依赖: Set.eq_empty_of_subset_empty, Set.isEmpty_coe_sort.mpr, Set.preimage_mono, eq_empty_of_subset_empty, hfU.le, isEmptyElim, isEmpty_coe_sort, isOpen_empty, mem_nhds_iff, mem_nhds_iff.mp, preimage_mono
-/
theorem of_preimage_eq_empty [IsEmpty I] {x : X} {U : Set X} (hUx : U in 𝓝 x) (hfU : f ⁻¹' U = ∅) :
    IsEvenlyCovered f x I :=
  have ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hUx
  have hfV : f ⁻¹' V = ∅ := Set.eq_empty_of_subset_empty ((Set.preimage_mono hVU).trans hfU.le)
  have := Set.isEmpty_coe_sort.mpr hfV
  ⟨inferInstance, _, hxV, hV, hfV ▸ isOpen_empty, .empty, isEmptyElim⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `restrictPreimage` / 定理 `restrictPreimage`

English:
theorem restrictPreimage
  given: {x : X} (hxs : x in s) (h : IsEvenlyCovered f x I)
  proof: have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  ⟨inst, Subtype.val ⁻¹' U, hxU, hU.preimage (by fun_prop), hfU.preimage continuous_subtype_val,
    { toFun e := (⟨⟨(H ⟨e, e.2⟩).1, hH _ ▸ e.1.2⟩, by simpa only [hH] using! e.2⟩, (H ⟨e, e.2⟩).2)
      invFun x := ⟨⟨H.symm (⟨x.1, x.1.2⟩, x.2), by simp [← hH]⟩

中文:
定理 restrictPreimage
  条件: {x : X} (hxs : x in s) (h : IsEvenlyCovered f x I)
  证明: have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  ⟨inst, Subtype.val ⁻¹' U, hxU, hU.preimage (by fun_prop), hfU.preimage continuous_subtype_val,
    { toFun e := (⟨⟨(H ⟨e, e.2⟩).1, hH _ ▸ e.1.2⟩, by simpa only [hH] using! e.2⟩, (H ⟨e, e.2⟩).2)
      invFun x := ⟨⟨H.symm (⟨x.1, x.1.2⟩, x.2), by simp [← hH]⟩

Depends on / 依赖: H.symm, Subtype, Subtype.val, continuous_subtype_val, fun_prop, hU.preimage, hfU.preimage, invFun, left_inv, preimage, right_inv
-/
theorem restrictPreimage {x : X} (hxs : x in s) (h : IsEvenlyCovered f x I) :
    IsEvenlyCovered (s.restrictPreimage f) ⟨x, hxs⟩ I :=
  have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  ⟨inst, Subtype.val ⁻¹' U, hxU, hU.preimage (by fun_prop), hfU.preimage continuous_subtype_val,
    { toFun e := (⟨⟨(H ⟨e, e.2⟩).1, hH _ ▸ e.1.2⟩, by simpa only [hH] using! e.2⟩, (H ⟨e, e.2⟩).2)
      invFun x := ⟨⟨H.symm (⟨x.1, x.1.2⟩, x.2), by simp [← hH]⟩, by simp [← hH]⟩
      left_inv _ := by simp, right_inv _ := by simp }, fun _ => by ext; apply hH⟩

/--
theorem `subtypeVal_comp` / 定理 `subtypeVal_comp`

English:
theorem subtypeVal_comp
  given: (hs : IsOpen s) {x : s} {f : E -> s} (h : IsEvenlyCovered f x I)
  proof: have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  have : Subtype.val ∘ f ⁻¹' Subtype.val '' U = f ⁻¹' U := by ext; simp
  ⟨inst, Subtype.val '' U, ⟨x, hxU, rfl⟩, hs.isOpenMap_subtype_val _ hU, by rwa [this], .trans
    (.setCongr this) (H.trans <| .prodCongr (IsEmbedding.subtypeVal.homeomorphImage U) (.ref

中文:
定理 subtypeVal_comp
  条件: (hs : IsOpen s) {x : s} {f : E -> s} (h : IsEvenlyCovered f x I)
  证明: have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  have : Subtype.val ∘ f ⁻¹' Subtype.val '' U = f ⁻¹' U := by ext; simp
  ⟨inst, Subtype.val '' U, ⟨x, hxU, rfl⟩, hs.isOpenMap_subtype_val _ hU, by rwa [this], .trans
    (.setCongr this) (H.trans <| .prodCongr (IsEmbedding.subtypeVal.homeomorphImage U) (.ref

Depends on / 依赖: H.trans, IsEmbedding, IsEmbedding.subtypeVal.homeomorphImage, Subtype, Subtype.val, congr_arg, homeomorphImage, hs.isOpenMap_subtype_val, isOpenMap_subtype_val, prodCongr, setCongr, subtypeVal
-/
theorem subtypeVal_comp (hs : IsOpen s) {x : s} {f : E -> s} (h : IsEvenlyCovered f x I) :
    IsEvenlyCovered (Subtype.val ∘ f) x I :=
  have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  have : Subtype.val ∘ f ⁻¹' Subtype.val '' U = f ⁻¹' U := by ext; simp
  ⟨inst, Subtype.val '' U, ⟨x, hxU, rfl⟩, hs.isOpenMap_subtype_val _ hU, by rwa [this], .trans
    (.setCongr this) (H.trans <| .prodCongr (IsEmbedding.subtypeVal.homeomorphImage U) (.refl I)),
    fun _ => congr_arg Subtype.val (hH _)⟩

/--
theorem `comp_subtypeVal` / 定理 `comp_subtypeVal`

English:
theorem comp_subtypeVal
  statement: (hs : IsOpen s) (hfs : IsOpen (f ⁻¹' s)) {x : X} (hx : x in s)
  proof: have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  (isEmpty_or_nonempty I).elim (fun _ => .of_preimage_eq_empty _ ((hs.inter hU).mem_nhds ⟨hx, hxU⟩)
 Set.not_nonempty_iff_eq_empty.mp fun ⟨e, he⟩ => isEmptyElim (H ⟨⟨e, he.1⟩, he.2⟩).2) fun _ =>
  have hUs : U subseteq s := fun y hy => by
    convert! Set.mem

中文:
定理 comp_subtypeVal
  结论: (hs : IsOpen s) (hfs : IsOpen (f ⁻¹' s)) {x : X} (hx : x in s)
  证明: have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  (isEmpty_or_nonempty I).elim (fun _ => .of_preimage_eq_empty _ ((hs.inter hU).mem_nhds ⟨hx, hxU⟩)
 Set.not_nonempty_iff_eq_empty.mp fun ⟨e, he⟩ => isEmptyElim (H ⟨⟨e, he.1⟩, he.2⟩).2) fun _ =>
  have hUs : U subseteq s := fun y hy => by
    convert! Set.mem

Depends on / 依赖: Classical, Classical.arbitrary, H.symm, Set.mem_preimage.mp, Set.not_nonempty_iff_eq_empty.mp, Subtype, Subtype.val, arbitrary, convert, hfs.isOpenMap_subt, hs.inter, isEmptyElim, isEmpty_or_nonempty, isOpenMap_subt, mem_nhds, mem_preimage, not_nonempty_iff_eq_empty, of_preimage_eq_empty, subseteq
-/
theorem comp_subtypeVal (hs : IsOpen s) (hfs : IsOpen (f ⁻¹' s)) {x : X} (hx : x in s)
    (h : IsEvenlyCovered (fun e : f ⁻¹' s => f e) x I) : IsEvenlyCovered f x I :=
  have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  (isEmpty_or_nonempty I).elim (fun _ => .of_preimage_eq_empty _ ((hs.inter hU).mem_nhds ⟨hx, hxU⟩)
 Set.not_nonempty_iff_eq_empty.mp fun ⟨e, he⟩ => isEmptyElim (H ⟨⟨e, he.1⟩, he.2⟩).2) fun _ =>
  have hUs : U subseteq s := fun y hy => by
    convert! Set.mem_preimage.mp (H.symm (⟨y, hy⟩, Classical.arbitrary I)).1.2; simp [← hH]
  have : Subtype.val '' (fun e : f ⁻¹' s => f e) ⁻¹' U = f ⁻¹' U := by ext; simpa using @hUs _
  ⟨inst, U, hxU, hU, this ▸ hfs.isOpenMap_subtype_val _ hfU, .trans (.symm <| .trans
(IsEmbedding.subtypeVal.homeomorphImage _) .setCongr this) H, fun x => by
    dsimp; convert! hH ⟨⟨x, hUs x.2⟩, x.2⟩ using 4; rw [Homeomorph.symm_apply_eq]; rfl⟩

/--
theorem `comp_homeomorph` / 定理 `comp_homeomorph`

English:
theorem comp_homeomorph
  statement: {x : X} (h : IsEvenlyCovered f x I) {E'} [TopologicalSpace E']
  proof: have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  ⟨inst, U, hxU, hU, hfU.preimage g.continuous, .trans (.trans
    (.setCongr <| by rw [Set.preimage_comp, g.image_symm]) (g.symm.image _).symm) H, fun _ => hH _⟩

中文:
定理 comp_homeomorph
  结论: {x : X} (h : IsEvenlyCovered f x I) {E'} [TopologicalSpace E']
  证明: have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  ⟨inst, U, hxU, hU, hfU.preimage g.continuous, .trans (.trans
    (.setCongr <| by rw [Set.preimage_comp, g.image_symm]) (g.symm.image _).symm) H, fun _ => hH _⟩

Depends on / 依赖: Set.preimage_comp, continuous, g.continuous, g.image_symm, g.symm.image, hfU.preimage, image_symm, preimage, preimage_comp, setCongr
-/
theorem comp_homeomorph {x : X} (h : IsEvenlyCovered f x I) {E'} [TopologicalSpace E']
    (g : E' ≃ₜ E) : IsEvenlyCovered (f ∘ g) x I :=
  have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  ⟨inst, U, hxU, hU, hfU.preimage g.continuous, .trans (.trans
    (.setCongr <| by rw [Set.preimage_comp, g.image_symm]) (g.symm.image _).symm) H, fun _ => hH _⟩

/--
theorem `comp_homeomorph_iff` / 定理 `comp_homeomorph_iff`

English:
theorem comp_homeomorph_iff
  given: {x : X} {E'} [TopologicalSpace E'] (g : E' ≃ₜ E)
  proof: by convert! h.comp_homeomorph g.symm; ext; simp
  mpr h := h.comp_homeomorph g

中文:
定理 comp_homeomorph_iff
  条件: {x : X} {E'} [TopologicalSpace E'] (g : E' ≃ₜ E)
  证明: by convert! h.comp_homeomorph g.symm; ext; simp
  mpr h := h.comp_homeomorph g
-/
@[simp] theorem comp_homeomorph_iff {x : X} {E'} [TopologicalSpace E'] (g : E' ≃ₜ E) :
    IsEvenlyCovered (f ∘ g) x I ↔ IsEvenlyCovered f x I where
  mp h := by convert! h.comp_homeomorph g.symm; ext; simp
  mpr h := h.comp_homeomorph g

/--
theorem `homeomorph_comp` / 定理 `homeomorph_comp`

English:
theorem homeomorph_comp
  given: {x : X} (h : IsEvenlyCovered f x I) {Y} [TopologicalSpace Y] (g : X ≃ₜ Y)
  proof: have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  ⟨inst, g '' U, ⟨x, hxU, rfl⟩, g.isOpen_image.mpr hU, by simpa [Set.preimage_comp],
    .trans (.setCongr <| by simp [Set.preimage_comp]) (H.trans <| (g.image U).prodCongr (.refl I)),
    fun _ => congr_arg g (hH _)⟩

中文:
定理 homeomorph_comp
  条件: {x : X} (h : IsEvenlyCovered f x I) {Y} [TopologicalSpace Y] (g : X ≃ₜ Y)
  证明: have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  ⟨inst, g '' U, ⟨x, hxU, rfl⟩, g.isOpen_image.mpr hU, by simpa [Set.preimage_comp],
    .trans (.setCongr <| by simp [Set.preimage_comp]) (H.trans <| (g.image U).prodCongr (.refl I)),
    fun _ => congr_arg g (hH _)⟩

Depends on / 依赖: H.trans, Set.preimage_comp, congr_arg, g.image, g.isOpen_image.mpr, isOpen_image, preimage_comp, prodCongr, setCongr
-/
theorem homeomorph_comp {x : X} (h : IsEvenlyCovered f x I) {Y} [TopologicalSpace Y] (g : X ≃ₜ Y) :
    IsEvenlyCovered (g ∘ f) (g x) I :=
  have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  ⟨inst, g '' U, ⟨x, hxU, rfl⟩, g.isOpen_image.mpr hU, by simpa [Set.preimage_comp],
    .trans (.setCongr <| by simp [Set.preimage_comp]) (H.trans <| (g.image U).prodCongr (.refl I)),
    fun _ => congr_arg g (hH _)⟩

/--
theorem `homeomorph_comp_iff` / 定理 `homeomorph_comp_iff`

English:
theorem homeomorph_comp_iff
  given: {x : X} {Y} [TopologicalSpace Y] (g : X ≃ₜ Y)
  proof: by convert! h.homeomorph_comp g.symm <;> ((try ext); simp)
  mpr h := h.homeomorph_comp g

中文:
定理 homeomorph_comp_iff
  条件: {x : X} {Y} [TopologicalSpace Y] (g : X ≃ₜ Y)
  证明: by convert! h.homeomorph_comp g.symm <;> ((try ext); simp)
  mpr h := h.homeomorph_comp g
-/
@[simp] theorem homeomorph_comp_iff {x : X} {Y} [TopologicalSpace Y] (g : X ≃ₜ Y) :
    IsEvenlyCovered (g ∘ f) (g x) I ↔ IsEvenlyCovered f x I where
  mp h := by convert! h.homeomorph_comp g.symm <;> ((try ext); simp)
  mpr h := h.homeomorph_comp g

end IsEvenlyCovered

/--
Definition of `IsCoveringMapOn` / `IsCoveringMapOn` 的定义

English:
definition IsCoveringMapOn
  body: forall x in s, IsEvenlyCovered f x (f ⁻¹' {x})

中文:
定义 IsCoveringMapOn
  定义体: forall x in s, IsEvenlyCovered f x (f ⁻¹' {x})

Depends on / 依赖: IsEvenlyCovered
-/
def IsCoveringMapOn :=
  forall x in s, IsEvenlyCovered f x (f ⁻¹' {x})

namespace IsCoveringMapOn

/--
theorem `of_isEmpty` / 定理 `of_isEmpty`

English:
theorem of_isEmpty
  given: [IsEmpty E]
  statement: IsCoveringMapOn f s
  proof: fun _ _ => .to_isEvenlyCovered_preimage
  (.of_preimage_eq_empty Empty Filter.univ_mem <| Set.eq_empty_of_isEmpty _)

中文:
定理 of_isEmpty
  条件: [IsEmpty E]
  结论: IsCoveringMapOn f s
  证明: fun _ _ => .to_isEvenlyCovered_preimage
  (.of_preimage_eq_empty Empty Filter.univ_mem <| Set.eq_empty_of_isEmpty _)

Depends on / 依赖: to_isEvenlyCovered_preimage
-/
theorem of_isEmpty [IsEmpty E] : IsCoveringMapOn f s := fun _ _ => .to_isEvenlyCovered_preimage
  (.of_preimage_eq_empty Empty Filter.univ_mem <| Set.eq_empty_of_isEmpty _)

/--
theorem `mk'` / 定理 `mk'`

English:
theorem mk'
  statement: (F : s -> Type*) [forall x : s, TopologicalSpace (F x)] [hF : forall x : s, DiscreteTopology (F x)]
  proof: fun x hx => by
  lift x to s using hx
  by_cases hxf : x.1 in Set.range f
  · exact .to_isEvenlyCovered_preimage (.of_trivialization (t x hxf).2)
  · have ⟨U, hUx, hfU⟩ := h x hxf
    exact .to_isEvenlyCovered_preimage (.of_preimage_eq_empty Empty hUx hfU)

中文:
定理 mk'
  结论: (F : s -> 类型) [对任意 x : s, TopologicalSpace (F x)] [hF : 对任意 x : s, DiscreteTopology (F x)]
  证明: fun x hx => by
  lift x to s using hx
  by_cases hxf : x.1 in Set.range f
  · exact .to_isEvenlyCovered_preimage (.of_trivialization (t x hxf).2)
  · have ⟨U, hUx, hfU⟩ := h x hxf
    exact .to_isEvenlyCovered_preimage (.of_preimage_eq_empty Empty hUx hfU)

Depends on / 依赖: Set.range, of_preimage_eq_empty, of_trivialization, to_isEvenlyCovered_preimage
-/
theorem mk' (F : s -> Type*) [forall x : s, TopologicalSpace (F x)] [hF : forall x : s, DiscreteTopology (F x)]
    (t : forall x : s, x.1 in Set.range f -> {t : Trivialization (F x) f // x.1 in t.baseSet})
    (h : forall x : s, x.1 ∉ Set.range f -> exists U in 𝓝 x.1, f ⁻¹' U = ∅) :
    IsCoveringMapOn f s := fun x hx => by
  lift x to s using hx
  by_cases hxf : x.1 in Set.range f
  · exact .to_isEvenlyCovered_preimage (.of_trivialization (t x hxf).2)
  · have ⟨U, hUx, hfU⟩ := h x hxf
    exact .to_isEvenlyCovered_preimage (.of_preimage_eq_empty Empty hUx hfU)

/--
theorem `mk` / 定理 `mk`

English:
theorem mk
  statement: (F : s -> Type*) [forall x, TopologicalSpace (F x)] [hF : forall x, DiscreteTopology (F x)]
  proof: by
  cases isEmpty_or_nonempty E
  · exact .of_isEmpty _ _
  refine .mk' _ _ _ (fun x _ => ⟨e x, h x⟩) fun x hx => (hx ?_).elim
  exact ⟨(e x).invFun (x, (e x <| Classical.arbitrary E).2), (e x).proj_symm_apply' (h x)⟩

中文:
定理 mk
  结论: (F : s -> 类型) [对任意 x, TopologicalSpace (F x)] [hF : 对任意 x, DiscreteTopology (F x)]
  证明: by
  cases isEmpty_or_nonempty E
  · exact .of_isEmpty _ _
  refine .mk' _ _ _ (fun x _ => ⟨e x, h x⟩) fun x hx => (hx ?_).elim
  exact ⟨(e x).invFun (x, (e x <| Classical.arbitrary E).2), (e x).proj_symm_apply' (h x)⟩

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, invFun, isEmpty_or_nonempty, of_isEmpty, proj_symm_apply
-/
theorem mk (F : s -> Type*) [forall x, TopologicalSpace (F x)] [hF : forall x, DiscreteTopology (F x)]
    (e : forall x, Trivialization (F x) f) (h : forall x, x.1 in (e x).baseSet) :
    IsCoveringMapOn f s := by
  cases isEmpty_or_nonempty E
  · exact .of_isEmpty _ _
  refine .mk' _ _ _ (fun x _ => ⟨e x, h x⟩) fun x hx => (hx ?_).elim
  exact ⟨(e x).invFun (x, (e x <| Classical.arbitrary E).2), (e x).proj_symm_apply' (h x)⟩

variable {f s}

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: {t : Set X} (hf : IsCoveringMapOn f s) (ht : t subseteq s)
  statement: IsCoveringMapOn f t
  proof: fun x hx => hf x (ht hx)

中文:
定理 mono
  条件: {t : Set X} (hf : IsCoveringMapOn f s) (ht : t subseteq s)
  结论: IsCoveringMapOn f t
  证明: fun x hx => hf x (ht hx)
-/
theorem mono {t : Set X} (hf : IsCoveringMapOn f s) (ht : t subseteq s) : IsCoveringMapOn f t :=
  fun x hx => hf x (ht hx)

/--
theorem `continuousAt` / 定理 `continuousAt`

English:
theorem continuousAt
  given: (hf : IsCoveringMapOn f s) {x : E} (hx : f x in s)
  proof: (hf (f x) hx).continuousAt

中文:
定理 continuousAt
  条件: (hf : IsCoveringMapOn f s) {x : E} (hx : f x in s)
  证明: (hf (f x) hx).continuousAt
-/
protected theorem continuousAt (hf : IsCoveringMapOn f s) {x : E} (hx : f x in s) :
    ContinuousAt f x := (hf (f x) hx).continuousAt

/--
theorem `continuousOn` / 定理 `continuousOn`

English:
theorem continuousOn
  given: (hf : IsCoveringMapOn f s)
  statement: ContinuousOn f (f ⁻¹' s)
  proof: continuousOn_of_forall_continuousAt fun _ => hf.continuousAt

中文:
定理 continuousOn
  条件: (hf : IsCoveringMapOn f s)
  结论: ContinuousOn f (f ⁻¹' s)
  证明: continuousOn_of_forall_continuousAt fun _ => hf.continuousAt
-/
protected theorem continuousOn (hf : IsCoveringMapOn f s) : ContinuousOn f (f ⁻¹' s) :=
  continuousOn_of_forall_continuousAt fun _ => hf.continuousAt

/--
theorem `isLocalHomeomorphOn` / 定理 `isLocalHomeomorphOn`

English:
theorem isLocalHomeomorphOn
  given: (hf : IsCoveringMapOn f s)
  proof: by
  refine IsLocalHomeomorphOn.mk f (f ⁻¹' s) fun x hx => ?_
  have : Nonempty (f ⁻¹' {f x}) := ⟨⟨x, rfl⟩⟩
  let e := (hf (f x) hx).toTrivialization
  have h := (hf (f x) hx).mem_toTrivialization_baseSet
  let he := e.mem_source.2 h
  refine
    ⟨e.toOpenPartialHomeomorph.trans
        { toFun := f

中文:
定理 isLocalHomeomorphOn
  条件: (hf : IsCoveringMapOn f s)
  证明: by
  refine IsLocalHomeomorphOn.mk f (f ⁻¹' s) fun x hx => ?_
  have : Nonempty (f ⁻¹' {f x}) := ⟨⟨x, rfl⟩⟩
  let e := (hf (f x) hx).toTrivialization
  have h := (hf (f x) hx).mem_toTrivialization_baseSet
  let he := e.mem_source.2 h
  refine
    ⟨e.toOpenPartialHomeomorph.trans
        { toFun := f
-/
protected theorem isLocalHomeomorphOn (hf : IsCoveringMapOn f s) :
    IsLocalHomeomorphOn f (f ⁻¹' s) := by
  refine IsLocalHomeomorphOn.mk f (f ⁻¹' s) fun x hx => ?_
  have : Nonempty (f ⁻¹' {f x}) := ⟨⟨x, rfl⟩⟩
  let e := (hf (f x) hx).toTrivialization
  have h := (hf (f x) hx).mem_toTrivialization_baseSet
  let he := e.mem_source.2 h
  refine
    ⟨e.toOpenPartialHomeomorph.trans
        { toFun := fun p => p.1
          invFun := fun p => ⟨p, x, rfl⟩
          source := e.baseSet ×ˢ ({⟨x, rfl⟩} : Set (f ⁻¹' {f x}))
          target := e.baseSet
          open_source :=
            e.open_baseSet.prod (discreteTopology_iff_isOpen_singleton.1 (hf (f x) hx).1 ⟨x, rfl⟩)
          open_target := e.open_baseSet
          map_source' := fun p => And.left
          map_target' := fun p hp => ⟨hp, rfl⟩
          left_inv' := fun p hp => Prod.ext rfl hp.2.symm
          right_inv' := fun p _ => rfl
          continuousOn_toFun := continuousOn_fst
          continuousOn_invFun := by fun_prop },
      ⟨he, by rwa [e.toOpenPartialHomeomorph.symm_symm, e.proj_toFun x he],
        (hf (f x) hx).toTrivialization_apply⟩,
      fun p h => (e.proj_toFun p h.1).symm⟩

/--
theorem `restrictPreimage` / 定理 `restrictPreimage`

English:
theorem restrictPreimage
  given: (hf : IsCoveringMapOn f s) (t : Set X)
  proof: fun x hs => ((hf x hs).restrictPreimage t x.2).to_isEvenlyCovered_preimage

中文:
定理 restrictPreimage
  条件: (hf : IsCoveringMapOn f s) (t : Set X)
  证明: fun x hs => ((hf x hs).restrictPreimage t x.2).to_isEvenlyCovered_preimage

Depends on / 依赖: restrictPreimage, to_isEvenlyCovered_preimage
-/
theorem restrictPreimage (hf : IsCoveringMapOn f s) (t : Set X) :
    IsCoveringMapOn (t.restrictPreimage f) (Subtype.val ⁻¹' s) :=
  fun x hs => ((hf x hs).restrictPreimage t x.2).to_isEvenlyCovered_preimage

/--
theorem `comp_homeomorph` / 定理 `comp_homeomorph`

English:
theorem comp_homeomorph
  given: (hf : IsCoveringMapOn f s) {E'} [TopologicalSpace E'] (g : E' ≃ₜ E)
  proof: fun x hx => ((hf x hx).comp_homeomorph _).to_isEvenlyCovered_preimage

中文:
定理 comp_homeomorph
  条件: (hf : IsCoveringMapOn f s) {E'} [TopologicalSpace E'] (g : E' ≃ₜ E)
  证明: fun x hx => ((hf x hx).comp_homeomorph _).to_isEvenlyCovered_preimage

Depends on / 依赖: comp_homeomorph, to_isEvenlyCovered_preimage
-/
theorem comp_homeomorph (hf : IsCoveringMapOn f s) {E'} [TopologicalSpace E'] (g : E' ≃ₜ E) :
    IsCoveringMapOn (f ∘ g) s :=
  fun x hx => ((hf x hx).comp_homeomorph _).to_isEvenlyCovered_preimage

/--
theorem `comp_homeomorph_iff` / 定理 `comp_homeomorph_iff`

English:
theorem comp_homeomorph_iff
  given: {E'} [TopologicalSpace E'] (g : E' ≃ₜ E)
  proof: by convert! h.comp_homeomorph g.symm; ext; simp
  mpr h := h.comp_homeomorph g

中文:
定理 comp_homeomorph_iff
  条件: {E'} [TopologicalSpace E'] (g : E' ≃ₜ E)
  证明: by convert! h.comp_homeomorph g.symm; ext; simp
  mpr h := h.comp_homeomorph g
-/
@[simp] theorem comp_homeomorph_iff {E'} [TopologicalSpace E'] (g : E' ≃ₜ E) :
    IsCoveringMapOn (f ∘ g) s ↔ IsCoveringMapOn f s where
  mp h := by convert! h.comp_homeomorph g.symm; ext; simp
  mpr h := h.comp_homeomorph g

/--
theorem `homeomorph_comp` / 定理 `homeomorph_comp`

English:
theorem homeomorph_comp
  given: (hf : IsCoveringMapOn f s) {Y} [TopologicalSpace Y] (g : X ≃ₜ Y)
  proof: fun y hy => (g.apply_symm_apply y ▸ (hf _ hy).homeomorph_comp _).to_isEvenlyCovered_preimage

中文:
定理 homeomorph_comp
  条件: (hf : IsCoveringMapOn f s) {Y} [TopologicalSpace Y] (g : X ≃ₜ Y)
  证明: fun y hy => (g.apply_symm_apply y ▸ (hf _ hy).homeomorph_comp _).to_isEvenlyCovered_preimage

Depends on / 依赖: apply_symm_apply, g.apply_symm_apply, homeomorph_comp, to_isEvenlyCovered_preimage
-/
theorem homeomorph_comp (hf : IsCoveringMapOn f s) {Y} [TopologicalSpace Y] (g : X ≃ₜ Y) :
    IsCoveringMapOn (g ∘ f) (g.symm ⁻¹' s) :=
  fun y hy => (g.apply_symm_apply y ▸ (hf _ hy).homeomorph_comp _).to_isEvenlyCovered_preimage

/--
theorem `homeomorph_comp_iff` / 定理 `homeomorph_comp_iff`

English:
theorem homeomorph_comp_iff
  given: {Y} [TopologicalSpace Y] (g : X ≃ₜ Y)
  proof: by convert! h.homeomorph_comp g.symm <;> (ext; simp)
  mpr h := h.homeomorph_comp g

中文:
定理 homeomorph_comp_iff
  条件: {Y} [TopologicalSpace Y] (g : X ≃ₜ Y)
  证明: by convert! h.homeomorph_comp g.symm <;> (ext; simp)
  mpr h := h.homeomorph_comp g
-/
@[simp] theorem homeomorph_comp_iff {Y} [TopologicalSpace Y] (g : X ≃ₜ Y) :
    IsCoveringMapOn (g ∘ f) (g.symm ⁻¹' s) ↔ IsCoveringMapOn f s where
  mp h := by convert! h.homeomorph_comp g.symm <;> (ext; simp)
  mpr h := h.homeomorph_comp g

end IsCoveringMapOn

/--
Definition of `IsCoveringMap` / `IsCoveringMap` 的定义

English:
definition IsCoveringMap
  body: forall x, IsEvenlyCovered f x (f ⁻¹' {x})

中文:
定义 IsCoveringMap
  定义体: forall x, IsEvenlyCovered f x (f ⁻¹' {x})

Depends on / 依赖: IsEvenlyCovered
-/
def IsCoveringMap :=
  forall x, IsEvenlyCovered f x (f ⁻¹' {x})

variable {f}

/--
theorem `isCoveringMap_iff_isCoveringMapOn_univ` / 定理 `isCoveringMap_iff_isCoveringMapOn_univ`

English:
theorem isCoveringMap_iff_isCoveringMapOn_univ
  statement: IsCoveringMap f ↔ IsCoveringMapOn f .univ
  proof: by
  simp only [IsCoveringMap, IsCoveringMapOn, Set.mem_univ, forall_true_left]

中文:
定理 isCoveringMap_iff_isCoveringMapOn_univ
  结论: IsCoveringMap f ↔ IsCoveringMapOn f .univ
  证明: by
  simp only [IsCoveringMap, IsCoveringMapOn, Set.mem_univ, forall_true_left]

Depends on / 依赖: IsCoveringMap, IsCoveringMapOn, Set.mem_univ, forall_true_left, mem_univ
-/
theorem isCoveringMap_iff_isCoveringMapOn_univ : IsCoveringMap f ↔ IsCoveringMapOn f .univ := by
  simp only [IsCoveringMap, IsCoveringMapOn, Set.mem_univ, forall_true_left]

/--
theorem `IsCoveringMap.isCoveringMapOn` / 定理 `IsCoveringMap.isCoveringMapOn`

English:
theorem IsCoveringMap.isCoveringMapOn
  given: (hf : IsCoveringMap f)
  statement: IsCoveringMapOn f .univ
  proof: isCoveringMap_iff_isCoveringMapOn_univ.mp hf

中文:
定理 IsCoveringMap.isCoveringMapOn
  条件: (hf : IsCoveringMap f)
  结论: IsCoveringMapOn f .univ
  证明: isCoveringMap_iff_isCoveringMapOn_univ.mp hf
-/
protected theorem IsCoveringMap.isCoveringMapOn (hf : IsCoveringMap f) : IsCoveringMapOn f .univ :=
  isCoveringMap_iff_isCoveringMapOn_univ.mp hf

/--
theorem `IsCoveringMapOn.isCoveringMap_restrictPreimage` / 定理 `IsCoveringMapOn.isCoveringMap_restrictPreimage`

English:
theorem IsCoveringMapOn.isCoveringMap_restrictPreimage
  given: (hf : IsCoveringMapOn f s)
  proof: isCoveringMap_iff_isCoveringMapOn_univ.mpr by simpa using hf.restrictPreimage s

中文:
定理 IsCoveringMapOn.isCoveringMap_restrictPreimage
  条件: (hf : IsCoveringMapOn f s)
  证明: isCoveringMap_iff_isCoveringMapOn_univ.mpr by simpa using hf.restrictPreimage s

Depends on / 依赖: hf.restrictPreimage, isCoveringMap_iff_isCoveringMapOn_univ, isCoveringMap_iff_isCoveringMapOn_univ.mpr, restrictPreimage
-/
theorem IsCoveringMapOn.isCoveringMap_restrictPreimage (hf : IsCoveringMapOn f s) :
    IsCoveringMap (s.restrictPreimage f) :=
isCoveringMap_iff_isCoveringMapOn_univ.mpr by simpa using hf.restrictPreimage s

/--
theorem `IsCoveringMapOn.of_isCoveringMap_restrictPreimage` / 定理 `IsCoveringMapOn.of_isCoveringMap_restrictPreimage`

English:
theorem IsCoveringMapOn.of_isCoveringMap_restrictPreimage
  statement: (hs : IsOpen s) (hfs : IsOpen (f ⁻¹' s))
  proof: fun x hx =>
  (((hf ⟨x, hx⟩).subtypeVal_comp _ hs).comp_subtypeVal _ hs hfs hx).to_isEvenlyCovered_preimage

中文:
定理 IsCoveringMapOn.of_isCoveringMap_restrictPreimage
  结论: (hs : IsOpen s) (hfs : IsOpen (f ⁻¹' s))
  证明: fun x hx =>
  (((hf ⟨x, hx⟩).subtypeVal_comp _ hs).comp_subtypeVal _ hs hfs hx).to_isEvenlyCovered_preimage
-/
theorem IsCoveringMapOn.of_isCoveringMap_restrictPreimage (hs : IsOpen s) (hfs : IsOpen (f ⁻¹' s))
    (hf : IsCoveringMap (s.restrictPreimage f)) : IsCoveringMapOn f s := fun x hx =>
  (((hf ⟨x, hx⟩).subtypeVal_comp _ hs).comp_subtypeVal _ hs hfs hx).to_isEvenlyCovered_preimage

variable (f)

namespace IsCoveringMap

/--
theorem `of_isEmpty` / 定理 `of_isEmpty`

English:
theorem of_isEmpty
  given: [IsEmpty E]
  statement: IsCoveringMap f
  proof: isCoveringMap_iff_isCoveringMapOn_univ.mpr .of_isEmpty _ _

中文:
定理 of_isEmpty
  条件: [IsEmpty E]
  结论: IsCoveringMap f
  证明: isCoveringMap_iff_isCoveringMapOn_univ.mpr .of_isEmpty _ _

Depends on / 依赖: isCoveringMap_iff_isCoveringMapOn_univ, isCoveringMap_iff_isCoveringMapOn_univ.mpr, of_isEmpty
-/
theorem of_isEmpty [IsEmpty E] : IsCoveringMap f :=
isCoveringMap_iff_isCoveringMapOn_univ.mpr .of_isEmpty _ _

/--
theorem `of_discreteTopology` / 定理 `of_discreteTopology`

English:
theorem of_discreteTopology
  given: [DiscreteTopology E] [DiscreteTopology X]
  statement: IsCoveringMap f
  proof: fun x => ⟨inferInstance, {x}, rfl, isOpen_discrete _, isOpen_discrete _,
    { toFun e := ⟨⟨x, rfl⟩, e⟩
      invFun xi := xi.2
      left_inv _ := rfl
      right_inv _ := Prod.ext (Subsingleton.elim ..) rfl },
    (·.2.symm)⟩

中文:
定理 of_discreteTopology
  条件: [DiscreteTopology E] [DiscreteTopology X]
  结论: IsCoveringMap f
  证明: fun x => ⟨inferInstance, {x}, rfl, isOpen_discrete _, isOpen_discrete _,
    { toFun e := ⟨⟨x, rfl⟩, e⟩
      invFun xi := xi.2
      left_inv _ := rfl
      right_inv _ := Prod.ext (Subsingleton.elim ..) rfl },
    (·.2.symm)⟩

Depends on / 依赖: Prod.ext, Subsingleton, Subsingleton.elim, invFun, isOpen_discrete, left_inv, right_inv
-/
theorem of_discreteTopology [DiscreteTopology E] [DiscreteTopology X] : IsCoveringMap f :=
  fun x => ⟨inferInstance, {x}, rfl, isOpen_discrete _, isOpen_discrete _,
    { toFun e := ⟨⟨x, rfl⟩, e⟩
      invFun xi := xi.2
      left_inv _ := rfl
      right_inv _ := Prod.ext (Subsingleton.elim ..) rfl },
    (·.2.symm)⟩

/--
theorem `mk'` / 定理 `mk'`

English:
theorem mk'
  statement: (F : X -> Type*) [forall x, TopologicalSpace (F x)] [forall x, DiscreteTopology (F x)]
  proof: isCoveringMap_iff_isCoveringMapOn_univ.mpr .mk' f _ _ (fun x h => t x h) fun _x hx =>
    ⟨_, h.isOpen_compl.mem_nhds hx, Set.eq_empty_of_forall_notMem fun x h => h ⟨x, rfl⟩⟩

中文:
定理 mk'
  结论: (F : X -> 类型) [对任意 x, TopologicalSpace (F x)] [对任意 x, DiscreteTopology (F x)]
  证明: isCoveringMap_iff_isCoveringMapOn_univ.mpr .mk' f _ _ (fun x h => t x h) fun _x hx =>
    ⟨_, h.isOpen_compl.mem_nhds hx, Set.eq_empty_of_forall_notMem fun x h => h ⟨x, rfl⟩⟩

Depends on / 依赖: Set.eq_empty_of_forall_notMem, eq_empty_of_forall_notMem, h.isOpen_compl.mem_nhds, isCoveringMap_iff_isCoveringMapOn_univ, isCoveringMap_iff_isCoveringMapOn_univ.mpr, isOpen_compl, mem_nhds
-/
theorem mk' (F : X -> Type*) [forall x, TopologicalSpace (F x)] [forall x, DiscreteTopology (F x)]
    (t : forall x, x in Set.range f -> {t : Trivialization (F x) f // x in t.baseSet})
    (h : IsClosed (Set.range f)) : IsCoveringMap f :=
isCoveringMap_iff_isCoveringMapOn_univ.mpr .mk' f _ _ (fun x h => t x h) fun _x hx =>
    ⟨_, h.isOpen_compl.mem_nhds hx, Set.eq_empty_of_forall_notMem fun x h => h ⟨x, rfl⟩⟩

/--
theorem `mk` / 定理 `mk`

English:
theorem mk
  statement: (F : X -> Type*) [forall x, TopologicalSpace (F x)] [forall x, DiscreteTopology (F x)]
  proof: isCoveringMap_iff_isCoveringMapOn_univ.mpr .mk _ _ _ _ fun x => h x

中文:
定理 mk
  结论: (F : X -> 类型) [对任意 x, TopologicalSpace (F x)] [对任意 x, DiscreteTopology (F x)]
  证明: isCoveringMap_iff_isCoveringMapOn_univ.mpr .mk _ _ _ _ fun x => h x

Depends on / 依赖: isCoveringMap_iff_isCoveringMapOn_univ, isCoveringMap_iff_isCoveringMapOn_univ.mpr
-/
theorem mk (F : X -> Type*) [forall x, TopologicalSpace (F x)] [forall x, DiscreteTopology (F x)]
    (e : forall x, Trivialization (F x) f) (h : forall x, x in (e x).baseSet) : IsCoveringMap f :=
isCoveringMap_iff_isCoveringMapOn_univ.mpr .mk _ _ _ _ fun x => h x

variable {f}
variable (hf : IsCoveringMap f)
include hf

/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  statement: Continuous f
  proof: continuousOn_univ.mp hf.isCoveringMapOn.continuousOn

中文:
定理 continuous
  结论: Continuous f
  证明: continuousOn_univ.mp hf.isCoveringMapOn.continuousOn
-/
protected theorem continuous : Continuous f :=
  continuousOn_univ.mp hf.isCoveringMapOn.continuousOn

/--
theorem `isLocalHomeomorph` / 定理 `isLocalHomeomorph`

English:
theorem isLocalHomeomorph
  statement: IsLocalHomeomorph f
  proof: isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr hf.isCoveringMapOn.isLocalHomeomorphOn

中文:
定理 isLocalHomeomorph
  结论: IsLocalHomeomorph f
  证明: isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr hf.isCoveringMapOn.isLocalHomeomorphOn
-/
protected theorem isLocalHomeomorph : IsLocalHomeomorph f :=
  isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr hf.isCoveringMapOn.isLocalHomeomorphOn

/--
theorem `isOpenMap` / 定理 `isOpenMap`

English:
theorem isOpenMap
  statement: IsOpenMap f
  proof: hf.isLocalHomeomorph.isOpenMap

中文:
定理 isOpenMap
  结论: IsOpenMap f
  证明: hf.isLocalHomeomorph.isOpenMap
-/
protected theorem isOpenMap : IsOpenMap f :=
  hf.isLocalHomeomorph.isOpenMap

/--
theorem `isQuotientMap` / 定理 `isQuotientMap`

English:
theorem isQuotientMap
  given: (hf' : Function.Surjective f)
  statement: IsQuotientMap f
  proof: hf.isOpenMap.isQuotientMap hf.continuous hf'

中文:
定理 isQuotientMap
  条件: (hf' : Function.Surjective f)
  结论: IsQuotientMap f
  证明: hf.isOpenMap.isQuotientMap hf.continuous hf'

Depends on / 依赖: continuous, hf.continuous, hf.isOpenMap.isQuotientMap, isOpenMap, isQuotientMap
-/
theorem isQuotientMap (hf' : Function.Surjective f) : IsQuotientMap f :=
  hf.isOpenMap.isQuotientMap hf.continuous hf'

/--
theorem `isSeparatedMap` / 定理 `isSeparatedMap`

English:
theorem isSeparatedMap
  statement: IsSeparatedMap f
  proof: fun e₁ e₂ he hne => by
    have : Nonempty (f ⁻¹' {f e₁}) := ⟨⟨e₁, rfl⟩⟩
    specialize hf (f e₁)
    let t := hf.toTrivialization
    have := hf.discreteTopology_fiber
    have he₁ := hf.mem_toTrivialization_baseSet
    have he₂ := he₁; simp_rw [he] at he₂; rw [← t.mem_source] at he₁ he₂
    refine

中文:
定理 isSeparatedMap
  结论: IsSeparatedMap f
  证明: fun e₁ e₂ he hne => by
    have : Nonempty (f ⁻¹' {f e₁}) := ⟨⟨e₁, rfl⟩⟩
    specialize hf (f e₁)
    let t := hf.toTrivialization
    have := hf.discreteTopology_fiber
    have he₁ := hf.mem_toTrivialization_baseSet
    have he₂ := he₁; simp_rw [he] at he₂; rw [← t.mem_source] at he₁ he₂
    refine
-/
protected theorem isSeparatedMap : IsSeparatedMap f :=
  fun e₁ e₂ he hne => by
    have : Nonempty (f ⁻¹' {f e₁}) := ⟨⟨e₁, rfl⟩⟩
    specialize hf (f e₁)
    let t := hf.toTrivialization
    have := hf.discreteTopology_fiber
    have he₁ := hf.mem_toTrivialization_baseSet
    have he₂ := he₁; simp_rw [he] at he₂; rw [← t.mem_source] at he₁ he₂
    refine ⟨t.source inter (Prod.snd ∘ t) ⁻¹' {(t e₁).2}, t.source inter (Prod.snd ∘ t) ⁻¹' {(t e₂).2},
      ?_, ?_, ⟨he₁, rfl⟩, ⟨he₂, rfl⟩, Set.disjoint_left.mpr fun x h₁ h₂ => hne (t.injOn he₁ he₂ ?_)⟩
    iterate 2
      exact t.continuousOn_toFun.isOpen_inter_preimage t.open_source
        (continuous_snd.isOpen_preimage _ <| isOpen_discrete _)
    refine Prod.ext ?_ (h₁.2.symm.trans h₂.2)
    rwa [t.proj_toFun e₁ he₁, t.proj_toFun e₂ he₂]

variable {A} [TopologicalSpace A] {s : Set A} {g g₁ g₂ : A -> E}

/--
theorem `eq_of_comp_eq` / 定理 `eq_of_comp_eq`

English:
theorem eq_of_comp_eq
  statement: [PreconnectedSpace A] (h₁ : Continuous g₁) (h₂ : Continuous g₂)
  proof: hf.isSeparatedMap.eq_of_comp_eq hf.isLocalHomeomorph.isLocallyInjective h₁ h₂ he a ha

中文:
定理 eq_of_comp_eq
  结论: [PreconnectedSpace A] (h₁ : Continuous g₁) (h₂ : Continuous g₂)
  证明: hf.isSeparatedMap.eq_of_comp_eq hf.isLocalHomeomorph.isLocallyInjective h₁ h₂ he a ha

Depends on / 依赖: eq_of_comp_eq, hf.isLocalHomeomorph.isLocallyInjective, hf.isSeparatedMap.eq_of_comp_eq, isLocalHomeomorph, isLocallyInjective, isSeparatedMap
-/
theorem eq_of_comp_eq [PreconnectedSpace A] (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (he : f ∘ g₁ = f ∘ g₂) (a : A) (ha : g₁ a = g₂ a) : g₁ = g₂ :=
  hf.isSeparatedMap.eq_of_comp_eq hf.isLocalHomeomorph.isLocallyInjective h₁ h₂ he a ha

/--
theorem `const_of_comp` / 定理 `const_of_comp`

English:
theorem const_of_comp
  statement: [PreconnectedSpace A] (cont : Continuous g)
  proof: hf.isSeparatedMap.const_of_comp hf.isLocalHomeomorph.isLocallyInjective cont he a a'

中文:
定理 const_of_comp
  结论: [PreconnectedSpace A] (cont : Continuous g)
  证明: hf.isSeparatedMap.const_of_comp hf.isLocalHomeomorph.isLocallyInjective cont he a a'

Depends on / 依赖: const_of_comp, hf.isLocalHomeomorph.isLocallyInjective, hf.isSeparatedMap.const_of_comp, isLocalHomeomorph, isLocallyInjective, isSeparatedMap
-/
theorem const_of_comp [PreconnectedSpace A] (cont : Continuous g)
    (he : forall a a', f (g a) = f (g a')) (a a') : g a = g a' :=
  hf.isSeparatedMap.const_of_comp hf.isLocalHomeomorph.isLocallyInjective cont he a a'

/--
theorem `eqOn_of_comp_eqOn` / 定理 `eqOn_of_comp_eqOn`

English:
theorem eqOn_of_comp_eqOn
  statement: (hs : IsPreconnected s) (h₁ : ContinuousOn g₁ s) (h₂ : ContinuousOn g₂ s)
  proof: hf.isSeparatedMap.eqOn_of_comp_eqOn hf.isLocalHomeomorph.isLocallyInjective hs h₁ h₂ he has ha

中文:
定理 eqOn_of_comp_eqOn
  结论: (hs : IsPreconnected s) (h₁ : ContinuousOn g₁ s) (h₂ : ContinuousOn g₂ s)
  证明: hf.isSeparatedMap.eqOn_of_comp_eqOn hf.isLocalHomeomorph.isLocallyInjective hs h₁ h₂ he has ha

Depends on / 依赖: eqOn_of_comp_eqOn, hf.isLocalHomeomorph.isLocallyInjective, hf.isSeparatedMap.eqOn_of_comp_eqOn, isLocalHomeomorph, isLocallyInjective, isSeparatedMap
-/
theorem eqOn_of_comp_eqOn (hs : IsPreconnected s) (h₁ : ContinuousOn g₁ s) (h₂ : ContinuousOn g₂ s)
    (he : s.EqOn (f ∘ g₁) (f ∘ g₂)) {a : A} (has : a in s) (ha : g₁ a = g₂ a) : s.EqOn g₁ g₂ :=
  hf.isSeparatedMap.eqOn_of_comp_eqOn hf.isLocalHomeomorph.isLocallyInjective hs h₁ h₂ he has ha

/--
theorem `constOn_of_comp` / 定理 `constOn_of_comp`

English:
theorem constOn_of_comp
  statement: (hs : IsPreconnected s) (cont : ContinuousOn g s)
  proof: hf.isSeparatedMap.constOn_of_comp hf.isLocalHomeomorph.isLocallyInjective hs cont he ha ha'

中文:
定理 constOn_of_comp
  结论: (hs : IsPreconnected s) (cont : ContinuousOn g s)
  证明: hf.isSeparatedMap.constOn_of_comp hf.isLocalHomeomorph.isLocallyInjective hs cont he ha ha'

Depends on / 依赖: constOn_of_comp, hf.isLocalHomeomorph.isLocallyInjective, hf.isSeparatedMap.constOn_of_comp, isLocalHomeomorph, isLocallyInjective, isSeparatedMap
-/
theorem constOn_of_comp (hs : IsPreconnected s) (cont : ContinuousOn g s)
    (he : forall a in s, forall a' in s, f (g a) = f (g a'))
    {a a'} (ha : a in s) (ha' : a' in s) : g a = g a' :=
  hf.isSeparatedMap.constOn_of_comp hf.isLocalHomeomorph.isLocallyInjective hs cont he ha ha'

/--
theorem `restrictPreimage` / 定理 `restrictPreimage`

English:
theorem restrictPreimage
  given: (t : Set X)
  statement: IsCoveringMap (t.restrictPreimage f)
  proof: by
  rw [isCoveringMap_iff_isCoveringMapOn_univ] at hf ⊢
  exact hf.restrictPreimage t

中文:
定理 restrictPreimage
  条件: (t : Set X)
  结论: IsCoveringMap (t.restrictPreimage f)
  证明: by
  rw [isCoveringMap_iff_isCoveringMapOn_univ] at hf ⊢
  exact hf.restrictPreimage t

Depends on / 依赖: hf.restrictPreimage, isCoveringMap_iff_isCoveringMapOn_univ, restrictPreimage
-/
theorem restrictPreimage (t : Set X) : IsCoveringMap (t.restrictPreimage f) := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ] at hf ⊢
  exact hf.restrictPreimage t

/--
theorem `comp_homeomorph` / 定理 `comp_homeomorph`

English:
theorem comp_homeomorph
  given: {E'} [TopologicalSpace E'] (g : E' ≃ₜ E)
  statement: IsCoveringMap (f ∘ g)
  proof: by
  rw [isCoveringMap_iff_isCoveringMapOn_univ] at hf ⊢
  exact hf.comp_homeomorph g

中文:
定理 comp_homeomorph
  条件: {E'} [TopologicalSpace E'] (g : E' ≃ₜ E)
  结论: IsCoveringMap (f ∘ g)
  证明: by
  rw [isCoveringMap_iff_isCoveringMapOn_univ] at hf ⊢
  exact hf.comp_homeomorph g

Depends on / 依赖: comp_homeomorph, hf.comp_homeomorph, isCoveringMap_iff_isCoveringMapOn_univ
-/
theorem comp_homeomorph {E'} [TopologicalSpace E'] (g : E' ≃ₜ E) : IsCoveringMap (f ∘ g) := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ] at hf ⊢
  exact hf.comp_homeomorph g

/--
theorem `homeomorph_comp` / 定理 `homeomorph_comp`

English:
theorem homeomorph_comp
  given: {Y} [TopologicalSpace Y] (g : X ≃ₜ Y)
  statement: IsCoveringMap (g ∘ f)
  proof: by
  rw [isCoveringMap_iff_isCoveringMapOn_univ] at hf ⊢
  exact hf.homeomorph_comp g

omit hf

中文:
定理 homeomorph_comp
  条件: {Y} [TopologicalSpace Y] (g : X ≃ₜ Y)
  结论: IsCoveringMap (g ∘ f)
  证明: by
  rw [isCoveringMap_iff_isCoveringMapOn_univ] at hf ⊢
  exact hf.homeomorph_comp g

omit hf

Depends on / 依赖: hf.homeomorph_comp, homeomorph_comp, isCoveringMap_iff_isCoveringMapOn_univ
-/
theorem homeomorph_comp {Y} [TopologicalSpace Y] (g : X ≃ₜ Y) : IsCoveringMap (g ∘ f) := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ] at hf ⊢
  exact hf.homeomorph_comp g

omit hf

/--
theorem `comp_homeomorph_iff` / 定理 `comp_homeomorph_iff`

English:
theorem comp_homeomorph_iff
  given: {E'} [TopologicalSpace E'] (g : E' ≃ₜ E)
  proof: by convert! h.comp_homeomorph g.symm; ext; simp
  mpr h := h.comp_homeomorph g

中文:
定理 comp_homeomorph_iff
  条件: {E'} [TopologicalSpace E'] (g : E' ≃ₜ E)
  证明: by convert! h.comp_homeomorph g.symm; ext; simp
  mpr h := h.comp_homeomorph g

Depends on / 依赖: comp_homeomorph, convert, g.symm, h.comp_homeomorph
-/
theorem comp_homeomorph_iff {E'} [TopologicalSpace E'] (g : E' ≃ₜ E) :
    IsCoveringMap (f ∘ g) ↔ IsCoveringMap f where
  mp h := by convert! h.comp_homeomorph g.symm; ext; simp
  mpr h := h.comp_homeomorph g

/--
theorem `homeomorph_comp_iff` / 定理 `homeomorph_comp_iff`

English:
theorem homeomorph_comp_iff
  given: {Y} [TopologicalSpace Y] (g : X ≃ₜ Y)
  proof: by convert! h.homeomorph_comp g.symm; ext; simp
  mpr h := h.homeomorph_comp g

中文:
定理 homeomorph_comp_iff
  条件: {Y} [TopologicalSpace Y] (g : X ≃ₜ Y)
  证明: by convert! h.homeomorph_comp g.symm; ext; simp
  mpr h := h.homeomorph_comp g

Depends on / 依赖: convert, g.symm, h.homeomorph_comp, homeomorph_comp
-/
theorem homeomorph_comp_iff {Y} [TopologicalSpace Y] (g : X ≃ₜ Y) :
    IsCoveringMap (g ∘ f) ↔ IsCoveringMap f where
  mp h := by convert! h.homeomorph_comp g.symm; ext; simp
  mpr h := h.homeomorph_comp g

end IsCoveringMap

/--
theorem `IsCoveringMapOn.of_isCoveringMap_subtype` / 定理 `IsCoveringMapOn.of_isCoveringMap_subtype`

English:
theorem IsCoveringMapOn.of_isCoveringMap_subtype
  statement: {s : Set X} (hs : IsOpen s) {f : E -> X}
  proof: have eq : f ⁻¹' s = .univ := by simpa [Set.range, Set.subset_def] using h
of_isCoveringMap_restrictPreimage _ hs (by simp [eq])
    hf.comp_homeomorph ((Homeomorph.setCongr eq).trans (Homeomorph.Set.univ E))

中文:
定理 IsCoveringMapOn.of_isCoveringMap_subtype
  结论: {s : Set X} (hs : IsOpen s) {f : E -> X}
  证明: have eq : f ⁻¹' s = .univ := by simpa [Set.range, Set.subset_def] using h
of_isCoveringMap_restrictPreimage _ hs (by simp [eq])
    hf.comp_homeomorph ((Homeomorph.setCongr eq).trans (Homeomorph.Set.univ E))

Depends on / 依赖: Homeomorph, Homeomorph.Set.univ, Homeomorph.setCongr, Set.range, Set.subset_def, comp_homeomorph, hf.comp_homeomorph, of_isCoveringMap_restrictPreimage, setCongr, subset_def
-/
theorem IsCoveringMapOn.of_isCoveringMap_subtype {s : Set X} (hs : IsOpen s) {f : E -> X}
    (h : forall x, f x in s) (hf : IsCoveringMap fun x => (⟨f x, h x⟩ : s)) : IsCoveringMapOn f s :=
  have eq : f ⁻¹' s = .univ := by simpa [Set.range, Set.subset_def] using h
of_isCoveringMap_restrictPreimage _ hs (by simp [eq])
    hf.comp_homeomorph ((Homeomorph.setCongr eq).trans (Homeomorph.Set.univ E))

variable {f}

/--
theorem `IsFiberBundle.isCoveringMap` / 定理 `IsFiberBundle.isCoveringMap`

English:
theorem IsFiberBundle.isCoveringMap
  statement: {F : Type*} [TopologicalSpace F] [DiscreteTopology F]
  proof: IsCoveringMap.mk f (fun _ => F) (fun x => Classical.choose (hf x)) fun x =>
    Classical.choose_spec (hf x)

中文:
定理 IsFiberBundle.isCoveringMap
  结论: {F : 类型} [TopologicalSpace F] [DiscreteTopology F]
  证明: IsCoveringMap.mk f (fun _ => F) (fun x => Classical.choose (hf x)) fun x =>
    Classical.choose_spec (hf x)
-/
protected theorem IsFiberBundle.isCoveringMap {F : Type*} [TopologicalSpace F] [DiscreteTopology F]
    (hf : forall x : X, exists e : Trivialization F f, x in e.baseSet) : IsCoveringMap f :=
  IsCoveringMap.mk f (fun _ => F) (fun x => Classical.choose (hf x)) fun x =>
    Classical.choose_spec (hf x)

/--
theorem `FiberBundle.isCoveringMap` / 定理 `FiberBundle.isCoveringMap`

English:
theorem FiberBundle.isCoveringMap
  statement: {F : Type*} {E : X -> Type*} [TopologicalSpace F]
  proof: IsFiberBundle.isCoveringMap fun x => ⟨trivializationAt F E x, mem_baseSet_trivializationAt F E x⟩

中文:
定理 FiberBundle.isCoveringMap
  结论: {F : 类型} {E : X -> 类型} [TopologicalSpace F]
  证明: IsFiberBundle.isCoveringMap fun x => ⟨trivializationAt F E x, mem_baseSet_trivializationAt F E x⟩
-/
protected theorem FiberBundle.isCoveringMap {F : Type*} {E : X -> Type*} [TopologicalSpace F]
    [DiscreteTopology F] [TopologicalSpace (Bundle.TotalSpace F E)] [forall x, TopologicalSpace (E x)]
    [FiberBundle F E] : IsCoveringMap (π F E) :=
  IsFiberBundle.isCoveringMap fun x => ⟨trivializationAt F E x, mem_baseSet_trivializationAt F E x⟩

open Function in
/--
Definition of `IsOpen.trivializationDiscrete` / `IsOpen.trivializationDiscrete` 的定义

English:
definition IsOpen.trivializationDiscrete
  signature: [Nonempty (X -> E)]
  body: by
  have exhaustive' := exhaustive
  simp_rw [Set.subset_def, Set.mem_iUnion] at exhaustive
  choose idx idx_U using exhaustive
  choose inv inv_U f_inv using surj
  classical
  let F : PartialEquiv E (X × ι) :=
  { toFun e := (f e, if he : f e in V then idx e he else Classical.arbitrary ι),
    in

中文:
定义 IsOpen.trivializationDiscrete
  签名: [Nonempty (X -> E)]
  定义体: by
  have exhaustive' := exhaustive
  simp_rw [Set.subset_def, Set.mem_iUnion] at exhaustive
  choose idx idx_U using exhaustive
  choose inv inv_U f_inv using surj
  classical
  let F : PartialEquiv E (X × ι) :=
  { toFun e := (f e, if he : f e in V then idx e he else Classical.arbitrary ι),
    in
-/
@[simps source target baseSet] noncomputable def IsOpen.trivializationDiscrete [Nonempty (X -> E)]
    {ι} [Nonempty ι] [TopologicalSpace ι] [DiscreteTopology ι] (U : ι -> Set E) (V : Set X)
    (open_V : IsOpen V) (open_iff : forall i {W}, W subseteq V -> (IsOpen W ↔ IsOpen (f ⁻¹' W inter U i)))
    (inj : forall i, (U i).InjOn f) (surj : forall i, (U i).SurjOn f V)
    (disjoint : Pairwise (Disjoint on U)) (exhaustive : f ⁻¹' V subseteq ⋃ i, U i) :
    Trivialization ι f := by
  have exhaustive' := exhaustive
  simp_rw [Set.subset_def, Set.mem_iUnion] at exhaustive
  choose idx idx_U using exhaustive
  choose inv inv_U f_inv using surj
  classical
  let F : PartialEquiv E (X × ι) :=
  { toFun e := (f e, if he : f e in V then idx e he else Classical.arbitrary ι),
    invFun x := if hx : x.1 in V then inv x.2 hx else Classical.arbitrary (X -> E) x.1,
    source := f ⁻¹' V,
    target := V ×ˢ Set.univ,
    map_source' x hx := ⟨hx, ⟨⟩⟩
    map_target' x hx := by rw [dif_pos hx.1]; apply (f_inv _ hx.1).symm ▸ hx.1,
    left_inv' e he := by
      simp_rw [dif_pos (id he : f e in V)]
      exact inj _ (inv_U _ he) (idx_U e he) (f_inv _ _)
    right_inv' x hx := by
      rw [dif_pos hx.1]
      refine Prod.ext (f_inv _ hx.1) ?_
      rw [dif_pos ((f_inv _ hx.1).symm ▸ hx.1)]
      by_contra h; exact (disjoint h).le_bot ⟨idx_U .., inv_U _ _⟩ }
  have open_preim {W} (hWV : W subseteq V) (open_W : IsOpen W) : IsOpen (f ⁻¹' W) := by
    convert! isOpen_iUnion (fun i => (open_iff i hWV).mp open_W)
    rw [← Set.inter_iUnion]; rw [eq_comm]; rw [Set.inter_eq_left]
    exact (Set.preimage_mono hWV).trans exhaustive'
  have open_source : IsOpen F.source := open_preim subset_rfl open_V
  have cont_f : ContinuousOn f F.source := (continuousOn_open_iff open_source).mpr
    fun W open_W => open_preim Set.inter_subset_left (open_V.inter open_W)
  refine
  { toPartialEquiv := F,
    open_source := open_source,
    open_target := open_V.prod isOpen_univ,
continuousOn_toFun := cont_f.prodMk continuousOn_of_forall_continuousAt fun e he =>
.continuousAt.congr mem_nhds_iff.mpr continuous_const (y := idx e he)
        ⟨U (idx e he) inter F.source, fun e' he' => ?_, ?_, idx_U e he, he⟩
    continuousOn_invFun := continuousOn_prod_of_discrete_right.mpr fun i => ?_,
    baseSet := V,
    open_baseSet := open_V,
    source_eq := rfl,
    target_eq := rfl,
    proj_toFun _ _ := rfl }
  · by_contra h; apply (disjoint h).le_bot
    · dsimp only; rw [dif_pos (by exact he'.2)]; exact ⟨he'.1, idx_U ..⟩
  · rwa [Set.inter_comm, ← open_iff _ subset_rfl]
  · simp_rw [F, Set.prodMk_mem_set_prod_eq, Set.mem_univ, and_true]
    refine (continuousOn_open_iff open_V).mpr fun W open_W => ?_
    rw [open_iff i Set.inter_subset_left]
    convert! ((open_iff i subset_rfl).mp open_V).inter open_W using 1
    refine Set.ext fun e => and_right_comm.trans (and_congr_right fun ⟨hV, hU⟩ => ?_)
    rw [Set.mem_preimage]; rw [dif_pos hV]; rw [inj i (inv_U i _) hU (f_inv i _)]

variable {s}

variable (f) in
/--
theorem `IsDiscrete.of_openPartialHomeomorph` / 定理 `IsDiscrete.of_openPartialHomeomorph`

English:
theorem IsDiscrete.of_openPartialHomeomorph
  statement: {t : Set E} {x : X}
  proof: isDiscrete_iff_forall_mem_exists_isOpen.mpr fun e he => by
    obtain ⟨φ, hφ, rfl⟩ := hf e he
    exact ⟨_, φ.open_source, subset_antisymm (fun e' he' => φ.injOn he'.1 hφ <|
      (htx he'.2).trans (htx he).symm) <| Set.singleton_subset_iff.mpr ⟨hφ, he⟩⟩

中文:
定理 IsDiscrete.of_openPartialHomeomorph
  结论: {t : Set E} {x : X}
  证明: isDiscrete_iff_forall_mem_exists_isOpen.mpr fun e he => by
    obtain ⟨φ, hφ, rfl⟩ := hf e he
    exact ⟨_, φ.open_source, subset_antisymm (fun e' he' => φ.injOn he'.1 hφ <|
      (htx he'.2).trans (htx he).symm) <| Set.singleton_subset_iff.mpr ⟨hφ, he⟩⟩

Depends on / 依赖: Set.singleton_subset_iff.mpr, isDiscrete_iff_forall_mem_exists_isOpen, isDiscrete_iff_forall_mem_exists_isOpen.mpr, open_source, singleton_subset_iff, subset_antisymm
-/
theorem IsDiscrete.of_openPartialHomeomorph {t : Set E} {x : X}
    (htx : t subseteq f ⁻¹' {x}) (hf : forall e in t, exists φ : OpenPartialHomeomorph E X, e in φ.source ∧ φ = f) :
    IsDiscrete t :=
  isDiscrete_iff_forall_mem_exists_isOpen.mpr fun e he => by
    obtain ⟨φ, hφ, rfl⟩ := hf e he
    exact ⟨_, φ.open_source, subset_antisymm (fun e' he' => φ.injOn he'.1 hφ <|
      (htx he'.2).trans (htx he).symm) <| Set.singleton_subset_iff.mpr ⟨hφ, he⟩⟩

open Set in
/--
theorem `IsClosedMap.isEvenlyCovered_of_openPartialHomeomorph` / 定理 `IsClosedMap.isEvenlyCovered_of_openPartialHomeomorph`

English:
theorem IsClosedMap.isEvenlyCovered_of_openPartialHomeomorph
  statement: [T2Space E] {x : X}
  proof: by
  have : DiscreteTopology (f ⁻¹' {x}) :=
    (IsDiscrete.of_openPartialHomeomorph f subset_rfl h).1
  /- for each preimage e of x, choose a homeomorphism φₑ
    from a neighborhood of e to its image -/
  choose φ hφ using fun e : f ⁻¹' {x} => h e e.2
  -- separately, choose pairwise disjoint neig

中文:
定理 IsClosedMap.isEvenlyCovered_of_openPartialHomeomorph
  结论: [T2Space E] {x : X}
  证明: by
  have : DiscreteTopology (f ⁻¹' {x}) :=
    (IsDiscrete.of_openPartialHomeomorph f subset_rfl h).1
  /- for each preimage e of x, choose a homeomorphism φₑ
    from a neighborhood of e to its image -/
  choose φ hφ using fun e : f ⁻¹' {x} => h e e.2
  -- separately, choose pairwise disjoint neig

Depends on / 依赖: DiscreteTopology, IsDiscrete, IsDiscrete.of_openPartialHomeomorph, of_openPartialHomeomorph, subset_rfl
-/
theorem IsClosedMap.isEvenlyCovered_of_openPartialHomeomorph [T2Space E] {x : X}
    (hf : IsClosedMap f) (fin : (f ⁻¹' {x}).Finite)
    (h : forall e in f ⁻¹' {x}, exists φ : OpenPartialHomeomorph E X, e in φ.source ∧ φ = f) :
    IsEvenlyCovered f x (f ⁻¹' {x}) := by
  have : DiscreteTopology (f ⁻¹' {x}) :=
    (IsDiscrete.of_openPartialHomeomorph f subset_rfl h).1
  /- for each preimage e of x, choose a homeomorphism φₑ
    from a neighborhood of e to its image -/
  choose φ hφ using fun e : f ⁻¹' {x} => h e e.2
  -- separately, choose pairwise disjoint neighborhoods Vₑ by Hausdorff-ness
  have ⟨V, hV, disj⟩ := fin.t2_separation
  -- let Vₑ' be the intersection Vₑ ∩ dom(φₑ)
  let V' (e : f ⁻¹' {x}) := V e inter (φ e).source
  have hV' e : IsOpen (V' e) := (hV e).2.inter (φ e).open_source
  have : ⋃ e, V' e in nhdsSet (f ⁻¹' {x}) :=
    (isOpen_iUnion hV').mem_nhdsSet.2 fun e he => mem_iUnion_of_mem ⟨e, he⟩ ⟨(hV e).1, (hφ _).1⟩
  -- since f is a closed map, the union of the Vₑ' contains the preimage of a neighborhood U of x
  have ⟨W, hWx, hWV⟩ := isClosedMap_iff_comap_nhds_le.mp hf this
  cases isEmpty_or_nonempty (f ⁻¹' {x})
  · exact .of_preimage_eq_empty _ hWx (by simpa using hWV)
  have ⟨U, hUW, hU, hxU⟩ := mem_nhds_iff.mp hWx
  -- show that the intersection of U with the images of Vₑ' is evenly covered
  let U' := U inter ⋂ e : f ⁻¹' {x}, f '' (V' e)
  have : Finite (f ⁻¹' {x}) := fin
have hU' : IsOpen U' := hU.inter isOpen_iInter_of_finite fun e => by
    convert! ← (φ e).isOpen_image_of_subset_source (hV' _) inter_subset_right; exact (hφ e).2
  have hUV e : U' subseteq f '' V' e := inter_subset_right.trans (iInter_subset ..)
  have : Nonempty E := ⟨Classical.arbitrary (f ⁻¹' {x})⟩
  refine .of_trivialization (t := hU'.trivializationDiscrete _ _
    (fun e s hs => ⟨fun h => ?_, fun h => ?_⟩) (fun e => ?_)
    (fun e => .mono subset_rfl (hUV e) (surjOn_image f _))
    (pairwise_disjoint_mono disj.subtype fun e => inter_subset_left)
    ((preimage_mono (inter_subset_left.trans hUW)).trans hWV))
    ⟨hxU, Set.mem_iInter.mpr fun e => ⟨e, ⟨(hV e).1, (hφ e).1⟩, e.2⟩⟩
  · convert! ((φ e).isOpen_inter_preimage h).inter (hV e).2 using 1
    simp_rw [(hφ e).2, V']; ac_rfl
· have : s subseteq (φ e).target := hs.trans (hUV e).trans by
      rw [← (φ e).image_source_eq_target]; rw [(hφ e).2]; exact image_mono inter_subset_right
    rw [← (φ e).isOpen_symm_image_iff_of_subset_target this]; rw [(φ e).symm_image_eq_source_inter_preimage this]; rw [(hφ e).2]; rw [inter_comm]
    convert! h using 1
    refine inter_eq_inter_iff_left.mpr ⟨fun e' h => h.2.2, fun e' h => ⟨?_ , h.2⟩⟩
    have ⟨e'', ⟨_, mem⟩, eq⟩ := mem_iInter.mp (hs h.1).2 e
    rwa [← (φ e).injOn mem h.2 (by rwa [(hφ e).2])]
  · convert! ← (φ e).injOn.mono inter_subset_right; exact (hφ e).2

/--
theorem `IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn` / 定理 `IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn`

English:
theorem IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
  statement: [T2Space E]
  proof: by
  intro x hx
  refine hf.isEvenlyCovered_of_openPartialHomeomorph (hs x hx) fun e he => ?_
  obtain ⟨φ, hφ, rfl⟩ := h e (by aesop)
  aesop

@[deprecated (since := "2026-06-25")]
alias IsClosedMap.isCoveringMapOn_of_openPartialHomeomorph :=
  IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn

中文:
定理 IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
  结论: [T2Space E]
  证明: by
  intro x hx
  refine hf.isEvenlyCovered_of_openPartialHomeomorph (hs x hx) fun e he => ?_
  obtain ⟨φ, hφ, rfl⟩ := h e (by aesop)
  aesop

@[deprecated (since := "2026-06-25")]
alias IsClosedMap.isCoveringMapOn_of_openPartialHomeomorph :=
  IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn

Depends on / 依赖: hf.isEvenlyCovered_of_openPartialHomeomorph, isEvenlyCovered_of_openPartialHomeomorph
-/
theorem IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn [T2Space E]
    (hf : IsClosedMap f) (hs : forall x in s, (f ⁻¹' {x}).Finite)
    (h : IsLocalHomeomorphOn f (f ⁻¹' s)) :
    IsCoveringMapOn f s := by
  intro x hx
  refine hf.isEvenlyCovered_of_openPartialHomeomorph (hs x hx) fun e he => ?_
  obtain ⟨φ, hφ, rfl⟩ := h e (by aesop)
  aesop

@[deprecated (since := "2026-06-25")]
alias IsClosedMap.isCoveringMapOn_of_openPartialHomeomorph :=
  IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn

/--
theorem `IsEvenlyCovered.of_openPartialHomeomorph` / 定理 `IsEvenlyCovered.of_openPartialHomeomorph`

English:
theorem IsEvenlyCovered.of_openPartialHomeomorph
  proof: hf.isClosedMap.isEvenlyCovered_of_openPartialHomeomorph
    ((isClosed_singleton.preimage hf).isCompact.finite (.of_openPartialHomeomorph f subset_rfl h)) h

中文:
定理 IsEvenlyCovered.of_openPartialHomeomorph
  证明: hf.isClosedMap.isEvenlyCovered_of_openPartialHomeomorph
    ((isClosed_singleton.preimage hf).isCompact.finite (.of_openPartialHomeomorph f subset_rfl h)) h

Depends on / 依赖: finite, hf.isClosedMap.isEvenlyCovered_of_openPartialHomeomorph, isClosedMap, isClosed_singleton, isClosed_singleton.preimage, isCompact, isCompact.finite, isEvenlyCovered_of_openPartialHomeomorph, of_openPartialHomeomorph, preimage, subset_rfl
-/
theorem IsEvenlyCovered.of_openPartialHomeomorph
    [T2Space E] [T2Space X] [CompactSpace E] {x : X} (hf : Continuous f)
    (h : forall e in f ⁻¹' {x}, exists φ : OpenPartialHomeomorph E X, e in φ.source ∧ φ = f) :
    IsEvenlyCovered f x (f ⁻¹' {x}) :=
  hf.isClosedMap.isEvenlyCovered_of_openPartialHomeomorph
    ((isClosed_singleton.preimage hf).isCompact.finite (.of_openPartialHomeomorph f subset_rfl h)) h

/--
theorem `IsCoveringMapOn.of_isLocalHomeomorphOn` / 定理 `IsCoveringMapOn.of_isLocalHomeomorphOn`

English:
theorem IsCoveringMapOn.of_isLocalHomeomorphOn
  proof: by
  intro x hx
  refine .of_openPartialHomeomorph hf fun e he => ?_
  obtain ⟨φ, hφ, rfl⟩ := h e (by aesop)
  aesop

@[deprecated (since := "2026-06-25")]
alias IsCoveringMapOn.of_openPartialHomeomorph := IsCoveringMapOn.of_isLocalHomeomorphOn

@[simp]

中文:
定理 IsCoveringMapOn.of_isLocalHomeomorphOn
  证明: by
  intro x hx
  refine .of_openPartialHomeomorph hf fun e he => ?_
  obtain ⟨φ, hφ, rfl⟩ := h e (by aesop)
  aesop

@[deprecated (since := "2026-06-25")]
alias IsCoveringMapOn.of_openPartialHomeomorph := IsCoveringMapOn.of_isLocalHomeomorphOn

@[simp]

Depends on / 依赖: of_openPartialHomeomorph
-/
theorem IsCoveringMapOn.of_isLocalHomeomorphOn
    [T2Space E] [T2Space X] [CompactSpace E] (hf : Continuous f)
    (h : IsLocalHomeomorphOn f (f ⁻¹' s)) :
    IsCoveringMapOn f s := by
  intro x hx
  refine .of_openPartialHomeomorph hf fun e he => ?_
  obtain ⟨φ, hφ, rfl⟩ := h e (by aesop)
  aesop

@[deprecated (since := "2026-06-25")]
alias IsCoveringMapOn.of_openPartialHomeomorph := IsCoveringMapOn.of_isLocalHomeomorphOn

@[simp]
/--
lemma `isLocalHomeomorph_iff_isCoveringMap` / 引理 `isLocalHomeomorph_iff_isCoveringMap`

English:
lemma isLocalHomeomorph_iff_isCoveringMap
  given: [T2Space E] [T2Space X] [CompactSpace E]
  proof: by
  refine ⟨fun h => ?_, IsCoveringMap.isLocalHomeomorph⟩
  have hf : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro e
    obtain ⟨φ, hφ, rfl⟩ := h e
    exact φ.continuousAt hφ
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  apply IsCoveringMapOn.of_isLocalHomeomorphOn hf
  simp

中文:
引理 isLocalHomeomorph_iff_isCoveringMap
  条件: [T2Space E] [T2Space X] [CompactSpace E]
  证明: by
  refine ⟨fun h => ?_, IsCoveringMap.isLocalHomeomorph⟩
  have hf : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro e
    obtain ⟨φ, hφ, rfl⟩ := h e
    exact φ.continuousAt hφ
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  apply IsCoveringMapOn.of_isLocalHomeomorphOn hf
  simp

Depends on / 依赖: Continuous, IsCoveringMap, IsCoveringMap.isLocalHomeomorph, IsCoveringMapOn, IsCoveringMapOn.of_isLocalHomeomorphOn, continuousAt, continuous_iff_continuousAt, isCoveringMap_iff_isCoveringMapOn_univ, isLocalHomeomorph, isLocalHomeomorph_iff_isLocalHomeomorphOn_univ, of_isLocalHomeomorphOn
-/
lemma isLocalHomeomorph_iff_isCoveringMap [T2Space E] [T2Space X] [CompactSpace E] :
    IsLocalHomeomorph f ↔ IsCoveringMap f := by
  refine ⟨fun h => ?_, IsCoveringMap.isLocalHomeomorph⟩
  have hf : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro e
    obtain ⟨φ, hφ, rfl⟩ := h e
    exact φ.continuousAt hφ
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  apply IsCoveringMapOn.of_isLocalHomeomorphOn hf
  simpa [← isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
