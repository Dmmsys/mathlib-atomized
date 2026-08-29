/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Maps.Basic

/-!
# Open quotient maps

An open quotient map is an open map `f : X → Y` which is both an open map and a quotient map.
Equivalently, it is a surjective continuous open map.
We use the latter characterization as a definition.

Many important quotient maps are open quotient maps, including

- the quotient map from a topological space to its quotient by the action of a group;
- the quotient map from a topological group to its quotient by a normal subgroup;
- the quotient map from a topological space to its separation quotient.

Contrary to general quotient maps,
the category of open quotient maps is closed under `Prod.map`.
-/

public section

open Filter Function Set Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {f : X -> Y}

namespace IsOpenQuotientMap

/--
theorem `id` / 定理 `id`

English:
theorem id
  statement: IsOpenQuotientMap (id : X -> X)
  proof: ⟨surjective_id, continuous_id, .id⟩

中文:
定理 id
  结论: 是OpenQuotient映射 (id : X -> X)
  证明: ⟨surjective_id, continuous_id, .id⟩
-/
protected theorem id : IsOpenQuotientMap (id : X -> X) := ⟨surjective_id, continuous_id, .id⟩

/--
theorem `isQuotientMap` / 定理 `isQuotientMap`

English:
theorem isQuotientMap
  given: (h : IsOpenQuotientMap f)
  statement: IsQuotientMap f
  proof: h.isOpenMap.isQuotientMap h.continuous h.surjective

中文:
定理 isQuotientMap
  条件: (h : 是OpenQuotient映射 f)
  结论: 是商映射 f
  证明: h.isOpenMap.isQuotientMap h.continuous h.surjective

Depends on / 依赖: continuous, h.continuous, h.isOpenMap.isQuotientMap, h.surjective, isOpenMap, isQuotientMap, surjective
-/
theorem isQuotientMap (h : IsOpenQuotientMap f) : IsQuotientMap f :=
  h.isOpenMap.isQuotientMap h.continuous h.surjective

/--
theorem `iff_isOpenMap_isQuotientMap` / 定理 `iff_isOpenMap_isQuotientMap`

English:
theorem iff_isOpenMap_isQuotientMap
  statement: IsOpenQuotientMap f ↔ IsOpenMap f ∧ IsQuotientMap f
  proof: ⟨fun h => ⟨h.isOpenMap, h.isQuotientMap⟩, fun ⟨ho, hq⟩ => ⟨hq.surjective, hq.continuous, ho⟩⟩

中文:
定理 iff_isOpenMap_isQuotientMap
  结论: 是OpenQuotient映射 f ↔ 是开映射 f ∧ 是商映射 f
  证明: ⟨fun h => ⟨h.isOpenMap, h.isQuotientMap⟩, fun ⟨ho, hq⟩ => ⟨hq.surjective, hq.continuous, ho⟩⟩

Depends on / 依赖: continuous, h.isOpenMap, h.isQuotientMap, hq.continuous, hq.surjective, isOpenMap, isQuotientMap, surjective
-/
theorem iff_isOpenMap_isQuotientMap : IsOpenQuotientMap f ↔ IsOpenMap f ∧ IsQuotientMap f :=
  ⟨fun h => ⟨h.isOpenMap, h.isQuotientMap⟩, fun ⟨ho, hq⟩ => ⟨hq.surjective, hq.continuous, ho⟩⟩

/--
theorem `of_isOpenMap_isQuotientMap` / 定理 `of_isOpenMap_isQuotientMap`

English:
theorem of_isOpenMap_isQuotientMap
  given: (ho : IsOpenMap f) (hq : IsQuotientMap f)
  proof: iff_isOpenMap_isQuotientMap.2 ⟨ho, hq⟩

中文:
定理 of_isOpenMap_isQuotientMap
  条件: (ho : 是开映射 f) (hq : 是商映射 f)
  证明: iff_isOpenMap_isQuotientMap.2 ⟨ho, hq⟩

Depends on / 依赖: iff_isOpenMap_isQuotientMap
-/
theorem of_isOpenMap_isQuotientMap (ho : IsOpenMap f) (hq : IsQuotientMap f) :
    IsOpenQuotientMap f :=
  iff_isOpenMap_isQuotientMap.2 ⟨ho, hq⟩

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: {g : Y -> Z} (hg : IsOpenQuotientMap g) (hf : IsOpenQuotientMap f)
  proof: ⟨.comp hg.1 hf.1, .comp hg.2 hf.2, .comp hg.3 hf.3⟩

中文:
定理 comp
  条件: {g : Y -> Z} (hg : 是OpenQuotient映射 g) (hf : 是OpenQuotient映射 f)
  证明: ⟨.comp hg.1 hf.1, .comp hg.2 hf.2, .comp hg.3 hf.3⟩
-/
theorem comp {g : Y -> Z} (hg : IsOpenQuotientMap g) (hf : IsOpenQuotientMap f) :
    IsOpenQuotientMap (g ∘ f) :=
  ⟨.comp hg.1 hf.1, .comp hg.2 hf.2, .comp hg.3 hf.3⟩

/--
theorem `of_comp` / 定理 `of_comp`

English:
theorem of_comp
  statement: {g : Y -> Z} (hf : Continuous f) (f_surj : Surjective f) (hg : Continuous g)
  proof: ⟨.of_comp h.surjective, hg, .of_comp hf f_surj h.isOpenMap ⟩

中文:
定理 of_comp
  结论: {g : Y -> Z} (hf : 连续 f) (f_surj : 满射 f) (hg : 连续 g)
  证明: ⟨.of_comp h.surjective, hg, .of_comp hf f_surj h.isOpenMap ⟩

Depends on / 依赖: f_surj, h.isOpenMap, h.surjective, isOpenMap, of_comp, surjective
-/
theorem of_comp {g : Y -> Z} (hf : Continuous f) (f_surj : Surjective f) (hg : Continuous g)
    (h : IsOpenQuotientMap (g ∘ f)) : IsOpenQuotientMap g :=
  ⟨.of_comp h.surjective, hg, .of_comp hf f_surj h.isOpenMap ⟩

/--
theorem `of_comp_iff` / 定理 `of_comp_iff`

English:
theorem of_comp_iff
  given: {g : Y -> Z} (hf : IsOpenQuotientMap f)
  proof: ⟨fun h => .of_comp hf.continuous hf.surjective
    (hf.isQuotientMap.continuous_iff.mpr h.continuous) h, fun hg => hg.comp hf⟩

中文:
定理 of_comp_iff
  条件: {g : Y -> Z} (hf : 是OpenQuotient映射 f)
  证明: ⟨fun h => .of_comp hf.continuous hf.surjective
    (hf.isQuotientMap.continuous_iff.mpr h.continuous) h, fun hg => hg.comp hf⟩

Depends on / 依赖: continuous, continuous_iff, h.continuous, hf.continuous, hf.isQuotientMap.continuous_iff.mpr, hf.surjective, hg.comp, isQuotientMap, of_comp, surjective
-/
theorem of_comp_iff {g : Y -> Z} (hf : IsOpenQuotientMap f) :
    IsOpenQuotientMap (g ∘ f) ↔ IsOpenQuotientMap g :=
  ⟨fun h => .of_comp hf.continuous hf.surjective
    (hf.isQuotientMap.continuous_iff.mpr h.continuous) h, fun hg => hg.comp hf⟩

/--
theorem `map_nhds_eq` / 定理 `map_nhds_eq`

English:
theorem map_nhds_eq
  given: (h : IsOpenQuotientMap f) (x : X)
  statement: map f (𝓝 x) = 𝓝 (f x)
  proof: le_antisymm h.continuous.continuousAt h.isOpenMap.nhds_le _

中文:
定理 map_nhds_eq
  条件: (h : 是OpenQuotient映射 f) (x : X)
  结论: map f (𝓝 x) = 𝓝 (f x)
  证明: le_antisymm h.continuous.continuousAt h.isOpenMap.nhds_le _

Depends on / 依赖: continuous, continuousAt, h.continuous.continuousAt, h.isOpenMap.nhds_le, isOpenMap, le_antisymm, nhds_le
-/
theorem map_nhds_eq (h : IsOpenQuotientMap f) (x : X) : map f (𝓝 x) = 𝓝 (f x) :=
le_antisymm h.continuous.continuousAt h.isOpenMap.nhds_le _

/--
theorem `continuous_comp_iff` / 定理 `continuous_comp_iff`

English:
theorem continuous_comp_iff
  given: (h : IsOpenQuotientMap f) {g : Y -> Z}
  proof: h.isQuotientMap.continuous_iff.symm

中文:
定理 continuous_comp_iff
  条件: (h : 是OpenQuotient映射 f) {g : Y -> Z}
  证明: h.isQuotientMap.continuous_iff.symm

Depends on / 依赖: continuous_iff, h.isQuotientMap.continuous_iff.symm, isQuotientMap
-/
theorem continuous_comp_iff (h : IsOpenQuotientMap f) {g : Y -> Z} :
    Continuous (g ∘ f) ↔ Continuous g :=
  h.isQuotientMap.continuous_iff.symm

/--
theorem `continuousAt_comp_iff` / 定理 `continuousAt_comp_iff`

English:
theorem continuousAt_comp_iff
  given: (h : IsOpenQuotientMap f) {g : Y -> Z} {x : X}
  proof: by
  simp only [ContinuousAt, ← h.map_nhds_eq, tendsto_map'_iff, comp_def]

中文:
定理 continuousAt_comp_iff
  条件: (h : 是OpenQuotient映射 f) {g : Y -> Z} {x : X}
  证明: by
  simp only [ContinuousAt, ← h.map_nhds_eq, tendsto_map'_iff, comp_def]

Depends on / 依赖: ContinuousAt, _iff, comp_def, h.map_nhds_eq, map_nhds_eq, tendsto_map
-/
theorem continuousAt_comp_iff (h : IsOpenQuotientMap f) {g : Y -> Z} {x : X} :
    ContinuousAt (g ∘ f) x ↔ ContinuousAt g (f x) := by
  simp only [ContinuousAt, ← h.map_nhds_eq, tendsto_map'_iff, comp_def]

/--
theorem `isOpenMap_iff` / 定理 `isOpenMap_iff`

English:
theorem isOpenMap_iff
  given: (hf : IsOpenQuotientMap f) {g : Y -> Z}
  proof: ⟨fun hg => hg.comp hf.isOpenMap, fun h => .of_comp hf.continuous hf.surjective h⟩

中文:
定理 isOpenMap_iff
  条件: (hf : 是OpenQuotient映射 f) {g : Y -> Z}
  证明: ⟨fun hg => hg.comp hf.isOpenMap, fun h => .of_comp hf.continuous hf.surjective h⟩

Depends on / 依赖: continuous, hf.continuous, hf.isOpenMap, hf.surjective, hg.comp, isOpenMap, of_comp, surjective
-/
theorem isOpenMap_iff (hf : IsOpenQuotientMap f) {g : Y -> Z} :
    IsOpenMap g ↔ IsOpenMap (g ∘ f) :=
  ⟨fun hg => hg.comp hf.isOpenMap, fun h => .of_comp hf.continuous hf.surjective h⟩

/--
theorem `dense_preimage_iff` / 定理 `dense_preimage_iff`

English:
theorem dense_preimage_iff
  given: (h : IsOpenQuotientMap f) {s : Set Y}
  statement: Dense (f ⁻¹' s) ↔ Dense s
  proof: ⟨fun hs => h.surjective.denseRange.dense_of_mapsTo h.continuous hs (mapsTo_preimage _ _),
    fun hs => hs.preimage h.isOpenMap⟩

中文:
定理 dense_preimage_iff
  条件: (h : 是OpenQuotient映射 f) {s : 集合 Y}
  结论: 稠密 (f ⁻¹' s) ↔ 稠密 s
  证明: ⟨fun hs => h.surjective.denseRange.dense_of_mapsTo h.continuous hs (mapsTo_preimage _ _),
    fun hs => hs.preimage h.isOpenMap⟩

Depends on / 依赖: continuous, denseRange, dense_of_mapsTo, h.continuous, h.isOpenMap, h.surjective.denseRange.dense_of_mapsTo, hs.preimage, isOpenMap, mapsTo_preimage, preimage, surjective
-/
theorem dense_preimage_iff (h : IsOpenQuotientMap f) {s : Set Y} : Dense (f ⁻¹' s) ↔ Dense s :=
  ⟨fun hs => h.surjective.denseRange.dense_of_mapsTo h.continuous hs (mapsTo_preimage _ _),
    fun hs => hs.preimage h.isOpenMap⟩

end IsOpenQuotientMap

/--
theorem `Topology.IsInducing.isOpenQuotientMap_of_surjective` / 定理 `Topology.IsInducing.isOpenQuotientMap_of_surjective`

English:
theorem Topology.IsInducing.isOpenQuotientMap_of_surjective
  statement: (ind : IsInducing f)
  proof: surj
  continuous := ind.continuous
  isOpenMap U U_open := by
    obtain ⟨V, hV, rfl⟩ := ind.isOpen_iff.mp U_open
    rwa [V.image_preimage_eq surj]

中文:
定理 拓扑.是Inducing.isOpenQuotientMap_of_surjective
  结论: (ind : 是Inducing f)
  证明: surj
  continuous := ind.continuous
  isOpenMap U U_open := by
    obtain ⟨V, hV, rfl⟩ := ind.isOpen_iff.mp U_open
    rwa [V.image_preimage_eq surj]
-/
theorem Topology.IsInducing.isOpenQuotientMap_of_surjective (ind : IsInducing f)
    (surj : Function.Surjective f) : IsOpenQuotientMap f where
  surjective := surj
  continuous := ind.continuous
  isOpenMap U U_open := by
    obtain ⟨V, hV, rfl⟩ := ind.isOpen_iff.mp U_open
    rwa [V.image_preimage_eq surj]

/--
theorem `Topology.IsInducing.isQuotientMap_of_surjective` / 定理 `Topology.IsInducing.isQuotientMap_of_surjective`

English:
theorem Topology.IsInducing.isQuotientMap_of_surjective
  statement: (ind : IsInducing f)
  proof: (ind.isOpenQuotientMap_of_surjective surj).isQuotientMap

中文:
定理 拓扑.是Inducing.isQuotientMap_of_surjective
  结论: (ind : 是Inducing f)
  证明: (ind.isOpenQuotientMap_of_surjective surj).isQuotientMap

Depends on / 依赖: ind.isOpenQuotientMap_of_surjective, isOpenQuotientMap_of_surjective, isQuotientMap
-/
theorem Topology.IsInducing.isQuotientMap_of_surjective (ind : IsInducing f)
    (surj : Function.Surjective f) : IsQuotientMap f :=
  (ind.isOpenQuotientMap_of_surjective surj).isQuotientMap

section Subquotient

variable {A B C D : Type*}
variable [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
variable (f : A -> B) (g : C -> D) (p : A -> C) (q : B -> D)

omit [TopologicalSpace C] in
/--
lemma `coinduced_eq_induced_of_isOpenQuotientMap_of_isInducing` / 引理 `coinduced_eq_induced_of_isOpenQuotientMap_of_isInducing`

English:
lemma coinduced_eq_induced_of_isOpenQuotientMap_of_isInducing
  proof: by
  ext U
  change IsOpen (p ⁻¹' U) ↔ exists V, _
  simp_rw [hf.isOpen_iff,
    (Set.image_surjective.mpr hq.surjective).exists,
    ← hq.isQuotientMap.isOpen_preimage]
  constructor
  · rintro ⟨V, hV, e⟩
    refine ⟨V, hq.continuous.1 _ (hq.isOpenMap _ hV), ?_⟩
    ext x
    obtain ⟨x, rfl⟩ := hp 

中文:
引理 coinduced_eq_induced_of_isOpenQuotientMap_of_isInducing
  证明: by
  ext U
  change IsOpen (p ⁻¹' U) ↔ exists V, _
  simp_rw [hf.isOpen_iff,
    (Set.image_surjective.mpr hq.surjective).exists,
    ← hq.isQuotientMap.isOpen_preimage]
  constructor
  · rintro ⟨V, hV, e⟩
    refine ⟨V, hq.continuous.1 _ (hq.isOpenMap _ hV), ?_⟩
    ext x
    obtain ⟨x, rfl⟩ := hp 

Depends on / 依赖: IsOpen, Set.image_surjective.mpr, congr_fun, continuous, e.ge, e.le, h.symm, hf.isOpen_iff, hq.continuous, hq.isOpenMap, hq.isQuotientMap.isOpen_preimage, hq.surjective, image_surjective, isOpenMap, isOpen_iff, isOpen_preimage, isQuotientMap, simp_rw, surjective
-/
lemma coinduced_eq_induced_of_isOpenQuotientMap_of_isInducing
    (h : g ∘ p = q ∘ f)
    (hf : IsInducing f) (hp : Function.Surjective p)
    (hq : IsOpenQuotientMap q) (hg : Function.Injective g)
    (H : q ⁻¹' q '' Set.range f subseteq Set.range f) :
    ‹TopologicalSpace A›.coinduced p = ‹TopologicalSpace D›.induced g := by
  ext U
  change IsOpen (p ⁻¹' U) ↔ exists V, _
  simp_rw [hf.isOpen_iff,
    (Set.image_surjective.mpr hq.surjective).exists,
    ← hq.isQuotientMap.isOpen_preimage]
  constructor
  · rintro ⟨V, hV, e⟩
    refine ⟨V, hq.continuous.1 _ (hq.isOpenMap _ hV), ?_⟩
    ext x
    obtain ⟨x, rfl⟩ := hp x
    constructor
    · rintro ⟨y, hy, e'⟩
      obtain ⟨y, rfl⟩ := H ⟨_, ⟨x, rfl⟩, (e'.trans (congr_fun h x)).symm⟩
      rw [← hg ((congr_fun h y).trans e')]
      exact e.le hy
    · intro H
      exact ⟨f x, e.ge H, congr_fun h.symm x⟩
  · rintro ⟨V, hV, rfl⟩
    refine ⟨_, hV, ?_⟩
    simp_rw [← Set.preimage_comp, h]

/--
lemma `isEmbedding_of_isOpenQuotientMap_of_isInducing` / 引理 `isEmbedding_of_isOpenQuotientMap_of_isInducing`

English:
lemma isEmbedding_of_isOpenQuotientMap_of_isInducing
  proof: ⟨⟨hp.eq_coinduced.trans (coinduced_eq_induced_of_isOpenQuotientMap_of_isInducing
    f g p q h hf hp.surjective hq hg H)⟩, hg⟩

中文:
引理 isEmbedding_of_isOpenQuotientMap_of_isInducing
  证明: ⟨⟨hp.eq_coinduced.trans (coinduced_eq_induced_of_isOpenQuotientMap_of_isInducing
    f g p q h hf hp.surjective hq hg H)⟩, hg⟩

Depends on / 依赖: coinduced_eq_induced_of_isOpenQuotientMap_of_isInducing, eq_coinduced, hp.eq_coinduced.trans, hp.surjective, surjective
-/
lemma isEmbedding_of_isOpenQuotientMap_of_isInducing
    (h : g ∘ p = q ∘ f)
    (hf : IsInducing f) (hp : IsQuotientMap p)
    (hq : IsOpenQuotientMap q) (hg : Function.Injective g)
    (H : q ⁻¹' q '' Set.range f subseteq Set.range f) :
    IsEmbedding g :=
  ⟨⟨hp.eq_coinduced.trans (coinduced_eq_induced_of_isOpenQuotientMap_of_isInducing
    f g p q h hf hp.surjective hq hg H)⟩, hg⟩

/--
lemma `isQuotientMap_of_isOpenQuotientMap_of_isInducing` / 引理 `isQuotientMap_of_isOpenQuotientMap_of_isInducing`

English:
lemma isQuotientMap_of_isOpenQuotientMap_of_isInducing
  proof: ⟨⟨hg.eq_induced.trans ((coinduced_eq_induced_of_isOpenQuotientMap_of_isInducing
    f g p q h hf hp hq hg.injective H)).symm⟩, hp⟩

中文:
引理 isQuotientMap_of_isOpenQuotientMap_of_isInducing
  证明: ⟨⟨hg.eq_induced.trans ((coinduced_eq_induced_of_isOpenQuotientMap_of_isInducing
    f g p q h hf hp hq hg.injective H)).symm⟩, hp⟩

Depends on / 依赖: coinduced_eq_induced_of_isOpenQuotientMap_of_isInducing, eq_induced, hg.eq_induced.trans, hg.injective, injective
-/
lemma isQuotientMap_of_isOpenQuotientMap_of_isInducing
    (h : g ∘ p = q ∘ f)
    (hf : IsInducing f) (hp : Surjective p)
    (hq : IsOpenQuotientMap q) (hg : IsEmbedding g)
    (H : q ⁻¹' q '' Set.range f subseteq Set.range f) :
    IsQuotientMap p :=
  ⟨⟨hg.eq_induced.trans ((coinduced_eq_induced_of_isOpenQuotientMap_of_isInducing
    f g p q h hf hp hq hg.injective H)).symm⟩, hp⟩

end Subquotient
