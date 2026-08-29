/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Topology.Order
public import Mathlib.Topology.NhdsSet

/-!
# Specific classes of maps between topological spaces

This file introduces the following properties of a map `f : X → Y` between topological spaces:

* `IsOpenMap f` means the image of an open set under `f` is open.
* `IsClosedMap f` means the image of a closed set under `f` is closed.

(Open and closed maps need not be continuous.)

* `IsInducing f` means the topology on `X` is the one induced via `f` from the topology on `Y`.
  These behave like embeddings except they need not be injective. Instead, points of `X` which
  are identified by `f` are also inseparable in the topology on `X`.
* `IsCoinducing f` means the topology on `Y` is the one coinduced via `f` from the topology on `X`.
* `IsEmbedding f` means `f` is inducing and also injective. Equivalently, `f` identifies `X` with
  a subspace of `Y`.
* `IsOpenEmbedding f` means `f` is an embedding with open image, so it identifies `X` with an
  open subspace of `Y`. Equivalently, `f` is an embedding and an open map.
* `IsClosedEmbedding f` similarly means `f` is an embedding with closed image, so it identifies
  `X` with a closed subspace of `Y`. Equivalently, `f` is an embedding and a closed map.

* `IsQuotientMap f` is the dual condition to `IsEmbedding f`: `f` is surjective and the topology
  on `Y` is the one coinduced via `f` from the topology on `X`. Equivalently, `f` identifies
  `Y` with a quotient of `X`. Quotient maps are also sometimes known as identification maps.

## References

* <https://en.wikipedia.org/wiki/Open_and_closed_maps>
* <https://en.wikipedia.org/wiki/Embedding#General_topology>
* <https://en.wikipedia.org/wiki/Quotient_space_(topology)#Quotient_map>

## Tags

open map, closed map, embedding, quotient map, identification map

-/

public section


open Set Filter Function

open TopologicalSpace Topology Filter

variable {X : Type*} {Y : Type*} {Z : Type*} {ι : Type*} {f : X -> Y} {g : Y -> Z}

namespace Topology
section IsInducing

variable [TopologicalSpace Y]

/--
lemma `IsInducing.induced` / 引理 `IsInducing.induced`

English:
lemma IsInducing.induced
  given: (f : X -> Y)
  statement: @IsInducing X Y (induced f ‹_›) _ f
  proof: @IsInducing.mk _ _ (TopologicalSpace.induced f ‹_›) _ _ rfl

中文:
引理 是Inducing.induced
  条件: (f : X -> Y)
  结论: @是Inducing X Y (induced f ‹_›) _ f
  证明: @IsInducing.mk _ _ (TopologicalSpace.induced f ‹_›) _ _ rfl
-/
protected lemma IsInducing.induced (f : X -> Y) : @IsInducing X Y (induced f ‹_›) _ f :=
  @IsInducing.mk _ _ (TopologicalSpace.induced f ‹_›) _ _ rfl

variable [TopologicalSpace X]

@[fun_prop]
/--
lemma `IsInducing.id` / 引理 `IsInducing.id`

English:
lemma IsInducing.id
  statement: IsInducing (@id X)
  proof: ⟨induced_id.symm⟩

中文:
引理 是Inducing.id
  结论: 是Inducing (@id X)
  证明: ⟨induced_id.symm⟩
-/
protected lemma IsInducing.id : IsInducing (@id X) := ⟨induced_id.symm⟩

variable [TopologicalSpace Z]

@[fun_prop]
/--
lemma `IsInducing.comp` / 引理 `IsInducing.comp`

English:
lemma IsInducing.comp
  given: (hg : IsInducing g) (hf : IsInducing f)
  proof: ⟨by rw [hf.eq_induced, hg.eq_induced, induced_compose]⟩

中文:
引理 是Inducing.comp
  条件: (hg : 是Inducing g) (hf : 是Inducing f)
  证明: ⟨by rw [hf.eq_induced, hg.eq_induced, induced_compose]⟩
-/
protected lemma IsInducing.comp (hg : IsInducing g) (hf : IsInducing f) :
    IsInducing (g ∘ f) :=
  ⟨by rw [hf.eq_induced, hg.eq_induced, induced_compose]⟩

/--
lemma `IsInducing.of_comp_iff` / 引理 `IsInducing.of_comp_iff`

English:
lemma IsInducing.of_comp_iff
  given: (hg : IsInducing g)
  statement: IsInducing (g ∘ f) ↔ IsInducing f
  proof: by
  refine ⟨fun h => ?_, hg.comp⟩
  rw [isInducing_iff]; rw [hg.eq_induced]; rw [induced_compose]; rw [h.eq_induced]

中文:
引理 是Inducing.of_comp_iff
  条件: (hg : 是Inducing g)
  结论: 是Inducing (g ∘ f) ↔ 是Inducing f
  证明: by
  refine ⟨fun h => ?_, hg.comp⟩
  rw [isInducing_iff]; rw [hg.eq_induced]; rw [induced_compose]; rw [h.eq_induced]

Depends on / 依赖: eq_induced, h.eq_induced, hg.comp, hg.eq_induced, induced_compose, isInducing_iff
-/
lemma IsInducing.of_comp_iff (hg : IsInducing g) : IsInducing (g ∘ f) ↔ IsInducing f := by
  refine ⟨fun h => ?_, hg.comp⟩
  rw [isInducing_iff]; rw [hg.eq_induced]; rw [induced_compose]; rw [h.eq_induced]

/--
lemma `IsInducing.of_comp` / 引理 `IsInducing.of_comp`

English:
lemma IsInducing.of_comp
  given: (hf : Continuous f) (hg : Continuous g) (hgf : IsInducing (g ∘ f))
  proof: ⟨le_antisymm hf.le_induced (by grw [hgf.eq_induced, ← induced_compose, ← hg.le_induced])⟩

中文:
引理 是Inducing.of_comp
  条件: (hf : 连续 f) (hg : 连续 g) (hgf : 是Inducing (g ∘ f))
  证明: ⟨le_antisymm hf.le_induced (by grw [hgf.eq_induced, ← induced_compose, ← hg.le_induced])⟩

Depends on / 依赖: eq_induced, hf.le_induced, hg.le_induced, hgf.eq_induced, induced_compose, le_antisymm, le_induced
-/
lemma IsInducing.of_comp (hf : Continuous f) (hg : Continuous g) (hgf : IsInducing (g ∘ f)) :
    IsInducing f :=
  ⟨le_antisymm hf.le_induced (by grw [hgf.eq_induced, ← induced_compose, ← hg.le_induced])⟩

/--
lemma `isInducing_iff_nhds` / 引理 `isInducing_iff_nhds`

English:
lemma isInducing_iff_nhds
  statement: IsInducing f ↔ forall x, 𝓝 x = comap f (𝓝 (f x))
  proof: (isInducing_iff _).trans (induced_iff_nhds_eq f)

中文:
引理 isInducing_iff_nhds
  结论: 是Inducing f ↔ 对任意 x, 𝓝 x = comap f (𝓝 (f x))
  证明: (isInducing_iff _).trans (induced_iff_nhds_eq f)

Depends on / 依赖: induced_iff_nhds_eq, isInducing_iff
-/
lemma isInducing_iff_nhds : IsInducing f ↔ forall x, 𝓝 x = comap f (𝓝 (f x)) :=
  (isInducing_iff _).trans (induced_iff_nhds_eq f)

namespace IsInducing

/--
lemma `nhds_eq_comap` / 引理 `nhds_eq_comap`

English:
lemma nhds_eq_comap
  given: (hf : IsInducing f)
  statement: forall x : X, 𝓝 x = comap f (𝓝 <| f x)
  proof: isInducing_iff_nhds.1 hf

中文:
引理 nhds_eq_comap
  条件: (hf : 是Inducing f)
  结论: 对任意 x : X, 𝓝 x = comap f (𝓝 <| f x)
  证明: isInducing_iff_nhds.1 hf

Depends on / 依赖: isInducing_iff_nhds
-/
lemma nhds_eq_comap (hf : IsInducing f) : forall x : X, 𝓝 x = comap f (𝓝 <| f x) :=
  isInducing_iff_nhds.1 hf

/--
lemma `basis_nhds` / 引理 `basis_nhds`

English:
lemma basis_nhds
  statement: {p : ι -> Prop} {s : ι -> Set Y} (hf : IsInducing f) {x : X}
  proof: hf.nhds_eq_comap x ▸ h_basis.comap f

中文:
引理 basis_nhds
  结论: {p : ι -> 命题} {s : ι -> 集合 Y} (hf : 是Inducing f) {x : X}
  证明: hf.nhds_eq_comap x ▸ h_basis.comap f

Depends on / 依赖: h_basis, h_basis.comap, hf.nhds_eq_comap, nhds_eq_comap
-/
lemma basis_nhds {p : ι -> Prop} {s : ι -> Set Y} (hf : IsInducing f) {x : X}
    (h_basis : (𝓝 (f x)).HasBasis p s) : (𝓝 x).HasBasis p (preimage f ∘ s) :=
  hf.nhds_eq_comap x ▸ h_basis.comap f

/--
lemma `nhdsSet_eq_comap` / 引理 `nhdsSet_eq_comap`

English:
lemma nhdsSet_eq_comap
  given: (hf : IsInducing f) (s : Set X)
  proof: by
  simp only [nhdsSet, sSup_image, comap_iSup, hf.nhds_eq_comap, iSup_image]

中文:
引理 nhdsSet_eq_comap
  条件: (hf : 是Inducing f) (s : 集合 X)
  证明: by
  simp only [nhdsSet, sSup_image, comap_iSup, hf.nhds_eq_comap, iSup_image]

Depends on / 依赖: comap_iSup, hf.nhds_eq_comap, iSup_image, nhdsSet, nhds_eq_comap, sSup_image
-/
lemma nhdsSet_eq_comap (hf : IsInducing f) (s : Set X) :
    𝓝ˢ s = comap f (𝓝ˢ (f '' s)) := by
  simp only [nhdsSet, sSup_image, comap_iSup, hf.nhds_eq_comap, iSup_image]

/--
lemma `map_nhds_eq` / 引理 `map_nhds_eq`

English:
lemma map_nhds_eq
  given: (hf : IsInducing f) (x : X)
  statement: (𝓝 x).map f = 𝓝[range f] f x
  proof: hf.eq_induced ▸ map_nhds_induced_eq x

中文:
引理 map_nhds_eq
  条件: (hf : 是Inducing f) (x : X)
  结论: (𝓝 x).map f = 𝓝[range f] f x
  证明: hf.eq_induced ▸ map_nhds_induced_eq x

Depends on / 依赖: eq_induced, hf.eq_induced, map_nhds_induced_eq
-/
lemma map_nhds_eq (hf : IsInducing f) (x : X) : (𝓝 x).map f = 𝓝[range f] f x :=
  hf.eq_induced ▸ map_nhds_induced_eq x

/--
lemma `map_nhds_of_mem` / 引理 `map_nhds_of_mem`

English:
lemma map_nhds_of_mem
  given: (hf : IsInducing f) (x : X) (h : range f in 𝓝 (f x))
  proof: hf.eq_induced ▸ map_nhds_induced_of_mem h

中文:
引理 map_nhds_of_mem
  条件: (hf : 是Inducing f) (x : X) (h : range f in 𝓝 (f x))
  证明: hf.eq_induced ▸ map_nhds_induced_of_mem h

Depends on / 依赖: eq_induced, hf.eq_induced, map_nhds_induced_of_mem
-/
lemma map_nhds_of_mem (hf : IsInducing f) (x : X) (h : range f in 𝓝 (f x)) :
    (𝓝 x).map f = 𝓝 (f x) := hf.eq_induced ▸ map_nhds_induced_of_mem h

/--
lemma `mapClusterPt_iff` / 引理 `mapClusterPt_iff`

English:
lemma mapClusterPt_iff
  given: (hf : IsInducing f) {x : X} {l : Filter X}
  proof: by
  delta MapClusterPt ClusterPt
  rw [← Filter.push_pull']; rw [← hf.nhds_eq_comap]; rw [map_neBot_iff]

中文:
引理 mapClusterPt_iff
  条件: (hf : 是Inducing f) {x : X} {l : 滤子 X}
  证明: by
  delta MapClusterPt ClusterPt
  rw [← Filter.push_pull']; rw [← hf.nhds_eq_comap]; rw [map_neBot_iff]

Depends on / 依赖: ClusterPt, Filter, Filter.push_pull, MapClusterPt, hf.nhds_eq_comap, map_neBot_iff, nhds_eq_comap, push_pull
-/
lemma mapClusterPt_iff (hf : IsInducing f) {x : X} {l : Filter X} :
    MapClusterPt (f x) l f ↔ ClusterPt x l := by
  delta MapClusterPt ClusterPt
  rw [← Filter.push_pull']; rw [← hf.nhds_eq_comap]; rw [map_neBot_iff]

/--
lemma `image_mem_nhdsWithin` / 引理 `image_mem_nhdsWithin`

English:
lemma image_mem_nhdsWithin
  given: (hf : IsInducing f) {x : X} {s : Set X} (hs : s in 𝓝 x)
  proof: hf.map_nhds_eq x ▸ image_mem_map hs

中文:
引理 image_mem_nhdsWithin
  条件: (hf : 是Inducing f) {x : X} {s : 集合 X} (hs : s in 𝓝 x)
  证明: hf.map_nhds_eq x ▸ image_mem_map hs

Depends on / 依赖: hf.map_nhds_eq, image_mem_map, map_nhds_eq
-/
lemma image_mem_nhdsWithin (hf : IsInducing f) {x : X} {s : Set X} (hs : s in 𝓝 x) :
    f '' s in 𝓝[range f] f x :=
  hf.map_nhds_eq x ▸ image_mem_map hs

/--
lemma `tendsto_nhds_iff` / 引理 `tendsto_nhds_iff`

English:
lemma tendsto_nhds_iff
  given: {f : ι -> Y} {l : Filter ι} {y : Y} (hg : IsInducing g)
  proof: by
  rw [hg.nhds_eq_comap]; rw [tendsto_comap_iff]

中文:
引理 tendsto_nhds_iff
  条件: {f : ι -> Y} {l : 滤子 ι} {y : Y} (hg : 是Inducing g)
  证明: by
  rw [hg.nhds_eq_comap]; rw [tendsto_comap_iff]

Depends on / 依赖: hg.nhds_eq_comap, nhds_eq_comap, tendsto_comap_iff
-/
lemma tendsto_nhds_iff {f : ι -> Y} {l : Filter ι} {y : Y} (hg : IsInducing g) :
    Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (𝓝 (g y)) := by
  rw [hg.nhds_eq_comap]; rw [tendsto_comap_iff]

/--
lemma `continuousAt_iff` / 引理 `continuousAt_iff`

English:
lemma continuousAt_iff
  given: (hg : IsInducing g) {x : X}
  proof: hg.tendsto_nhds_iff

中文:
引理 continuousAt_iff
  条件: (hg : 是Inducing g) {x : X}
  证明: hg.tendsto_nhds_iff

Depends on / 依赖: hg.tendsto_nhds_iff, tendsto_nhds_iff
-/
lemma continuousAt_iff (hg : IsInducing g) {x : X} :
    ContinuousAt f x ↔ ContinuousAt (g ∘ f) x :=
  hg.tendsto_nhds_iff

/--
lemma `continuous_iff` / 引理 `continuous_iff`

English:
lemma continuous_iff
  given: (hg : IsInducing g)
  proof: by
  simp_rw [continuous_iff_continuousAt, hg.continuousAt_iff]

中文:
引理 continuous_iff
  条件: (hg : 是Inducing g)
  证明: by
  simp_rw [continuous_iff_continuousAt, hg.continuousAt_iff]

Depends on / 依赖: continuousAt_iff, continuous_iff_continuousAt, hg.continuousAt_iff, simp_rw
-/
lemma continuous_iff (hg : IsInducing g) :
    Continuous f ↔ Continuous (g ∘ f) := by
  simp_rw [continuous_iff_continuousAt, hg.continuousAt_iff]

/--
lemma `continuousAt_iff'` / 引理 `continuousAt_iff'`

English:
lemma continuousAt_iff'
  given: (hf : IsInducing f) {x : X} (h : range f in 𝓝 (f x))
  proof: by
  simp_rw [ContinuousAt, Filter.Tendsto, ← hf.map_nhds_of_mem _ h, Filter.map_map, comp]

@[fun_prop]

中文:
引理 continuousAt_iff'
  条件: (hf : 是Inducing f) {x : X} (h : range f in 𝓝 (f x))
  证明: by
  simp_rw [ContinuousAt, Filter.Tendsto, ← hf.map_nhds_of_mem _ h, Filter.map_map, comp]

@[fun_prop]

Depends on / 依赖: ContinuousAt, Filter, Filter.Tendsto, Filter.map_map, Tendsto, hf.map_nhds_of_mem, map_map, map_nhds_of_mem, simp_rw
-/
lemma continuousAt_iff' (hf : IsInducing f) {x : X} (h : range f in 𝓝 (f x)) :
    ContinuousAt (g ∘ f) x ↔ ContinuousAt g (f x) := by
  simp_rw [ContinuousAt, Filter.Tendsto, ← hf.map_nhds_of_mem _ h, Filter.map_map, comp]

@[fun_prop]
/--
lemma `continuous` / 引理 `continuous`

English:
lemma continuous
  given: (hf : IsInducing f)
  statement: Continuous f
  proof: hf.continuous_iff.mp continuous_id

中文:
引理 continuous
  条件: (hf : 是Inducing f)
  结论: 连续 f
  证明: hf.continuous_iff.mp continuous_id
-/
protected lemma continuous (hf : IsInducing f) : Continuous f :=
  hf.continuous_iff.mp continuous_id

/--
lemma `closure_eq_preimage_closure_image` / 引理 `closure_eq_preimage_closure_image`

English:
lemma closure_eq_preimage_closure_image
  given: (hf : IsInducing f) (s : Set X)
  proof: by
  ext x
  rw [Set.mem_preimage]; rw [← closure_induced]; rw [hf.eq_induced]

中文:
引理 closure_eq_preimage_closure_image
  条件: (hf : 是Inducing f) (s : 集合 X)
  证明: by
  ext x
  rw [Set.mem_preimage]; rw [← closure_induced]; rw [hf.eq_induced]

Depends on / 依赖: Set.mem_preimage, closure_induced, eq_induced, hf.eq_induced, mem_preimage
-/
lemma closure_eq_preimage_closure_image (hf : IsInducing f) (s : Set X) :
    closure s = f ⁻¹' closure (f '' s) := by
  ext x
  rw [Set.mem_preimage]; rw [← closure_induced]; rw [hf.eq_induced]

/--
theorem `isClosed_iff` / 定理 `isClosed_iff`

English:
theorem isClosed_iff
  given: (hf : IsInducing f) {s : Set X}
  proof: by rw [hf.eq_induced, isClosed_induced_iff]

中文:
定理 isClosed_iff
  条件: (hf : 是Inducing f) {s : 集合 X}
  证明: by rw [hf.eq_induced, isClosed_induced_iff]

Depends on / 依赖: eq_induced, hf.eq_induced, isClosed_induced_iff
-/
theorem isClosed_iff (hf : IsInducing f) {s : Set X} :
    IsClosed s ↔ exists t, IsClosed t ∧ f ⁻¹' t = s := by rw [hf.eq_induced, isClosed_induced_iff]

/--
theorem `image_eq_isClosed_inter_range` / 定理 `image_eq_isClosed_inter_range`

English:
theorem image_eq_isClosed_inter_range
  given: (hf : IsInducing f) {s : Set X} (hs : IsClosed s)
  proof: by
  obtain ⟨c, hc, rfl⟩ := hf.isClosed_iff.1 hs
  exact ⟨c, hc, image_preimage_eq_inter_range⟩

中文:
定理 image_eq_isClosed_inter_range
  条件: (hf : 是Inducing f) {s : 集合 X} (hs : 是闭集 s)
  证明: by
  obtain ⟨c, hc, rfl⟩ := hf.isClosed_iff.1 hs
  exact ⟨c, hc, image_preimage_eq_inter_range⟩

Depends on / 依赖: hf.isClosed_iff, image_preimage_eq_inter_range, isClosed_iff
-/
theorem image_eq_isClosed_inter_range (hf : IsInducing f) {s : Set X} (hs : IsClosed s) :
    exists c, IsClosed c ∧ f '' s = c inter range f := by
  obtain ⟨c, hc, rfl⟩ := hf.isClosed_iff.1 hs
  exact ⟨c, hc, image_preimage_eq_inter_range⟩

/--
theorem `isClosed_iff'` / 定理 `isClosed_iff'`

English:
theorem isClosed_iff'
  given: (hf : IsInducing f) {s : Set X}
  proof: by rw [hf.eq_induced, isClosed_induced_iff']

中文:
定理 isClosed_iff'
  条件: (hf : 是Inducing f) {s : 集合 X}
  证明: by rw [hf.eq_induced, isClosed_induced_iff']

Depends on / 依赖: eq_induced, hf.eq_induced, isClosed_induced_iff
-/
theorem isClosed_iff' (hf : IsInducing f) {s : Set X} :
    IsClosed s ↔ forall x, f x in closure (f '' s) -> x in s := by rw [hf.eq_induced, isClosed_induced_iff']

/--
theorem `isClosed_preimage` / 定理 `isClosed_preimage`

English:
theorem isClosed_preimage
  given: (h : IsInducing f) (s : Set Y) (hs : IsClosed s)
  proof: (isClosed_iff h).mpr ⟨s, hs, rfl⟩

中文:
定理 isClosed_preimage
  条件: (h : 是Inducing f) (s : 集合 Y) (hs : 是闭集 s)
  证明: (isClosed_iff h).mpr ⟨s, hs, rfl⟩

Depends on / 依赖: isClosed_iff
-/
theorem isClosed_preimage (h : IsInducing f) (s : Set Y) (hs : IsClosed s) :
    IsClosed (f ⁻¹' s) :=
  (isClosed_iff h).mpr ⟨s, hs, rfl⟩

/--
theorem `isOpen_iff` / 定理 `isOpen_iff`

English:
theorem isOpen_iff
  given: (hf : IsInducing f) {s : Set X}
  proof: by rw [hf.eq_induced, isOpen_induced_iff]

中文:
定理 isOpen_iff
  条件: (hf : 是Inducing f) {s : 集合 X}
  证明: by rw [hf.eq_induced, isOpen_induced_iff]

Depends on / 依赖: eq_induced, hf.eq_induced, isOpen_induced_iff
-/
theorem isOpen_iff (hf : IsInducing f) {s : Set X} :
    IsOpen s ↔ exists t, IsOpen t ∧ f ⁻¹' t = s := by rw [hf.eq_induced, isOpen_induced_iff]

/--
theorem `image_eq_isOpen_inter_range` / 定理 `image_eq_isOpen_inter_range`

English:
theorem image_eq_isOpen_inter_range
  given: (hf : IsInducing f) {s : Set X} (hs : IsOpen s)
  proof: by
  obtain ⟨c, hc, rfl⟩ := hf.isOpen_iff.1 hs
  exact ⟨c, hc, image_preimage_eq_inter_range⟩

中文:
定理 image_eq_isOpen_inter_range
  条件: (hf : 是Inducing f) {s : 集合 X} (hs : 是开集 s)
  证明: by
  obtain ⟨c, hc, rfl⟩ := hf.isOpen_iff.1 hs
  exact ⟨c, hc, image_preimage_eq_inter_range⟩

Depends on / 依赖: hf.isOpen_iff, image_preimage_eq_inter_range, isOpen_iff
-/
theorem image_eq_isOpen_inter_range (hf : IsInducing f) {s : Set X} (hs : IsOpen s) :
    exists c, IsOpen c ∧ f '' s = c inter range f := by
  obtain ⟨c, hc, rfl⟩ := hf.isOpen_iff.1 hs
  exact ⟨c, hc, image_preimage_eq_inter_range⟩

/--
theorem `setOfPred_isOpen` / 定理 `setOfPred_isOpen`

English:
theorem setOfPred_isOpen
  given: (hf : IsInducing f)
  proof: Set.ext fun _ => hf.isOpen_iff

@[deprecated (since := "2026-07-09")] alias setOf_isOpen := setOfPred_isOpen

中文:
定理 setOfPred_isOpen
  条件: (hf : 是Inducing f)
  证明: Set.ext fun _ => hf.isOpen_iff

@[deprecated (since := "2026-07-09")] alias setOf_isOpen := setOfPred_isOpen

Depends on / 依赖: Set.ext, hf.isOpen_iff, isOpen_iff
-/
theorem setOfPred_isOpen (hf : IsInducing f) :
    {s : Set X | IsOpen s} = preimage f '' {t | IsOpen t} :=
  Set.ext fun _ => hf.isOpen_iff

@[deprecated (since := "2026-07-09")] alias setOf_isOpen := setOfPred_isOpen

/--
theorem `dense_iff` / 定理 `dense_iff`

English:
theorem dense_iff
  given: (hf : IsInducing f) {s : Set X}
  proof: by
  simp only [Dense, hf.closure_eq_preimage_closure_image, mem_preimage]

中文:
定理 dense_iff
  条件: (hf : 是Inducing f) {s : 集合 X}
  证明: by
  simp only [Dense, hf.closure_eq_preimage_closure_image, mem_preimage]

Depends on / 依赖: closure_eq_preimage_closure_image, hf.closure_eq_preimage_closure_image, mem_preimage
-/
theorem dense_iff (hf : IsInducing f) {s : Set X} :
    Dense s ↔ forall x, f x in closure (f '' s) := by
  simp only [Dense, hf.closure_eq_preimage_closure_image, mem_preimage]

/--
theorem `of_subsingleton` / 定理 `of_subsingleton`

English:
theorem of_subsingleton
  given: [Subsingleton X] (f : X -> Y)
  statement: IsInducing f
  proof: ⟨Subsingleton.elim _ _⟩

中文:
定理 of_subsingleton
  条件: [子单例 X] (f : X -> Y)
  结论: 是Inducing f
  证明: ⟨Subsingleton.elim _ _⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem of_subsingleton [Subsingleton X] (f : X -> Y) : IsInducing f :=
  ⟨Subsingleton.elim _ _⟩

/--
theorem `indiscreteTopology` / 定理 `indiscreteTopology`

English:
theorem indiscreteTopology
  given: [IndiscreteTopology Y] {f : X -> Y} (hf : IsInducing f)
  proof: by
    cases IndiscreteTopology.eq_top Y
    let : TopologicalSpace Y := ⊤
    rw [hf.eq_induced]; rw [induced_top]

中文:
定理 indiscreteTopology
  条件: [Indiscrete拓扑 Y] {f : X -> Y} (hf : 是Inducing f)
  证明: by
    cases IndiscreteTopology.eq_top Y
    let : TopologicalSpace Y := ⊤
    rw [hf.eq_induced]; rw [induced_top]

Depends on / 依赖: IndiscreteTopology, IndiscreteTopology.eq_top, TopologicalSpace, eq_induced, eq_top, hf.eq_induced, induced_top
-/
theorem indiscreteTopology [IndiscreteTopology Y] {f : X -> Y} (hf : IsInducing f) :
    IndiscreteTopology X where
  eq_top := by
    cases IndiscreteTopology.eq_top Y
    let : TopologicalSpace Y := ⊤
    rw [hf.eq_induced]; rw [induced_top]

/--
theorem `nontrivialTopology` / 定理 `nontrivialTopology`

English:
theorem nontrivialTopology
  given: [NontrivialTopology X] {f : X -> Y} (hf : IsInducing f)
  proof: not_imp_not.1
    (by simpa using (fun _ : IndiscreteTopology Y => hf.indiscreteTopology)) ‹NontrivialTopology X›

中文:
定理 nontrivialTopology
  条件: [非平凡拓扑 X] {f : X -> Y} (hf : 是Inducing f)
  证明: not_imp_not.1
    (by simpa using (fun _ : IndiscreteTopology Y => hf.indiscreteTopology)) ‹NontrivialTopology X›

Depends on / 依赖: IndiscreteTopology, NontrivialTopology, hf.indiscreteTopology, indiscreteTopology, not_imp_not
-/
theorem nontrivialTopology [NontrivialTopology X] {f : X -> Y} (hf : IsInducing f) :
    NontrivialTopology Y :=
  not_imp_not.1
    (by simpa using (fun _ : IndiscreteTopology Y => hf.indiscreteTopology)) ‹NontrivialTopology X›

end IsInducing.IsInducing

namespace IsEmbedding

/--
lemma `induced` / 引理 `induced`

English:
lemma induced
  given: [t : TopologicalSpace Y] (hf : Injective f)
  proof: @IsEmbedding.mk X Y (t.induced f) t _ (.induced f) hf

alias _root_.Function.Injective.isEmbedding_induced := IsEmbedding.induced

中文:
引理 induced
  条件: [t : 拓扑空间 Y] (hf : 单射 f)
  证明: @IsEmbedding.mk X Y (t.induced f) t _ (.induced f) hf

alias _root_.Function.Injective.isEmbedding_induced := IsEmbedding.induced

Depends on / 依赖: IsEmbedding, IsEmbedding.mk, induced, t.induced
-/
lemma induced [t : TopologicalSpace Y] (hf : Injective f) :
    @IsEmbedding X Y (t.induced f) t f :=
  @IsEmbedding.mk X Y (t.induced f) t _ (.induced f) hf

alias _root_.Function.Injective.isEmbedding_induced := IsEmbedding.induced

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

@[fun_prop]
/--
lemma `isInducing` / 引理 `isInducing`

English:
lemma isInducing
  given: (hf : IsEmbedding f)
  statement: IsInducing f
  proof: hf.toIsInducing

中文:
引理 isInducing
  条件: (hf : 是嵌入 f)
  结论: 是Inducing f
  证明: hf.toIsInducing

Depends on / 依赖: hf.toIsInducing, toIsInducing
-/
lemma isInducing (hf : IsEmbedding f) : IsInducing f := hf.toIsInducing

/--
lemma `mk'` / 引理 `mk'`

English:
lemma mk'
  given: (f : X -> Y) (inj : Injective f) (induced : forall x, comap f (𝓝 (f x)) = 𝓝 x)
  proof: ⟨isInducing_iff_nhds.2 fun x => (induced x).symm, inj⟩

@[fun_prop]

中文:
引理 mk'
  条件: (f : X -> Y) (inj : 单射 f) (induced : 对任意 x, comap f (𝓝 (f x)) = 𝓝 x)
  证明: ⟨isInducing_iff_nhds.2 fun x => (induced x).symm, inj⟩

@[fun_prop]

Depends on / 依赖: induced, isInducing_iff_nhds
-/
lemma mk' (f : X -> Y) (inj : Injective f) (induced : forall x, comap f (𝓝 (f x)) = 𝓝 x) :
    IsEmbedding f :=
  ⟨isInducing_iff_nhds.2 fun x => (induced x).symm, inj⟩

@[fun_prop]
/--
lemma `id` / 引理 `id`

English:
lemma id
  statement: IsEmbedding (@id X)
  proof: ⟨.id, fun _ _ h => h⟩

@[fun_prop]

中文:
引理 id
  结论: 是嵌入 (@id X)
  证明: ⟨.id, fun _ _ h => h⟩

@[fun_prop]
-/
protected lemma id : IsEmbedding (@id X) := ⟨.id, fun _ _ h => h⟩

@[fun_prop]
/--
lemma `comp` / 引理 `comp`

English:
lemma comp
  given: (hg : IsEmbedding g) (hf : IsEmbedding f)
  statement: IsEmbedding (g ∘ f)
  proof: { hg.isInducing.comp hf.isInducing with injective := fun _ _ h => hf.injective <| hg.injective h }

中文:
引理 comp
  条件: (hg : 是嵌入 g) (hf : 是嵌入 f)
  结论: 是嵌入 (g ∘ f)
  证明: { hg.isInducing.comp hf.isInducing with injective := fun _ _ h => hf.injective <| hg.injective h }
-/
protected lemma comp (hg : IsEmbedding g) (hf : IsEmbedding f) : IsEmbedding (g ∘ f) :=
  { hg.isInducing.comp hf.isInducing with injective := fun _ _ h => hf.injective <| hg.injective h }

/--
lemma `of_comp_iff` / 引理 `of_comp_iff`

English:
lemma of_comp_iff
  given: (hg : IsEmbedding g)
  statement: IsEmbedding (g ∘ f) ↔ IsEmbedding f
  proof: by
  simp_rw [isEmbedding_iff, hg.isInducing.of_comp_iff, hg.injective.of_comp_iff f]

中文:
引理 of_comp_iff
  条件: (hg : 是嵌入 g)
  结论: 是嵌入 (g ∘ f) ↔ 是嵌入 f
  证明: by
  simp_rw [isEmbedding_iff, hg.isInducing.of_comp_iff, hg.injective.of_comp_iff f]

Depends on / 依赖: hg.injective.of_comp_iff, hg.isInducing.of_comp_iff, injective, isEmbedding_iff, isInducing, of_comp_iff, simp_rw
-/
lemma of_comp_iff (hg : IsEmbedding g) : IsEmbedding (g ∘ f) ↔ IsEmbedding f := by
  simp_rw [isEmbedding_iff, hg.isInducing.of_comp_iff, hg.injective.of_comp_iff f]

/--
lemma `of_comp` / 引理 `of_comp`

English:
lemma of_comp
  given: (hf : Continuous f) (hg : Continuous g) (hgf : IsEmbedding (g ∘ f))
  proof: hgf.isInducing.of_comp hf hg
  injective := hgf.injective.of_comp

中文:
引理 of_comp
  条件: (hf : 连续 f) (hg : 连续 g) (hgf : 是嵌入 (g ∘ f))
  证明: hgf.isInducing.of_comp hf hg
  injective := hgf.injective.of_comp
-/
protected lemma of_comp (hf : Continuous f) (hg : Continuous g) (hgf : IsEmbedding (g ∘ f)) :
    IsEmbedding f where
  toIsInducing := hgf.isInducing.of_comp hf hg
  injective := hgf.injective.of_comp

/--
lemma `of_leftInverse` / 引理 `of_leftInverse`

English:
lemma of_leftInverse
  statement: {f : X -> Y} {g : Y -> X} (h : LeftInverse f g) (hf : Continuous f)
  proof: .of_comp hg hf h.comp_eq_id.symm ▸ .id

alias _root_.Function.LeftInverse.isEmbedding := of_leftInverse

中文:
引理 of_leftInverse
  结论: {f : X -> Y} {g : Y -> X} (h : 左逆 f g) (hf : 连续 f)
  证明: .of_comp hg hf h.comp_eq_id.symm ▸ .id

alias _root_.Function.LeftInverse.isEmbedding := of_leftInverse

Depends on / 依赖: comp_eq_id, h.comp_eq_id.symm, of_comp
-/
lemma of_leftInverse {f : X -> Y} {g : Y -> X} (h : LeftInverse f g) (hf : Continuous f)
(hg : Continuous g) : IsEmbedding g := .of_comp hg hf h.comp_eq_id.symm ▸ .id

alias _root_.Function.LeftInverse.isEmbedding := of_leftInverse

/--
lemma `map_nhds_eq` / 引理 `map_nhds_eq`

English:
lemma map_nhds_eq
  given: (hf : IsEmbedding f) (x : X)
  statement: (𝓝 x).map f = 𝓝[range f] f x
  proof: hf.1.map_nhds_eq x

中文:
引理 map_nhds_eq
  条件: (hf : 是嵌入 f) (x : X)
  结论: (𝓝 x).map f = 𝓝[range f] f x
  证明: hf.1.map_nhds_eq x

Depends on / 依赖: map_nhds_eq
-/
lemma map_nhds_eq (hf : IsEmbedding f) (x : X) : (𝓝 x).map f = 𝓝[range f] f x :=
  hf.1.map_nhds_eq x

/--
lemma `map_nhds_of_mem` / 引理 `map_nhds_of_mem`

English:
lemma map_nhds_of_mem
  given: (hf : IsEmbedding f) (x : X) (h : range f in 𝓝 (f x))
  proof: hf.1.map_nhds_of_mem x h

中文:
引理 map_nhds_of_mem
  条件: (hf : 是嵌入 f) (x : X) (h : range f in 𝓝 (f x))
  证明: hf.1.map_nhds_of_mem x h

Depends on / 依赖: map_nhds_of_mem
-/
lemma map_nhds_of_mem (hf : IsEmbedding f) (x : X) (h : range f in 𝓝 (f x)) :
    (𝓝 x).map f = 𝓝 (f x) :=
  hf.1.map_nhds_of_mem x h

/--
lemma `tendsto_nhds_iff` / 引理 `tendsto_nhds_iff`

English:
lemma tendsto_nhds_iff
  given: {f : ι -> Y} {l : Filter ι} {y : Y} (hg : IsEmbedding g)
  proof: hg.isInducing.tendsto_nhds_iff

中文:
引理 tendsto_nhds_iff
  条件: {f : ι -> Y} {l : 滤子 ι} {y : Y} (hg : 是嵌入 g)
  证明: hg.isInducing.tendsto_nhds_iff

Depends on / 依赖: hg.isInducing.tendsto_nhds_iff, isInducing, tendsto_nhds_iff
-/
lemma tendsto_nhds_iff {f : ι -> Y} {l : Filter ι} {y : Y} (hg : IsEmbedding g) :
    Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (𝓝 (g y)) := hg.isInducing.tendsto_nhds_iff

/--
lemma `continuous_iff` / 引理 `continuous_iff`

English:
lemma continuous_iff
  given: (hg : IsEmbedding g)
  statement: Continuous f ↔ Continuous (g ∘ f)
  proof: hg.isInducing.continuous_iff

@[fun_prop]

中文:
引理 continuous_iff
  条件: (hg : 是嵌入 g)
  结论: 连续 f ↔ 连续 (g ∘ f)
  证明: hg.isInducing.continuous_iff

@[fun_prop]

Depends on / 依赖: continuous_iff, hg.isInducing.continuous_iff, isInducing
-/
lemma continuous_iff (hg : IsEmbedding g) : Continuous f ↔ Continuous (g ∘ f) :=
  hg.isInducing.continuous_iff

@[fun_prop]
/--
lemma `continuous` / 引理 `continuous`

English:
lemma continuous
  given: (hf : IsEmbedding f)
  statement: Continuous f
  proof: hf.isInducing.continuous

中文:
引理 continuous
  条件: (hf : 是嵌入 f)
  结论: 连续 f
  证明: hf.isInducing.continuous

Depends on / 依赖: continuous, hf.isInducing.continuous, isInducing
-/
lemma continuous (hf : IsEmbedding f) : Continuous f := hf.isInducing.continuous

/--
lemma `closure_eq_preimage_closure_image` / 引理 `closure_eq_preimage_closure_image`

English:
lemma closure_eq_preimage_closure_image
  given: (hf : IsEmbedding f) (s : Set X)
  proof: hf.1.closure_eq_preimage_closure_image s

中文:
引理 closure_eq_preimage_closure_image
  条件: (hf : 是嵌入 f) (s : 集合 X)
  证明: hf.1.closure_eq_preimage_closure_image s

Depends on / 依赖: closure_eq_preimage_closure_image
-/
lemma closure_eq_preimage_closure_image (hf : IsEmbedding f) (s : Set X) :
    closure s = f ⁻¹' closure (f '' s) :=
  hf.1.closure_eq_preimage_closure_image s

/--
lemma `discreteTopology` / 引理 `discreteTopology`

English:
lemma discreteTopology
  given: [DiscreteTopology Y] (hf : IsEmbedding f)
  statement: DiscreteTopology X
  proof: .of_continuous_injective hf.continuous hf.injective

中文:
引理 discreteTopology
  条件: [离散拓扑 Y] (hf : 是嵌入 f)
  结论: 离散拓扑 X
  证明: .of_continuous_injective hf.continuous hf.injective

Depends on / 依赖: continuous, hf.continuous, hf.injective, injective, of_continuous_injective
-/
lemma discreteTopology [DiscreteTopology Y] (hf : IsEmbedding f) : DiscreteTopology X :=
  .of_continuous_injective hf.continuous hf.injective

/--
lemma `of_subsingleton` / 引理 `of_subsingleton`

English:
lemma of_subsingleton
  given: [Subsingleton X] (f : X -> Y)
  statement: IsEmbedding f
  proof: ⟨.of_subsingleton f, f.injective_of_subsingleton⟩

中文:
引理 of_subsingleton
  条件: [子单例 X] (f : X -> Y)
  结论: 是嵌入 f
  证明: ⟨.of_subsingleton f, f.injective_of_subsingleton⟩

Depends on / 依赖: f.injective_of_subsingleton, injective_of_subsingleton, of_subsingleton
-/
lemma of_subsingleton [Subsingleton X] (f : X -> Y) : IsEmbedding f :=
  ⟨.of_subsingleton f, f.injective_of_subsingleton⟩

end IsEmbedding

section IsCoinducing

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/--
lemma `isCoinducing_iff` / 引理 `isCoinducing_iff`

English:
lemma isCoinducing_iff
  statement: IsCoinducing f ↔ forall s : Set Y, IsOpen (f ⁻¹' s) ↔ IsOpen s
  proof: (isCoinducing_iff' _).trans eq_comm.trans TopologicalSpace.ext_iff

中文:
引理 isCoinducing_iff
  结论: 是余inducing f ↔ 对任意 s : 集合 Y, 是开集 (f ⁻¹' s) ↔ 是开集 s
  证明: (isCoinducing_iff' _).trans eq_comm.trans TopologicalSpace.ext_iff

Depends on / 依赖: TopologicalSpace, TopologicalSpace.ext_iff, eq_comm, eq_comm.trans, ext_iff, isCoinducing_iff
-/
lemma isCoinducing_iff : IsCoinducing f ↔ forall s : Set Y, IsOpen (f ⁻¹' s) ↔ IsOpen s :=
(isCoinducing_iff' _).trans eq_comm.trans TopologicalSpace.ext_iff

/--
lemma `isCoinducing_iff_isClosed` / 引理 `isCoinducing_iff_isClosed`

English:
lemma isCoinducing_iff_isClosed
  proof: isCoinducing_iff.trans compl_surjective.forall.trans by simp

中文:
引理 isCoinducing_iff_isClosed
  证明: isCoinducing_iff.trans compl_surjective.forall.trans by simp

Depends on / 依赖: compl_surjective, compl_surjective.forall.trans, isCoinducing_iff, isCoinducing_iff.trans
-/
lemma isCoinducing_iff_isClosed :
    IsCoinducing f ↔ forall s : Set Y, IsClosed (f ⁻¹' s) ↔ IsClosed s :=
isCoinducing_iff.trans compl_surjective.forall.trans by simp

namespace IsCoinducing

/--
lemma `isOpen_preimage` / 引理 `isOpen_preimage`

English:
lemma isOpen_preimage
  given: (hf : IsCoinducing f) {s : Set Y}
  proof: isCoinducing_iff.mp hf _

中文:
引理 isOpen_preimage
  条件: (hf : 是余inducing f) {s : 集合 Y}
  证明: isCoinducing_iff.mp hf _
-/
protected lemma isOpen_preimage (hf : IsCoinducing f) {s : Set Y} :
    IsOpen (f ⁻¹' s) ↔ IsOpen s :=
  isCoinducing_iff.mp hf _

/--
lemma `isClosed_preimage` / 引理 `isClosed_preimage`

English:
lemma isClosed_preimage
  given: (hf : IsCoinducing f) {s : Set Y}
  proof: isCoinducing_iff_isClosed.mp hf _

alias ⟨_, of_isOpen_preimage_iff_isOpen⟩ := isCoinducing_iff

alias ⟨_, of_isClosed_preimage_iff_isClosed⟩ := isCoinducing_iff_isClosed

中文:
引理 isClosed_preimage
  条件: (hf : 是余inducing f) {s : 集合 Y}
  证明: isCoinducing_iff_isClosed.mp hf _

alias ⟨_, of_isOpen_preimage_iff_isOpen⟩ := isCoinducing_iff

alias ⟨_, of_isClosed_preimage_iff_isClosed⟩ := isCoinducing_iff_isClosed
-/
protected lemma isClosed_preimage (hf : IsCoinducing f) {s : Set Y} :
    IsClosed (f ⁻¹' s) ↔ IsClosed s :=
  isCoinducing_iff_isClosed.mp hf _

alias ⟨_, of_isOpen_preimage_iff_isOpen⟩ := isCoinducing_iff

alias ⟨_, of_isClosed_preimage_iff_isClosed⟩ := isCoinducing_iff_isClosed

/--
lemma `continuous` / 引理 `continuous`

English:
lemma continuous
  given: (hf : IsCoinducing f)
  statement: Continuous f where
  proof: by rwa [hf.isOpen_preimage]

中文:
引理 continuous
  条件: (hf : 是余inducing f)
  结论: 连续 f where
  证明: by rwa [hf.isOpen_preimage]
-/
protected lemma continuous (hf : IsCoinducing f) : Continuous f where
  isOpen_preimage s hs := by rwa [hf.isOpen_preimage]

variable (X) in
@[fun_prop]
/--
lemma `id` / 引理 `id`

English:
lemma id
  statement: IsCoinducing (id (α := X)) where
  proof: coinduced_id.symm

@[fun_prop]

中文:
引理 id
  结论: 是余inducing (id (α := X)) where
  证明: coinduced_id.symm

@[fun_prop]
-/
protected lemma id : IsCoinducing (id (α := X)) where
  eq_coinduced := coinduced_id.symm

@[fun_prop]
/--
lemma `comp` / 引理 `comp`

English:
lemma comp
  given: (hg : IsCoinducing g) (hf : IsCoinducing f)
  statement: IsCoinducing (g.comp f) where
  proof: by rw [hg.eq_coinduced, hf.eq_coinduced, coinduced_compose]

中文:
引理 comp
  条件: (hg : 是余inducing g) (hf : 是余inducing f)
  结论: 是余inducing (g.comp f) where
  证明: by rw [hg.eq_coinduced, hf.eq_coinduced, coinduced_compose]
-/
protected lemma comp (hg : IsCoinducing g) (hf : IsCoinducing f) : IsCoinducing (g.comp f) where
  eq_coinduced := by rw [hg.eq_coinduced, hf.eq_coinduced, coinduced_compose]

/--
lemma `of_comp_iff` / 引理 `of_comp_iff`

English:
lemma of_comp_iff
  given: (hf : IsCoinducing f)
  proof: by
  refine ⟨fun hgf => .of_isOpen_preimage_iff_isOpen fun s => ?_, fun hg => hg.comp hf⟩
  rw [← hgf.isOpen_preimage]; rw [Set.preimage_comp]; rw [hf.isOpen_preimage]

中文:
引理 of_comp_iff
  条件: (hf : 是余inducing f)
  证明: by
  refine ⟨fun hgf => .of_isOpen_preimage_iff_isOpen fun s => ?_, fun hg => hg.comp hf⟩
  rw [← hgf.isOpen_preimage]; rw [Set.preimage_comp]; rw [hf.isOpen_preimage]
-/
protected lemma of_comp_iff (hf : IsCoinducing f) :
    IsCoinducing (g ∘ f) ↔ IsCoinducing g := by
  refine ⟨fun hgf => .of_isOpen_preimage_iff_isOpen fun s => ?_, fun hg => hg.comp hf⟩
  rw [← hgf.isOpen_preimage]; rw [Set.preimage_comp]; rw [hf.isOpen_preimage]

/--
lemma `of_comp` / 引理 `of_comp`

English:
lemma of_comp
  given: (hf : Continuous f) (hg : Continuous g) (hgf : IsCoinducing (g ∘ f))
  proof: ⟨le_antisymm (by grw [hgf.eq_coinduced, ← coinduced_compose, hf.coinduced_le]) hg.coinduced_le⟩

中文:
引理 of_comp
  条件: (hf : 连续 f) (hg : 连续 g) (hgf : 是余inducing (g ∘ f))
  证明: ⟨le_antisymm (by grw [hgf.eq_coinduced, ← coinduced_compose, hf.coinduced_le]) hg.coinduced_le⟩
-/
protected lemma of_comp (hf : Continuous f) (hg : Continuous g) (hgf : IsCoinducing (g ∘ f)) :
    IsCoinducing g :=
  ⟨le_antisymm (by grw [hgf.eq_coinduced, ← coinduced_compose, hf.coinduced_le]) hg.coinduced_le⟩

/--
lemma `isOpenMap_of_injective` / 引理 `isOpenMap_of_injective`

English:
lemma isOpenMap_of_injective
  given: (hf : IsCoinducing f) (hf' : Injective f)
  statement: IsOpenMap f
  proof: by
  intro s hs
  rwa [← hf.isOpen_preimage, preimage_image_eq _ hf']

中文:
引理 isOpenMap_of_injective
  条件: (hf : 是余inducing f) (hf' : 单射 f)
  结论: 是开映射 f
  证明: by
  intro s hs
  rwa [← hf.isOpen_preimage, preimage_image_eq _ hf']

Depends on / 依赖: hf.isOpen_preimage, isOpen_preimage, preimage_image_eq
-/
lemma isOpenMap_of_injective (hf : IsCoinducing f) (hf' : Injective f) : IsOpenMap f := by
  intro s hs
  rwa [← hf.isOpen_preimage, preimage_image_eq _ hf']

end IsCoinducing

end IsCoinducing

section IsQuotientMap

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/--
theorem `isQuotientMap_iff_isClosed` / 定理 `isQuotientMap_iff_isClosed`

English:
theorem isQuotientMap_iff_isClosed
  proof: by
  simp_rw [isQuotientMap_iff, isCoinducing_iff_isClosed, and_comm, iff_comm]

中文:
定理 isQuotientMap_iff_isClosed
  证明: by
  simp_rw [isQuotientMap_iff, isCoinducing_iff_isClosed, and_comm, iff_comm]

Depends on / 依赖: and_comm, iff_comm, isCoinducing_iff_isClosed, isQuotientMap_iff, simp_rw
-/
theorem isQuotientMap_iff_isClosed :
    IsQuotientMap f ↔ Surjective f ∧ forall s : Set Y, IsClosed s ↔ IsClosed (f ⁻¹' s) := by
  simp_rw [isQuotientMap_iff, isCoinducing_iff_isClosed, and_comm, iff_comm]

namespace IsQuotientMap

@[fun_prop]
/--
theorem `id` / 定理 `id`

English:
theorem id
  statement: IsQuotientMap (@id X)
  proof: ⟨.id _, fun x => ⟨x, rfl⟩⟩

@[fun_prop]

中文:
定理 id
  结论: 是商映射 (@id X)
  证明: ⟨.id _, fun x => ⟨x, rfl⟩⟩

@[fun_prop]
-/
protected theorem id : IsQuotientMap (@id X) :=
  ⟨.id _, fun x => ⟨x, rfl⟩⟩

@[fun_prop]
/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: (hg : IsQuotientMap g) (hf : IsQuotientMap f)
  statement: IsQuotientMap (g ∘ f)
  proof: ⟨.comp hg.1 hf.1, hg.surjective.comp hf.surjective, ⟩

中文:
定理 comp
  条件: (hg : 是商映射 g) (hf : 是商映射 f)
  结论: 是商映射 (g ∘ f)
  证明: ⟨.comp hg.1 hf.1, hg.surjective.comp hf.surjective, ⟩
-/
protected theorem comp (hg : IsQuotientMap g) (hf : IsQuotientMap f) : IsQuotientMap (g ∘ f) :=
  ⟨.comp hg.1 hf.1, hg.surjective.comp hf.surjective, ⟩

/--
theorem `of_comp` / 定理 `of_comp`

English:
theorem of_comp
  statement: (hf : Continuous f) (hg : Continuous g)
  proof: ⟨.of_comp hf hg hgf.1, hgf.2.of_comp⟩

中文:
定理 of_comp
  结论: (hf : 连续 f) (hg : 连续 g)
  证明: ⟨.of_comp hf hg hgf.1, hgf.2.of_comp⟩
-/
protected theorem of_comp (hf : Continuous f) (hg : Continuous g)
    (hgf : IsQuotientMap (g ∘ f)) : IsQuotientMap g :=
  ⟨.of_comp hf hg hgf.1, hgf.2.of_comp⟩

/--
theorem `of_comp_of_isCoinducing` / 定理 `of_comp_of_isCoinducing`

English:
theorem of_comp_of_isCoinducing
  given: (hgf : IsQuotientMap (g ∘ f)) (hf : IsCoinducing f)
  proof: ⟨hf.of_comp_iff.mp hgf.1, hgf.2.of_comp⟩

@[deprecated (since := "2026-03-21")]
alias of_comp_of_eq_coinduced := of_comp_of_isCoinducing

中文:
定理 of_comp_of_isCoinducing
  条件: (hgf : 是商映射 (g ∘ f)) (hf : 是余inducing f)
  证明: ⟨hf.of_comp_iff.mp hgf.1, hgf.2.of_comp⟩

@[deprecated (since := "2026-03-21")]
alias of_comp_of_eq_coinduced := of_comp_of_isCoinducing

Depends on / 依赖: hf.of_comp_iff.mp, of_comp, of_comp_iff
-/
theorem of_comp_of_isCoinducing (hgf : IsQuotientMap (g ∘ f)) (hf : IsCoinducing f) :
    IsQuotientMap g :=
  ⟨hf.of_comp_iff.mp hgf.1, hgf.2.of_comp⟩

@[deprecated (since := "2026-03-21")]
alias of_comp_of_eq_coinduced := of_comp_of_isCoinducing

/--
theorem `of_comp_iff` / 定理 `of_comp_iff`

English:
theorem of_comp_iff
  given: (hf : IsQuotientMap f)
  proof: by
  rw [isQuotientMap_iff]; rw [isQuotientMap_iff]; rw [hf.isCoinducing.of_comp_iff]; rw [hf.surjective.of_comp_iff]

中文:
定理 of_comp_iff
  条件: (hf : 是商映射 f)
  证明: by
  rw [isQuotientMap_iff]; rw [isQuotientMap_iff]; rw [hf.isCoinducing.of_comp_iff]; rw [hf.surjective.of_comp_iff]
-/
protected theorem of_comp_iff (hf : IsQuotientMap f) :
    IsQuotientMap (g ∘ f) ↔ IsQuotientMap g := by
  rw [isQuotientMap_iff]; rw [isQuotientMap_iff]; rw [hf.isCoinducing.of_comp_iff]; rw [hf.surjective.of_comp_iff]

/--
theorem `of_comp_isQuotientMap` / 定理 `of_comp_isQuotientMap`

English:
theorem of_comp_isQuotientMap
  given: (hf : IsQuotientMap f) (hgf : IsQuotientMap (g ∘ f))
  proof: of_comp_of_isCoinducing hgf hf.isCoinducing

中文:
定理 of_comp_isQuotientMap
  条件: (hf : 是商映射 f) (hgf : 是商映射 (g ∘ f))
  证明: of_comp_of_isCoinducing hgf hf.isCoinducing

Depends on / 依赖: hf.isCoinducing, isCoinducing, of_comp_of_isCoinducing
-/
theorem of_comp_isQuotientMap (hf : IsQuotientMap f) (hgf : IsQuotientMap (g ∘ f)) :
    IsQuotientMap g := of_comp_of_isCoinducing hgf hf.isCoinducing

/--
theorem `of_inverse` / 定理 `of_inverse`

English:
theorem of_inverse
  given: {g : Y -> X} (hf : Continuous f) (hg : Continuous g) (h : LeftInverse g f)
  proof: .of_comp hf hg h.comp_eq_id.symm ▸ IsQuotientMap.id

中文:
定理 of_inverse
  条件: {g : Y -> X} (hf : 连续 f) (hg : 连续 g) (h : 左逆 g f)
  证明: .of_comp hf hg h.comp_eq_id.symm ▸ IsQuotientMap.id

Depends on / 依赖: IsQuotientMap, IsQuotientMap.id, comp_eq_id, h.comp_eq_id.symm, of_comp
-/
theorem of_inverse {g : Y -> X} (hf : Continuous f) (hg : Continuous g) (h : LeftInverse g f) :
IsQuotientMap g := .of_comp hf hg h.comp_eq_id.symm ▸ IsQuotientMap.id

/--
theorem `continuous_iff` / 定理 `continuous_iff`

English:
theorem continuous_iff
  given: (hf : IsQuotientMap f)
  statement: Continuous g ↔ Continuous (g ∘ f)
  proof: by
  rw [continuous_iff_coinduced_le]; rw [continuous_iff_coinduced_le]; rw [hf.eq_coinduced]; rw [coinduced_compose]

@[fun_prop]

中文:
定理 continuous_iff
  条件: (hf : 是商映射 f)
  结论: 连续 g ↔ 连续 (g ∘ f)
  证明: by
  rw [continuous_iff_coinduced_le]; rw [continuous_iff_coinduced_le]; rw [hf.eq_coinduced]; rw [coinduced_compose]

@[fun_prop]
-/
protected theorem continuous_iff (hf : IsQuotientMap f) : Continuous g ↔ Continuous (g ∘ f) := by
  rw [continuous_iff_coinduced_le]; rw [continuous_iff_coinduced_le]; rw [hf.eq_coinduced]; rw [coinduced_compose]

@[fun_prop]
/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (hf : IsQuotientMap f)
  statement: Continuous f
  proof: hf.continuous_iff.mp continuous_id

中文:
定理 continuous
  条件: (hf : 是商映射 f)
  结论: 连续 f
  证明: hf.continuous_iff.mp continuous_id
-/
protected theorem continuous (hf : IsQuotientMap f) : Continuous f :=
  hf.continuous_iff.mp continuous_id

end IsQuotientMap

end Topology.IsQuotientMap

section OpenMap
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace IsOpenMap

/--
theorem `id` / 定理 `id`

English:
theorem id
  statement: IsOpenMap (@id X)
  proof: fun s hs => by rwa [image_id]

中文:
定理 id
  结论: 是开映射 (@id X)
  证明: fun s hs => by rwa [image_id]
-/
protected theorem id : IsOpenMap (@id X) := fun s hs => by rwa [image_id]

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: (hg : IsOpenMap g) (hf : IsOpenMap f)
  proof: fun s hs => by rw [image_comp]; exact hg _ (hf _ hs)

中文:
定理 comp
  条件: (hg : 是开映射 g) (hf : 是开映射 f)
  证明: fun s hs => by rw [image_comp]; exact hg _ (hf _ hs)
-/
protected theorem comp (hg : IsOpenMap g) (hf : IsOpenMap f) :
    IsOpenMap (g ∘ f) := fun s hs => by rw [image_comp]; exact hg _ (hf _ hs)

/--
theorem `of_comp` / 定理 `of_comp`

English:
theorem of_comp
  given: (hf : Continuous f) (f_surj : Surjective f) (h : IsOpenMap (g ∘ f))
  proof: fun s hs => by
  rw [← f_surj.image_preimage s]; rw [← image_comp]
  exact h _ (hs.preimage hf)

中文:
定理 of_comp
  条件: (hf : 连续 f) (f_surj : 满射 f) (h : 是开映射 (g ∘ f))
  证明: fun s hs => by
  rw [← f_surj.image_preimage s]; rw [← image_comp]
  exact h _ (hs.preimage hf)

Depends on / 依赖: f_surj, f_surj.image_preimage, hs.preimage, image_comp, image_preimage, preimage
-/
theorem of_comp (hf : Continuous f) (f_surj : Surjective f) (h : IsOpenMap (g ∘ f)) :
    IsOpenMap g := fun s hs => by
  rw [← f_surj.image_preimage s]; rw [← image_comp]
  exact h _ (hs.preimage hf)

/--
theorem `isOpen_range` / 定理 `isOpen_range`

English:
theorem isOpen_range
  given: (hf : IsOpenMap f)
  statement: IsOpen (range f)
  proof: by
  rw [← image_univ]
  exact hf _ isOpen_univ

中文:
定理 isOpen_range
  条件: (hf : 是开映射 f)
  结论: 是开集 (range f)
  证明: by
  rw [← image_univ]
  exact hf _ isOpen_univ

Depends on / 依赖: image_univ, isOpen_univ
-/
theorem isOpen_range (hf : IsOpenMap f) : IsOpen (range f) := by
  rw [← image_univ]
  exact hf _ isOpen_univ

/--
theorem `image_mem_nhds` / 定理 `image_mem_nhds`

English:
theorem image_mem_nhds
  given: (hf : IsOpenMap f) {x : X} {s : Set X} (hx : s in 𝓝 x)
  statement: f '' s in 𝓝 (f x)
  proof: let ⟨t, hts, ht, hxt⟩ := mem_nhds_iff.1 hx
  mem_of_superset (IsOpen.mem_nhds (hf t ht) (mem_image_of_mem _ hxt)) (image_mono hts)

中文:
定理 image_mem_nhds
  条件: (hf : 是开映射 f) {x : X} {s : 集合 X} (hx : s in 𝓝 x)
  结论: f '' s in 𝓝 (f x)
  证明: let ⟨t, hts, ht, hxt⟩ := mem_nhds_iff.1 hx
  mem_of_superset (IsOpen.mem_nhds (hf t ht) (mem_image_of_mem _ hxt)) (image_mono hts)

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, image_mono, mem_image_of_mem, mem_nhds, mem_nhds_iff, mem_of_superset
-/
theorem image_mem_nhds (hf : IsOpenMap f) {x : X} {s : Set X} (hx : s in 𝓝 x) : f '' s in 𝓝 (f x) :=
  let ⟨t, hts, ht, hxt⟩ := mem_nhds_iff.1 hx
  mem_of_superset (IsOpen.mem_nhds (hf t ht) (mem_image_of_mem _ hxt)) (image_mono hts)

/--
theorem `range_mem_nhds` / 定理 `range_mem_nhds`

English:
theorem range_mem_nhds
  given: (hf : IsOpenMap f) (x : X)
  statement: range f in 𝓝 (f x)
  proof: hf.isOpen_range.mem_nhds mem_range_self _

中文:
定理 range_mem_nhds
  条件: (hf : 是开映射 f) (x : X)
  结论: range f in 𝓝 (f x)
  证明: hf.isOpen_range.mem_nhds mem_range_self _

Depends on / 依赖: hf.isOpen_range.mem_nhds, isOpen_range, mem_nhds, mem_range_self
-/
theorem range_mem_nhds (hf : IsOpenMap f) (x : X) : range f in 𝓝 (f x) :=
hf.isOpen_range.mem_nhds mem_range_self _

/--
theorem `mapsTo_interior` / 定理 `mapsTo_interior`

English:
theorem mapsTo_interior
  given: (hf : IsOpenMap f) {s : Set X} {t : Set Y} (h : MapsTo f s t)
  proof: mapsTo_iff_image_subset.2
    interior_maximal (h.mono interior_subset Subset.rfl).image_subset (hf _ isOpen_interior)

中文:
定理 mapsTo_interior
  条件: (hf : 是开映射 f) {s : 集合 X} {t : 集合 Y} (h : 映射到 f s t)
  证明: mapsTo_iff_image_subset.2
    interior_maximal (h.mono interior_subset Subset.rfl).image_subset (hf _ isOpen_interior)

Depends on / 依赖: Subset, Subset.rfl, h.mono, image_subset, interior_maximal, interior_subset, isOpen_interior, mapsTo_iff_image_subset
-/
theorem mapsTo_interior (hf : IsOpenMap f) {s : Set X} {t : Set Y} (h : MapsTo f s t) :
    MapsTo f (interior s) (interior t) :=
mapsTo_iff_image_subset.2
    interior_maximal (h.mono interior_subset Subset.rfl).image_subset (hf _ isOpen_interior)

/--
theorem `image_interior_subset` / 定理 `image_interior_subset`

English:
theorem image_interior_subset
  given: (hf : IsOpenMap f) (s : Set X)
  proof: (hf.mapsTo_interior (mapsTo_image f s)).image_subset

中文:
定理 image_interior_subset
  条件: (hf : 是开映射 f) (s : 集合 X)
  证明: (hf.mapsTo_interior (mapsTo_image f s)).image_subset

Depends on / 依赖: hf.mapsTo_interior, image_subset, mapsTo_image, mapsTo_interior
-/
theorem image_interior_subset (hf : IsOpenMap f) (s : Set X) :
    f '' interior s subseteq interior (f '' s) :=
  (hf.mapsTo_interior (mapsTo_image f s)).image_subset

/--
theorem `nhds_le` / 定理 `nhds_le`

English:
theorem nhds_le
  given: (hf : IsOpenMap f) (x : X)
  statement: 𝓝 (f x) <= map f (𝓝 x)
  proof: le_map fun _ => hf.image_mem_nhds

中文:
定理 nhds_le
  条件: (hf : 是开映射 f) (x : X)
  结论: 𝓝 (f x) <= map f (𝓝 x)
  证明: le_map fun _ => hf.image_mem_nhds

Depends on / 依赖: hf.image_mem_nhds, image_mem_nhds, le_map
-/
theorem nhds_le (hf : IsOpenMap f) (x : X) : 𝓝 (f x) <= map f (𝓝 x) :=
  le_map fun _ => hf.image_mem_nhds

/--
theorem `map_nhds_eq` / 定理 `map_nhds_eq`

English:
theorem map_nhds_eq
  given: (hf : IsOpenMap f) {x : X} (hf' : ContinuousAt f x)
  statement: map f (𝓝 x) = 𝓝 (f x)
  proof: le_antisymm hf' (hf.nhds_le x)

中文:
定理 map_nhds_eq
  条件: (hf : 是开映射 f) {x : X} (hf' : ContinuousAt f x)
  结论: map f (𝓝 x) = 𝓝 (f x)
  证明: le_antisymm hf' (hf.nhds_le x)

Depends on / 依赖: hf.nhds_le, le_antisymm, nhds_le
-/
theorem map_nhds_eq (hf : IsOpenMap f) {x : X} (hf' : ContinuousAt f x) : map f (𝓝 x) = 𝓝 (f x) :=
  le_antisymm hf' (hf.nhds_le x)

/--
theorem `map_nhdsSet_eq` / 定理 `map_nhdsSet_eq`

English:
theorem map_nhdsSet_eq
  given: (hf : IsOpenMap f) (hf' : Continuous f) (s : Set X)
  proof: by
  rw [← biUnion_of_singleton s]
  simp_rw [image_iUnion, nhdsSet_iUnion, map_iSup, image_singleton, nhdsSet_singleton,
    hf.map_nhds_eq hf'.continuousAt]

中文:
定理 map_nhdsSet_eq
  条件: (hf : 是开映射 f) (hf' : 连续 f) (s : 集合 X)
  证明: by
  rw [← biUnion_of_singleton s]
  simp_rw [image_iUnion, nhdsSet_iUnion, map_iSup, image_singleton, nhdsSet_singleton,
    hf.map_nhds_eq hf'.continuousAt]

Depends on / 依赖: biUnion_of_singleton, continuousAt, hf.map_nhds_eq, image_iUnion, image_singleton, map_iSup, map_nhds_eq, nhdsSet_iUnion, nhdsSet_singleton, simp_rw
-/
theorem map_nhdsSet_eq (hf : IsOpenMap f) (hf' : Continuous f) (s : Set X) :
    map f (𝓝ˢ s) = 𝓝ˢ (f '' s) := by
  rw [← biUnion_of_singleton s]
  simp_rw [image_iUnion, nhdsSet_iUnion, map_iSup, image_singleton, nhdsSet_singleton,
    hf.map_nhds_eq hf'.continuousAt]

/--
theorem `of_nhds_le` / 定理 `of_nhds_le`

English:
theorem of_nhds_le
  given: (hf : forall x, 𝓝 (f x) <= map f (𝓝 x))
  statement: IsOpenMap f
  proof: fun _s hs =>
  isOpen_iff_mem_nhds.2 fun _y ⟨_x, hxs, hxy⟩ => hxy ▸ hf _ (image_mem_map <| hs.mem_nhds hxs)

中文:
定理 of_nhds_le
  条件: (hf : 对任意 x, 𝓝 (f x) <= map f (𝓝 x))
  结论: 是开映射 f
  证明: fun _s hs =>
  isOpen_iff_mem_nhds.2 fun _y ⟨_x, hxs, hxy⟩ => hxy ▸ hf _ (image_mem_map <| hs.mem_nhds hxs)
-/
theorem of_nhds_le (hf : forall x, 𝓝 (f x) <= map f (𝓝 x)) : IsOpenMap f := fun _s hs =>
  isOpen_iff_mem_nhds.2 fun _y ⟨_x, hxs, hxy⟩ => hxy ▸ hf _ (image_mem_map <| hs.mem_nhds hxs)

/--
theorem `of_sections` / 定理 `of_sections`

English:
theorem of_sections
  proof: of_nhds_le fun x =>
    let ⟨g, hgc, hgx, hgf⟩ := h x
    calc
      𝓝 (f x) = map f (map g (𝓝 (f x))) := by rw [map_map, hgf.comp_eq_id, map_id]
      _ <= map f (𝓝 (g (f x))) := map_mono hgc
      _ = map f (𝓝 x) := by rw [hgx]

中文:
定理 of_sections
  证明: of_nhds_le fun x =>
    let ⟨g, hgc, hgx, hgf⟩ := h x
    calc
      𝓝 (f x) = map f (map g (𝓝 (f x))) := by rw [map_map, hgf.comp_eq_id, map_id]
      _ <= map f (𝓝 (g (f x))) := map_mono hgc
      _ = map f (𝓝 x) := by rw [hgx]

Depends on / 依赖: comp_eq_id, hgf.comp_eq_id, map_id, map_map, map_mono, of_nhds_le
-/
theorem of_sections
    (h : forall x, exists g : Y -> X, ContinuousAt g (f x) ∧ g (f x) = x ∧ RightInverse g f) : IsOpenMap f :=
  of_nhds_le fun x =>
    let ⟨g, hgc, hgx, hgf⟩ := h x
    calc
      𝓝 (f x) = map f (map g (𝓝 (f x))) := by rw [map_map, hgf.comp_eq_id, map_id]
      _ <= map f (𝓝 (g (f x))) := map_mono hgc
      _ = map f (𝓝 x) := by rw [hgx]

/--
theorem `of_inverse` / 定理 `of_inverse`

English:
theorem of_inverse
  statement: {f' : Y -> X} (h : Continuous f') (l_inv : LeftInverse f f')
  proof: of_sections fun _ => ⟨f', h.continuousAt, r_inv _, l_inv⟩

中文:
定理 of_inverse
  结论: {f' : Y -> X} (h : 连续 f') (l_inv : 左逆 f f')
  证明: of_sections fun _ => ⟨f', h.continuousAt, r_inv _, l_inv⟩

Depends on / 依赖: continuousAt, h.continuousAt, l_inv, of_sections, r_inv
-/
theorem of_inverse {f' : Y -> X} (h : Continuous f') (l_inv : LeftInverse f f')
    (r_inv : RightInverse f f') : IsOpenMap f :=
  of_sections fun _ => ⟨f', h.continuousAt, r_inv _, l_inv⟩

/--
theorem `isQuotientMap` / 定理 `isQuotientMap`

English:
theorem isQuotientMap
  given: (open_map : IsOpenMap f) (cont : Continuous f) (surj : Surjective f)
  proof: by
  rw [isQuotientMap_iff]
  refine ⟨.of_isOpen_preimage_iff_isOpen fun s => ?_, surj⟩
  exact ⟨fun h => surj.image_preimage s ▸ open_map _ h, fun h => h.preimage cont⟩

中文:
定理 isQuotientMap
  条件: (open_map : 是开映射 f) (cont : 连续 f) (surj : 满射 f)
  证明: by
  rw [isQuotientMap_iff]
  refine ⟨.of_isOpen_preimage_iff_isOpen fun s => ?_, surj⟩
  exact ⟨fun h => surj.image_preimage s ▸ open_map _ h, fun h => h.preimage cont⟩

Depends on / 依赖: h.preimage, image_preimage, isQuotientMap_iff, of_isOpen_preimage_iff_isOpen, open_map, preimage, surj.image_preimage
-/
theorem isQuotientMap (open_map : IsOpenMap f) (cont : Continuous f) (surj : Surjective f) :
    IsQuotientMap f := by
  rw [isQuotientMap_iff]
  refine ⟨.of_isOpen_preimage_iff_isOpen fun s => ?_, surj⟩
  exact ⟨fun h => surj.image_preimage s ▸ open_map _ h, fun h => h.preimage cont⟩

/--
theorem `interior_preimage_subset_preimage_interior` / 定理 `interior_preimage_subset_preimage_interior`

English:
theorem interior_preimage_subset_preimage_interior
  given: (hf : IsOpenMap f) {s : Set Y}
  proof: hf.mapsTo_interior (mapsTo_preimage _ _)

中文:
定理 interior_preimage_subset_preimage_interior
  条件: (hf : 是开映射 f) {s : 集合 Y}
  证明: hf.mapsTo_interior (mapsTo_preimage _ _)

Depends on / 依赖: hf.mapsTo_interior, mapsTo_interior, mapsTo_preimage
-/
theorem interior_preimage_subset_preimage_interior (hf : IsOpenMap f) {s : Set Y} :
    interior (f ⁻¹' s) subseteq f ⁻¹' interior s :=
  hf.mapsTo_interior (mapsTo_preimage _ _)

/--
theorem `preimage_interior_eq_interior_preimage` / 定理 `preimage_interior_eq_interior_preimage`

English:
theorem preimage_interior_eq_interior_preimage
  statement: (hf₁ : IsOpenMap f) (hf₂ : Continuous f)
  proof: Subset.antisymm (preimage_interior_subset_interior_preimage hf₂)
    (interior_preimage_subset_preimage_interior hf₁)

中文:
定理 preimage_interior_eq_interior_preimage
  结论: (hf₁ : 是开映射 f) (hf₂ : 连续 f)
  证明: Subset.antisymm (preimage_interior_subset_interior_preimage hf₂)
    (interior_preimage_subset_preimage_interior hf₁)

Depends on / 依赖: Subset, Subset.antisymm, antisymm, interior_preimage_subset_preimage_interior, preimage_interior_subset_interior_preimage
-/
theorem preimage_interior_eq_interior_preimage (hf₁ : IsOpenMap f) (hf₂ : Continuous f)
    (s : Set Y) : f ⁻¹' interior s = interior (f ⁻¹' s) :=
  Subset.antisymm (preimage_interior_subset_interior_preimage hf₂)
    (interior_preimage_subset_preimage_interior hf₁)

/--
theorem `preimage_closure_subset_closure_preimage` / 定理 `preimage_closure_subset_closure_preimage`

English:
theorem preimage_closure_subset_closure_preimage
  given: (hf : IsOpenMap f) {s : Set Y}
  proof: by
  rw [← compl_subset_compl]
  simp only [← interior_compl, ← preimage_compl, hf.interior_preimage_subset_preimage_interior]

中文:
定理 preimage_closure_subset_closure_preimage
  条件: (hf : 是开映射 f) {s : 集合 Y}
  证明: by
  rw [← compl_subset_compl]
  simp only [← interior_compl, ← preimage_compl, hf.interior_preimage_subset_preimage_interior]

Depends on / 依赖: compl_subset_compl, hf.interior_preimage_subset_preimage_interior, interior_compl, interior_preimage_subset_preimage_interior, preimage_compl
-/
theorem preimage_closure_subset_closure_preimage (hf : IsOpenMap f) {s : Set Y} :
    f ⁻¹' closure s subseteq closure (f ⁻¹' s) := by
  rw [← compl_subset_compl]
  simp only [← interior_compl, ← preimage_compl, hf.interior_preimage_subset_preimage_interior]

/--
theorem `preimage_closure_eq_closure_preimage` / 定理 `preimage_closure_eq_closure_preimage`

English:
theorem preimage_closure_eq_closure_preimage
  given: (hf : IsOpenMap f) (hfc : Continuous f) (s : Set Y)
  proof: hf.preimage_closure_subset_closure_preimage.antisymm (hfc.closure_preimage_subset s)

中文:
定理 preimage_closure_eq_closure_preimage
  条件: (hf : 是开映射 f) (hfc : 连续 f) (s : 集合 Y)
  证明: hf.preimage_closure_subset_closure_preimage.antisymm (hfc.closure_preimage_subset s)

Depends on / 依赖: antisymm, closure_preimage_subset, hf.preimage_closure_subset_closure_preimage.antisymm, hfc.closure_preimage_subset, preimage_closure_subset_closure_preimage
-/
theorem preimage_closure_eq_closure_preimage (hf : IsOpenMap f) (hfc : Continuous f) (s : Set Y) :
    f ⁻¹' closure s = closure (f ⁻¹' s) :=
  hf.preimage_closure_subset_closure_preimage.antisymm (hfc.closure_preimage_subset s)

/--
lemma `preimage_closure_image` / 引理 `preimage_closure_image`

English:
lemma preimage_closure_image
  statement: (h₁ : IsOpenMap f) (h₂ : Function.Injective f)
  proof: by
  rw [h₁.preimage_closure_eq_closure_preimage h₃]; rw [Set.preimage_image_eq _ h₂]; rw [hs'.closure_eq]

中文:
引理 preimage_closure_image
  结论: (h₁ : 是开映射 f) (h₂ : 函数.单射 f)
  证明: by
  rw [h₁.preimage_closure_eq_closure_preimage h₃]; rw [Set.preimage_image_eq _ h₂]; rw [hs'.closure_eq]

Depends on / 依赖: Set.preimage_image_eq, closure_eq, preimage_closure_eq_closure_preimage, preimage_image_eq
-/
lemma preimage_closure_image (h₁ : IsOpenMap f) (h₂ : Function.Injective f)
    (h₃ : Continuous f) (s : Set X) (hs' : IsClosed s) : f ⁻¹' closure (f '' s) = s := by
  rw [h₁.preimage_closure_eq_closure_preimage h₃]; rw [Set.preimage_image_eq _ h₂]; rw [hs'.closure_eq]

/--
theorem `preimage_frontier_subset_frontier_preimage` / 定理 `preimage_frontier_subset_frontier_preimage`

English:
theorem preimage_frontier_subset_frontier_preimage
  given: (hf : IsOpenMap f) {s : Set Y}
  proof: by
  simpa only [frontier_eq_closure_inter_closure, preimage_inter] using!
    inter_subset_inter hf.preimage_closure_subset_closure_preimage
      hf.preimage_closure_subset_closure_preimage

中文:
定理 preimage_frontier_subset_frontier_preimage
  条件: (hf : 是开映射 f) {s : 集合 Y}
  证明: by
  simpa only [frontier_eq_closure_inter_closure, preimage_inter] using!
    inter_subset_inter hf.preimage_closure_subset_closure_preimage
      hf.preimage_closure_subset_closure_preimage

Depends on / 依赖: frontier_eq_closure_inter_closure, hf.preimage_closure_subset_closure_preimage, inter_subset_inter, preimage_closure_subset_closure_preimage, preimage_inter
-/
theorem preimage_frontier_subset_frontier_preimage (hf : IsOpenMap f) {s : Set Y} :
    f ⁻¹' frontier s subseteq frontier (f ⁻¹' s) := by
  simpa only [frontier_eq_closure_inter_closure, preimage_inter] using!
    inter_subset_inter hf.preimage_closure_subset_closure_preimage
      hf.preimage_closure_subset_closure_preimage

/--
theorem `preimage_frontier_eq_frontier_preimage` / 定理 `preimage_frontier_eq_frontier_preimage`

English:
theorem preimage_frontier_eq_frontier_preimage
  given: (hf : IsOpenMap f) (hfc : Continuous f) (s : Set Y)
  proof: by
  simp only [frontier_eq_closure_inter_closure, preimage_inter, preimage_compl,
    hf.preimage_closure_eq_closure_preimage hfc]

中文:
定理 preimage_frontier_eq_frontier_preimage
  条件: (hf : 是开映射 f) (hfc : 连续 f) (s : 集合 Y)
  证明: by
  simp only [frontier_eq_closure_inter_closure, preimage_inter, preimage_compl,
    hf.preimage_closure_eq_closure_preimage hfc]

Depends on / 依赖: frontier_eq_closure_inter_closure, hf.preimage_closure_eq_closure_preimage, preimage_closure_eq_closure_preimage, preimage_compl, preimage_inter
-/
theorem preimage_frontier_eq_frontier_preimage (hf : IsOpenMap f) (hfc : Continuous f) (s : Set Y) :
    f ⁻¹' frontier s = frontier (f ⁻¹' s) := by
  simp only [frontier_eq_closure_inter_closure, preimage_inter, preimage_compl,
    hf.preimage_closure_eq_closure_preimage hfc]

/--
theorem `of_isEmpty` / 定理 `of_isEmpty`

English:
theorem of_isEmpty
  given: [h : IsEmpty X] (f : X -> Y)
  statement: IsOpenMap f
  proof: of_nhds_le h.elim

中文:
定理 of_isEmpty
  条件: [h : 是空 X] (f : X -> Y)
  结论: 是开映射 f
  证明: of_nhds_le h.elim

Depends on / 依赖: h.elim, of_nhds_le
-/
theorem of_isEmpty [h : IsEmpty X] (f : X -> Y) : IsOpenMap f := of_nhds_le h.elim

/--
theorem `clusterPt_comap` / 定理 `clusterPt_comap`

English:
theorem clusterPt_comap
  given: (hf : IsOpenMap f) {x : X} {l : Filter Y} (h : ClusterPt (f x) l)
  proof: by
  rw [ClusterPt]; rw [← map_neBot_iff]; rw [Filter.push_pull]
exact h.neBot.mono inf_le_inf_right _ hf.nhds_le _

中文:
定理 clusterPt_comap
  条件: (hf : 是开映射 f) {x : X} {l : 滤子 Y} (h : ClusterPt (f x) l)
  证明: by
  rw [ClusterPt]; rw [← map_neBot_iff]; rw [Filter.push_pull]
exact h.neBot.mono inf_le_inf_right _ hf.nhds_le _

Depends on / 依赖: ClusterPt, Filter, Filter.push_pull, h.neBot.mono, hf.nhds_le, inf_le_inf_right, map_neBot_iff, nhds_le, push_pull
-/
theorem clusterPt_comap (hf : IsOpenMap f) {x : X} {l : Filter Y} (h : ClusterPt (f x) l) :
    ClusterPt x (comap f l) := by
  rw [ClusterPt]; rw [← map_neBot_iff]; rw [Filter.push_pull]
exact h.neBot.mono inf_le_inf_right _ hf.nhds_le _

/--
theorem `accPt_comap` / 定理 `accPt_comap`

English:
theorem accPt_comap
  given: (hf : IsOpenMap f) {x : X} {l : Filter Y} (h : AccPt (f x) l)
  proof: by
  rw [accPt_iff_clusterPt] at h ⊢
  apply (hf.clusterPt_comap h).mono
  rw [comap_inf]; rw [comap_principal]; rw [preimage_compl]
  exact inf_le_inf_right (comap f l) (by simp)

中文:
定理 accPt_comap
  条件: (hf : 是开映射 f) {x : X} {l : 滤子 Y} (h : 聚点 (f x) l)
  证明: by
  rw [accPt_iff_clusterPt] at h ⊢
  apply (hf.clusterPt_comap h).mono
  rw [comap_inf]; rw [comap_principal]; rw [preimage_compl]
  exact inf_le_inf_right (comap f l) (by simp)

Depends on / 依赖: accPt_iff_clusterPt, clusterPt_comap, comap_inf, comap_principal, hf.clusterPt_comap, inf_le_inf_right, preimage_compl
-/
theorem accPt_comap (hf : IsOpenMap f) {x : X} {l : Filter Y} (h : AccPt (f x) l) :
    AccPt x (comap f l) := by
  rw [accPt_iff_clusterPt] at h ⊢
  apply (hf.clusterPt_comap h).mono
  rw [comap_inf]; rw [comap_principal]; rw [preimage_compl]
  exact inf_le_inf_right (comap f l) (by simp)

/--
theorem `clusterPt_comap_iff` / 定理 `clusterPt_comap_iff`

English:
theorem clusterPt_comap_iff
  given: (hf : IsOpenMap f) (hfc : Continuous f) {x : X} {l : Filter Y}
  proof: ⟨fun h => h.map hfc.continuousAt tendsto_comap, hf.clusterPt_comap⟩

中文:
定理 clusterPt_comap_iff
  条件: (hf : 是开映射 f) (hfc : 连续 f) {x : X} {l : 滤子 Y}
  证明: ⟨fun h => h.map hfc.continuousAt tendsto_comap, hf.clusterPt_comap⟩

Depends on / 依赖: clusterPt_comap, continuousAt, h.map, hf.clusterPt_comap, hfc.continuousAt, tendsto_comap
-/
theorem clusterPt_comap_iff (hf : IsOpenMap f) (hfc : Continuous f) {x : X} {l : Filter Y} :
    ClusterPt x (comap f l) ↔ ClusterPt (f x) l :=
  ⟨fun h => h.map hfc.continuousAt tendsto_comap, hf.clusterPt_comap⟩

end IsOpenMap

/--
lemma `isOpenMap_iff_kernImage` / 引理 `isOpenMap_iff_kernImage`

English:
lemma isOpenMap_iff_kernImage
  proof: by
  rw [IsOpenMap]; rw [compl_surjective.forall]
  simp [kernImage_eq_compl]

中文:
引理 isOpenMap_iff_kernImage
  证明: by
  rw [IsOpenMap]; rw [compl_surjective.forall]
  simp [kernImage_eq_compl]

Depends on / 依赖: IsOpenMap, compl_surjective, compl_surjective.forall, kernImage_eq_compl
-/
lemma isOpenMap_iff_kernImage :
    IsOpenMap f ↔ forall {u : Set X}, IsClosed u -> IsClosed (kernImage f u) := by
  rw [IsOpenMap]; rw [compl_surjective.forall]
  simp [kernImage_eq_compl]

/--
theorem `isOpenMap_iff_nhds_le` / 定理 `isOpenMap_iff_nhds_le`

English:
theorem isOpenMap_iff_nhds_le
  statement: IsOpenMap f ↔ forall x : X, 𝓝 (f x) <= (𝓝 x).map f
  proof: ⟨fun hf => hf.nhds_le, IsOpenMap.of_nhds_le⟩

中文:
定理 isOpenMap_iff_nhds_le
  结论: 是开映射 f ↔ 对任意 x : X, 𝓝 (f x) <= (𝓝 x).map f
  证明: ⟨fun hf => hf.nhds_le, IsOpenMap.of_nhds_le⟩

Depends on / 依赖: IsOpenMap, IsOpenMap.of_nhds_le, hf.nhds_le, nhds_le, of_nhds_le
-/
theorem isOpenMap_iff_nhds_le : IsOpenMap f ↔ forall x : X, 𝓝 (f x) <= (𝓝 x).map f :=
  ⟨fun hf => hf.nhds_le, IsOpenMap.of_nhds_le⟩

/--
theorem `isOpenMap_iff_clusterPt_comap` / 定理 `isOpenMap_iff_clusterPt_comap`

English:
theorem isOpenMap_iff_clusterPt_comap
  proof: by
  refine ⟨fun hf _ _ => hf.clusterPt_comap, fun h => ?_⟩
  simp only [isOpenMap_iff_nhds_le, le_map_iff]
  intro x s hs
  contrapose hs
  rw [← mem_interior_iff_mem_nhds]; rw [mem_interior_iff_not_clusterPt_compl]; rw [not_not] at hs ⊢
exact (h _ _ hs).mono by simp [subset_preimage_image]

中文:
定理 isOpenMap_iff_clusterPt_comap
  证明: by
  refine ⟨fun hf _ _ => hf.clusterPt_comap, fun h => ?_⟩
  simp only [isOpenMap_iff_nhds_le, le_map_iff]
  intro x s hs
  contrapose hs
  rw [← mem_interior_iff_mem_nhds]; rw [mem_interior_iff_not_clusterPt_compl]; rw [not_not] at hs ⊢
exact (h _ _ hs).mono by simp [subset_preimage_image]

Depends on / 依赖: clusterPt_comap, contrapose, hf.clusterPt_comap, isOpenMap_iff_nhds_le, le_map_iff, mem_interior_iff_mem_nhds, mem_interior_iff_not_clusterPt_compl, not_not, subset_preimage_image
-/
theorem isOpenMap_iff_clusterPt_comap :
    IsOpenMap f ↔ forall x l, ClusterPt (f x) l -> ClusterPt x (comap f l) := by
  refine ⟨fun hf _ _ => hf.clusterPt_comap, fun h => ?_⟩
  simp only [isOpenMap_iff_nhds_le, le_map_iff]
  intro x s hs
  contrapose hs
  rw [← mem_interior_iff_mem_nhds]; rw [mem_interior_iff_not_clusterPt_compl]; rw [not_not] at hs ⊢
exact (h _ _ hs).mono by simp [subset_preimage_image]

/--
theorem `isOpenMap_iff_image_interior` / 定理 `isOpenMap_iff_image_interior`

English:
theorem isOpenMap_iff_image_interior
  statement: IsOpenMap f ↔ forall s, f '' interior s subseteq interior (f '' s)
  proof: ⟨IsOpenMap.image_interior_subset, fun hs u hu =>
subset_interior_iff_isOpen.mp by simpa only [hu.interior_eq] using hs u⟩

中文:
定理 isOpenMap_iff_image_interior
  结论: 是开映射 f ↔ 对任意 s, f '' interior s subseteq interior (f '' s)
  证明: ⟨IsOpenMap.image_interior_subset, fun hs u hu =>
subset_interior_iff_isOpen.mp by simpa only [hu.interior_eq] using hs u⟩

Depends on / 依赖: IsOpenMap, IsOpenMap.image_interior_subset, hu.interior_eq, image_interior_subset, interior_eq, subset_interior_iff_isOpen, subset_interior_iff_isOpen.mp
-/
theorem isOpenMap_iff_image_interior : IsOpenMap f ↔ forall s, f '' interior s subseteq interior (f '' s) :=
  ⟨IsOpenMap.image_interior_subset, fun hs u hu =>
subset_interior_iff_isOpen.mp by simpa only [hu.interior_eq] using hs u⟩

/--
lemma `isOpenMap_iff_closure_kernImage` / 引理 `isOpenMap_iff_closure_kernImage`

English:
lemma isOpenMap_iff_closure_kernImage
  proof: by
  rw [isOpenMap_iff_image_interior]; rw [compl_surjective.forall]
  simp [kernImage_eq_compl]

中文:
引理 isOpenMap_iff_closure_kernImage
  证明: by
  rw [isOpenMap_iff_image_interior]; rw [compl_surjective.forall]
  simp [kernImage_eq_compl]

Depends on / 依赖: compl_surjective, compl_surjective.forall, isOpenMap_iff_image_interior, kernImage_eq_compl
-/
lemma isOpenMap_iff_closure_kernImage :
    IsOpenMap f ↔ forall {s : Set X}, closure (kernImage f s) subseteq kernImage f (closure s) := by
  rw [isOpenMap_iff_image_interior]; rw [compl_surjective.forall]
  simp [kernImage_eq_compl]

/--
lemma `Topology.IsInducing.isOpenMap` / 引理 `Topology.IsInducing.isOpenMap`

English:
lemma Topology.IsInducing.isOpenMap
  given: (hi : IsInducing f) (ho : IsOpen (range f))
  proof: IsOpenMap.of_nhds_le fun _ => (hi.map_nhds_of_mem _ <| IsOpen.mem_nhds ho <| mem_range_self _).ge

中文:
引理 拓扑.是Inducing.isOpenMap
  条件: (hi : 是Inducing f) (ho : 是开集 (range f))
  证明: IsOpenMap.of_nhds_le fun _ => (hi.map_nhds_of_mem _ <| IsOpen.mem_nhds ho <| mem_range_self _).ge
-/
protected lemma Topology.IsInducing.isOpenMap (hi : IsInducing f) (ho : IsOpen (range f)) :
    IsOpenMap f :=
  IsOpenMap.of_nhds_le fun _ => (hi.map_nhds_of_mem _ <| IsOpen.mem_nhds ho <| mem_range_self _).ge

/--
theorem `Dense.preimage` / 定理 `Dense.preimage`

English:
theorem Dense.preimage
  given: {s : Set Y} (hs : Dense s) (hf : IsOpenMap f)
  proof: fun x =>
hf.preimage_closure_subset_closure_preimage hs (f x)

中文:
定理 稠密.原像
  条件: {s : 集合 Y} (hs : 稠密 s) (hf : 是开映射 f)
  证明: fun x =>
hf.preimage_closure_subset_closure_preimage hs (f x)
-/
protected theorem Dense.preimage {s : Set Y} (hs : Dense s) (hf : IsOpenMap f) :
    Dense (f ⁻¹' s) := fun x =>
hf.preimage_closure_subset_closure_preimage hs (f x)

end OpenMap

section IsClosedMap

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace IsClosedMap
open Function

/--
theorem `id` / 定理 `id`

English:
theorem id
  statement: IsClosedMap (@id X)
  proof: fun s hs => by rwa [image_id]

中文:
定理 id
  结论: 是闭映射 (@id X)
  证明: fun s hs => by rwa [image_id]
-/
protected theorem id : IsClosedMap (@id X) := fun s hs => by rwa [image_id]

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: (hg : IsClosedMap g) (hf : IsClosedMap f)
  statement: IsClosedMap (g ∘ f)
  proof: by
  intro s hs
  rw [image_comp]
  exact hg _ (hf _ hs)

中文:
定理 comp
  条件: (hg : 是闭映射 g) (hf : 是闭映射 f)
  结论: 是闭映射 (g ∘ f)
  证明: by
  intro s hs
  rw [image_comp]
  exact hg _ (hf _ hs)
-/
protected theorem comp (hg : IsClosedMap g) (hf : IsClosedMap f) : IsClosedMap (g ∘ f) := by
  intro s hs
  rw [image_comp]
  exact hg _ (hf _ hs)

/--
theorem `of_comp_surjective` / 定理 `of_comp_surjective`

English:
theorem of_comp_surjective
  statement: (hf : Surjective f) (hf' : Continuous f)
  proof: by
  intro K hK
  rw [← image_preimage_eq K hf]; rw [← image_comp]
  exact hfg _ (hK.preimage hf')

中文:
定理 of_comp_surjective
  结论: (hf : 满射 f) (hf' : 连续 f)
  证明: by
  intro K hK
  rw [← image_preimage_eq K hf]; rw [← image_comp]
  exact hfg _ (hK.preimage hf')
-/
protected theorem of_comp_surjective (hf : Surjective f) (hf' : Continuous f)
    (hfg : IsClosedMap (g ∘ f)) : IsClosedMap g := by
  intro K hK
  rw [← image_preimage_eq K hf]; rw [← image_comp]
  exact hfg _ (hK.preimage hf')

/--
theorem `closure_image_subset` / 定理 `closure_image_subset`

English:
theorem closure_image_subset
  given: (hf : IsClosedMap f) (s : Set X)
  proof: closure_minimal (image_mono subset_closure) (hf _ isClosed_closure)

中文:
定理 closure_image_subset
  条件: (hf : 是闭映射 f) (s : 集合 X)
  证明: closure_minimal (image_mono subset_closure) (hf _ isClosed_closure)

Depends on / 依赖: closure_minimal, image_mono, isClosed_closure, subset_closure
-/
theorem closure_image_subset (hf : IsClosedMap f) (s : Set X) :
    closure (f '' s) subseteq f '' closure s :=
  closure_minimal (image_mono subset_closure) (hf _ isClosed_closure)

/--
theorem `of_inverse` / 定理 `of_inverse`

English:
theorem of_inverse
  statement: {f' : Y -> X} (h : Continuous f') (l_inv : LeftInverse f f')
  proof: fun s hs => by
  rw [image_eq_preimage_of_inverse r_inv l_inv]
  exact hs.preimage h

中文:
定理 of_inverse
  结论: {f' : Y -> X} (h : 连续 f') (l_inv : 左逆 f f')
  证明: fun s hs => by
  rw [image_eq_preimage_of_inverse r_inv l_inv]
  exact hs.preimage h

Depends on / 依赖: hs.preimage, image_eq_preimage_of_inverse, l_inv, preimage, r_inv
-/
theorem of_inverse {f' : Y -> X} (h : Continuous f') (l_inv : LeftInverse f f')
    (r_inv : RightInverse f f') : IsClosedMap f := fun s hs => by
  rw [image_eq_preimage_of_inverse r_inv l_inv]
  exact hs.preimage h

/--
theorem `of_nonempty` / 定理 `of_nonempty`

English:
theorem of_nonempty
  given: (h : forall s, IsClosed s -> s.Nonempty -> IsClosed (f '' s))
  proof: by
  intro s hs; rcases eq_empty_or_nonempty s with h2s | h2s
  · simp_rw [h2s, image_empty, isClosed_empty]
  · exact h s hs h2s

中文:
定理 of_nonempty
  条件: (h : 对任意 s, 是闭集 s -> s.非空 -> 是闭集 (f '' s))
  证明: by
  intro s hs; rcases eq_empty_or_nonempty s with h2s | h2s
  · simp_rw [h2s, image_empty, isClosed_empty]
  · exact h s hs h2s

Depends on / 依赖: eq_empty_or_nonempty, image_empty, isClosed_empty, simp_rw
-/
theorem of_nonempty (h : forall s, IsClosed s -> s.Nonempty -> IsClosed (f '' s)) :
    IsClosedMap f := by
  intro s hs; rcases eq_empty_or_nonempty s with h2s | h2s
  · simp_rw [h2s, image_empty, isClosed_empty]
  · exact h s hs h2s

/--
theorem `isClosed_range` / 定理 `isClosed_range`

English:
theorem isClosed_range
  given: (hf : IsClosedMap f)
  statement: IsClosed (range f)
  proof: @image_univ _ _ f ▸ hf _ isClosed_univ

中文:
定理 isClosed_range
  条件: (hf : 是闭映射 f)
  结论: 是闭集 (range f)
  证明: @image_univ _ _ f ▸ hf _ isClosed_univ

Depends on / 依赖: image_univ, isClosed_univ
-/
theorem isClosed_range (hf : IsClosedMap f) : IsClosed (range f) :=
  @image_univ _ _ f ▸ hf _ isClosed_univ


/--
theorem `isQuotientMap` / 定理 `isQuotientMap`

English:
theorem isQuotientMap
  statement: (hcl : IsClosedMap f) (hcont : Continuous f)
  proof: isQuotientMap_iff_isClosed.2 ⟨hsurj, fun s =>
    ⟨fun hs => hs.preimage hcont, fun hs => hsurj.image_preimage s ▸ hcl _ hs⟩⟩

中文:
定理 isQuotientMap
  结论: (hcl : 是闭映射 f) (hcont : 连续 f)
  证明: isQuotientMap_iff_isClosed.2 ⟨hsurj, fun s =>
    ⟨fun hs => hs.preimage hcont, fun hs => hsurj.image_preimage s ▸ hcl _ hs⟩⟩

Depends on / 依赖: hs.preimage, hsurj.image_preimage, image_preimage, isQuotientMap_iff_isClosed, preimage
-/
theorem isQuotientMap (hcl : IsClosedMap f) (hcont : Continuous f)
    (hsurj : Surjective f) : IsQuotientMap f :=
  isQuotientMap_iff_isClosed.2 ⟨hsurj, fun s =>
    ⟨fun hs => hs.preimage hcont, fun hs => hsurj.image_preimage s ▸ hcl _ hs⟩⟩

end IsClosedMap

/--
lemma `isClosedMap_iff_kernImage` / 引理 `isClosedMap_iff_kernImage`

English:
lemma isClosedMap_iff_kernImage
  proof: by
  rw [IsClosedMap]; rw [compl_surjective.forall]
  simp [kernImage_eq_compl]

中文:
引理 isClosedMap_iff_kernImage
  证明: by
  rw [IsClosedMap]; rw [compl_surjective.forall]
  simp [kernImage_eq_compl]

Depends on / 依赖: IsClosedMap, compl_surjective, compl_surjective.forall, kernImage_eq_compl
-/
lemma isClosedMap_iff_kernImage :
    IsClosedMap f ↔ forall {u : Set X}, IsOpen u -> IsOpen (kernImage f u) := by
  rw [IsClosedMap]; rw [compl_surjective.forall]
  simp [kernImage_eq_compl]

/--
lemma `Topology.IsInducing.isClosedMap` / 引理 `Topology.IsInducing.isClosedMap`

English:
lemma Topology.IsInducing.isClosedMap
  given: (hf : IsInducing f) (h : IsClosed (range f))
  proof: by
  intro s hs
  rcases hf.isClosed_iff.1 hs with ⟨t, ht, rfl⟩
  rw [image_preimage_eq_inter_range]
  exact ht.inter h

中文:
引理 拓扑.是Inducing.isClosedMap
  条件: (hf : 是Inducing f) (h : 是闭集 (range f))
  证明: by
  intro s hs
  rcases hf.isClosed_iff.1 hs with ⟨t, ht, rfl⟩
  rw [image_preimage_eq_inter_range]
  exact ht.inter h

Depends on / 依赖: hf.isClosed_iff, ht.inter, image_preimage_eq_inter_range, isClosed_iff
-/
lemma Topology.IsInducing.isClosedMap (hf : IsInducing f) (h : IsClosed (range f)) :
    IsClosedMap f := by
  intro s hs
  rcases hf.isClosed_iff.1 hs with ⟨t, ht, rfl⟩
  rw [image_preimage_eq_inter_range]
  exact ht.inter h

/--
theorem `isClosedMap_iff_closure_image` / 定理 `isClosedMap_iff_closure_image`

English:
theorem isClosedMap_iff_closure_image
  proof: ⟨IsClosedMap.closure_image_subset, fun hs c hc =>
isClosed_of_closure_subset
      calc
        closure (f '' c) subseteq f '' closure c := hs c
        _ = f '' c := by rw [hc.closure_eq]⟩

中文:
定理 isClosedMap_iff_closure_image
  证明: ⟨IsClosedMap.closure_image_subset, fun hs c hc =>
isClosed_of_closure_subset
      calc
        closure (f '' c) subseteq f '' closure c := hs c
        _ = f '' c := by rw [hc.closure_eq]⟩

Depends on / 依赖: IsClosedMap, IsClosedMap.closure_image_subset, closure, closure_eq, closure_image_subset, hc.closure_eq, isClosed_of_closure_subset, subseteq
-/
theorem isClosedMap_iff_closure_image :
    IsClosedMap f ↔ forall s, closure (f '' s) subseteq f '' closure s :=
  ⟨IsClosedMap.closure_image_subset, fun hs c hc =>
isClosed_of_closure_subset
      calc
        closure (f '' c) subseteq f '' closure c := hs c
        _ = f '' c := by rw [hc.closure_eq]⟩

/--
theorem `isClosedMap_iff_kernImage_interior` / 定理 `isClosedMap_iff_kernImage_interior`

English:
theorem isClosedMap_iff_kernImage_interior
  proof: by
  rw [isClosedMap_iff_closure_image]; rw [compl_surjective.forall]
  simp [kernImage_eq_compl]

中文:
定理 isClosedMap_iff_kernImage_interior
  证明: by
  rw [isClosedMap_iff_closure_image]; rw [compl_surjective.forall]
  simp [kernImage_eq_compl]

Depends on / 依赖: compl_surjective, compl_surjective.forall, isClosedMap_iff_closure_image, kernImage_eq_compl
-/
theorem isClosedMap_iff_kernImage_interior :
    IsClosedMap f ↔ forall {s : Set X}, kernImage f (interior s) subseteq interior (kernImage f s) := by
  rw [isClosedMap_iff_closure_image]; rw [compl_surjective.forall]
  simp [kernImage_eq_compl]

/--
theorem `isClosedMap_iff_clusterPt` / 定理 `isClosedMap_iff_clusterPt`

English:
theorem isClosedMap_iff_clusterPt
  proof: by
  simp [MapClusterPt, isClosedMap_iff_closure_image, subset_def, mem_closure_iff_clusterPt,
    and_comm]

中文:
定理 isClosedMap_iff_clusterPt
  证明: by
  simp [MapClusterPt, isClosedMap_iff_closure_image, subset_def, mem_closure_iff_clusterPt,
    and_comm]

Depends on / 依赖: MapClusterPt, and_comm, isClosedMap_iff_closure_image, mem_closure_iff_clusterPt, subset_def
-/
theorem isClosedMap_iff_clusterPt :
    IsClosedMap f ↔ forall s y, MapClusterPt y (𝓟 s) f -> exists x, f x = y ∧ ClusterPt x (𝓟 s) := by
  simp [MapClusterPt, isClosedMap_iff_closure_image, subset_def, mem_closure_iff_clusterPt,
    and_comm]

/--
theorem `isClosedMap_iff_comap_nhdsSet_le` / 定理 `isClosedMap_iff_comap_nhdsSet_le`

English:
theorem isClosedMap_iff_comap_nhdsSet_le
  proof: by
  simp_rw [Filter.le_def, mem_comap'', ← subset_interior_iff_mem_nhdsSet,
    ← subset_kernImage_iff, isClosedMap_iff_kernImage_interior]
  exact ⟨fun H s t hst => hst.trans H, fun H s => H _ subset_rfl⟩

alias ⟨IsClosedMap.comap_nhdsSet_le, _⟩ := isClosedMap_iff_comap_nhdsSet_le

中文:
定理 isClosedMap_iff_comap_nhdsSet_le
  证明: by
  simp_rw [Filter.le_def, mem_comap'', ← subset_interior_iff_mem_nhdsSet,
    ← subset_kernImage_iff, isClosedMap_iff_kernImage_interior]
  exact ⟨fun H s t hst => hst.trans H, fun H s => H _ subset_rfl⟩

alias ⟨IsClosedMap.comap_nhdsSet_le, _⟩ := isClosedMap_iff_comap_nhdsSet_le

Depends on / 依赖: Filter, Filter.le_def, hst.trans, isClosedMap_iff_kernImage_interior, le_def, mem_comap, simp_rw, subset_interior_iff_mem_nhdsSet, subset_kernImage_iff, subset_rfl
-/
theorem isClosedMap_iff_comap_nhdsSet_le :
    IsClosedMap f ↔ forall {s : Set Y}, comap f (𝓝ˢ s) <= 𝓝ˢ (f ⁻¹' s) := by
  simp_rw [Filter.le_def, mem_comap'', ← subset_interior_iff_mem_nhdsSet,
    ← subset_kernImage_iff, isClosedMap_iff_kernImage_interior]
  exact ⟨fun H s t hst => hst.trans H, fun H s => H _ subset_rfl⟩

alias ⟨IsClosedMap.comap_nhdsSet_le, _⟩ := isClosedMap_iff_comap_nhdsSet_le

/--
theorem `isClosedMap_iff_comap_nhds_le` / 定理 `isClosedMap_iff_comap_nhds_le`

English:
theorem isClosedMap_iff_comap_nhds_le
  proof: by
  rw [isClosedMap_iff_comap_nhdsSet_le]
  constructor
  · exact fun H y => nhdsSet_singleton (x := y) ▸ H
  · intro H s
    rw [← Set.biUnion_of_singleton s]
    simp_rw [preimage_iUnion, nhdsSet_iUnion, comap_iSup, nhdsSet_singleton]
    exact iSup₂_mono fun _ _ => H

alias ⟨IsClosedMap.comap_nh

中文:
定理 isClosedMap_iff_comap_nhds_le
  证明: by
  rw [isClosedMap_iff_comap_nhdsSet_le]
  constructor
  · exact fun H y => nhdsSet_singleton (x := y) ▸ H
  · intro H s
    rw [← Set.biUnion_of_singleton s]
    simp_rw [preimage_iUnion, nhdsSet_iUnion, comap_iSup, nhdsSet_singleton]
    exact iSup₂_mono fun _ _ => H

alias ⟨IsClosedMap.comap_nh

Depends on / 依赖: Set.biUnion_of_singleton, biUnion_of_singleton, comap_iSup, isClosedMap_iff_comap_nhdsSet_le, nhdsSet_iUnion, nhdsSet_singleton, preimage_iUnion, simp_rw
-/
theorem isClosedMap_iff_comap_nhds_le :
    IsClosedMap f ↔ forall {y : Y}, comap f (𝓝 y) <= 𝓝ˢ (f ⁻¹' {y}) := by
  rw [isClosedMap_iff_comap_nhdsSet_le]
  constructor
  · exact fun H y => nhdsSet_singleton (x := y) ▸ H
  · intro H s
    rw [← Set.biUnion_of_singleton s]
    simp_rw [preimage_iUnion, nhdsSet_iUnion, comap_iSup, nhdsSet_singleton]
    exact iSup₂_mono fun _ _ => H

alias ⟨IsClosedMap.comap_nhds_le, _⟩ := isClosedMap_iff_comap_nhds_le

/--
theorem `IsClosedMap.comap_nhds_eq` / 定理 `IsClosedMap.comap_nhds_eq`

English:
theorem IsClosedMap.comap_nhds_eq
  given: (hf : IsClosedMap f) (hf' : Continuous f) (y : Y)
  proof: le_antisymm (isClosedMap_iff_comap_nhds_le.mp hf)
  -- Note: below should be an application of `Continuous.tendsto_nhdsSet_nhds`, but this is only
  -- proven later...
    (nhdsSet_le.mpr fun x hx => hx ▸ (hf'.tendsto x).le_comap)

中文:
定理 是闭映射.comap_nhds_eq
  条件: (hf : 是闭映射 f) (hf' : 连续 f) (y : Y)
  证明: le_antisymm (isClosedMap_iff_comap_nhds_le.mp hf)
  -- Note: below should be an application of `Continuous.tendsto_nhdsSet_nhds`, but this is only
  -- proven later...
    (nhdsSet_le.mpr fun x hx => hx ▸ (hf'.tendsto x).le_comap)

Depends on / 依赖: isClosedMap_iff_comap_nhds_le, isClosedMap_iff_comap_nhds_le.mp, le_antisymm
-/
theorem IsClosedMap.comap_nhds_eq (hf : IsClosedMap f) (hf' : Continuous f) (y : Y) :
    comap f (𝓝 y) = 𝓝ˢ (f ⁻¹' {y}) :=
  le_antisymm (isClosedMap_iff_comap_nhds_le.mp hf)
  -- Note: below should be an application of `Continuous.tendsto_nhdsSet_nhds`, but this is only
  -- proven later...
    (nhdsSet_le.mpr fun x hx => hx ▸ (hf'.tendsto x).le_comap)

/--
theorem `IsClosedMap.comap_nhdsSet_eq` / 定理 `IsClosedMap.comap_nhdsSet_eq`

English:
theorem IsClosedMap.comap_nhdsSet_eq
  given: (hf : IsClosedMap f) (hf' : Continuous f) (s : Set Y)
  proof: le_antisymm (isClosedMap_iff_comap_nhdsSet_le.mp hf)
  -- Note: below should be an application of `Continuous.tendsto_nhdsSet_nhdsSet`, but this is only
  -- proven later...
    (nhdsSet_le.mpr fun x hx => (hf'.tendsto x).le_comap.trans (comap_mono (nhds_le_nhdsSet hx)))

中文:
定理 是闭映射.comap_nhdsSet_eq
  条件: (hf : 是闭映射 f) (hf' : 连续 f) (s : 集合 Y)
  证明: le_antisymm (isClosedMap_iff_comap_nhdsSet_le.mp hf)
  -- Note: below should be an application of `Continuous.tendsto_nhdsSet_nhdsSet`, but this is only
  -- proven later...
    (nhdsSet_le.mpr fun x hx => (hf'.tendsto x).le_comap.trans (comap_mono (nhds_le_nhdsSet hx)))

Depends on / 依赖: isClosedMap_iff_comap_nhdsSet_le, isClosedMap_iff_comap_nhdsSet_le.mp, le_antisymm
-/
theorem IsClosedMap.comap_nhdsSet_eq (hf : IsClosedMap f) (hf' : Continuous f) (s : Set Y) :
    comap f (𝓝ˢ s) = 𝓝ˢ (f ⁻¹' s) :=
  le_antisymm (isClosedMap_iff_comap_nhdsSet_le.mp hf)
  -- Note: below should be an application of `Continuous.tendsto_nhdsSet_nhdsSet`, but this is only
  -- proven later...
    (nhdsSet_le.mpr fun x hx => (hf'.tendsto x).le_comap.trans (comap_mono (nhds_le_nhdsSet hx)))

/--
theorem `IsClosedMap.eventually_nhds_fiber` / 定理 `IsClosedMap.eventually_nhds_fiber`

English:
theorem IsClosedMap.eventually_nhds_fiber
  statement: (hf : IsClosedMap f) {p : X -> Prop} (y₀ : Y)
  proof: by
  rw [← eventually_nhdsSet_iff_forall] at H
  replace H := H.filter_mono hf.comap_nhds_le
  rwa [eventually_comap] at H

中文:
定理 是闭映射.eventually_nhds_fiber
  结论: (hf : 是闭映射 f) {p : X -> 命题} (y₀ : Y)
  证明: by
  rw [← eventually_nhdsSet_iff_forall] at H
  replace H := H.filter_mono hf.comap_nhds_le
  rwa [eventually_comap] at H

Depends on / 依赖: H.filter_mono, comap_nhds_le, eventually_comap, eventually_nhdsSet_iff_forall, filter_mono, hf.comap_nhds_le, replace
-/
theorem IsClosedMap.eventually_nhds_fiber (hf : IsClosedMap f) {p : X -> Prop} (y₀ : Y)
    (H : forall x₀ in f ⁻¹' {y₀}, forallᶠ x in 𝓝 x₀, p x) :
    forallᶠ y in 𝓝 y₀, forall x in f ⁻¹' {y}, p x := by
  rw [← eventually_nhdsSet_iff_forall] at H
  replace H := H.filter_mono hf.comap_nhds_le
  rwa [eventually_comap] at H

/--
theorem `IsClosedMap.frequently_nhds_fiber` / 定理 `IsClosedMap.frequently_nhds_fiber`

English:
theorem IsClosedMap.frequently_nhds_fiber
  statement: (hf : IsClosedMap f) {p : X -> Prop} (y₀ : Y)
  proof: by
  /-
  Note: this result could also be seen as a reformulation of `isClosedMap_iff_clusterPt`.
  One would then be able to deduce the `eventually` statement,
  and then go back to `isClosedMap_iff_comap_nhdsSet_le`.
  Ultimately, this makes no difference.
  -/
  contrapose! H
  exact hf.eventuall

中文:
定理 是闭映射.frequently_nhds_fiber
  结论: (hf : 是闭映射 f) {p : X -> 命题} (y₀ : Y)
  证明: by
  /-
  Note: this result could also be seen as a reformulation of `isClosedMap_iff_clusterPt`.
  One would then be able to deduce the `eventually` statement,
  and then go back to `isClosedMap_iff_comap_nhdsSet_le`.
  Ultimately, this makes no difference.
  -/
  contrapose! H
  exact hf.eventuall
-/
theorem IsClosedMap.frequently_nhds_fiber (hf : IsClosedMap f) {p : X -> Prop} (y₀ : Y)
    (H : existsᶠ y in 𝓝 y₀, exists x in f ⁻¹' {y}, p x) :
    exists x₀ in f ⁻¹' {y₀}, existsᶠ x in 𝓝 x₀, p x := by
  /-
  Note: this result could also be seen as a reformulation of `isClosedMap_iff_clusterPt`.
  One would then be able to deduce the `eventually` statement,
  and then go back to `isClosedMap_iff_comap_nhdsSet_le`.
  Ultimately, this makes no difference.
  -/
  contrapose! H
  exact hf.eventually_nhds_fiber y₀ H

/--
theorem `IsClosedMap.closure_image_eq_of_continuous` / 定理 `IsClosedMap.closure_image_eq_of_continuous`

English:
theorem IsClosedMap.closure_image_eq_of_continuous
  proof: subset_antisymm (f_closed.closure_image_subset s) (image_closure_subset_closure_image f_cont)

中文:
定理 是闭映射.closure_image_eq_of_continuous
  证明: subset_antisymm (f_closed.closure_image_subset s) (image_closure_subset_closure_image f_cont)

Depends on / 依赖: closure_image_subset, f_closed, f_closed.closure_image_subset, f_cont, image_closure_subset_closure_image, subset_antisymm
-/
theorem IsClosedMap.closure_image_eq_of_continuous
    (f_closed : IsClosedMap f) (f_cont : Continuous f) (s : Set X) :
    closure (f '' s) = f '' closure s :=
  subset_antisymm (f_closed.closure_image_subset s) (image_closure_subset_closure_image f_cont)

/--
theorem `IsClosedMap.lift'_closure_map_eq` / 定理 `IsClosedMap.lift'_closure_map_eq`

English:
theorem IsClosedMap.lift'_closure_map_eq
  proof: by
  rw [map_lift'_eq2 (monotone_closure Y)]; rw [map_lift'_eq (monotone_closure X)]
  congr 1
  ext s : 1
  exact f_closed.closure_image_eq_of_continuous f_cont s

中文:
定理 是闭映射.lift'_closure_map_eq
  证明: by
  rw [map_lift'_eq2 (monotone_closure Y)]; rw [map_lift'_eq (monotone_closure X)]
  congr 1
  ext s : 1
  exact f_closed.closure_image_eq_of_continuous f_cont s

Depends on / 依赖: _eq2, closure_image_eq_of_continuous, f_closed, f_closed.closure_image_eq_of_continuous, f_cont, map_lift, monotone_closure
-/
theorem IsClosedMap.lift'_closure_map_eq
    (f_closed : IsClosedMap f) (f_cont : Continuous f) (F : Filter X) :
    (map f F).lift' closure = map f (F.lift' closure) := by
  rw [map_lift'_eq2 (monotone_closure Y)]; rw [map_lift'_eq (monotone_closure X)]
  congr 1
  ext s : 1
  exact f_closed.closure_image_eq_of_continuous f_cont s

/--
theorem `IsClosedMap.mapClusterPt_iff_lift'_closure` / 定理 `IsClosedMap.mapClusterPt_iff_lift'_closure`

English:
theorem IsClosedMap.mapClusterPt_iff_lift'_closure
  proof: by
  rw [MapClusterPt]; rw [clusterPt_iff_lift'_closure']; rw [f_closed.lift'_closure_map_eq f_cont]; rw [← comap_principal]; rw [← map_neBot_iff f]; rw [Filter.push_pull]; rw [principal_singleton]

中文:
定理 是闭映射.mapClusterPt_iff_lift'_closure
  证明: by
  rw [MapClusterPt]; rw [clusterPt_iff_lift'_closure']; rw [f_closed.lift'_closure_map_eq f_cont]; rw [← comap_principal]; rw [← map_neBot_iff f]; rw [Filter.push_pull]; rw [principal_singleton]

Depends on / 依赖: Filter, Filter.push_pull, MapClusterPt, _closure, _closure_map_eq, clusterPt_iff_lift, comap_principal, f_closed, f_closed.lift, f_cont, map_neBot_iff, principal_singleton, push_pull
-/
theorem IsClosedMap.mapClusterPt_iff_lift'_closure
    {F : Filter X} (f_closed : IsClosedMap f) (f_cont : Continuous f) {y : Y} :
    MapClusterPt y F f ↔ ((F.lift' closure) ⊓ 𝓟 (f ⁻¹' {y})).NeBot := by
  rw [MapClusterPt]; rw [clusterPt_iff_lift'_closure']; rw [f_closed.lift'_closure_map_eq f_cont]; rw [← comap_principal]; rw [← map_neBot_iff f]; rw [Filter.push_pull]; rw [principal_singleton]

end IsClosedMap

namespace Topology
section IsOpenEmbedding

variable [TopologicalSpace X] [TopologicalSpace Y]

@[fun_prop]
/--
lemma `IsOpenEmbedding.isEmbedding` / 引理 `IsOpenEmbedding.isEmbedding`

English:
lemma IsOpenEmbedding.isEmbedding
  given: (hf : IsOpenEmbedding f)
  statement: IsEmbedding f
  proof: hf.toIsEmbedding

中文:
引理 是开嵌入.isEmbedding
  条件: (hf : 是开嵌入 f)
  结论: 是嵌入 f
  证明: hf.toIsEmbedding

Depends on / 依赖: hf.toIsEmbedding, toIsEmbedding
-/
lemma IsOpenEmbedding.isEmbedding (hf : IsOpenEmbedding f) : IsEmbedding f := hf.toIsEmbedding

/--
lemma `IsOpenEmbedding.isInducing` / 引理 `IsOpenEmbedding.isInducing`

English:
lemma IsOpenEmbedding.isInducing
  given: (hf : IsOpenEmbedding f)
  statement: IsInducing f
  proof: hf.isEmbedding.isInducing

中文:
引理 是开嵌入.isInducing
  条件: (hf : 是开嵌入 f)
  结论: 是Inducing f
  证明: hf.isEmbedding.isInducing

Depends on / 依赖: hf.isEmbedding.isInducing, isEmbedding, isInducing
-/
lemma IsOpenEmbedding.isInducing (hf : IsOpenEmbedding f) : IsInducing f :=
  hf.isEmbedding.isInducing

/--
lemma `IsOpenEmbedding.isOpenMap` / 引理 `IsOpenEmbedding.isOpenMap`

English:
lemma IsOpenEmbedding.isOpenMap
  given: (hf : IsOpenEmbedding f)
  statement: IsOpenMap f
  proof: hf.isEmbedding.isInducing.isOpenMap hf.isOpen_range

中文:
引理 是开嵌入.isOpenMap
  条件: (hf : 是开嵌入 f)
  结论: 是开映射 f
  证明: hf.isEmbedding.isInducing.isOpenMap hf.isOpen_range

Depends on / 依赖: hf.isEmbedding.isInducing.isOpenMap, hf.isOpen_range, isEmbedding, isInducing, isOpenMap, isOpen_range
-/
lemma IsOpenEmbedding.isOpenMap (hf : IsOpenEmbedding f) : IsOpenMap f :=
  hf.isEmbedding.isInducing.isOpenMap hf.isOpen_range

/--
theorem `IsOpenEmbedding.map_nhds_eq` / 定理 `IsOpenEmbedding.map_nhds_eq`

English:
theorem IsOpenEmbedding.map_nhds_eq
  given: (hf : IsOpenEmbedding f) (x : X)
  proof: hf.isEmbedding.map_nhds_of_mem _ hf.isOpen_range.mem_nhds mem_range_self _

中文:
定理 是开嵌入.map_nhds_eq
  条件: (hf : 是开嵌入 f) (x : X)
  证明: hf.isEmbedding.map_nhds_of_mem _ hf.isOpen_range.mem_nhds mem_range_self _

Depends on / 依赖: hf.isEmbedding.map_nhds_of_mem, hf.isOpen_range.mem_nhds, isEmbedding, isOpen_range, map_nhds_of_mem, mem_nhds, mem_range_self
-/
theorem IsOpenEmbedding.map_nhds_eq (hf : IsOpenEmbedding f) (x : X) :
    map f (𝓝 x) = 𝓝 (f x) :=
hf.isEmbedding.map_nhds_of_mem _ hf.isOpen_range.mem_nhds mem_range_self _

/--
lemma `IsOpenEmbedding.isOpen_iff_image_isOpen` / 引理 `IsOpenEmbedding.isOpen_iff_image_isOpen`

English:
lemma IsOpenEmbedding.isOpen_iff_image_isOpen
  given: (hf : IsOpenEmbedding f) {s : Set X}
  proof: hf.isOpenMap s
  mpr h := by
    convert! ← h.preimage hf.isEmbedding.continuous
    apply preimage_image_eq _ hf.injective

中文:
引理 是开嵌入.isOpen_iff_image_isOpen
  条件: (hf : 是开嵌入 f) {s : 集合 X}
  证明: hf.isOpenMap s
  mpr h := by
    convert! ← h.preimage hf.isEmbedding.continuous
    apply preimage_image_eq _ hf.injective

Depends on / 依赖: hf.isOpenMap, isOpenMap
-/
lemma IsOpenEmbedding.isOpen_iff_image_isOpen (hf : IsOpenEmbedding f) {s : Set X} :
    IsOpen s ↔ IsOpen (f '' s) where
  mp := hf.isOpenMap s
  mpr h := by
    convert! ← h.preimage hf.isEmbedding.continuous
    apply preimage_image_eq _ hf.injective

/--
theorem `IsOpenEmbedding.tendsto_nhds_iff` / 定理 `IsOpenEmbedding.tendsto_nhds_iff`

English:
theorem IsOpenEmbedding.tendsto_nhds_iff
  statement: [TopologicalSpace Z] {f : ι -> Y} {l : Filter ι} {y : Y}
  proof: hg.isEmbedding.tendsto_nhds_iff

中文:
定理 是开嵌入.tendsto_nhds_iff
  结论: [拓扑空间 Z] {f : ι -> Y} {l : 滤子 ι} {y : Y}
  证明: hg.isEmbedding.tendsto_nhds_iff

Depends on / 依赖: hg.isEmbedding.tendsto_nhds_iff, isEmbedding, tendsto_nhds_iff
-/
theorem IsOpenEmbedding.tendsto_nhds_iff [TopologicalSpace Z] {f : ι -> Y} {l : Filter ι} {y : Y}
    (hg : IsOpenEmbedding g) : Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (𝓝 (g y)) :=
  hg.isEmbedding.tendsto_nhds_iff

/--
theorem `IsOpenEmbedding.tendsto_nhds_iff'` / 定理 `IsOpenEmbedding.tendsto_nhds_iff'`

English:
theorem IsOpenEmbedding.tendsto_nhds_iff'
  given: (hf : IsOpenEmbedding f) {l : Filter Z} {x : X}
  proof: by
  rw [Tendsto]; rw [← map_map]; rw [hf.map_nhds_eq]; rfl

中文:
定理 是开嵌入.tendsto_nhds_iff'
  条件: (hf : 是开嵌入 f) {l : 滤子 Z} {x : X}
  证明: by
  rw [Tendsto]; rw [← map_map]; rw [hf.map_nhds_eq]; rfl

Depends on / 依赖: Tendsto, hf.map_nhds_eq, map_map, map_nhds_eq
-/
theorem IsOpenEmbedding.tendsto_nhds_iff' (hf : IsOpenEmbedding f) {l : Filter Z} {x : X} :
    Tendsto (g ∘ f) (𝓝 x) l ↔ Tendsto g (𝓝 (f x)) l := by
  rw [Tendsto]; rw [← map_map]; rw [hf.map_nhds_eq]; rfl

/--
theorem `IsOpenEmbedding.continuousAt_iff` / 定理 `IsOpenEmbedding.continuousAt_iff`

English:
theorem IsOpenEmbedding.continuousAt_iff
  given: [TopologicalSpace Z] (hf : IsOpenEmbedding f) {x : X}
  proof: hf.tendsto_nhds_iff'

@[fun_prop]

中文:
定理 是开嵌入.continuousAt_iff
  条件: [拓扑空间 Z] (hf : 是开嵌入 f) {x : X}
  证明: hf.tendsto_nhds_iff'

@[fun_prop]

Depends on / 依赖: hf.tendsto_nhds_iff, tendsto_nhds_iff
-/
theorem IsOpenEmbedding.continuousAt_iff [TopologicalSpace Z] (hf : IsOpenEmbedding f) {x : X} :
    ContinuousAt (g ∘ f) x ↔ ContinuousAt g (f x) :=
  hf.tendsto_nhds_iff'

@[fun_prop]
/--
theorem `IsOpenEmbedding.continuous` / 定理 `IsOpenEmbedding.continuous`

English:
theorem IsOpenEmbedding.continuous
  given: (hf : IsOpenEmbedding f)
  statement: Continuous f
  proof: hf.isEmbedding.continuous

中文:
定理 是开嵌入.continuous
  条件: (hf : 是开嵌入 f)
  结论: 连续 f
  证明: hf.isEmbedding.continuous

Depends on / 依赖: continuous, hf.isEmbedding.continuous, isEmbedding
-/
theorem IsOpenEmbedding.continuous (hf : IsOpenEmbedding f) : Continuous f :=
  hf.isEmbedding.continuous

/--
lemma `IsOpenEmbedding.isOpen_iff_preimage_isOpen` / 引理 `IsOpenEmbedding.isOpen_iff_preimage_isOpen`

English:
lemma IsOpenEmbedding.isOpen_iff_preimage_isOpen
  statement: (hf : IsOpenEmbedding f) {s : Set Y}
  proof: by
  rw [hf.isOpen_iff_image_isOpen]; rw [image_preimage_eq_inter_range]; rw [inter_eq_self_of_subset_left hs]

@[fun_prop]

中文:
引理 是开嵌入.isOpen_iff_preimage_isOpen
  结论: (hf : 是开嵌入 f) {s : 集合 Y}
  证明: by
  rw [hf.isOpen_iff_image_isOpen]; rw [image_preimage_eq_inter_range]; rw [inter_eq_self_of_subset_left hs]

@[fun_prop]

Depends on / 依赖: hf.isOpen_iff_image_isOpen, image_preimage_eq_inter_range, inter_eq_self_of_subset_left, isOpen_iff_image_isOpen
-/
lemma IsOpenEmbedding.isOpen_iff_preimage_isOpen (hf : IsOpenEmbedding f) {s : Set Y}
    (hs : s subseteq range f) : IsOpen s ↔ IsOpen (f ⁻¹' s) := by
  rw [hf.isOpen_iff_image_isOpen]; rw [image_preimage_eq_inter_range]; rw [inter_eq_self_of_subset_left hs]

@[fun_prop]
/--
lemma `IsOpenEmbedding.of_isEmbedding_isOpenMap` / 引理 `IsOpenEmbedding.of_isEmbedding_isOpenMap`

English:
lemma IsOpenEmbedding.of_isEmbedding_isOpenMap
  given: (h₁ : IsEmbedding f) (h₂ : IsOpenMap f)
  proof: ⟨h₁, h₂.isOpen_range⟩

中文:
引理 是开嵌入.of_isEmbedding_isOpenMap
  条件: (h₁ : 是嵌入 f) (h₂ : 是开映射 f)
  证明: ⟨h₁, h₂.isOpen_range⟩

Depends on / 依赖: isOpen_range
-/
lemma IsOpenEmbedding.of_isEmbedding_isOpenMap (h₁ : IsEmbedding f) (h₂ : IsOpenMap f) :
    IsOpenEmbedding f :=
  ⟨h₁, h₂.isOpen_range⟩

/--
lemma `IsEmbedding.isOpenEmbedding_of_surjective` / 引理 `IsEmbedding.isOpenEmbedding_of_surjective`

English:
lemma IsEmbedding.isOpenEmbedding_of_surjective
  given: (hf : IsEmbedding f) (hsurj : f.Surjective)
  proof: ⟨hf, hsurj.range_eq ▸ isOpen_univ⟩

alias IsOpenEmbedding.of_isEmbedding := IsEmbedding.isOpenEmbedding_of_surjective

中文:
引理 是嵌入.isOpenEmbedding_of_surjective
  条件: (hf : 是嵌入 f) (hsurj : f.满射)
  证明: ⟨hf, hsurj.range_eq ▸ isOpen_univ⟩

alias IsOpenEmbedding.of_isEmbedding := IsEmbedding.isOpenEmbedding_of_surjective

Depends on / 依赖: hsurj.range_eq, isOpen_univ, range_eq
-/
lemma IsEmbedding.isOpenEmbedding_of_surjective (hf : IsEmbedding f) (hsurj : f.Surjective) :
    IsOpenEmbedding f :=
  ⟨hf, hsurj.range_eq ▸ isOpen_univ⟩

alias IsOpenEmbedding.of_isEmbedding := IsEmbedding.isOpenEmbedding_of_surjective

/--
lemma `isOpenEmbedding_iff_isEmbedding_isOpenMap` / 引理 `isOpenEmbedding_iff_isEmbedding_isOpenMap`

English:
lemma isOpenEmbedding_iff_isEmbedding_isOpenMap
  statement: IsOpenEmbedding f ↔ IsEmbedding f ∧ IsOpenMap f
  proof: ⟨fun h => ⟨h.1, h.isOpenMap⟩, fun h => .of_isEmbedding_isOpenMap h.1 h.2⟩

中文:
引理 isOpenEmbedding_iff_isEmbedding_isOpenMap
  结论: 是开嵌入 f ↔ 是嵌入 f ∧ 是开映射 f
  证明: ⟨fun h => ⟨h.1, h.isOpenMap⟩, fun h => .of_isEmbedding_isOpenMap h.1 h.2⟩

Depends on / 依赖: h.isOpenMap, isOpenMap, of_isEmbedding_isOpenMap
-/
lemma isOpenEmbedding_iff_isEmbedding_isOpenMap : IsOpenEmbedding f ↔ IsEmbedding f ∧ IsOpenMap f :=
  ⟨fun h => ⟨h.1, h.isOpenMap⟩, fun h => .of_isEmbedding_isOpenMap h.1 h.2⟩

/--
theorem `IsOpenEmbedding.of_continuous_injective_isOpenMap` / 定理 `IsOpenEmbedding.of_continuous_injective_isOpenMap`

English:
theorem IsOpenEmbedding.of_continuous_injective_isOpenMap
  proof: by
  simp only [isOpenEmbedding_iff_isEmbedding_isOpenMap, isEmbedding_iff, isInducing_iff_nhds, *,
    and_true]
  exact fun x =>
    le_antisymm (h₁.tendsto _).le_comap (@comap_map _ _ (𝓝 x) _ h₂ ▸ comap_mono (h₃.nhds_le _))

中文:
定理 是开嵌入.of_continuous_injective_isOpenMap
  证明: by
  simp only [isOpenEmbedding_iff_isEmbedding_isOpenMap, isEmbedding_iff, isInducing_iff_nhds, *,
    and_true]
  exact fun x =>
    le_antisymm (h₁.tendsto _).le_comap (@comap_map _ _ (𝓝 x) _ h₂ ▸ comap_mono (h₃.nhds_le _))

Depends on / 依赖: and_true, comap_map, comap_mono, isEmbedding_iff, isInducing_iff_nhds, isOpenEmbedding_iff_isEmbedding_isOpenMap, le_antisymm, le_comap, nhds_le, tendsto
-/
theorem IsOpenEmbedding.of_continuous_injective_isOpenMap
    (h₁ : Continuous f) (h₂ : Injective f) (h₃ : IsOpenMap f) : IsOpenEmbedding f := by
  simp only [isOpenEmbedding_iff_isEmbedding_isOpenMap, isEmbedding_iff, isInducing_iff_nhds, *,
    and_true]
  exact fun x =>
    le_antisymm (h₁.tendsto _).le_comap (@comap_map _ _ (𝓝 x) _ h₂ ▸ comap_mono (h₃.nhds_le _))

/--
lemma `isOpenEmbedding_iff_continuous_injective_isOpenMap` / 引理 `isOpenEmbedding_iff_continuous_injective_isOpenMap`

English:
lemma isOpenEmbedding_iff_continuous_injective_isOpenMap
  proof: ⟨fun h => ⟨h.continuous, h.injective, h.isOpenMap⟩, fun h =>
    .of_continuous_injective_isOpenMap h.1 h.2.1 h.2.2⟩

中文:
引理 isOpenEmbedding_iff_continuous_injective_isOpenMap
  证明: ⟨fun h => ⟨h.continuous, h.injective, h.isOpenMap⟩, fun h =>
    .of_continuous_injective_isOpenMap h.1 h.2.1 h.2.2⟩

Depends on / 依赖: continuous, h.continuous, h.injective, h.isOpenMap, injective, isOpenMap, of_continuous_injective_isOpenMap
-/
lemma isOpenEmbedding_iff_continuous_injective_isOpenMap :
    IsOpenEmbedding f ↔ Continuous f ∧ Injective f ∧ IsOpenMap f :=
  ⟨fun h => ⟨h.continuous, h.injective, h.isOpenMap⟩, fun h =>
    .of_continuous_injective_isOpenMap h.1 h.2.1 h.2.2⟩

namespace IsOpenEmbedding
variable [TopologicalSpace Z]

@[fun_prop]
/--
lemma `id` / 引理 `id`

English:
lemma id
  statement: IsOpenEmbedding (@id X)
  proof: ⟨.id, IsOpenMap.id.isOpen_range⟩

@[fun_prop]

中文:
引理 id
  结论: 是开嵌入 (@id X)
  证明: ⟨.id, IsOpenMap.id.isOpen_range⟩

@[fun_prop]
-/
protected lemma id : IsOpenEmbedding (@id X) := ⟨.id, IsOpenMap.id.isOpen_range⟩

@[fun_prop]
/--
lemma `comp` / 引理 `comp`

English:
lemma comp
  statement: (hg : IsOpenEmbedding g)
  proof: ⟨hg.1.comp hf.1, (hg.isOpenMap.comp hf.isOpenMap).isOpen_range⟩

中文:
引理 comp
  结论: (hg : 是开嵌入 g)
  证明: ⟨hg.1.comp hf.1, (hg.isOpenMap.comp hf.isOpenMap).isOpen_range⟩
-/
protected lemma comp (hg : IsOpenEmbedding g)
    (hf : IsOpenEmbedding f) : IsOpenEmbedding (g ∘ f) :=
  ⟨hg.1.comp hf.1, (hg.isOpenMap.comp hf.isOpenMap).isOpen_range⟩

/--
theorem `isOpenMap_iff` / 定理 `isOpenMap_iff`

English:
theorem isOpenMap_iff
  given: (hg : IsOpenEmbedding g)
  proof: by
  simp_rw [isOpenMap_iff_nhds_le, ← map_map, comp, ← hg.map_nhds_eq, map_le_map_iff hg.injective]

中文:
定理 isOpenMap_iff
  条件: (hg : 是开嵌入 g)
  证明: by
  simp_rw [isOpenMap_iff_nhds_le, ← map_map, comp, ← hg.map_nhds_eq, map_le_map_iff hg.injective]

Depends on / 依赖: hg.injective, hg.map_nhds_eq, injective, isOpenMap_iff_nhds_le, map_le_map_iff, map_map, map_nhds_eq, simp_rw
-/
theorem isOpenMap_iff (hg : IsOpenEmbedding g) :
    IsOpenMap f ↔ IsOpenMap (g ∘ f) := by
  simp_rw [isOpenMap_iff_nhds_le, ← map_map, comp, ← hg.map_nhds_eq, map_le_map_iff hg.injective]

/--
theorem `of_comp_iff` / 定理 `of_comp_iff`

English:
theorem of_comp_iff
  given: (f : X -> Y) (hg : IsOpenEmbedding g)
  proof: by
  simp only [isOpenEmbedding_iff_continuous_injective_isOpenMap, ← hg.isOpenMap_iff, ←
    hg.1.continuous_iff, hg.injective.of_comp_iff]

中文:
定理 of_comp_iff
  条件: (f : X -> Y) (hg : 是开嵌入 g)
  证明: by
  simp only [isOpenEmbedding_iff_continuous_injective_isOpenMap, ← hg.isOpenMap_iff, ←
    hg.1.continuous_iff, hg.injective.of_comp_iff]

Depends on / 依赖: continuous_iff, hg.injective.of_comp_iff, hg.isOpenMap_iff, injective, isOpenEmbedding_iff_continuous_injective_isOpenMap, isOpenMap_iff, of_comp_iff
-/
theorem of_comp_iff (f : X -> Y) (hg : IsOpenEmbedding g) :
    IsOpenEmbedding (g ∘ f) ↔ IsOpenEmbedding f := by
  simp only [isOpenEmbedding_iff_continuous_injective_isOpenMap, ← hg.isOpenMap_iff, ←
    hg.1.continuous_iff, hg.injective.of_comp_iff]

/--
lemma `of_comp` / 引理 `of_comp`

English:
lemma of_comp
  given: (f : X -> Y) (hg : IsOpenEmbedding g) (h : IsOpenEmbedding (g ∘ f))
  proof: (IsOpenEmbedding.of_comp_iff f hg).1 h

中文:
引理 of_comp
  条件: (f : X -> Y) (hg : 是开嵌入 g) (h : 是开嵌入 (g ∘ f))
  证明: (IsOpenEmbedding.of_comp_iff f hg).1 h

Depends on / 依赖: IsOpenEmbedding, IsOpenEmbedding.of_comp_iff, of_comp_iff
-/
lemma of_comp (f : X -> Y) (hg : IsOpenEmbedding g) (h : IsOpenEmbedding (g ∘ f)) :
    IsOpenEmbedding f := (IsOpenEmbedding.of_comp_iff f hg).1 h

/--
theorem `of_isEmpty` / 定理 `of_isEmpty`

English:
theorem of_isEmpty
  given: [IsEmpty X] (f : X -> Y)
  statement: IsOpenEmbedding f
  proof: of_isEmbedding_isOpenMap (.of_subsingleton f) (.of_isEmpty f)

中文:
定理 of_isEmpty
  条件: [是空 X] (f : X -> Y)
  结论: 是开嵌入 f
  证明: of_isEmbedding_isOpenMap (.of_subsingleton f) (.of_isEmpty f)

Depends on / 依赖: of_isEmbedding_isOpenMap, of_isEmpty, of_subsingleton
-/
theorem of_isEmpty [IsEmpty X] (f : X -> Y) : IsOpenEmbedding f :=
  of_isEmbedding_isOpenMap (.of_subsingleton f) (.of_isEmpty f)

/--
theorem `image_mem_nhds` / 定理 `image_mem_nhds`

English:
theorem image_mem_nhds
  given: {f : X -> Y} (hf : IsOpenEmbedding f) {s : Set X} {x : X}
  proof: by
  rw [← hf.map_nhds_eq]; rw [mem_map]; rw [preimage_image_eq _ hf.injective]

中文:
定理 image_mem_nhds
  条件: {f : X -> Y} (hf : 是开嵌入 f) {s : 集合 X} {x : X}
  证明: by
  rw [← hf.map_nhds_eq]; rw [mem_map]; rw [preimage_image_eq _ hf.injective]

Depends on / 依赖: hf.injective, hf.map_nhds_eq, injective, map_nhds_eq, mem_map, preimage_image_eq
-/
theorem image_mem_nhds {f : X -> Y} (hf : IsOpenEmbedding f) {s : Set X} {x : X} :
    f '' s in 𝓝 (f x) ↔ s in 𝓝 x := by
  rw [← hf.map_nhds_eq]; rw [mem_map]; rw [preimage_image_eq _ hf.injective]

/--
theorem `accPt_comap_iff` / 定理 `accPt_comap_iff`

English:
theorem accPt_comap_iff
  proof: by
  rw [accPt_iff_clusterPt]; rw [accPt_iff_clusterPt]; rw [← hf.injective.preimage_image {x}]; rw [image_singleton]; rw [← preimage_compl]; rw [← comap_principal]; rw [← comap_inf]; rw [hf.isOpenMap.clusterPt_comap_iff hf.continuous]

中文:
定理 accPt_comap_iff
  证明: by
  rw [accPt_iff_clusterPt]; rw [accPt_iff_clusterPt]; rw [← hf.injective.preimage_image {x}]; rw [image_singleton]; rw [← preimage_compl]; rw [← comap_principal]; rw [← comap_inf]; rw [hf.isOpenMap.clusterPt_comap_iff hf.continuous]

Depends on / 依赖: accPt_iff_clusterPt, clusterPt_comap_iff, comap_inf, comap_principal, continuous, hf.continuous, hf.injective.preimage_image, hf.isOpenMap.clusterPt_comap_iff, image_singleton, injective, isOpenMap, preimage_compl, preimage_image
-/
theorem accPt_comap_iff
    (hf : IsOpenEmbedding f) {x : X} {l : Filter Y} :
    AccPt x (comap f l) ↔ AccPt (f x) l := by
  rw [accPt_iff_clusterPt]; rw [accPt_iff_clusterPt]; rw [← hf.injective.preimage_image {x}]; rw [image_singleton]; rw [← preimage_compl]; rw [← comap_principal]; rw [← comap_inf]; rw [hf.isOpenMap.clusterPt_comap_iff hf.continuous]

end IsOpenEmbedding

end IsOpenEmbedding

section IsClosedEmbedding

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace IsClosedEmbedding

@[fun_prop]
/--
lemma `isEmbedding` / 引理 `isEmbedding`

English:
lemma isEmbedding
  given: (hf : IsClosedEmbedding f)
  statement: IsEmbedding f
  proof: hf.toIsEmbedding
@[fun_prop]

中文:
引理 isEmbedding
  条件: (hf : 是闭嵌入 f)
  结论: 是嵌入 f
  证明: hf.toIsEmbedding
@[fun_prop]

Depends on / 依赖: hf.toIsEmbedding, toIsEmbedding
-/
lemma isEmbedding (hf : IsClosedEmbedding f) : IsEmbedding f := hf.toIsEmbedding
@[fun_prop]
/--
lemma `isInducing` / 引理 `isInducing`

English:
lemma isInducing
  given: (hf : IsClosedEmbedding f)
  statement: IsInducing f
  proof: hf.isEmbedding.isInducing
@[fun_prop]

中文:
引理 isInducing
  条件: (hf : 是闭嵌入 f)
  结论: 是Inducing f
  证明: hf.isEmbedding.isInducing
@[fun_prop]

Depends on / 依赖: hf.isEmbedding.isInducing, isEmbedding, isInducing
-/
lemma isInducing (hf : IsClosedEmbedding f) : IsInducing f := hf.isEmbedding.isInducing
@[fun_prop]
/--
lemma `continuous` / 引理 `continuous`

English:
lemma continuous
  given: (hf : IsClosedEmbedding f)
  statement: Continuous f
  proof: hf.isEmbedding.continuous

中文:
引理 continuous
  条件: (hf : 是闭嵌入 f)
  结论: 连续 f
  证明: hf.isEmbedding.continuous

Depends on / 依赖: continuous, hf.isEmbedding.continuous, isEmbedding
-/
lemma continuous (hf : IsClosedEmbedding f) : Continuous f := hf.isEmbedding.continuous

/--
lemma `tendsto_nhds_iff` / 引理 `tendsto_nhds_iff`

English:
lemma tendsto_nhds_iff
  given: {g : ι -> X} {l : Filter ι} {x : X} (hf : IsClosedEmbedding f)
  proof: hf.isEmbedding.tendsto_nhds_iff

中文:
引理 tendsto_nhds_iff
  条件: {g : ι -> X} {l : 滤子 ι} {x : X} (hf : 是闭嵌入 f)
  证明: hf.isEmbedding.tendsto_nhds_iff

Depends on / 依赖: hf.isEmbedding.tendsto_nhds_iff, isEmbedding, tendsto_nhds_iff
-/
lemma tendsto_nhds_iff {g : ι -> X} {l : Filter ι} {x : X} (hf : IsClosedEmbedding f) :
    Tendsto g l (𝓝 x) ↔ Tendsto (f ∘ g) l (𝓝 (f x)) := hf.isEmbedding.tendsto_nhds_iff

/--
lemma `isClosedMap` / 引理 `isClosedMap`

English:
lemma isClosedMap
  given: (hf : IsClosedEmbedding f)
  statement: IsClosedMap f
  proof: hf.isEmbedding.isInducing.isClosedMap hf.isClosed_range

中文:
引理 isClosedMap
  条件: (hf : 是闭嵌入 f)
  结论: 是闭映射 f
  证明: hf.isEmbedding.isInducing.isClosedMap hf.isClosed_range

Depends on / 依赖: hf.isClosed_range, hf.isEmbedding.isInducing.isClosedMap, isClosedMap, isClosed_range, isEmbedding, isInducing
-/
lemma isClosedMap (hf : IsClosedEmbedding f) : IsClosedMap f :=
  hf.isEmbedding.isInducing.isClosedMap hf.isClosed_range

/--
lemma `isClosed_iff_image_isClosed` / 引理 `isClosed_iff_image_isClosed`

English:
lemma isClosed_iff_image_isClosed
  given: (hf : IsClosedEmbedding f) {s : Set X}
  proof: ⟨hf.isClosedMap s, fun h => by
    rw [← preimage_image_eq s hf.injective]
    exact h.preimage hf.continuous⟩

中文:
引理 isClosed_iff_image_isClosed
  条件: (hf : 是闭嵌入 f) {s : 集合 X}
  证明: ⟨hf.isClosedMap s, fun h => by
    rw [← preimage_image_eq s hf.injective]
    exact h.preimage hf.continuous⟩

Depends on / 依赖: continuous, h.preimage, hf.continuous, hf.injective, hf.isClosedMap, injective, isClosedMap, preimage, preimage_image_eq
-/
lemma isClosed_iff_image_isClosed (hf : IsClosedEmbedding f) {s : Set X} :
    IsClosed s ↔ IsClosed (f '' s) :=
  ⟨hf.isClosedMap s, fun h => by
    rw [← preimage_image_eq s hf.injective]
    exact h.preimage hf.continuous⟩

/--
lemma `isClosed_iff_preimage_isClosed` / 引理 `isClosed_iff_preimage_isClosed`

English:
lemma isClosed_iff_preimage_isClosed
  statement: (hf : IsClosedEmbedding f) {s : Set Y}
  proof: by
  rw [hf.isClosed_iff_image_isClosed]; rw [image_preimage_eq_of_subset hs]

中文:
引理 isClosed_iff_preimage_isClosed
  结论: (hf : 是闭嵌入 f) {s : 集合 Y}
  证明: by
  rw [hf.isClosed_iff_image_isClosed]; rw [image_preimage_eq_of_subset hs]

Depends on / 依赖: hf.isClosed_iff_image_isClosed, image_preimage_eq_of_subset, isClosed_iff_image_isClosed
-/
lemma isClosed_iff_preimage_isClosed (hf : IsClosedEmbedding f) {s : Set Y}
    (hs : s subseteq range f) : IsClosed s ↔ IsClosed (f ⁻¹' s) := by
  rw [hf.isClosed_iff_image_isClosed]; rw [image_preimage_eq_of_subset hs]

/--
lemma `of_isEmbedding_isClosedMap` / 引理 `of_isEmbedding_isClosedMap`

English:
lemma of_isEmbedding_isClosedMap
  given: (h₁ : IsEmbedding f) (h₂ : IsClosedMap f)
  proof: ⟨h₁, image_univ (f := f) ▸ h₂ univ isClosed_univ⟩

中文:
引理 of_isEmbedding_isClosedMap
  条件: (h₁ : 是嵌入 f) (h₂ : 是闭映射 f)
  证明: ⟨h₁, image_univ (f := f) ▸ h₂ univ isClosed_univ⟩

Depends on / 依赖: image_univ, isClosed_univ
-/
lemma of_isEmbedding_isClosedMap (h₁ : IsEmbedding f) (h₂ : IsClosedMap f) :
    IsClosedEmbedding f :=
  ⟨h₁, image_univ (f := f) ▸ h₂ univ isClosed_univ⟩

/--
lemma `of_continuous_injective_isClosedMap` / 引理 `of_continuous_injective_isClosedMap`

English:
lemma of_continuous_injective_isClosedMap
  statement: (h₁ : Continuous f) (h₂ : Injective f)
  proof: by
  refine .of_isEmbedding_isClosedMap ⟨⟨?_⟩, h₂⟩ h₃
  refine h₁.le_induced.antisymm fun s hs => ?_
  refine ⟨(f '' sᶜ)ᶜ, (h₃ _ hs.isClosed_compl).isOpen_compl, ?_⟩
  rw [preimage_compl]; rw [preimage_image_eq _ h₂]; rw [compl_compl]

中文:
引理 of_continuous_injective_isClosedMap
  结论: (h₁ : 连续 f) (h₂ : 单射 f)
  证明: by
  refine .of_isEmbedding_isClosedMap ⟨⟨?_⟩, h₂⟩ h₃
  refine h₁.le_induced.antisymm fun s hs => ?_
  refine ⟨(f '' sᶜ)ᶜ, (h₃ _ hs.isClosed_compl).isOpen_compl, ?_⟩
  rw [preimage_compl]; rw [preimage_image_eq _ h₂]; rw [compl_compl]

Depends on / 依赖: antisymm, compl_compl, hs.isClosed_compl, isClosed_compl, isOpen_compl, le_induced, le_induced.antisymm, of_isEmbedding_isClosedMap, preimage_compl, preimage_image_eq
-/
lemma of_continuous_injective_isClosedMap (h₁ : Continuous f) (h₂ : Injective f)
    (h₃ : IsClosedMap f) : IsClosedEmbedding f := by
  refine .of_isEmbedding_isClosedMap ⟨⟨?_⟩, h₂⟩ h₃
  refine h₁.le_induced.antisymm fun s hs => ?_
  refine ⟨(f '' sᶜ)ᶜ, (h₃ _ hs.isClosed_compl).isOpen_compl, ?_⟩
  rw [preimage_compl]; rw [preimage_image_eq _ h₂]; rw [compl_compl]

/--
lemma `isClosedEmbedding_iff_continuous_injective_isClosedMap` / 引理 `isClosedEmbedding_iff_continuous_injective_isClosedMap`

English:
lemma isClosedEmbedding_iff_continuous_injective_isClosedMap
  given: {f : X -> Y}
  proof: ⟨h.continuous, h.injective, h.isClosedMap⟩
  mpr h := .of_continuous_injective_isClosedMap h.1 h.2.1 h.2.2

@[fun_prop]

中文:
引理 isClosedEmbedding_iff_continuous_injective_isClosedMap
  条件: {f : X -> Y}
  证明: ⟨h.continuous, h.injective, h.isClosedMap⟩
  mpr h := .of_continuous_injective_isClosedMap h.1 h.2.1 h.2.2

@[fun_prop]

Depends on / 依赖: continuous, h.continuous, h.injective, h.isClosedMap, injective, isClosedMap
-/
lemma isClosedEmbedding_iff_continuous_injective_isClosedMap {f : X -> Y} :
    IsClosedEmbedding f ↔ Continuous f ∧ Injective f ∧ IsClosedMap f where
  mp h := ⟨h.continuous, h.injective, h.isClosedMap⟩
  mpr h := .of_continuous_injective_isClosedMap h.1 h.2.1 h.2.2

@[fun_prop]
/--
theorem `id` / 定理 `id`

English:
theorem id
  statement: IsClosedEmbedding (@id X)
  proof: ⟨.id, IsClosedMap.id.isClosed_range⟩

@[fun_prop]

中文:
定理 id
  结论: 是闭嵌入 (@id X)
  证明: ⟨.id, IsClosedMap.id.isClosed_range⟩

@[fun_prop]
-/
protected theorem id : IsClosedEmbedding (@id X) := ⟨.id, IsClosedMap.id.isClosed_range⟩

@[fun_prop]
/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: (hg : IsClosedEmbedding g) (hf : IsClosedEmbedding f)
  proof: ⟨hg.isEmbedding.comp hf.isEmbedding, (hg.isClosedMap.comp hf.isClosedMap).isClosed_range⟩

中文:
定理 comp
  条件: (hg : 是闭嵌入 g) (hf : 是闭嵌入 f)
  证明: ⟨hg.isEmbedding.comp hf.isEmbedding, (hg.isClosedMap.comp hf.isClosedMap).isClosed_range⟩

Depends on / 依赖: hf.isClosedMap, hf.isEmbedding, hg.isClosedMap.comp, hg.isEmbedding.comp, isClosedMap, isClosed_range, isEmbedding
-/
theorem comp (hg : IsClosedEmbedding g) (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (g ∘ f) :=
  ⟨hg.isEmbedding.comp hf.isEmbedding, (hg.isClosedMap.comp hf.isClosedMap).isClosed_range⟩

/--
lemma `of_comp_iff` / 引理 `of_comp_iff`

English:
lemma of_comp_iff
  given: (hg : IsClosedEmbedding g)
  statement: IsClosedEmbedding (g ∘ f) ↔ IsClosedEmbedding f
  proof: by
  simp_rw [isClosedEmbedding_iff, hg.isEmbedding.of_comp_iff, Set.range_comp,
    ← hg.isClosed_iff_image_isClosed]

中文:
引理 of_comp_iff
  条件: (hg : 是闭嵌入 g)
  结论: 是闭嵌入 (g ∘ f) ↔ 是闭嵌入 f
  证明: by
  simp_rw [isClosedEmbedding_iff, hg.isEmbedding.of_comp_iff, Set.range_comp,
    ← hg.isClosed_iff_image_isClosed]

Depends on / 依赖: Set.range_comp, hg.isClosed_iff_image_isClosed, hg.isEmbedding.of_comp_iff, isClosedEmbedding_iff, isClosed_iff_image_isClosed, isEmbedding, of_comp_iff, range_comp, simp_rw
-/
lemma of_comp_iff (hg : IsClosedEmbedding g) : IsClosedEmbedding (g ∘ f) ↔ IsClosedEmbedding f := by
  simp_rw [isClosedEmbedding_iff, hg.isEmbedding.of_comp_iff, Set.range_comp,
    ← hg.isClosed_iff_image_isClosed]

/--
lemma `of_comp` / 引理 `of_comp`

English:
lemma of_comp
  given: (hg : IsEmbedding g) (hgf : IsClosedEmbedding (g ∘ f))
  proof: hg.of_comp_iff.mp hgf.isEmbedding
  isClosed_range := by
    convert! hg.isClosed_preimage _ hgf.isClosed_range
    rw [range_comp]; rw [hg.injective.preimage_image]

中文:
引理 of_comp
  条件: (hg : 是嵌入 g) (hgf : 是闭嵌入 (g ∘ f))
  证明: hg.of_comp_iff.mp hgf.isEmbedding
  isClosed_range := by
    convert! hg.isClosed_preimage _ hgf.isClosed_range
    rw [range_comp]; rw [hg.injective.preimage_image]
-/
protected lemma of_comp (hg : IsEmbedding g) (hgf : IsClosedEmbedding (g ∘ f)) :
    IsClosedEmbedding f where
  __ := hg.of_comp_iff.mp hgf.isEmbedding
  isClosed_range := by
    convert! hg.isClosed_preimage _ hgf.isClosed_range
    rw [range_comp]; rw [hg.injective.preimage_image]

/--
theorem `closure_image_eq` / 定理 `closure_image_eq`

English:
theorem closure_image_eq
  given: (hf : IsClosedEmbedding f) (s : Set X)
  proof: hf.isClosedMap.closure_image_eq_of_continuous hf.continuous s

中文:
定理 closure_image_eq
  条件: (hf : 是闭嵌入 f) (s : 集合 X)
  证明: hf.isClosedMap.closure_image_eq_of_continuous hf.continuous s

Depends on / 依赖: closure_image_eq_of_continuous, continuous, hf.continuous, hf.isClosedMap.closure_image_eq_of_continuous, isClosedMap
-/
theorem closure_image_eq (hf : IsClosedEmbedding f) (s : Set X) :
    closure (f '' s) = f '' closure s :=
  hf.isClosedMap.closure_image_eq_of_continuous hf.continuous s

end Topology.IsClosedEmbedding.IsClosedEmbedding
