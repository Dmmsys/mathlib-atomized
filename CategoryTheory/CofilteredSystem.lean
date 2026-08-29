/-
Copyright (c) 2022 Kyle Miller, Adam Topaz, Rémi Bottinelli, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Adam Topaz, Rémi Bottinelli, Junyan Xu
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Konig

/-!
# Cofiltered systems

This file deals with properties of cofiltered (and inverse) systems.

## Main definitions

Given a functor `F : J ⥤ Type v`:

* For `j : J`, `F.eventualRange j` is the intersection of all ranges of morphisms `F.map f`
  where `f` has codomain `j`.
* `F.IsMittagLeffler` states that the functor `F` satisfies the Mittag-Leffler
  condition: the ranges of morphisms `F.map f` (with `f` having codomain `j`) stabilize.
* If `J` is cofiltered `F.toEventualRanges` is the subfunctor of `F` obtained by restriction
  to `F.eventualRange`.
* `F.toPreimages` restricts a functor to preimages of a given set in some `F.obj i`. If `J` is
  cofiltered, then it is Mittag-Leffler if `F` is, see `IsMittagLeffler.toPreimages`.

## Main statements

* `nonempty_sections_of_finite_cofiltered_system` shows that if `J` is cofiltered and each
  `F.obj j` is nonempty and finite, `F.sections` is nonempty.
* `nonempty_sections_of_finite_inverse_system` is a specialization of the above to `J` being a
  directed set (and `F : Jᵒᵖ ⥤ Type v`).
* `isMittagLeffler_of_exists_finite_range` shows that if `J` is cofiltered and for all `j`,
  there exists some `i` and `f : i ⟶ j` such that the range of `F.map f` is finite, then
  `F` is Mittag-Leffler.
* `surjective_toEventualRanges` shows that if `F` is Mittag-Leffler, then `F.toEventualRanges`
  has all morphisms `F.map f` surjective.

## TODO

* Prove [Stacks: Lemma 0597](https://stacks.math.columbia.edu/tag/0597)

## References

* [Stacks: Mittag-Leffler systems](https://stacks.math.columbia.edu/tag/0594)

## Tags

Mittag-Leffler, surjective, eventual range, inverse system,

-/

@[expose] public section


universe u v w

open CategoryTheory CategoryTheory.IsCofiltered Set CategoryTheory.FunctorToTypes

section FiniteKonig

/--
theorem `nonempty_sections_of_finite_cofiltered_system.init` / 定理 `nonempty_sections_of_finite_cofiltered_system.init`

English:
theorem nonempty_sections_of_finite_cofiltered_system.init
  statement: {J : Type u} [SmallCategory J]
  proof: by
  let F' : J ⥤ TopCat := F ⋙ TopCat.discrete
  have : forall j, DiscreteTopology (F'.obj j) := fun _ => ⟨rfl⟩
  have : forall j, Finite (F'.obj j) := hf
  have : forall j, Nonempty (F'.obj j) := hne
  obtain ⟨⟨u, hu⟩⟩ := TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system.{u} F'
  exact ⟨u,

中文:
定理 nonempty_sections_of_finite_cofiltered_system.init
  结论: {J : 类型u} [SmallCategory J]
  证明: by
  let F' : J ⥤ TopCat := F ⋙ TopCat.discrete
  have : forall j, DiscreteTopology (F'.obj j) := fun _ => ⟨rfl⟩
  have : forall j, Finite (F'.obj j) := hf
  have : forall j, Nonempty (F'.obj j) := hne
  obtain ⟨⟨u, hu⟩⟩ := TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system.{u} F'
  exact ⟨u,

Depends on / 依赖: DiscreteTopology, Finite, Nonempty, TopCat, TopCat.discrete, TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system, discrete, nonempty_limitCone_of_compact_t2_cofiltered_system
-/
theorem nonempty_sections_of_finite_cofiltered_system.init {J : Type u} [SmallCategory J]
    [IsCofilteredOrEmpty J] (F : J ⥤ Type u) [hf : forall j, Finite (F.obj j)]
    [hne : forall j, Nonempty (F.obj j)] : F.sections.Nonempty := by
  let F' : J ⥤ TopCat := F ⋙ TopCat.discrete
  have : forall j, DiscreteTopology (F'.obj j) := fun _ => ⟨rfl⟩
  have : forall j, Finite (F'.obj j) := hf
  have : forall j, Nonempty (F'.obj j) := hne
  obtain ⟨⟨u, hu⟩⟩ := TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system.{u} F'
  exact ⟨u, hu⟩

/--
theorem `nonempty_sections_of_finite_cofiltered_system` / 定理 `nonempty_sections_of_finite_cofiltered_system`

English:
theorem nonempty_sections_of_finite_cofiltered_system
  statement: {J : Type u} [Category.{w} J]
  proof: by
  -- Step 1: lift everything to the `max u v w` universe.
  let J' : Type max w v u := AsSmall.{max w v} J
  let down : J' ⥤ J := AsSmall.down
  let F' : J' ⥤ Type (max u v w) := down ⋙ F ⋙ uliftFunctor.{max u w, v}
  have : forall i, Nonempty (F'.obj i) := fun i => ⟨⟨Classical.arbitrary (F.obj (

中文:
定理 nonempty_sections_of_finite_cofiltered_system
  结论: {J : 类型u} [Category.{w} J]
  证明: by
  -- Step 1: lift everything to the `max u v w` universe.
  let J' : Type max w v u := AsSmall.{max w v} J
  let down : J' ⥤ J := AsSmall.down
  let F' : J' ⥤ Type (max u v w) := down ⋙ F ⋙ uliftFunctor.{max u w, v}
  have : forall i, Nonempty (F'.obj i) := fun i => ⟨⟨Classical.arbitrary (F.obj (
-/
theorem nonempty_sections_of_finite_cofiltered_system {J : Type u} [Category.{w} J]
    [IsCofilteredOrEmpty J] (F : J ⥤ Type v) [forall j : J, Finite (F.obj j)]
    [forall j : J, Nonempty (F.obj j)] : F.sections.Nonempty := by
  -- Step 1: lift everything to the `max u v w` universe.
  let J' : Type max w v u := AsSmall.{max w v} J
  let down : J' ⥤ J := AsSmall.down
  let F' : J' ⥤ Type (max u v w) := down ⋙ F ⋙ uliftFunctor.{max u w, v}
  have : forall i, Nonempty (F'.obj i) := fun i => ⟨⟨Classical.arbitrary (F.obj (down.obj i))⟩⟩
  have : forall i, Finite (F'.obj i) := fun i => Finite.of_equiv (F.obj (down.obj i)) Equiv.ulift.symm
  -- Step 2: apply the bootstrap theorem
  cases isEmpty_or_nonempty J
  · fconstructor <;> apply isEmptyElim
  have : IsCofiltered J := ⟨⟩
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_cofiltered_system.init F'
  -- Step 3: interpret the results
  use fun j => (u ⟨j⟩).down
  intro j j' f
  have h := @hu (⟨j⟩ : J') (⟨j'⟩ : J') (ULift.up f)
  simp only [F', down, AsSmall.down] at h
  simp_rw [← h]
  rfl

/--
theorem `nonempty_sections_of_finite_inverse_system` / 定理 `nonempty_sections_of_finite_inverse_system`

English:
theorem nonempty_sections_of_finite_inverse_system
  statement: {J : Type u} [Preorder J] [IsDirectedOrder J]
  proof: nonempty_sections_of_finite_cofiltered_system F

中文:
定理 nonempty_sections_of_finite_inverse_system
  结论: {J : 类型u} [Preorder J] [IsDirectedOrder J]
  证明: nonempty_sections_of_finite_cofiltered_system F

Depends on / 依赖: nonempty_sections_of_finite_cofiltered_system
-/
theorem nonempty_sections_of_finite_inverse_system {J : Type u} [Preorder J] [IsDirectedOrder J]
    (F : Jᵒᵖ ⥤ Type v) [forall j : Jᵒᵖ, Finite (F.obj j)] [forall j : Jᵒᵖ, Nonempty (F.obj j)] :
    F.sections.Nonempty := nonempty_sections_of_finite_cofiltered_system F

end FiniteKonig

namespace CategoryTheory

namespace Functor

variable {J : Type u} [Category* J] (F : J ⥤ Type v) {i j k : J} (s : Set (F.obj i))

/--
Definition of `eventualRange` / `eventualRange` 的定义

English:
definition eventualRange
  signature: (j : J)
  body: ⋂ (i) (f : i ⟶ j), range (F.map f)

中文:
定义 eventualRange
  签名: (j : J)
  定义体: ⋂ (i) (f : i ⟶ j), range (F.map f)

Depends on / 依赖: F.map
-/
def eventualRange (j : J) :=
  ⋂ (i) (f : i ⟶ j), range (F.map f)

/--
theorem `mem_eventualRange_iff` / 定理 `mem_eventualRange_iff`

English:
theorem mem_eventualRange_iff
  given: {x : F.obj j}
  proof: mem_iInter₂

中文:
定理 mem_eventualRange_iff
  条件: {x : F.obj j}
  证明: mem_iInter₂
-/
theorem mem_eventualRange_iff {x : F.obj j} :
    x in F.eventualRange j ↔ forall ⦃i⦄ (f : i ⟶ j), x in range (F.map f) :=
  mem_iInter₂

/--
Definition of `IsMittagLeffler` / `IsMittagLeffler` 的定义

English:
definition IsMittagLeffler
  signature: : Prop
  body: forall j : J, exists (i : _) (f : i ⟶ j), forall ⦃k⦄ (g : k ⟶ j), range (F.map f) subseteq range (F.map g)

中文:
定义 IsMittagLeffler
  签名: : 命题
  定义体: forall j : J, exists (i : _) (f : i ⟶ j), forall ⦃k⦄ (g : k ⟶ j), range (F.map f) subseteq range (F.map g)

Depends on / 依赖: F.map, subseteq
-/
def IsMittagLeffler : Prop :=
  forall j : J, exists (i : _) (f : i ⟶ j), forall ⦃k⦄ (g : k ⟶ j), range (F.map f) subseteq range (F.map g)

/--
theorem `isMittagLeffler_iff_eventualRange` / 定理 `isMittagLeffler_iff_eventualRange`

English:
theorem isMittagLeffler_iff_eventualRange
  proof: forall_congr' fun _ =>
    exists₂_congr fun _ _ =>
⟨fun h => (iInter₂_subset _ _).antisymm subset_iInter₂ h, fun h => h ▸ iInter₂_subset⟩

中文:
定理 isMittagLeffler_iff_eventualRange
  证明: forall_congr' fun _ =>
    exists₂_congr fun _ _ =>
⟨fun h => (iInter₂_subset _ _).antisymm subset_iInter₂ h, fun h => h ▸ iInter₂_subset⟩

Depends on / 依赖: antisymm, forall_congr
-/
theorem isMittagLeffler_iff_eventualRange :
    F.IsMittagLeffler ↔ forall j : J, exists (i : _) (f : i ⟶ j), F.eventualRange j = range (F.map f) :=
  forall_congr' fun _ =>
    exists₂_congr fun _ _ =>
⟨fun h => (iInter₂_subset _ _).antisymm subset_iInter₂ h, fun h => h ▸ iInter₂_subset⟩

/--
theorem `IsMittagLeffler.subset_image_eventualRange` / 定理 `IsMittagLeffler.subset_image_eventualRange`

English:
theorem IsMittagLeffler.subset_image_eventualRange
  given: (h : F.IsMittagLeffler) (f : j ⟶ i)
  proof: by
  obtain ⟨k, g, hg⟩ := F.isMittagLeffler_iff_eventualRange.1 h j
  rw [hg]; intro x hx
  obtain ⟨x, rfl⟩ := F.mem_eventualRange_iff.1 hx (g ≫ f)
  exact ⟨_, ⟨x, rfl⟩, by rw [map_comp, comp_apply]⟩

中文:
定理 IsMittagLeffler.subset_image_eventualRange
  条件: (h : F.IsMittagLeffler) (f : j ⟶ i)
  证明: by
  obtain ⟨k, g, hg⟩ := F.isMittagLeffler_iff_eventualRange.1 h j
  rw [hg]; intro x hx
  obtain ⟨x, rfl⟩ := F.mem_eventualRange_iff.1 hx (g ≫ f)
  exact ⟨_, ⟨x, rfl⟩, by rw [map_comp, comp_apply]⟩

Depends on / 依赖: F.isMittagLeffler_iff_eventualRange, F.mem_eventualRange_iff, comp_apply, isMittagLeffler_iff_eventualRange, map_comp, mem_eventualRange_iff
-/
theorem IsMittagLeffler.subset_image_eventualRange (h : F.IsMittagLeffler) (f : j ⟶ i) :
    F.eventualRange i subseteq F.map f '' F.eventualRange j := by
  obtain ⟨k, g, hg⟩ := F.isMittagLeffler_iff_eventualRange.1 h j
  rw [hg]; intro x hx
  obtain ⟨x, rfl⟩ := F.mem_eventualRange_iff.1 hx (g ≫ f)
  exact ⟨_, ⟨x, rfl⟩, by rw [map_comp, comp_apply]⟩

/--
theorem `eventualRange_eq_range_precomp` / 定理 `eventualRange_eq_range_precomp`

English:
theorem eventualRange_eq_range_precomp
  statement: (f : i ⟶ j) (g : j ⟶ k)
  proof: by
  apply subset_antisymm
  · apply iInter₂_subset
  · rw [h, F.map_comp, types_comp]
    apply range_comp_subset_range

中文:
定理 eventualRange_eq_range_precomp
  结论: (f : i ⟶ j) (g : j ⟶ k)
  证明: by
  apply subset_antisymm
  · apply iInter₂_subset
  · rw [h, F.map_comp, types_comp]
    apply range_comp_subset_range

Depends on / 依赖: F.map_comp, map_comp, range_comp_subset_range, subset_antisymm, types_comp
-/
theorem eventualRange_eq_range_precomp (f : i ⟶ j) (g : j ⟶ k)
    (h : F.eventualRange k = range (F.map g)) : F.eventualRange k = range (F.map <| f ≫ g) := by
  apply subset_antisymm
  · apply iInter₂_subset
  · rw [h, F.map_comp, types_comp]
    apply range_comp_subset_range

/--
theorem `isMittagLeffler_of_surjective` / 定理 `isMittagLeffler_of_surjective`

English:
theorem isMittagLeffler_of_surjective
  given: (h : forall ⦃i j : J⦄ (f : i ⟶ j), Function.Surjective (F.map f))
  proof: fun j => ⟨j, 𝟙 j, fun k g => by rw [map_id, types_id, range_id, (h g).range_eq]⟩

中文:
定理 isMittagLeffler_of_surjective
  条件: (h : 对任意 ⦃i j : J⦄ (f : i ⟶ j), Function.Surjective (F.map f))
  证明: fun j => ⟨j, 𝟙 j, fun k g => by rw [map_id, types_id, range_id, (h g).range_eq]⟩

Depends on / 依赖: map_id, range_eq, range_id, types_id
-/
theorem isMittagLeffler_of_surjective (h : forall ⦃i j : J⦄ (f : i ⟶ j), Function.Surjective (F.map f)) :
    F.IsMittagLeffler :=
  fun j => ⟨j, 𝟙 j, fun k g => by rw [map_id, types_id, range_id, (h g).range_eq]⟩

/-- The subfunctor of `F` obtained by restricting to the preimages of a set `s ∈ F.obj i`. -/
@[simps]
/--
Definition of `toPreimages` / `toPreimages` 的定义

English:
definition toPreimages
  signature: : J ⥤ Type v where
  body: ⋂ f : j ⟶ i, F.map f ⁻¹' s
  map g := ↾(MapsTo.restrict (F.map g) _ _ fun x h => by
    rw [mem_iInter] at h ⊢
    intro f
    rw [← mem_preimage]; rw [preimage_preimage]; rw [mem_preimage]
    convert! h (g ≫ f); rw [F.map_comp]; rfl)

中文:
定义 toPreimages
  签名: : J ⥤ 类型v where
  定义体: ⋂ f : j ⟶ i, F.map f ⁻¹' s
  map g := ↾(MapsTo.restrict (F.map g) _ _ fun x h => by
    rw [mem_iInter] at h ⊢
    intro f
    rw [← mem_preimage]; rw [preimage_preimage]; rw [mem_preimage]
    convert! h (g ≫ f); rw [F.map_comp]; rfl)

Depends on / 依赖: F.map
-/
def toPreimages : J ⥤ Type v where
  obj j := ⋂ f : j ⟶ i, F.map f ⁻¹' s
  map g := ↾(MapsTo.restrict (F.map g) _ _ fun x h => by
    rw [mem_iInter] at h ⊢
    intro f
    rw [← mem_preimage]; rw [preimage_preimage]; rw [mem_preimage]
    convert! h (g ≫ f); rw [F.map_comp]; rfl)

/--
Instance `toPreimages_finite` / 实例 `toPreimages_finite`

English:
instance toPreimages_finite
  signature: [forall j, Finite (F.obj j)]
  body: fun _ => Subtype.finite

中文:
实例 toPreimages_finite
  签名: [对任意 j, Finite (F.obj j)]
  定义体: fun _ => Subtype.finite

Depends on / 依赖: Subtype, Subtype.finite, finite
-/
instance toPreimages_finite [forall j, Finite (F.obj j)] : forall j, Finite ((F.toPreimages s).obj j) :=
  fun _ => Subtype.finite

variable [IsCofilteredOrEmpty J]

/--
theorem `eventualRange_mapsTo` / 定理 `eventualRange_mapsTo`

English:
theorem eventualRange_mapsTo
  given: (f : j ⟶ i)
  proof: fun x hx => by
  rw [mem_eventualRange_iff] at hx ⊢
  intro k f'
  obtain ⟨l, g, g', he⟩ := cospan f f'
  obtain ⟨x, rfl⟩ := hx g
  rw [← comp_apply]; rw [← map_comp]; rw [he]; rw [F.map_comp]
  exact ⟨_, rfl⟩

中文:
定理 eventualRange_mapsTo
  条件: (f : j ⟶ i)
  证明: fun x hx => by
  rw [mem_eventualRange_iff] at hx ⊢
  intro k f'
  obtain ⟨l, g, g', he⟩ := cospan f f'
  obtain ⟨x, rfl⟩ := hx g
  rw [← comp_apply]; rw [← map_comp]; rw [he]; rw [F.map_comp]
  exact ⟨_, rfl⟩

Depends on / 依赖: F.map_comp, comp_apply, cospan, map_comp, mem_eventualRange_iff
-/
theorem eventualRange_mapsTo (f : j ⟶ i) :
    (F.eventualRange j).MapsTo (F.map f) (F.eventualRange i) := fun x hx => by
  rw [mem_eventualRange_iff] at hx ⊢
  intro k f'
  obtain ⟨l, g, g', he⟩ := cospan f f'
  obtain ⟨x, rfl⟩ := hx g
  rw [← comp_apply]; rw [← map_comp]; rw [he]; rw [F.map_comp]
  exact ⟨_, rfl⟩

/--
theorem `IsMittagLeffler.eq_image_eventualRange` / 定理 `IsMittagLeffler.eq_image_eventualRange`

English:
theorem IsMittagLeffler.eq_image_eventualRange
  given: (h : F.IsMittagLeffler) (f : j ⟶ i)
  proof: (h.subset_image_eventualRange F f).antisymm mapsTo_iff_image_subset.1
    (F.eventualRange_mapsTo f)

中文:
定理 IsMittagLeffler.eq_image_eventualRange
  条件: (h : F.IsMittagLeffler) (f : j ⟶ i)
  证明: (h.subset_image_eventualRange F f).antisymm mapsTo_iff_image_subset.1
    (F.eventualRange_mapsTo f)

Depends on / 依赖: F.eventualRange_mapsTo, antisymm, eventualRange_mapsTo, h.subset_image_eventualRange, mapsTo_iff_image_subset, subset_image_eventualRange
-/
theorem IsMittagLeffler.eq_image_eventualRange (h : F.IsMittagLeffler) (f : j ⟶ i) :
    F.eventualRange i = F.map f '' F.eventualRange j :=
(h.subset_image_eventualRange F f).antisymm mapsTo_iff_image_subset.1
    (F.eventualRange_mapsTo f)

/--
theorem `eventualRange_eq_iff` / 定理 `eventualRange_eq_iff`

English:
theorem eventualRange_eq_iff
  given: {f : i ⟶ j}
  proof: by
  rw [subset_antisymm_iff]; rw [eventualRange]; rw [and_iff_right (iInter₂_subset _ _)]; rw [subset_iInter₂_iff]
  refine ⟨fun h k g => h _ _, fun h j' f' => ?_⟩
  obtain ⟨k, g, g', he⟩ := cospan f f'
  refine (h g).trans ?_
  rw [he]; rw [F.map_comp]; rw [types_comp]
  apply range_comp_subset_ra

中文:
定理 eventualRange_eq_iff
  条件: {f : i ⟶ j}
  证明: by
  rw [subset_antisymm_iff]; rw [eventualRange]; rw [and_iff_right (iInter₂_subset _ _)]; rw [subset_iInter₂_iff]
  refine ⟨fun h k g => h _ _, fun h j' f' => ?_⟩
  obtain ⟨k, g, g', he⟩ := cospan f f'
  refine (h g).trans ?_
  rw [he]; rw [F.map_comp]; rw [types_comp]
  apply range_comp_subset_ra

Depends on / 依赖: F.map_comp, and_iff_right, cospan, eventualRange, map_comp, range_comp_subset_range, subset_antisymm_iff, types_comp
-/
theorem eventualRange_eq_iff {f : i ⟶ j} :
    F.eventualRange j = range (F.map f) ↔
      forall ⦃k⦄ (g : k ⟶ i), range (F.map f) subseteq range (F.map <| g ≫ f) := by
  rw [subset_antisymm_iff]; rw [eventualRange]; rw [and_iff_right (iInter₂_subset _ _)]; rw [subset_iInter₂_iff]
  refine ⟨fun h k g => h _ _, fun h j' f' => ?_⟩
  obtain ⟨k, g, g', he⟩ := cospan f f'
  refine (h g).trans ?_
  rw [he]; rw [F.map_comp]; rw [types_comp]
  apply range_comp_subset_range

/--
theorem `isMittagLeffler_iff_subset_range_comp` / 定理 `isMittagLeffler_iff_subset_range_comp`

English:
theorem isMittagLeffler_iff_subset_range_comp
  statement: F.IsMittagLeffler ↔ forall j : J, exists (i : _) (f : i ⟶ j),
  proof: by
  simp_rw [isMittagLeffler_iff_eventualRange, eventualRange_eq_iff]

中文:
定理 isMittagLeffler_iff_subset_range_comp
  结论: F.IsMittagLeffler ↔ 对任意 j : J, 存在 (i : _) (f : i ⟶ j),
  证明: by
  simp_rw [isMittagLeffler_iff_eventualRange, eventualRange_eq_iff]

Depends on / 依赖: HasTerminal, OrderTop, eventualRange_eq_iff, hasTerminal_of_unique, isMittagLeffler_iff_eventualRange, simp_rw
-/
theorem isMittagLeffler_iff_subset_range_comp : F.IsMittagLeffler ↔ forall j : J, exists (i : _) (f : i ⟶ j),
    forall ⦃k⦄ (g : k ⟶ i), range (F.map f) subseteq range (F.map <| g ≫ f) := by
  simp_rw [isMittagLeffler_iff_eventualRange, eventualRange_eq_iff]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsMittagLeffler.toPreimages` / 定理 `IsMittagLeffler.toPreimages`

English:
theorem IsMittagLeffler.toPreimages
  given: (h : F.IsMittagLeffler)
  statement: (F.toPreimages s).IsMittagLeffler
  proof: (isMittagLeffler_iff_subset_range_comp _).2 fun j => by
    obtain ⟨j₁, g₁, f₁, -⟩ := IsCofilteredOrEmpty.cone_objs i j
    obtain ⟨j₂, f₂, h₂⟩ := F.isMittagLeffler_iff_eventualRange.1 h j₁
    refine ⟨j₂, f₂ ≫ f₁, fun j₃ f₃ => ?_⟩
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    have : F.map f₂ x in F.eventualRange

中文:
定理 IsMittagLeffler.toPreimages
  条件: (h : F.IsMittagLeffler)
  结论: (F.toPreimages s).IsMittagLeffler
  证明: (isMittagLeffler_iff_subset_range_comp _).2 fun j => by
    obtain ⟨j₁, g₁, f₁, -⟩ := IsCofilteredOrEmpty.cone_objs i j
    obtain ⟨j₂, f₂, h₂⟩ := F.isMittagLeffler_iff_eventualRange.1 h j₁
    refine ⟨j₂, f₂ ≫ f₁, fun j₃ f₃ => ?_⟩
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    have : F.map f₂ x in F.eventualRange

Depends on / 依赖: F.eventualRange, F.isMittagLeffler_iff_eventualRange, F.map, IsCofilteredOrEmpty, IsCofilteredOrEmpty.cone_maps, IsCofilteredOrEmpty.cone_objs, Subtype, Subtype.ext, cone_maps, cone_objs, eventualRange, h.subset_image_eventualRange, isMittagLeffler_iff_eventualRange, isMittagLeffler_iff_subset_range_comp, mem_iInter, subset_image_eventualRange
-/
theorem IsMittagLeffler.toPreimages (h : F.IsMittagLeffler) : (F.toPreimages s).IsMittagLeffler :=
  (isMittagLeffler_iff_subset_range_comp _).2 fun j => by
    obtain ⟨j₁, g₁, f₁, -⟩ := IsCofilteredOrEmpty.cone_objs i j
    obtain ⟨j₂, f₂, h₂⟩ := F.isMittagLeffler_iff_eventualRange.1 h j₁
    refine ⟨j₂, f₂ ≫ f₁, fun j₃ f₃ => ?_⟩
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    have : F.map f₂ x in F.eventualRange j₁ := by
      rw [h₂]
      exact ⟨_, rfl⟩
    obtain ⟨y, hy, h₃⟩ := h.subset_image_eventualRange F (f₃ ≫ f₂) this
    refine ⟨⟨y, mem_iInter.2 fun g₂ => ?_⟩, Subtype.ext ?_⟩
    · obtain ⟨j₄, f₄, h₄⟩ := IsCofilteredOrEmpty.cone_maps g₂ ((f₃ ≫ f₂) ≫ g₁)
      obtain ⟨y, rfl⟩ := F.mem_eventualRange_iff.1 hy f₄
      rw [← comp_apply]; rw [← map_comp] at h₃
      rw [mem_preimage]; rw [← comp_apply]; rw [← map_comp]; rw [h₄]; rw [← Category.assoc]; rw [map_comp]; rw [comp_apply]; rw [h₃]; rw [← comp_apply]; rw [← map_comp]
      apply mem_iInter.1 hx
    · simp only [toPreimages_obj, toPreimages_map, ConcreteCategory.hom_ofHom,
        TypeCat.Fun.coe_mk, MapsTo.val_restrict_apply]
      rw [← Category.assoc]; rw [map_comp]; rw [comp_apply]; rw [h₃]; rw [map_comp]; rw [comp_apply]

/--
theorem `isMittagLeffler_of_exists_finite_range` / 定理 `isMittagLeffler_of_exists_finite_range`

English:
theorem isMittagLeffler_of_exists_finite_range
  proof: by
  intro j
  obtain ⟨i, hi, hf⟩ := h j
  obtain ⟨m, ⟨i, f, hm⟩, hmin⟩ := Finset.wellFoundedLT.wf.has_min
    { s : Finset (F.obj j) | exists (i : _) (f : i ⟶ j), ↑s = range (F.map f) }
    ⟨_, i, hi, hf.coe_toFinset⟩
  refine ⟨i, f, fun k g =>
    (F.ranges_directed j).directedOn_range.is_bot_of_i

中文:
定理 isMittagLeffler_of_exists_finite_range
  证明: by
  intro j
  obtain ⟨i, hi, hf⟩ := h j
  obtain ⟨m, ⟨i, f, hm⟩, hmin⟩ := Finset.wellFoundedLT.wf.has_min
    { s : Finset (F.obj j) | exists (i : _) (f : i ⟶ j), ↑s = range (F.map f) }
    ⟨_, i, hi, hf.coe_toFinset⟩
  refine ⟨i, f, fun k g =>
    (F.ranges_directed j).directedOn_range.is_bot_of_i

Depends on / 依赖: F.map, F.obj, F.ranges_directed, Finite, Finset, Finset.coe_ssubset, Finset.wellFoundedLT.wf.has_min, Set.Finite, coe_ssubset, coe_toFinset, directedOn_range, directedOn_range.is_bot_of_is_min, eq_of_le_of_not_lt, finite_toSet, has_min, hf.coe_toFinset, hm.substr, is_bot_of_is_min, m.finite_toSet.subset, ranges_directed
-/
theorem isMittagLeffler_of_exists_finite_range
    (h : forall j : J, exists (i : _) (f : i ⟶ j), (range <| F.map f).Finite) : F.IsMittagLeffler := by
  intro j
  obtain ⟨i, hi, hf⟩ := h j
  obtain ⟨m, ⟨i, f, hm⟩, hmin⟩ := Finset.wellFoundedLT.wf.has_min
    { s : Finset (F.obj j) | exists (i : _) (f : i ⟶ j), ↑s = range (F.map f) }
    ⟨_, i, hi, hf.coe_toFinset⟩
  refine ⟨i, f, fun k g =>
    (F.ranges_directed j).directedOn_range.is_bot_of_is_min ⟨⟨i, f⟩, rfl⟩ ?_ _ ⟨⟨k, g⟩, rfl⟩⟩
  rintro _ ⟨⟨k', g'⟩, rfl⟩ hl
  refine (eq_of_le_of_not_lt hl ?_).ge
  have := hmin _ ⟨k', g', (m.finite_toSet.subset <| hm.substr hl).coe_toFinset⟩
  rwa [← Finset.coe_ssubset, Set.Finite.coe_toFinset, hm] at this

/-- The subfunctor of `F` obtained by restricting to the eventual range at each index. -/
@[simps obj map]
/--
Definition of `toEventualRanges` / `toEventualRanges` 的定义

English:
definition toEventualRanges
  signature: : J ⥤ Type v where
  body: F.eventualRange j
  map f := ↾((F.eventualRange_mapsTo f).restrict _ _ _)

中文:
定义 toEventualRanges
  签名: : J ⥤ 类型v where
  定义体: F.eventualRange j
  map f := ↾((F.eventualRange_mapsTo f).restrict _ _ _)

Depends on / 依赖: F.eventualRange, eventualRange
-/
def toEventualRanges : J ⥤ Type v where
  obj j := F.eventualRange j
  map f := ↾((F.eventualRange_mapsTo f).restrict _ _ _)

/--
Instance `toEventualRanges_finite` / 实例 `toEventualRanges_finite`

English:
instance toEventualRanges_finite
  signature: [forall j, Finite (F.obj j)]
  body: fun _ => Subtype.finite

中文:
实例 toEventualRanges_finite
  签名: [对任意 j, Finite (F.obj j)]
  定义体: fun _ => Subtype.finite

Depends on / 依赖: HasInitial, OrderBot, Subtype, Subtype.finite, finite, hasInitial_of_unique
-/
instance toEventualRanges_finite [forall j, Finite (F.obj j)] : forall j, Finite (F.toEventualRanges.obj j) :=
  fun _ => Subtype.finite

/--
Definition of `toEventualRangesSectionsEquiv` / `toEventualRangesSectionsEquiv` 的定义

English:
definition toEventualRangesSectionsEquiv
  signature: : F.toEventualRanges.sections ≃ F.sections where
  body: ⟨_, fun f => Subtype.coe_inj.2 s.prop f⟩
  invFun s :=
⟨fun _ => ⟨_, mem_iInter₂.2 fun _ f => ⟨_, s.prop f⟩⟩, fun f => Subtype.ext s.prop f⟩

中文:
定义 toEventualRangesSectionsEquiv
  签名: : F.toEventualRanges.sections ≃ F.sections where
  定义体: ⟨_, fun f => Subtype.coe_inj.2 s.prop f⟩
  invFun s :=
⟨fun _ => ⟨_, mem_iInter₂.2 fun _ f => ⟨_, s.prop f⟩⟩, fun f => Subtype.ext s.prop f⟩

Depends on / 依赖: Subtype, Subtype.coe_inj, coe_inj, s.prop
-/
def toEventualRangesSectionsEquiv : F.toEventualRanges.sections ≃ F.sections where
toFun s := ⟨_, fun f => Subtype.coe_inj.2 s.prop f⟩
  invFun s :=
⟨fun _ => ⟨_, mem_iInter₂.2 fun _ f => ⟨_, s.prop f⟩⟩, fun f => Subtype.ext s.prop f⟩

/--
theorem `surjective_toEventualRanges` / 定理 `surjective_toEventualRanges`

English:
theorem surjective_toEventualRanges
  given: (h : F.IsMittagLeffler) ⦃i j⦄ (f : i ⟶ j)
  proof: fun ⟨x, hx⟩ => by
  obtain ⟨y, hy, rfl⟩ := h.subset_image_eventualRange F f hx
  exact ⟨⟨y, hy⟩, rfl⟩

中文:
定理 surjective_toEventualRanges
  条件: (h : F.IsMittagLeffler) ⦃i j⦄ (f : i ⟶ j)
  证明: fun ⟨x, hx⟩ => by
  obtain ⟨y, hy, rfl⟩ := h.subset_image_eventualRange F f hx
  exact ⟨⟨y, hy⟩, rfl⟩

Depends on / 依赖: h.subset_image_eventualRange, subset_image_eventualRange
-/
theorem surjective_toEventualRanges (h : F.IsMittagLeffler) ⦃i j⦄ (f : i ⟶ j) :
    Function.Surjective (F.toEventualRanges.map f) := fun ⟨x, hx⟩ => by
  obtain ⟨y, hy, rfl⟩ := h.subset_image_eventualRange F f hx
  exact ⟨⟨y, hy⟩, rfl⟩

/--
theorem `toEventualRanges_nonempty` / 定理 `toEventualRanges_nonempty`

English:
theorem toEventualRanges_nonempty
  given: (h : F.IsMittagLeffler) [forall j : J, Nonempty (F.obj j)] (j : J)
  proof: by
  let ⟨i, f, h⟩ := F.isMittagLeffler_iff_eventualRange.1 h j
  rw [toEventualRanges_obj]; rw [h]
  infer_instance

中文:
定理 toEventualRanges_nonempty
  条件: (h : F.IsMittagLeffler) [对任意 j : J, Nonempty (F.obj j)] (j : J)
  证明: by
  let ⟨i, f, h⟩ := F.isMittagLeffler_iff_eventualRange.1 h j
  rw [toEventualRanges_obj]; rw [h]
  infer_instance

Depends on / 依赖: F.isMittagLeffler_iff_eventualRange, infer_instance, isMittagLeffler_iff_eventualRange, toEventualRanges_obj
-/
theorem toEventualRanges_nonempty (h : F.IsMittagLeffler) [forall j : J, Nonempty (F.obj j)] (j : J) :
    Nonempty (F.toEventualRanges.obj j) := by
  let ⟨i, f, h⟩ := F.isMittagLeffler_iff_eventualRange.1 h j
  rw [toEventualRanges_obj]; rw [h]
  infer_instance

/--
theorem `thin_diagram_of_surjective` / 定理 `thin_diagram_of_surjective`

English:
theorem thin_diagram_of_surjective
  proof: by
  let ⟨k, φ, hφ⟩ := IsCofilteredOrEmpty.cone_maps f g
  apply ConcreteCategory.ext
  have := congrArg F.map hφ
  simp only [map_comp, ConcreteCategory.ext_iff, DFunLike.ext_iff, comp_apply, ← funext_iff] at this
simpa using (Fsur φ).injective_comp_right this

中文:
定理 thin_diagram_of_surjective
  证明: by
  let ⟨k, φ, hφ⟩ := IsCofilteredOrEmpty.cone_maps f g
  apply ConcreteCategory.ext
  have := congrArg F.map hφ
  simp only [map_comp, ConcreteCategory.ext_iff, DFunLike.ext_iff, comp_apply, ← funext_iff] at this
simpa using (Fsur φ).injective_comp_right this

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ext, ConcreteCategory.ext_iff, DFunLike, DFunLike.ext_iff, F.map, IsCofilteredOrEmpty, IsCofilteredOrEmpty.cone_maps, comp_apply, cone_maps, ext_iff, funext_iff, injective_comp_right, map_comp
-/
theorem thin_diagram_of_surjective
    (Fsur : forall ⦃i j : J⦄ (f : i ⟶ j), Function.Surjective (F.map f)) {i j}
    (f g : i ⟶ j) : F.map f = F.map g := by
  let ⟨k, φ, hφ⟩ := IsCofilteredOrEmpty.cone_maps f g
  apply ConcreteCategory.ext
  have := congrArg F.map hφ
  simp only [map_comp, ConcreteCategory.ext_iff, DFunLike.ext_iff, comp_apply, ← funext_iff] at this
simpa using (Fsur φ).injective_comp_right this

/--
theorem `toPreimages_nonempty_of_surjective` / 定理 `toPreimages_nonempty_of_surjective`

English:
theorem toPreimages_nonempty_of_surjective
  statement: [hFn : forall j : J, Nonempty (F.obj j)]
  proof: by
  simp only [toPreimages_obj, nonempty_coe_sort, nonempty_iInter, mem_preimage]
  obtain h | ⟨⟨ji⟩⟩ := isEmpty_or_nonempty (j ⟶ i)
  · exact ⟨(hFn j).some, fun ji => h.elim ji⟩
  · obtain ⟨y, ys⟩ := hs
    obtain ⟨x, rfl⟩ := Fsur ji y
    exact ⟨x, fun ji' => (F.thin_diagram_of_surjective Fsur ji

中文:
定理 toPreimages_nonempty_of_surjective
  结论: [hFn : 对任意 j : J, Nonempty (F.obj j)]
  证明: by
  simp only [toPreimages_obj, nonempty_coe_sort, nonempty_iInter, mem_preimage]
  obtain h | ⟨⟨ji⟩⟩ := isEmpty_or_nonempty (j ⟶ i)
  · exact ⟨(hFn j).some, fun ji => h.elim ji⟩
  · obtain ⟨y, ys⟩ := hs
    obtain ⟨x, rfl⟩ := Fsur ji y
    exact ⟨x, fun ji' => (F.thin_diagram_of_surjective Fsur ji

Depends on / 依赖: F.thin_diagram_of_surjective, h.elim, isEmpty_or_nonempty, mem_preimage, nonempty_coe_sort, nonempty_iInter, thin_diagram_of_surjective, toPreimages_obj
-/
theorem toPreimages_nonempty_of_surjective [hFn : forall j : J, Nonempty (F.obj j)]
    (Fsur : forall ⦃i j : J⦄ (f : i ⟶ j), Function.Surjective (F.map f)) (hs : s.Nonempty) (j) :
    Nonempty ((F.toPreimages s).obj j) := by
  simp only [toPreimages_obj, nonempty_coe_sort, nonempty_iInter, mem_preimage]
  obtain h | ⟨⟨ji⟩⟩ := isEmpty_or_nonempty (j ⟶ i)
  · exact ⟨(hFn j).some, fun ji => h.elim ji⟩
  · obtain ⟨y, ys⟩ := hs
    obtain ⟨x, rfl⟩ := Fsur ji y
    exact ⟨x, fun ji' => (F.thin_diagram_of_surjective Fsur ji' ji).symm ▸ ys⟩

/--
theorem `eval_section_injective_of_eventually_injective` / 定理 `eval_section_injective_of_eventually_injective`

English:
theorem eval_section_injective_of_eventually_injective
  statement: {j}
  proof: by
refine fun s₀ s₁ h => Subtype.ext funext fun k => ?_
  obtain ⟨m, mi, mk, _⟩ := IsCofilteredOrEmpty.cone_objs i k
  dsimp at h
  rw [← s₀.prop (mi ≫ f)]; rw [← s₁.prop (mi ≫ f)] at h
  rw [← s₀.prop mk]; rw [← s₁.prop mk]
  exact congr_arg _ (Finj m (mi ≫ f) h)

中文:
定理 eval_section_injective_of_eventually_injective
  结论: {j}
  证明: by
refine fun s₀ s₁ h => Subtype.ext funext fun k => ?_
  obtain ⟨m, mi, mk, _⟩ := IsCofilteredOrEmpty.cone_objs i k
  dsimp at h
  rw [← s₀.prop (mi ≫ f)]; rw [← s₁.prop (mi ≫ f)] at h
  rw [← s₀.prop mk]; rw [← s₁.prop mk]
  exact congr_arg _ (Finj m (mi ≫ f) h)

Depends on / 依赖: HasBinaryProducts, IsCofilteredOrEmpty, IsCofilteredOrEmpty.cone_objs, SemilatticeInf, Subtype, Subtype.ext, cone_objs, congr_arg
-/
theorem eval_section_injective_of_eventually_injective {j}
    (Finj : forall (i) (f : i ⟶ j), Function.Injective (F.map f)) (i) (f : i ⟶ j) :
    (fun s : F.sections => s.val j).Injective := by
refine fun s₀ s₁ h => Subtype.ext funext fun k => ?_
  obtain ⟨m, mi, mk, _⟩ := IsCofilteredOrEmpty.cone_objs i k
  dsimp at h
  rw [← s₀.prop (mi ≫ f)]; rw [← s₁.prop (mi ≫ f)] at h
  rw [← s₀.prop mk]; rw [← s₁.prop mk]
  exact congr_arg _ (Finj m (mi ≫ f) h)

section FiniteCofilteredSystem

variable [forall j : J, Nonempty (F.obj j)] [forall j : J, Finite (F.obj j)]
  (Fsur : forall ⦃i j : J⦄ (f : i ⟶ j), Function.Surjective (F.map f))
include Fsur

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `eval_section_surjective_of_surjective` / 定理 `eval_section_surjective_of_surjective`

English:
theorem eval_section_surjective_of_surjective
  given: (i : J)
  proof: fun x => by
  let s : Set (F.obj i) := {x}
  have := F.toPreimages_nonempty_of_surjective s Fsur (singleton_nonempty x)
  obtain ⟨sec, h⟩ := nonempty_sections_of_finite_cofiltered_system (F.toPreimages s)
  refine ⟨⟨fun j => (sec j).val, fun jk => by simpa [Subtype.ext_iff] using! h jk⟩, ?_⟩
  · hav

中文:
定理 eval_section_surjective_of_surjective
  条件: (i : J)
  证明: fun x => by
  let s : Set (F.obj i) := {x}
  have := F.toPreimages_nonempty_of_surjective s Fsur (singleton_nonempty x)
  obtain ⟨sec, h⟩ := nonempty_sections_of_finite_cofiltered_system (F.toPreimages s)
  refine ⟨⟨fun j => (sec j).val, fun jk => by simpa [Subtype.ext_iff] using! h jk⟩, ?_⟩
  · hav

Depends on / 依赖: F.obj, F.toPreimages, F.toPreimages_nonempty_of_surjective, Subtype, Subtype.ext_iff, ext_iff, id_apply, map_id, mem_iInter, mem_preimage, nonempty_sections_of_finite_cofiltered_system, singleton_nonempty, toPreimages, toPreimages_nonempty_of_surjective
-/
theorem eval_section_surjective_of_surjective (i : J) :
    (fun s : F.sections => s.val i).Surjective := fun x => by
  let s : Set (F.obj i) := {x}
  have := F.toPreimages_nonempty_of_surjective s Fsur (singleton_nonempty x)
  obtain ⟨sec, h⟩ := nonempty_sections_of_finite_cofiltered_system (F.toPreimages s)
  refine ⟨⟨fun j => (sec j).val, fun jk => by simpa [Subtype.ext_iff] using! h jk⟩, ?_⟩
  · have := (sec i).prop
    simp only [mem_iInter, mem_preimage] at this
    have := this (𝟙 i)
    rwa [map_id, id_apply] at this

/--
theorem `eventually_injective` / 定理 `eventually_injective`

English:
theorem eventually_injective
  given: [Nonempty J] [Finite F.sections]
  proof: by
  have : forall j, Fintype (F.obj j) := fun j => Fintype.ofFinite (F.obj j)
  have : Fintype F.sections := Fintype.ofFinite F.sections
  have card_le : forall j, Fintype.card (F.obj j) <= Fintype.card F.sections :=
    fun j => Fintype.card_le_of_surjective _ (F.eval_section_surjective_of_surject

中文:
定理 eventually_injective
  条件: [Nonempty J] [Finite F.sections]
  证明: by
  have : forall j, Fintype (F.obj j) := fun j => Fintype.ofFinite (F.obj j)
  have : Fintype F.sections := Fintype.ofFinite F.sections
  have card_le : forall j, Fintype.card (F.obj j) <= Fintype.card F.sections :=
    fun j => Fintype.card_le_of_surjective _ (F.eval_section_surjective_of_surject

Depends on / 依赖: F.eval_section_surjective_of_surjective, F.obj, F.sections, Fintype, Fintype.bijective_iff_surjective_and_card, Fintype.card, Fintype.card_le_of_surjective, Fintype.ofFinite, HasBinaryCoproducts, SemilatticeSup, argmin, bijective_iff_surjective_and_card, card_le, card_le_of_surjective, eval_section_surjective_of_surjective, fn.argmin, le_antisymm, ofFinite, sections
-/
theorem eventually_injective [Nonempty J] [Finite F.sections] :
    exists j, forall (i) (f : i ⟶ j), Function.Injective (F.map f) := by
  have : forall j, Fintype (F.obj j) := fun j => Fintype.ofFinite (F.obj j)
  have : Fintype F.sections := Fintype.ofFinite F.sections
  have card_le : forall j, Fintype.card (F.obj j) <= Fintype.card F.sections :=
    fun j => Fintype.card_le_of_surjective _ (F.eval_section_surjective_of_surjective Fsur j)
  let fn j := Fintype.card F.sections - Fintype.card (F.obj j)
  refine ⟨fn.argmin,
    fun i f => ((Fintype.bijective_iff_surjective_and_card _).2
      ⟨Fsur f, le_antisymm ?_ (Fintype.card_le_of_surjective _ <| Fsur f)⟩).1⟩
  rw [← Nat.sub_le_sub_iff_left (card_le i)]
  apply fn.argmin_le

end FiniteCofilteredSystem

end Functor

end CategoryTheory
