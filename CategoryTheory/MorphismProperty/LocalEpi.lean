/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Localization.Bousfield

/-!
# Local epimorphisms with respect to an object property

Let `P` be an object property on a category `C`. We say that `f : X ⟶ Y`
is a local epimorphism wrt. `P` if `f` cancels on the left for morphisms with
codomain in `P`.

If `C` is the category of presheafs on some category with Grothendieck topology `J` and `P` the
property of being a sheaf for `J`, then being a local epimorphism wrt. `P` is being
an epimorphism after sheafification.

## Main declarations

- `CategoryTheory.ObjectProperty.localEpi`: The morphism property of local epimorphisms.
- `CategoryTheory.ObjectProperty.localEpi_mem_range_iff_epi`: If `F ⊣ G` and `G`
  is fully faithful, then `f : X ⟶ Y` is a local epimorphism if and only if `F.map f` is an
  epimorphism.

## References

The terminology is from [M. Kashiwara, P. Schapira, *Categories and Sheaves*, 16.1][Kashiwara2006].
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] {P : ObjectProperty C}

namespace ObjectProperty

/--
Definition of `localEpi` / `localEpi` 的定义

English:
definition localEpi
  signature: (P : ObjectProperty C)
  body: fun _ _ f =>
  forall ⦃Z⦄, P Z -> Function.Injective fun (g : _ ⟶ Z) => f ≫ g

中文:
定义 localEpi
  签名: (P : ObjectProperty C)
  定义体: fun _ _ f =>
  forall ⦃Z⦄, P Z -> Function.Injective fun (g : _ ⟶ Z) => f ≫ g

Depends on / 依赖: Functor, Functor.ShiftSequence.tautological, ShiftSequence, tautological
-/
def localEpi (P : ObjectProperty C) : MorphismProperty C := fun _ _ f =>
  forall ⦃Z⦄, P Z -> Function.Injective fun (g : _ ⟶ Z) => f ≫ g

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.localEpi.IsMultiplicative
  body: by simpa using! Function.injective_id
  comp_mem f g hf hg T hT _ _ huv := hg hT (hf hT <| by simpa using huv)

中文:
实例 :
  签名: P.localEpi.是Multiplicative
  定义体: by simpa using! Function.injective_id
  comp_mem f g hf hg T hT _ _ huv := hg hT (hf hT <| by simpa using huv)

Depends on / 依赖: Function, Function.injective_id, comp_mem, injective_id
-/
instance : P.localEpi.IsMultiplicative where
  id_mem X Z _ := by simpa using! Function.injective_id
  comp_mem f g hf hg T hT _ _ huv := hg hT (hf hT <| by simpa using huv)

/--
lemma `localEpi.of_epi` / 引理 `localEpi.of_epi`

English:
lemma localEpi.of_epi
  given: {X Y : C} (f : X ⟶ Y) [Epi f]
  statement: P.localEpi f
  proof: by
  intro Z hZ u v huv
  rwa [← cancel_epi f]

@[simp]

中文:
引理 localEpi.of_epi
  条件: {X Y : C} (f : X ⟶ Y) [满态射 f]
  结论: P.localEpi f
  证明: by
  intro Z hZ u v huv
  rwa [← cancel_epi f]

@[simp]

Depends on / 依赖: cancel_epi, preadditiveYoneda, preadditiveYoneda.obj
-/
lemma localEpi.of_epi {X Y : C} (f : X ⟶ Y) [Epi f] : P.localEpi f := by
  intro Z hZ u v huv
  rwa [← cancel_epi f]

@[simp]
/--
lemma `localEpi_top_apply_iff` / 引理 `localEpi_top_apply_iff`

English:
lemma localEpi_top_apply_iff
  given: {X Y : C} {f : X ⟶ Y}
  proof: ⟨fun h => ⟨fun _ _ huv => h trivial huv⟩, fun _ => .of_epi _⟩

中文:
引理 localEpi_top_apply_iff
  条件: {X Y : C} {f : X ⟶ Y}
  证明: ⟨fun h => ⟨fun _ _ huv => h trivial huv⟩, fun _ => .of_epi _⟩

Depends on / 依赖: of_epi
-/
lemma localEpi_top_apply_iff {X Y : C} {f : X ⟶ Y} :
    (⊤ : ObjectProperty C).localEpi f ↔ Epi f :=
  ⟨fun h => ⟨fun _ _ huv => h trivial huv⟩, fun _ => .of_epi _⟩

/--
lemma `localEpi_top_eq_epimorphisms` / 引理 `localEpi_top_eq_epimorphisms`

English:
lemma localEpi_top_eq_epimorphisms
  statement: (⊤ : ObjectProperty C).localEpi = .epimorphisms C
  proof: by
  ext
  simp

中文:
引理 localEpi_top_eq_epimorphisms
  结论: (⊤ : ObjectProperty C).localEpi = .epimorphisms C
  证明: by
  ext
  simp
-/
lemma localEpi_top_eq_epimorphisms : (⊤ : ObjectProperty C).localEpi = .epimorphisms C := by
  ext
  simp

/--
lemma `localEpi_antitone` / 引理 `localEpi_antitone`

English:
lemma localEpi_antitone
  statement: Antitone (localEpi (C := C))
  proof: fun _ _ hPQ _ _ _ hf _ hZ _ _ huv => hf (hPQ _ hZ) huv

中文:
引理 localEpi_antitone
  结论: 递减 (localEpi (C := C))
  证明: fun _ _ hPQ _ _ _ hf _ hZ _ _ huv => hf (hPQ _ hZ) huv
-/
lemma localEpi_antitone : Antitone (localEpi (C := C)) :=
  fun _ _ hPQ _ _ _ hf _ hZ _ _ huv => hf (hPQ _ hZ) huv

/--
lemma `localEpi_isoClosure` / 引理 `localEpi_isoClosure`

English:
lemma localEpi_isoClosure
  statement: P.isoClosure.localEpi = P.localEpi
  proof: by
  refine le_antisymm (localEpi_antitone <| le_isoClosure P) ?_
  intro X Y f hf Z ⟨T, hT, ⟨e⟩⟩ u v huv
  rw [← cancel_mono e.hom]
  apply hf hT
  simpa

中文:
引理 localEpi_isoClosure
  结论: P.isoClosure.localEpi = P.localEpi
  证明: by
  refine le_antisymm (localEpi_antitone <| le_isoClosure P) ?_
  intro X Y f hf Z ⟨T, hT, ⟨e⟩⟩ u v huv
  rw [← cancel_mono e.hom]
  apply hf hT
  simpa

Depends on / 依赖: cancel_mono, e.hom, le_antisymm, le_isoClosure, localEpi_antitone
-/
lemma localEpi_isoClosure : P.isoClosure.localEpi = P.localEpi := by
  refine le_antisymm (localEpi_antitone <| le_isoClosure P) ?_
  intro X Y f hf Z ⟨T, hT, ⟨e⟩⟩ u v huv
  rw [← cancel_mono e.hom]
  apply hf hT
  simpa

/--
lemma `isLocal_le_localEpi` / 引理 `isLocal_le_localEpi`

English:
lemma isLocal_le_localEpi
  statement: P.isLocal <= P.localEpi
  proof: fun _ _ _ hf Z hZ => (hf Z hZ).injective

中文:
引理 isLocal_le_localEpi
  结论: P.isLocal <= P.localEpi
  证明: fun _ _ _ hf Z hZ => (hf Z hZ).injective

Depends on / 依赖: injective
-/
lemma isLocal_le_localEpi : P.isLocal <= P.localEpi :=
  fun _ _ _ hf Z hZ => (hf Z hZ).injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.localEpi.RespectsIso
  body: MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ _ _ => .of_epi _

中文:
实例 :
  签名: P.localEpi.RespectsIso
  定义体: MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ _ _ => .of_epi _

Depends on / 依赖: MorphismProperty, MorphismProperty.respectsIso_of_isStableUnderComposition, of_epi, respectsIso_of_isStableUnderComposition
-/
instance : P.localEpi.RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ _ _ => .of_epi _

instance (W : MorphismProperty C) : P.localEpi.HasOfPrecompProperty W where
  of_precomp {X Y Z} f g _ hfg T hT u v huv := hfg hT (by simp [huv])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.localEpi.HasOfPostcompProperty P.isLocal
  body: by
    obtain ⟨u, rfl⟩ := (hg _ hT).surjective u
    obtain ⟨v, rfl⟩ := (hg _ hT).surjective v
    simp [hfg hT (by simpa using huv)]

中文:
实例 :
  签名: P.localEpi.有OfPostcompProperty P.isLocal
  定义体: by
    obtain ⟨u, rfl⟩ := (hg _ hT).surjective u
    obtain ⟨v, rfl⟩ := (hg _ hT).surjective v
    simp [hfg hT (by simpa using huv)]

Depends on / 依赖: surjective
-/
instance : P.localEpi.HasOfPostcompProperty P.isLocal where
  of_postcomp {X Y Z} f g hg hfg T hT u v huv := by
    obtain ⟨u, rfl⟩ := (hg _ hT).surjective u
    obtain ⟨v, rfl⟩ := (hg _ hT).surjective v
    simp [hfg hT (by simpa using huv)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.localEpi.IsStableUnderCobaseChange
  body: by
  refine .mk' fun X Y S f g _ hg T hT u v huv => ?_
  refine pushout.hom_ext (hg hT ?_) huv
  simp [pushout.condition_assoc, huv]

中文:
实例 :
  签名: P.localEpi.是StableUnderCobaseChange
  定义体: by
  refine .mk' fun X Y S f g _ hg T hT u v huv => ?_
  refine pushout.hom_ext (hg hT ?_) huv
  simp [pushout.condition_assoc, huv]

Depends on / 依赖: Functor, Functor.map_comp_assoc, Functor.map_id, Iso.hom_inv_id_app, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc, _op_hom_app, cancel_epi, condition_assoc, hom.app, hom_ext, hom_inv_id_app, id_comp, inv_hom_id_app, inv_hom_id_app_assoc, map_comp_assoc, map_id, op_comp_assoc, op_id, pushout
-/
instance : P.localEpi.IsStableUnderCobaseChange := by
  refine .mk' fun X Y S f g _ hg T hT u v huv => ?_
  refine pushout.hom_ext (hg hT ?_) huv
  simp [pushout.condition_assoc, huv]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.localEpi.Respects P.isLocal
  body: MorphismProperty.comp_mem _ _ _ (isLocal_le_localEpi _ hf) hg
  postcomp _ hf _ hg := MorphismProperty.comp_mem _ _ _ hg (isLocal_le_localEpi _ hf)

中文:
实例 :
  签名: P.localEpi.Respects P.isLocal
  定义体: MorphismProperty.comp_mem _ _ _ (isLocal_le_localEpi _ hf) hg
  postcomp _ hf _ hg := MorphismProperty.comp_mem _ _ _ hg (isLocal_le_localEpi _ hf)

Depends on / 依赖: MorphismProperty, MorphismProperty.comp_mem, comp_mem, isLocal_le_localEpi
-/
instance : P.localEpi.Respects P.isLocal where
  precomp _ hf _ hg := MorphismProperty.comp_mem _ _ _ (isLocal_le_localEpi _ hf) hg
  postcomp _ hf _ hg := MorphismProperty.comp_mem _ _ _ hg (isLocal_le_localEpi _ hf)

variable {D : Type*} [Category* D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  [G.Faithful] [G.Full]
include adj

set_option backward.isDefEq.respectTransparency false in
/--
lemma `localEpi_mem_range_iff_epi` / 引理 `localEpi_mem_range_iff_epi`

English:
lemma localEpi_mem_range_iff_epi
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  rw [← dsimp% (localEpi (· in Set.range G.obj)).postcomp_iff _ _ (isLocal_adj_unit_app adj Y)]; rw [dsimp% adj.unit.naturality f]; rw [dsimp% (localEpi (· in Set.range G.obj)).precomp_iff _ _ (isLocal_adj_unit_app adj X)]
  refine ⟨fun h => ⟨fun {Z} u v huv => ?_⟩, ?_⟩
  · refine G.map_injective

中文:
引理 localEpi_mem_range_iff_epi
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  rw [← dsimp% (localEpi (· in Set.range G.obj)).postcomp_iff _ _ (isLocal_adj_unit_app adj Y)]; rw [dsimp% adj.unit.naturality f]; rw [dsimp% (localEpi (· in Set.range G.obj)).precomp_iff _ _ (isLocal_adj_unit_app adj X)]
  refine ⟨fun h => ⟨fun {Z} u v huv => ?_⟩, ?_⟩
  · refine G.map_injective

Depends on / 依赖: Functor, Functor.map_comp, G.map_comp, G.map_injective, G.map_injective_iff, G.map_surjective, G.obj, Set.range, adj.unit.naturality, isLocal_adj_unit_app, localEpi, map_comp, map_injective, map_injective_iff, map_surjective, naturality, postcomp_iff, precomp_iff
-/
lemma localEpi_mem_range_iff_epi {X Y : C} (f : X ⟶ Y) :
    localEpi (· in Set.range G.obj) f ↔ Epi (F.map f) := by
  rw [← dsimp% (localEpi (· in Set.range G.obj)).postcomp_iff _ _ (isLocal_adj_unit_app adj Y)]; rw [dsimp% adj.unit.naturality f]; rw [dsimp% (localEpi (· in Set.range G.obj)).precomp_iff _ _ (isLocal_adj_unit_app adj X)]
  refine ⟨fun h => ⟨fun {Z} u v huv => ?_⟩, ?_⟩
  · refine G.map_injective ?_
    apply h ⟨Z, rfl⟩
    simp [← Functor.map_comp, huv]
  · rintro h _ ⟨Z, rfl⟩ u v huv
    obtain ⟨u, rfl⟩ := G.map_surjective u
    obtain ⟨v, rfl⟩ := G.map_surjective v
    simp only [← G.map_comp, G.map_injective_iff, cancel_epi] at huv
    rw [huv]

/--
lemma `localEpi_mem_range_eq_inverseImage_epimorphisms` / 引理 `localEpi_mem_range_eq_inverseImage_epimorphisms`

English:
lemma localEpi_mem_range_eq_inverseImage_epimorphisms
  proof: by
  ext X Y f
  rw [localEpi_mem_range_iff_epi adj]
  simp

中文:
引理 localEpi_mem_range_eq_inverseImage_epimorphisms
  证明: by
  ext X Y f
  rw [localEpi_mem_range_iff_epi adj]
  simp

Depends on / 依赖: localEpi_mem_range_iff_epi
-/
lemma localEpi_mem_range_eq_inverseImage_epimorphisms :
    localEpi (· in Set.range G.obj) = (MorphismProperty.epimorphisms _).inverseImage F := by
  ext X Y f
  rw [localEpi_mem_range_iff_epi adj]
  simp

/--
lemma `localEpi_essImage` / 引理 `localEpi_essImage`

English:
lemma localEpi_essImage
  proof: by
  rw [← Functor.isoClosure_eq_essImage]; rw [localEpi_isoClosure]; rw [localEpi_mem_range_eq_inverseImage_epimorphisms adj]

中文:
引理 localEpi_essImage
  证明: by
  rw [← Functor.isoClosure_eq_essImage]; rw [localEpi_isoClosure]; rw [localEpi_mem_range_eq_inverseImage_epimorphisms adj]

Depends on / 依赖: Functor, Functor.isoClosure_eq_essImage, isoClosure_eq_essImage, localEpi_isoClosure, localEpi_mem_range_eq_inverseImage_epimorphisms
-/
lemma localEpi_essImage :
    G.essImage.localEpi = (MorphismProperty.epimorphisms _).inverseImage F := by
  rw [← Functor.isoClosure_eq_essImage]; rw [localEpi_isoClosure]; rw [localEpi_mem_range_eq_inverseImage_epimorphisms adj]

end ObjectProperty

end CategoryTheory
