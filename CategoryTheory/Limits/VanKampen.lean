/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered
public import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!

# Universal colimits and van Kampen colimits

## Main definitions
- `CategoryTheory.IsUniversalColimit`: A (colimit) cocone over a diagram `F : J ⥤ C` is universal
  if it is stable under pullbacks.
- `CategoryTheory.IsVanKampenColimit`: A (colimit) cocone over a diagram `F : J ⥤ C` is van
  Kampen if for every cocone `c'` over the pullback of the diagram `F' : J ⥤ C'`,
  `c'` is colimiting iff `c'` is the pullback of `c`.

## References
- https://ncatlab.org/nlab/show/van+Kampen+colimit
- [Stephen Lack and Paweł Sobociński, Adhesive Categories][adhesive2004]

-/

@[expose] public section


open CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory

universe v' u' v u

variable {J : Type v'} [Category.{u'} J] {C : Type u} [Category.{v} C]
variable {K : Type*} [Category* K] {D : Type*} [Category* D]

/--
Definition of `IsUniversalColimit` / `IsUniversalColimit` 的定义

English:
definition IsUniversalColimit
  signature: {F : J ⥤ C} (c : Cocone F)
  body: forall ⦃F' : J ⥤ C⦄ (c' : Cocone F') (α : F' ⟶ F) (f : c'.pt ⟶ c.pt)
    (_ : α ≫ c.ι = c'.ι ≫ (Functor.const J).map f) (_ : NatTrans.Equifibered α),
    (forall j : J, IsPullback (c'.ι.app j) (α.app j) f (c.ι.app j)) -> Nonempty (IsColimit c')

中文:
定义 IsUniversalColimit
  签名: {F : J ⥤ C} (c : 余锥 F)
  定义体: forall ⦃F' : J ⥤ C⦄ (c' : Cocone F') (α : F' ⟶ F) (f : c'.pt ⟶ c.pt)
    (_ : α ≫ c.ι = c'.ι ≫ (Functor.const J).map f) (_ : NatTrans.Equifibered α),
    (forall j : J, IsPullback (c'.ι.app j) (α.app j) f (c.ι.app j)) -> Nonempty (IsColimit c')

Depends on / 依赖: Cocone, Equifibered, Functor, Functor.const, IsColimit, IsPullback, NatTrans, NatTrans.Equifibered, Nonempty, c.pt
-/
def IsUniversalColimit {F : J ⥤ C} (c : Cocone F) : Prop :=
  forall ⦃F' : J ⥤ C⦄ (c' : Cocone F') (α : F' ⟶ F) (f : c'.pt ⟶ c.pt)
    (_ : α ≫ c.ι = c'.ι ≫ (Functor.const J).map f) (_ : NatTrans.Equifibered α),
    (forall j : J, IsPullback (c'.ι.app j) (α.app j) f (c.ι.app j)) -> Nonempty (IsColimit c')

/--
Definition of `IsVanKampenColimit` / `IsVanKampenColimit` 的定义

English:
definition IsVanKampenColimit
  signature: {F : J ⥤ C} (c : Cocone F)
  body: forall ⦃F' : J ⥤ C⦄ (c' : Cocone F') (α : F' ⟶ F) (f : c'.pt ⟶ c.pt)
    (_ : α ≫ c.ι = c'.ι ≫ (Functor.const J).map f) (_ : NatTrans.Equifibered α),
    Nonempty (IsColimit c') ↔ forall j : J, IsPullback (c'.ι.app j) (α.app j) f (c.ι.app j)

中文:
定义 IsVanKampenColimit
  签名: {F : J ⥤ C} (c : 余锥 F)
  定义体: forall ⦃F' : J ⥤ C⦄ (c' : Cocone F') (α : F' ⟶ F) (f : c'.pt ⟶ c.pt)
    (_ : α ≫ c.ι = c'.ι ≫ (Functor.const J).map f) (_ : NatTrans.Equifibered α),
    Nonempty (IsColimit c') ↔ forall j : J, IsPullback (c'.ι.app j) (α.app j) f (c.ι.app j)

Depends on / 依赖: Cocone, Equifibered, Functor, Functor.const, I.isLimitKernelFork, IsColimit, IsPullback, NatTrans, NatTrans.Equifibered, Nonempty, c.pt, infer_instance, isLimitKernelFork, mono_of_isLimit_fork
-/
def IsVanKampenColimit {F : J ⥤ C} (c : Cocone F) : Prop :=
  forall ⦃F' : J ⥤ C⦄ (c' : Cocone F') (α : F' ⟶ F) (f : c'.pt ⟶ c.pt)
    (_ : α ≫ c.ι = c'.ι ≫ (Functor.const J).map f) (_ : NatTrans.Equifibered α),
    Nonempty (IsColimit c') ↔ forall j : J, IsPullback (c'.ι.app j) (α.app j) f (c.ι.app j)

/--
theorem `IsVanKampenColimit.isUniversal` / 定理 `IsVanKampenColimit.isUniversal`

English:
theorem IsVanKampenColimit.isUniversal
  given: {F : J ⥤ C} {c : Cocone F} (H : IsVanKampenColimit c)
  proof: fun _ c' α f h hα => (H c' α f h hα).mpr

中文:
定理 IsVanKampenColimit.isUniversal
  条件: {F : J ⥤ C} {c : 余锥 F} (H : IsVanKampenColimit c)
  证明: fun _ c' α f h hα => (H c' α f h hα).mpr
-/
theorem IsVanKampenColimit.isUniversal {F : J ⥤ C} {c : Cocone F} (H : IsVanKampenColimit c) :
    IsUniversalColimit c :=
  fun _ c' α f h hα => (H c' α f h hα).mpr

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `IsUniversalColimit.isColimit` / `IsUniversalColimit.isColimit` 的定义

English:
definition IsUniversalColimit.isColimit
  signature: {F : J ⥤ C} {c : Cocone F}
  body: by
  refine ((h c (𝟙 F) (𝟙 c.pt :) (by rw [Functor.map_id, Category.comp_id, Category.id_comp])
    (.of_isIso _)) fun j => ?_).some
  have : IsIso (𝟙 c.pt) := inferInstance
  exact IsPullback.of_vert_isIso ⟨by simp⟩

中文:
定义 IsUniversalColimit.isColimit
  签名: {F : J ⥤ C} {c : 余锥 F}
  定义体: by
  refine ((h c (𝟙 F) (𝟙 c.pt :) (by rw [Functor.map_id, Category.comp_id, Category.id_comp])
    (.of_isIso _)) fun j => ?_).some
  have : IsIso (𝟙 c.pt) := inferInstance
  exact IsPullback.of_vert_isIso ⟨by simp⟩

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, Functor, Functor.map_id, IsPullback, IsPullback.of_vert_isIso, c.pt, comp_id, id_comp, map_id, of_isIso, of_vert_isIso
-/
noncomputable def IsUniversalColimit.isColimit {F : J ⥤ C} {c : Cocone F}
    (h : IsUniversalColimit c) : IsColimit c := by
  refine ((h c (𝟙 F) (𝟙 c.pt :) (by rw [Functor.map_id, Category.comp_id, Category.id_comp])
    (.of_isIso _)) fun j => ?_).some
  have : IsIso (𝟙 c.pt) := inferInstance
  exact IsPullback.of_vert_isIso ⟨by simp⟩

/--
Definition of `IsVanKampenColimit.isColimit` / `IsVanKampenColimit.isColimit` 的定义

English:
definition IsVanKampenColimit.isColimit
  signature: {F : J ⥤ C} {c : Cocone F}
  body: h.isUniversal.isColimit

中文:
定义 IsVanKampenColimit.isColimit
  签名: {F : J ⥤ C} {c : 余锥 F}
  定义体: h.isUniversal.isColimit

Depends on / 依赖: h.isUniversal.isColimit, isColimit, isUniversal
-/
noncomputable def IsVanKampenColimit.isColimit {F : J ⥤ C} {c : Cocone F}
    (h : IsVanKampenColimit c) : IsColimit c :=
  h.isUniversal.isColimit

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsInitial.isVanKampenColimit` / 定理 `IsInitial.isVanKampenColimit`

English:
theorem IsInitial.isVanKampenColimit
  given: [HasStrictInitialObjects C] {X : C} (h : IsInitial X)
  proof: by
  intro F' c' α f hf hα
  have : F' = Functor.empty C := by apply Functor.hext <;> rintro ⟨⟨⟩⟩
  subst this
  have := h.isIso_to f
  refine ⟨by rintro _ ⟨⟨⟩⟩,
    fun _ => ⟨IsColimit.ofIsoColimit h (Cocone.ext (asIso f).symm <| by rintro ⟨⟨⟩⟩)⟩⟩

中文:
定理 IsInitial.isVanKampenColimit
  条件: [有StrictInitialObjects C] {X : C} (h : IsInitial X)
  证明: by
  intro F' c' α f hf hα
  have : F' = Functor.empty C := by apply Functor.hext <;> rintro ⟨⟨⟩⟩
  subst this
  have := h.isIso_to f
  refine ⟨by rintro _ ⟨⟨⟩⟩,
    fun _ => ⟨IsColimit.ofIsoColimit h (Cocone.ext (asIso f).symm <| by rintro ⟨⟨⟩⟩)⟩⟩

Depends on / 依赖: Cocone, Cocone.ext, Functor, Functor.empty, Functor.hext, IsColimit, IsColimit.ofIsoColimit, h.isIso_to, isIso_to, ofIsoColimit
-/
theorem IsInitial.isVanKampenColimit [HasStrictInitialObjects C] {X : C} (h : IsInitial X) :
    IsVanKampenColimit (asEmptyCocone X) := by
  intro F' c' α f hf hα
  have : F' = Functor.empty C := by apply Functor.hext <;> rintro ⟨⟨⟩⟩
  subst this
  have := h.isIso_to f
  refine ⟨by rintro _ ⟨⟨⟩⟩,
    fun _ => ⟨IsColimit.ofIsoColimit h (Cocone.ext (asIso f).symm <| by rintro ⟨⟨⟩⟩)⟩⟩

section Functor

/--
theorem `IsUniversalColimit.of_iso` / 定理 `IsUniversalColimit.of_iso`

English:
theorem IsUniversalColimit.of_iso
  statement: {F : J ⥤ C} {c c' : Cocone F} (hc : IsUniversalColimit c)
  proof: by
  intro F' c'' α f h hα H
  have : c'.ι ≫ (Functor.const J).map e.inv.hom = c.ι := by
    ext j
    exact e.inv.2 j
  apply hc c'' α (f ≫ e.inv.1) (by rw [Functor.map_comp, ← reassoc_of% h, this]) hα
  intro j
  rw [← Category.comp_id (α.app j)]
  exact (H j).paste_vert (IsPullback.of_vert_isIso ⟨by simp⟩)

中文:
定理 IsUniversalColimit.of_iso
  结论: {F : J ⥤ C} {c c' : 余锥 F} (hc : IsUniversalColimit c)
  证明: by
  intro F' c'' α f h hα H
  have : c'.ι ≫ (Functor.const J).map e.inv.hom = c.ι := by
    ext j
    exact e.inv.2 j
  apply hc c'' α (f ≫ e.inv.1) (by rw [Functor.map_comp, ← reassoc_of% h, this]) hα
  intro j
  rw [← Category.comp_id (α.app j)]
  exact (H j).paste_vert (IsPullback.of_vert_isIso ⟨by simp⟩)

Depends on / 依赖: Category, Category.comp_id, Functor, Functor.const, Functor.map_comp, IsPullback, IsPullback.of_vert_isIso, comp_id, e.inv, e.inv.hom, map_comp, of_vert_isIso, paste_vert, reassoc_of
-/
theorem IsUniversalColimit.of_iso {F : J ⥤ C} {c c' : Cocone F} (hc : IsUniversalColimit c)
    (e : c ≅ c') : IsUniversalColimit c' := by
  intro F' c'' α f h hα H
  have : c'.ι ≫ (Functor.const J).map e.inv.hom = c.ι := by
    ext j
    exact e.inv.2 j
  apply hc c'' α (f ≫ e.inv.1) (by rw [Functor.map_comp, ← reassoc_of% h, this]) hα
  intro j
  rw [← Category.comp_id (α.app j)]
  exact (H j).paste_vert (IsPullback.of_vert_isIso ⟨by simp⟩)

/--
theorem `IsVanKampenColimit.of_iso` / 定理 `IsVanKampenColimit.of_iso`

English:
theorem IsVanKampenColimit.of_iso
  statement: {F : J ⥤ C} {c c' : Cocone F} (H : IsVanKampenColimit c)
  proof: by
  intro F' c'' α f h hα
  have : c'.ι ≫ (Functor.const J).map e.inv.hom = c.ι := by
    ext j
    exact e.inv.2 j
  rw [H c'' α (f ≫ e.inv.1) (by rw [Functor.map_comp]; rw [← reassoc_of% h]; rw [this]) hα]
  apply forall_congr'
  intro j
  conv_lhs => rw [← Category.comp_id (α.app j)]
  have : IsIso e.inv.hom := Functor.map_isIso (Cocone.forget _) e.inv
  exact (IsPullback.of_vert_isIso ⟨by simp⟩).paste_vert_iff (NatTrans.congr_app h j).symm

中文:
定理 IsVanKampenColimit.of_iso
  结论: {F : J ⥤ C} {c c' : 余锥 F} (H : IsVanKampenColimit c)
  证明: by
  intro F' c'' α f h hα
  have : c'.ι ≫ (Functor.const J).map e.inv.hom = c.ι := by
    ext j
    exact e.inv.2 j
  rw [H c'' α (f ≫ e.inv.1) (by rw [Functor.map_comp]; rw [← reassoc_of% h]; rw [this]) hα]
  apply forall_congr'
  intro j
  conv_lhs => rw [← Category.comp_id (α.app j)]
  have : IsIso e.inv.hom := Functor.map_isIso (Cocone.forget _) e.inv
  exact (IsPullback.of_vert_isIso ⟨by simp⟩).paste_vert_iff (NatTrans.congr_app h j).symm

Depends on / 依赖: Category, Category.comp_id, Cocone, Cocone.forget, Functor, Functor.const, Functor.map_comp, Functor.map_isIso, IsPullback, IsPullback.of_vert_isIso, NatTrans, NatTrans.congr_app, comp_id, congr_app, conv_lhs, e.inv, e.inv.hom, forall_congr, forget, map_comp
-/
theorem IsVanKampenColimit.of_iso {F : J ⥤ C} {c c' : Cocone F} (H : IsVanKampenColimit c)
    (e : c ≅ c') : IsVanKampenColimit c' := by
  intro F' c'' α f h hα
  have : c'.ι ≫ (Functor.const J).map e.inv.hom = c.ι := by
    ext j
    exact e.inv.2 j
  rw [H c'' α (f ≫ e.inv.1) (by rw [Functor.map_comp]; rw [← reassoc_of% h]; rw [this]) hα]
  apply forall_congr'
  intro j
  conv_lhs => rw [← Category.comp_id (α.app j)]
  have : IsIso e.inv.hom := Functor.map_isIso (Cocone.forget _) e.inv
  exact (IsPullback.of_vert_isIso ⟨by simp⟩).paste_vert_iff (NatTrans.congr_app h j).symm

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsVanKampenColimit.precompose_isIso` / 定理 `IsVanKampenColimit.precompose_isIso`

English:
theorem IsVanKampenColimit.precompose_isIso
  statement: {F G : J ⥤ C} (α : F ⟶ G) [IsIso α]
  proof: by
  intro F' c' α' f e hα
  refine (hc c' (α' ≫ α) f ((Category.assoc _ _ _).trans e) (hα.comp (.of_isIso _))).trans ?_
  apply forall_congr'
  intro j
  simp only [NatTrans.comp_app, Cocone.precompose_obj_ι]
  have : IsPullback (α.app j ≫ c.ι.app j) (α.app j) (𝟙 _) (c.ι.app j) :=
    IsPullback.of_vert_isIso ⟨Category.comp_id _⟩
  rw [← IsPullback.paste_vert_iff this _]; rw [Category.comp_id]
  exact (congr_app e j).symm

中文:
定理 IsVanKampenColimit.precompose_isIso
  结论: {F G : J ⥤ C} (α : F ⟶ G) [是同构 α]
  证明: by
  intro F' c' α' f e hα
  refine (hc c' (α' ≫ α) f ((Category.assoc _ _ _).trans e) (hα.comp (.of_isIso _))).trans ?_
  apply forall_congr'
  intro j
  simp only [NatTrans.comp_app, Cocone.precompose_obj_ι]
  have : IsPullback (α.app j ≫ c.ι.app j) (α.app j) (𝟙 _) (c.ι.app j) :=
    IsPullback.of_vert_isIso ⟨Category.comp_id _⟩
  rw [← IsPullback.paste_vert_iff this _]; rw [Category.comp_id]
  exact (congr_app e j).symm

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Cocone, Cocone.precompose_obj_, IsPullback, IsPullback.of_vert_isIso, IsPullback.paste_vert_iff, NatTrans, NatTrans.comp_app, comp_app, comp_id, congr_app, forall_congr, of_isIso, of_vert_isIso, paste_vert_iff
-/
theorem IsVanKampenColimit.precompose_isIso {F G : J ⥤ C} (α : F ⟶ G) [IsIso α]
    {c : Cocone G} (hc : IsVanKampenColimit c) :
    IsVanKampenColimit ((Cocone.precompose α).obj c) := by
  intro F' c' α' f e hα
  refine (hc c' (α' ≫ α) f ((Category.assoc _ _ _).trans e) (hα.comp (.of_isIso _))).trans ?_
  apply forall_congr'
  intro j
  simp only [NatTrans.comp_app, Cocone.precompose_obj_ι]
  have : IsPullback (α.app j ≫ c.ι.app j) (α.app j) (𝟙 _) (c.ι.app j) :=
    IsPullback.of_vert_isIso ⟨Category.comp_id _⟩
  rw [← IsPullback.paste_vert_iff this _]; rw [Category.comp_id]
  exact (congr_app e j).symm

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsUniversalColimit.precompose_isIso` / 定理 `IsUniversalColimit.precompose_isIso`

English:
theorem IsUniversalColimit.precompose_isIso
  statement: {F G : J ⥤ C} (α : F ⟶ G) [IsIso α]
  proof: by
  intro F' c' α' f e hα H
  apply (hc c' (α' ≫ α) f ((Category.assoc _ _ _).trans e) (hα.comp (.of_isIso _)))
  intro j
  simp only [NatTrans.comp_app]
  rw [← Category.comp_id f]
  exact (H j).paste_vert (IsPullback.of_vert_isIso ⟨Category.comp_id _⟩)

中文:
定理 IsUniversalColimit.precompose_isIso
  结论: {F G : J ⥤ C} (α : F ⟶ G) [是同构 α]
  证明: by
  intro F' c' α' f e hα H
  apply (hc c' (α' ≫ α) f ((Category.assoc _ _ _).trans e) (hα.comp (.of_isIso _)))
  intro j
  simp only [NatTrans.comp_app]
  rw [← Category.comp_id f]
  exact (H j).paste_vert (IsPullback.of_vert_isIso ⟨Category.comp_id _⟩)

Depends on / 依赖: Category, Category.assoc, Category.comp_id, IsPullback, IsPullback.of_vert_isIso, NatTrans, NatTrans.comp_app, comp_app, comp_id, of_isIso, of_vert_isIso, paste_vert
-/
theorem IsUniversalColimit.precompose_isIso {F G : J ⥤ C} (α : F ⟶ G) [IsIso α]
    {c : Cocone G} (hc : IsUniversalColimit c) :
    IsUniversalColimit ((Cocone.precompose α).obj c) := by
  intro F' c' α' f e hα H
  apply (hc c' (α' ≫ α) f ((Category.assoc _ _ _).trans e) (hα.comp (.of_isIso _)))
  intro j
  simp only [NatTrans.comp_app]
  rw [← Category.comp_id f]
  exact (H j).paste_vert (IsPullback.of_vert_isIso ⟨Category.comp_id _⟩)

set_option backward.defeqAttrib.useBackward true in
/--
theorem `IsVanKampenColimit.precompose_isIso_iff` / 定理 `IsVanKampenColimit.precompose_isIso_iff`

English:
theorem IsVanKampenColimit.precompose_isIso_iff
  statement: {F G : J ⥤ C} (α : F ⟶ G) [IsIso α]
  proof: ⟨fun hc => IsVanKampenColimit.of_iso (IsVanKampenColimit.precompose_isIso (inv α) hc)
    (Cocone.ext (Iso.refl _) (by simp)),
    IsVanKampenColimit.precompose_isIso α⟩

中文:
定理 IsVanKampenColimit.precompose_isIso_iff
  结论: {F G : J ⥤ C} (α : F ⟶ G) [是同构 α]
  证明: ⟨fun hc => IsVanKampenColimit.of_iso (IsVanKampenColimit.precompose_isIso (inv α) hc)
    (Cocone.ext (Iso.refl _) (by simp)),
    IsVanKampenColimit.precompose_isIso α⟩

Depends on / 依赖: Cocone, Cocone.ext, IsVanKampenColimit, IsVanKampenColimit.of_iso, IsVanKampenColimit.precompose_isIso, Iso.refl, of_iso, precompose_isIso
-/
theorem IsVanKampenColimit.precompose_isIso_iff {F G : J ⥤ C} (α : F ⟶ G) [IsIso α]
    {c : Cocone G} : IsVanKampenColimit ((Cocone.precompose α).obj c) ↔ IsVanKampenColimit c :=
  ⟨fun hc => IsVanKampenColimit.of_iso (IsVanKampenColimit.precompose_isIso (inv α) hc)
    (Cocone.ext (Iso.refl _) (by simp)),
    IsVanKampenColimit.precompose_isIso α⟩

/--
theorem `IsUniversalColimit.of_mapCocone` / 定理 `IsUniversalColimit.of_mapCocone`

English:
theorem IsUniversalColimit.of_mapCocone
  statement: (G : C ⥤ D) {F : J ⥤ C} {c : Cocone F}
  proof: fun F' c' α f h hα H =>
    ⟨isColimitOfReflects _ (hc (G.mapCocone c') (whiskerRight α G) (G.map f)
    (by ext j; simpa using! G.congr_map (NatTrans.congr_app h j))
    (hα.whiskerRight G) (fun j => (H j).map G)).some⟩

中文:
定理 IsUniversalColimit.of_mapCocone
  结论: (G : C ⥤ D) {F : J ⥤ C} {c : 余锥 F}
  证明: fun F' c' α f h hα H =>
    ⟨isColimitOfReflects _ (hc (G.mapCocone c') (whiskerRight α G) (G.map f)
    (by ext j; simpa using! G.congr_map (NatTrans.congr_app h j))
    (hα.whiskerRight G) (fun j => (H j).map G)).some⟩

Depends on / 依赖: Function, Function.Surjective, G.congr_map, G.map, G.mapCocone, NatTrans, NatTrans.congr_app, Surjective, choose_spec, congr_app, congr_map, isColimitOfReflects, mapCocone, surjective_of_epi, whiskerRight
-/
theorem IsUniversalColimit.of_mapCocone (G : C ⥤ D) {F : J ⥤ C} {c : Cocone F}
    [PreservesLimitsOfShape WalkingCospan G] [ReflectsColimitsOfShape J G]
    (hc : IsUniversalColimit (G.mapCocone c)) : IsUniversalColimit c :=
  fun F' c' α f h hα H =>
    ⟨isColimitOfReflects _ (hc (G.mapCocone c') (whiskerRight α G) (G.map f)
    (by ext j; simpa using! G.congr_map (NatTrans.congr_app h j))
    (hα.whiskerRight G) (fun j => (H j).map G)).some⟩

/--
theorem `IsVanKampenColimit.of_mapCocone` / 定理 `IsVanKampenColimit.of_mapCocone`

English:
theorem IsVanKampenColimit.of_mapCocone
  statement: (G : C ⥤ D) {F : J ⥤ C} {c : Cocone F}
  proof: by
  intro F' c' α f h hα
  refine (Iff.trans ?_ (H (G.mapCocone c') (whiskerRight α G) (G.map f)
      (by ext j; simpa using! G.congr_map (NatTrans.congr_app h j))
      (hα.whiskerRight G))).trans (forall_congr' fun j => ?_)
  · exact ⟨fun h => ⟨isColimitOfPreserves G h.some⟩, fun h => ⟨isColimitOfReflects G h.some⟩⟩
  · exact IsPullback.map_iff G (NatTrans.congr_app h.symm j)

中文:
定理 IsVanKampenColimit.of_mapCocone
  结论: (G : C ⥤ D) {F : J ⥤ C} {c : 余锥 F}
  证明: by
  intro F' c' α f h hα
  refine (Iff.trans ?_ (H (G.mapCocone c') (whiskerRight α G) (G.map f)
      (by ext j; simpa using! G.congr_map (NatTrans.congr_app h j))
      (hα.whiskerRight G))).trans (forall_congr' fun j => ?_)
  · exact ⟨fun h => ⟨isColimitOfPreserves G h.some⟩, fun h => ⟨isColimitOfReflects G h.some⟩⟩
  · exact IsPullback.map_iff G (NatTrans.congr_app h.symm j)

Depends on / 依赖: G.congr_map, G.map, G.mapCocone, Iff.trans, IsPullback, IsPullback.map_iff, NatTrans, NatTrans.congr_app, congr_app, congr_map, forall_congr, h.some, h.symm, isColimitOfPreserves, isColimitOfReflects, mapCocone, map_iff, whiskerRight
-/
theorem IsVanKampenColimit.of_mapCocone (G : C ⥤ D) {F : J ⥤ C} {c : Cocone F}
    [forall (i j : J) (X : C) (f : X ⟶ F.obj j) (g : i ⟶ j), PreservesLimit (cospan f (F.map g)) G]
    [forall (i : J) (X : C) (f : X ⟶ c.pt), PreservesLimit (cospan f (c.ι.app i)) G]
    [ReflectsLimitsOfShape WalkingCospan G]
    [PreservesColimitsOfShape J G]
    [ReflectsColimitsOfShape J G]
    (H : IsVanKampenColimit (G.mapCocone c)) : IsVanKampenColimit c := by
  intro F' c' α f h hα
  refine (Iff.trans ?_ (H (G.mapCocone c') (whiskerRight α G) (G.map f)
      (by ext j; simpa using! G.congr_map (NatTrans.congr_app h j))
      (hα.whiskerRight G))).trans (forall_congr' fun j => ?_)
  · exact ⟨fun h => ⟨isColimitOfPreserves G h.some⟩, fun h => ⟨isColimitOfReflects G h.some⟩⟩
  · exact IsPullback.map_iff G (NatTrans.congr_app h.symm j)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsVanKampenColimit.mapCocone_iff` / 定理 `IsVanKampenColimit.mapCocone_iff`

English:
theorem IsVanKampenColimit.mapCocone_iff
  statement: (G : C ⥤ D) {F : J ⥤ C} {c : Cocone F}
  proof: ⟨IsVanKampenColimit.of_mapCocone G, fun hc => by
    let e : F ⋙ G ⋙ Functor.inv G ≅ F := NatIso.hcomp (Iso.refl F) G.asEquivalence.unitIso.symm
    apply IsVanKampenColimit.of_mapCocone G.inv
    apply (IsVanKampenColimit.precompose_isIso_iff e.inv).mp
    exact hc.of_iso (Cocone.ext (G.asEquivalence.unitIso.app c.pt) (fun j => (by simp [e])))⟩

中文:
定理 IsVanKampenColimit.mapCocone_iff
  结论: (G : C ⥤ D) {F : J ⥤ C} {c : 余锥 F}
  证明: ⟨IsVanKampenColimit.of_mapCocone G, fun hc => by
    let e : F ⋙ G ⋙ Functor.inv G ≅ F := NatIso.hcomp (Iso.refl F) G.asEquivalence.unitIso.symm
    apply IsVanKampenColimit.of_mapCocone G.inv
    apply (IsVanKampenColimit.precompose_isIso_iff e.inv).mp
    exact hc.of_iso (Cocone.ext (G.asEquivalence.unitIso.app c.pt) (fun j => (by simp [e])))⟩

Depends on / 依赖: Cocone, Cocone.ext, Functor, Functor.inv, G.asEquivalence.unitIso.app, G.asEquivalence.unitIso.symm, G.inv, IsVanKampenColimit, IsVanKampenColimit.of_mapCocone, IsVanKampenColimit.precompose_isIso_iff, Iso.refl, NatIso, NatIso.hcomp, asEquivalence, c.pt, coprod, coprod.desc, coprod.inl, coprod.inr, e.inv
-/
theorem IsVanKampenColimit.mapCocone_iff (G : C ⥤ D) {F : J ⥤ C} {c : Cocone F}
    [G.IsEquivalence] : IsVanKampenColimit (G.mapCocone c) ↔ IsVanKampenColimit c :=
  ⟨IsVanKampenColimit.of_mapCocone G, fun hc => by
    let e : F ⋙ G ⋙ Functor.inv G ≅ F := NatIso.hcomp (Iso.refl F) G.asEquivalence.unitIso.symm
    apply IsVanKampenColimit.of_mapCocone G.inv
    apply (IsVanKampenColimit.precompose_isIso_iff e.inv).mp
    exact hc.of_iso (Cocone.ext (G.asEquivalence.unitIso.app c.pt) (fun j => (by simp [e])))⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsUniversalColimit.whiskerEquivalence` / 定理 `IsUniversalColimit.whiskerEquivalence`

English:
theorem IsUniversalColimit.whiskerEquivalence
  statement: {K : Type*} [Category* K] (e : J ≌ K)
  proof: by
  intro F' c' α f e' hα H
  convert!
    hc (c'.whisker e.inverse) (whiskerLeft e.inverse α ≫ (e.invFunIdAssoc F).hom) f ?_
      ((hα.whiskerLeft _).comp (.of_isIso _)) ?_ using 1
  · exact (IsColimit.whiskerEquivalenceEquiv e.symm).nonempty_congr
  · convert! congr_arg (whiskerLeft e.inverse) e'
    ext
    simp
  · intro k
    rw [← Category.comp_id f]
    refine (H (e.inverse.obj k)).paste_vert ?_
    exact IsPullback.of_vert_isIso ⟨by simp⟩

中文:
定理 IsUniversalColimit.whiskerEquivalence
  结论: {K : 类型} [范畴* K] (e : J ≌ K)
  证明: by
  intro F' c' α f e' hα H
  convert!
    hc (c'.whisker e.inverse) (whiskerLeft e.inverse α ≫ (e.invFunIdAssoc F).hom) f ?_
      ((hα.whiskerLeft _).comp (.of_isIso _)) ?_ using 1
  · exact (IsColimit.whiskerEquivalenceEquiv e.symm).nonempty_congr
  · convert! congr_arg (whiskerLeft e.inverse) e'
    ext
    simp
  · intro k
    rw [← Category.comp_id f]
    refine (H (e.inverse.obj k)).paste_vert ?_
    exact IsPullback.of_vert_isIso ⟨by simp⟩

Depends on / 依赖: Category, Category.comp_id, IsColimit, IsColimit.whiskerEquivalenceEquiv, IsPullback, IsPullback.of_vert_isIso, Sigma.desc, cat_disch, comp_id, congr_arg, convert, e.invFunIdAssoc, e.inverse, e.inverse.obj, e.symm, factorThru, invFunIdAssoc, inverse, nonempty_congr, of_isIso
-/
theorem IsUniversalColimit.whiskerEquivalence {K : Type*} [Category* K] (e : J ≌ K)
    {F : K ⥤ C} {c : Cocone F} (hc : IsUniversalColimit c) :
    IsUniversalColimit (c.whisker e.functor) := by
  intro F' c' α f e' hα H
  convert!
    hc (c'.whisker e.inverse) (whiskerLeft e.inverse α ≫ (e.invFunIdAssoc F).hom) f ?_
      ((hα.whiskerLeft _).comp (.of_isIso _)) ?_ using 1
  · exact (IsColimit.whiskerEquivalenceEquiv e.symm).nonempty_congr
  · convert! congr_arg (whiskerLeft e.inverse) e'
    ext
    simp
  · intro k
    rw [← Category.comp_id f]
    refine (H (e.inverse.obj k)).paste_vert ?_
    exact IsPullback.of_vert_isIso ⟨by simp⟩

set_option backward.defeqAttrib.useBackward true in
/--
theorem `IsUniversalColimit.whiskerEquivalence_iff` / 定理 `IsUniversalColimit.whiskerEquivalence_iff`

English:
theorem IsUniversalColimit.whiskerEquivalence_iff
  statement: {K : Type*} [Category* K] (e : J ≌ K)
  proof: ⟨fun hc => ((hc.whiskerEquivalence e.symm).precompose_isIso (e.invFunIdAssoc F).inv).of_iso
      (Cocone.ext (Iso.refl _) (by simp)), IsUniversalColimit.whiskerEquivalence e⟩

中文:
定理 IsUniversalColimit.whiskerEquivalence_iff
  结论: {K : 类型} [范畴* K] (e : J ≌ K)
  证明: ⟨fun hc => ((hc.whiskerEquivalence e.symm).precompose_isIso (e.invFunIdAssoc F).inv).of_iso
      (Cocone.ext (Iso.refl _) (by simp)), IsUniversalColimit.whiskerEquivalence e⟩

Depends on / 依赖: Cocone, Cocone.ext, IsUniversalColimit, IsUniversalColimit.whiskerEquivalence, Iso.refl, biprod, biprod.desc, biprod.inl, biprod.inr, e.invFunIdAssoc, e.symm, factorThru, hc.whiskerEquivalence, invFunIdAssoc, of_iso, precompose_isIso, whiskerEquivalence
-/
theorem IsUniversalColimit.whiskerEquivalence_iff {K : Type*} [Category* K] (e : J ≌ K)
    {F : K ⥤ C} {c : Cocone F} :
    IsUniversalColimit (c.whisker e.functor) ↔ IsUniversalColimit c :=
  ⟨fun hc => ((hc.whiskerEquivalence e.symm).precompose_isIso (e.invFunIdAssoc F).inv).of_iso
      (Cocone.ext (Iso.refl _) (by simp)), IsUniversalColimit.whiskerEquivalence e⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsVanKampenColimit.whiskerEquivalence` / 定理 `IsVanKampenColimit.whiskerEquivalence`

English:
theorem IsVanKampenColimit.whiskerEquivalence
  statement: {K : Type*} [Category* K] (e : J ≌ K)
  proof: by
  intro F' c' α f e' hα
  convert!
    hc (c'.whisker e.inverse) (whiskerLeft e.inverse α ≫ (e.invFunIdAssoc F).hom) f ?_
      ((hα.whiskerLeft _).comp (.of_isIso _)) using 1
  · exact (IsColimit.whiskerEquivalenceEquiv e.symm).nonempty_congr
  · simp only [Functor.const_obj_obj, Functor.comp_obj, Cocone.whisker_pt, Cocone.whisker_ι,
      whiskerLeft_app, NatTrans.comp_app, Equivalence.invFunIdAssoc_hom_app, Functor.id_obj]
    constructor
    · intro H k
      rw [← Category.comp_id f]
      refine (H (e.inverse.obj k)).paste_vert ?_
      have : IsIso (𝟙 (Cocone.whisker e.functor c).pt) := inferInstance
      exact IsPullback.of_vert_isIso ⟨by simp⟩
    · intro H j
      have : α.app j
          = F'.map (e.unit.app _) ≫ α.app _ ≫ F.map (e.counit.app (e.functor.obj j)) := by
        simp [← Functor.map_comp]
      rw [← Category.id_comp f]; rw [this]
      refine IsPullback.paste_vert ?_ (H (e.functor.obj j))
      exact IsPullback.of_vert_isIso ⟨by simp⟩
  · ext k
    simpa using congr_app e' (e.inverse.obj k)

中文:
定理 IsVanKampenColimit.whiskerEquivalence
  结论: {K : 类型} [范畴* K] (e : J ≌ K)
  证明: by
  intro F' c' α f e' hα
  convert!
    hc (c'.whisker e.inverse) (whiskerLeft e.inverse α ≫ (e.invFunIdAssoc F).hom) f ?_
      ((hα.whiskerLeft _).comp (.of_isIso _)) using 1
  · exact (IsColimit.whiskerEquivalenceEquiv e.symm).nonempty_congr
  · simp only [Functor.const_obj_obj, Functor.comp_obj, Cocone.whisker_pt, Cocone.whisker_ι,
      whiskerLeft_app, NatTrans.comp_app, Equivalence.invFunIdAssoc_hom_app, Functor.id_obj]
    constructor
    · intro H k
      rw [← Category.comp_id f]
      refine (H (e.inverse.obj k)).paste_vert ?_
      have : IsIso (𝟙 (Cocone.whisker e.functor c).pt) := inferInstance
      exact IsPullback.of_vert_isIso ⟨by simp⟩
    · intro H j
      have : α.app j
          = F'.map (e.unit.app _) ≫ α.app _ ≫ F.map (e.counit.app (e.functor.obj j)) := by
        simp [← Functor.map_comp]
      rw [← Category.id_comp f]; rw [this]
      refine IsPullback.paste_vert ?_ (H (e.functor.obj j))
      exact IsPullback.of_vert_isIso ⟨by simp⟩
  · ext k
    simpa using congr_app e' (e.inverse.obj k)

Depends on / 依赖: Category, Category.comp_id, Cocone, Cocone.whisker_, Cocone.whisker_pt, Equivalence, Equivalence.invFunIdAssoc_hom_app, Functor, Functor.comp_obj, Functor.const_obj_obj, Functor.id_obj, IsColimit, IsColimit.whiskerEquivalenceEquiv, NatTrans, NatTrans.comp_app, biproduct, biproduct.desc, cat_disch, comp_app, comp_id
-/
theorem IsVanKampenColimit.whiskerEquivalence {K : Type*} [Category* K] (e : J ≌ K)
    {F : K ⥤ C} {c : Cocone F} (hc : IsVanKampenColimit c) :
    IsVanKampenColimit (c.whisker e.functor) := by
  intro F' c' α f e' hα
  convert!
    hc (c'.whisker e.inverse) (whiskerLeft e.inverse α ≫ (e.invFunIdAssoc F).hom) f ?_
      ((hα.whiskerLeft _).comp (.of_isIso _)) using 1
  · exact (IsColimit.whiskerEquivalenceEquiv e.symm).nonempty_congr
  · simp only [Functor.const_obj_obj, Functor.comp_obj, Cocone.whisker_pt, Cocone.whisker_ι,
      whiskerLeft_app, NatTrans.comp_app, Equivalence.invFunIdAssoc_hom_app, Functor.id_obj]
    constructor
    · intro H k
      rw [← Category.comp_id f]
      refine (H (e.inverse.obj k)).paste_vert ?_
      have : IsIso (𝟙 (Cocone.whisker e.functor c).pt) := inferInstance
      exact IsPullback.of_vert_isIso ⟨by simp⟩
    · intro H j
      have : α.app j
          = F'.map (e.unit.app _) ≫ α.app _ ≫ F.map (e.counit.app (e.functor.obj j)) := by
        simp [← Functor.map_comp]
      rw [← Category.id_comp f]; rw [this]
      refine IsPullback.paste_vert ?_ (H (e.functor.obj j))
      exact IsPullback.of_vert_isIso ⟨by simp⟩
  · ext k
    simpa using congr_app e' (e.inverse.obj k)

set_option backward.defeqAttrib.useBackward true in
/--
theorem `IsVanKampenColimit.whiskerEquivalence_iff` / 定理 `IsVanKampenColimit.whiskerEquivalence_iff`

English:
theorem IsVanKampenColimit.whiskerEquivalence_iff
  statement: {K : Type*} [Category* K] (e : J ≌ K)
  proof: ⟨fun hc => ((hc.whiskerEquivalence e.symm).precompose_isIso (e.invFunIdAssoc F).inv).of_iso
      (Cocone.ext (Iso.refl _) (by simp)), IsVanKampenColimit.whiskerEquivalence e⟩

中文:
定理 IsVanKampenColimit.whiskerEquivalence_iff
  结论: {K : 类型} [范畴* K] (e : J ≌ K)
  证明: ⟨fun hc => ((hc.whiskerEquivalence e.symm).precompose_isIso (e.invFunIdAssoc F).inv).of_iso
      (Cocone.ext (Iso.refl _) (by simp)), IsVanKampenColimit.whiskerEquivalence e⟩

Depends on / 依赖: Cocone, Cocone.ext, IsVanKampenColimit, IsVanKampenColimit.whiskerEquivalence, Iso.refl, e.invFunIdAssoc, e.symm, hc.whiskerEquivalence, invFunIdAssoc, of_iso, precompose_isIso, whiskerEquivalence
-/
theorem IsVanKampenColimit.whiskerEquivalence_iff {K : Type*} [Category* K] (e : J ≌ K)
    {F : K ⥤ C} {c : Cocone F} :
    IsVanKampenColimit (c.whisker e.functor) ↔ IsVanKampenColimit c :=
  ⟨fun hc => ((hc.whiskerEquivalence e.symm).precompose_isIso (e.invFunIdAssoc F).inv).of_iso
      (Cocone.ext (Iso.refl _) (by simp)), IsVanKampenColimit.whiskerEquivalence e⟩

/--
theorem `isVanKampenColimit_of_evaluation` / 定理 `isVanKampenColimit_of_evaluation`

English:
theorem isVanKampenColimit_of_evaluation
  statement: [HasPullbacks D] [HasColimitsOfShape J D] (F : J ⥤ C ⥤ D)
  proof: by
  intro F' c' α f e hα
  have := fun x => hc x (((evaluation C D).obj x).mapCocone c') (whiskerRight α _)
      (((evaluation C D).obj x).map f)
      (by
        ext y
        dsimp
        exact NatTrans.congr_app (NatTrans.congr_app e y) x)
      (hα.whiskerRight _)
  constructor
  · rintro ⟨hc'⟩ j
    refine ⟨⟨(NatTrans.congr_app e j).symm⟩, ⟨evaluationJointlyReflectsLimits _ ?_⟩⟩
    refine fun x => (isLimitMapConePullbackConeEquiv _ _).symm ?_
    exact ((this x).mp ⟨isColimitOfPreserves _ hc'⟩ _).isLimit
  · exact fun H => ⟨evaluationJointlyReflectsColimits _ fun x =>
      ((this x).mpr fun j => (H j).map ((evaluation C D).obj x)).some⟩

中文:
定理 isVanKampenColimit_of_evaluation
  结论: [有Pullbacks D] [有形状余极限 J D] (F : J ⥤ C ⥤ D)
  证明: by
  intro F' c' α f e hα
  have := fun x => hc x (((evaluation C D).obj x).mapCocone c') (whiskerRight α _)
      (((evaluation C D).obj x).map f)
      (by
        ext y
        dsimp
        exact NatTrans.congr_app (NatTrans.congr_app e y) x)
      (hα.whiskerRight _)
  constructor
  · rintro ⟨hc'⟩ j
    refine ⟨⟨(NatTrans.congr_app e j).symm⟩, ⟨evaluationJointlyReflectsLimits _ ?_⟩⟩
    refine fun x => (isLimitMapConePullbackConeEquiv _ _).symm ?_
    exact ((this x).mp ⟨isColimitOfPreserves _ hc'⟩ _).isLimit
  · exact fun H => ⟨evaluationJointlyReflectsColimits _ fun x =>
      ((this x).mpr fun j => (H j).map ((evaluation C D).obj x)).some⟩

Depends on / 依赖: NatTrans, NatTrans.congr_app, congr_app, evaluation, evaluationJointlyReflect, evaluationJointlyReflectsLimits, isColimitOfPreserves, isLimit, isLimitMapConePullbackConeEquiv, mapCocone, whiskerRight
-/
theorem isVanKampenColimit_of_evaluation [HasPullbacks D] [HasColimitsOfShape J D] (F : J ⥤ C ⥤ D)
    (c : Cocone F) (hc : forall x : C, IsVanKampenColimit (((evaluation C D).obj x).mapCocone c)) :
    IsVanKampenColimit c := by
  intro F' c' α f e hα
  have := fun x => hc x (((evaluation C D).obj x).mapCocone c') (whiskerRight α _)
      (((evaluation C D).obj x).map f)
      (by
        ext y
        dsimp
        exact NatTrans.congr_app (NatTrans.congr_app e y) x)
      (hα.whiskerRight _)
  constructor
  · rintro ⟨hc'⟩ j
    refine ⟨⟨(NatTrans.congr_app e j).symm⟩, ⟨evaluationJointlyReflectsLimits _ ?_⟩⟩
    refine fun x => (isLimitMapConePullbackConeEquiv _ _).symm ?_
    exact ((this x).mp ⟨isColimitOfPreserves _ hc'⟩ _).isLimit
  · exact fun H => ⟨evaluationJointlyReflectsColimits _ fun x =>
      ((this x).mpr fun j => (H j).map ((evaluation C D).obj x)).some⟩

end Functor

section reflective

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsUniversalColimit.map_reflective` / 定理 `IsUniversalColimit.map_reflective`

English:
theorem IsUniversalColimit.map_reflective
  proof: by
  have := adj.rightAdjoint_preservesLimits
  have : PreservesColimitsOfSize.{u', v'} Gl := adj.leftAdjoint_preservesColimits
  intro F' c' α f h hα hc'
  have : HasPullback (Gl.map (Gr.map f)) (Gl.map (adj.unit.app c.pt)) :=
    ⟨⟨_, isLimitPullbackConeMapOfIsLimit _ pullback.condition
      (IsPullback.of_hasPullback _ _).isLimit⟩⟩
  let α' := α ≫ (Functor.associator _ _ _).hom ≫ whiskerLeft F adj.counit ≫ F.rightUnitor.hom
  have hα' : NatTrans.Equifibered α' := hα.comp (.of_isIso _)
  have hadj : forall X, Gl.map (adj.unit.app X) = inv (adj.counit.app _) := by
    intro X
    apply IsIso.eq_inv_of_inv_hom_id
    exact adj.left_triangle_components _
  have : forall X, IsIso (Gl.map (adj.unit.app X)) := by
    simp_rw [hadj]
    infer_instance
  have hα'' : forall j, Gl.map (Gr.map <| α'.app j) = adj.counit.app _ ≫ α.app j := by
    intro j
    rw [← cancel_mono (adj.counit.app <| F.obj j)]
    dsimp [α']
    simp only [Category.comp_id, Adjunction.counit_naturality_assoc, Category.id_comp,
      Adjunction.counit_naturality, Category.assoc, Functor.map_comp]
  have hc'' : forall j, α.app j ≫ Gl.map (c.ι.app j) = c'.ι.app j ≫ f := NatTrans.congr_app h
  let β := isoWhiskerLeft F' (asIso adj.counit) ≪≫ F'.rightUnitor
  let c'' : Cocone (F' ⋙ Gr) := by
    refine
    { pt := pullback (Gr.map f) (adj.unit.app _)
      ι := { app := fun j => pullback.lift (Gr.map <| c'.ι.app j) (Gr.map (α'.app j) ≫ c.ι.app j) ?_
             naturality := ?_ } }
    · rw [← Gr.map_comp, ← hc'']
      simp_all [← adj.unit_naturality]
    · intro i j g
      dsimp [α']
      ext
      all_goals simp only [Category.comp_id, Category.id_comp, Category.assoc,
        ← Functor.map_comp, pullback.lift_fst, pullback.lift_snd, ← Functor.map_comp_assoc]
      · congr 1
        exact c'.w _
      · rw [α.naturality_assoc]
        dsimp
        rw [adj.counit_naturality]; rw [← Category.assoc]; rw [Gr.map_comp_assoc]
        congr 1
        exact c.w _
  let cf : (Cocone.precompose β.hom).obj c' ⟶ Gl.mapCocone c'' := by
    refine { hom := pullback.lift ?_ f ?_ ≫ (PreservesPullback.iso _ _ _).inv, w := ?_ }
· exact inv adj.counit.app c'.pt
    · simp [← cancel_mono (adj.counit.app <| Gl.obj c.pt)]
    · intro j
      rw [← Category.assoc]; rw [Iso.comp_inv_eq]
      ext
      all_goals simp only [c'', PreservesPullback.iso_hom_fst, PreservesPullback.iso_hom_snd,
          pullback.lift_fst, pullback.lift_snd, Category.assoc,
          Functor.mapCocone_ι_app, ← Gl.map_comp]
      · dsimp [β]
        simp only [IsIso.comp_inv_eq, adj.counit_naturality, Category.comp_id]
      · rw [Gl.map_comp, hα'', Category.assoc, hc'']
        dsimp [β]
        rw [Category.comp_id]; rw [Category.assoc]
  have :
      cf.hom ≫ (PreservesPullback.iso _ _ _).hom ≫ pullback.fst _ _ ≫ adj.counit.app _ = 𝟙 _ := by
    simp only [cf, IsIso.inv_hom_id, Iso.inv_hom_id_assoc, Category.assoc,
      pullback.lift_fst_assoc]
  have : IsIso cf := by
    apply @Cocone.cocone_iso_of_hom_iso (i := ?_)
    rw [← IsIso.eq_comp_inv] at this
    rw [this]
    infer_instance
  have ⟨Hc''⟩ := H c'' (whiskerRight α' Gr) (pullback.snd _ _) ?_ (hα'.whiskerRight Gr) ?_
· exact ⟨IsColimit.precomposeHomEquiv β c'
      (isColimitOfPreserves Gl Hc'').ofIsoColimit (asIso cf).symm⟩
  · ext j
    dsimp [c'']
    simp only [pullback.lift_snd]
  · intro j
    apply IsPullback.of_right _ _ (IsPullback.of_hasPullback _ _)
    · dsimp [α', c'']
      simp only [Category.comp_id, Category.id_comp, Category.assoc, Functor.map_comp,
        pullback.lift_fst]
      rw [← Category.comp_id (Gr.map f)]
      refine ((hc' j).map Gr).paste_vert (IsPullback.of_vert_isIso ⟨?_⟩)
      rw [← adj.unit_naturality]; rw [Category.comp_id]; rw [← Category.assoc]; rw [← Category.id_comp (Gr.map ((Gl.mapCocone c).ι.app j))]
      congr 1
      rw [← cancel_mono (Gr.map (adj.counit.app (F.obj j)))]
      dsimp
      simp only [Category.comp_id, Adjunction.right_triangle_components, Category.id_comp,
        Category.assoc]
    · dsimp [c'']
      simp only [pullback.lift_snd]

中文:
定理 IsUniversalColimit.map_reflective
  证明: by
  have := adj.rightAdjoint_preservesLimits
  have : PreservesColimitsOfSize.{u', v'} Gl := adj.leftAdjoint_preservesColimits
  intro F' c' α f h hα hc'
  have : HasPullback (Gl.map (Gr.map f)) (Gl.map (adj.unit.app c.pt)) :=
    ⟨⟨_, isLimitPullbackConeMapOfIsLimit _ pullback.condition
      (IsPullback.of_hasPullback _ _).isLimit⟩⟩
  let α' := α ≫ (Functor.associator _ _ _).hom ≫ whiskerLeft F adj.counit ≫ F.rightUnitor.hom
  have hα' : NatTrans.Equifibered α' := hα.comp (.of_isIso _)
  have hadj : forall X, Gl.map (adj.unit.app X) = inv (adj.counit.app _) := by
    intro X
    apply IsIso.eq_inv_of_inv_hom_id
    exact adj.left_triangle_components _
  have : forall X, IsIso (Gl.map (adj.unit.app X)) := by
    simp_rw [hadj]
    infer_instance
  have hα'' : forall j, Gl.map (Gr.map <| α'.app j) = adj.counit.app _ ≫ α.app j := by
    intro j
    rw [← cancel_mono (adj.counit.app <| F.obj j)]
    dsimp [α']
    simp only [Category.comp_id, Adjunction.counit_naturality_assoc, Category.id_comp,
      Adjunction.counit_naturality, Category.assoc, Functor.map_comp]
  have hc'' : forall j, α.app j ≫ Gl.map (c.ι.app j) = c'.ι.app j ≫ f := NatTrans.congr_app h
  let β := isoWhiskerLeft F' (asIso adj.counit) ≪≫ F'.rightUnitor
  let c'' : Cocone (F' ⋙ Gr) := by
    refine
    { pt := pullback (Gr.map f) (adj.unit.app _)
      ι := { app := fun j => pullback.lift (Gr.map <| c'.ι.app j) (Gr.map (α'.app j) ≫ c.ι.app j) ?_
             naturality := ?_ } }
    · rw [← Gr.map_comp, ← hc'']
      simp_all [← adj.unit_naturality]
    · intro i j g
      dsimp [α']
      ext
      all_goals simp only [Category.comp_id, Category.id_comp, Category.assoc,
        ← Functor.map_comp, pullback.lift_fst, pullback.lift_snd, ← Functor.map_comp_assoc]
      · congr 1
        exact c'.w _
      · rw [α.naturality_assoc]
        dsimp
        rw [adj.counit_naturality]; rw [← Category.assoc]; rw [Gr.map_comp_assoc]
        congr 1
        exact c.w _
  let cf : (Cocone.precompose β.hom).obj c' ⟶ Gl.mapCocone c'' := by
    refine { hom := pullback.lift ?_ f ?_ ≫ (PreservesPullback.iso _ _ _).inv, w := ?_ }
· exact inv adj.counit.app c'.pt
    · simp [← cancel_mono (adj.counit.app <| Gl.obj c.pt)]
    · intro j
      rw [← Category.assoc]; rw [Iso.comp_inv_eq]
      ext
      all_goals simp only [c'', PreservesPullback.iso_hom_fst, PreservesPullback.iso_hom_snd,
          pullback.lift_fst, pullback.lift_snd, Category.assoc,
          Functor.mapCocone_ι_app, ← Gl.map_comp]
      · dsimp [β]
        simp only [IsIso.comp_inv_eq, adj.counit_naturality, Category.comp_id]
      · rw [Gl.map_comp, hα'', Category.assoc, hc'']
        dsimp [β]
        rw [Category.comp_id]; rw [Category.assoc]
  have :
      cf.hom ≫ (PreservesPullback.iso _ _ _).hom ≫ pullback.fst _ _ ≫ adj.counit.app _ = 𝟙 _ := by
    simp only [cf, IsIso.inv_hom_id, Iso.inv_hom_id_assoc, Category.assoc,
      pullback.lift_fst_assoc]
  have : IsIso cf := by
    apply @Cocone.cocone_iso_of_hom_iso (i := ?_)
    rw [← IsIso.eq_comp_inv] at this
    rw [this]
    infer_instance
  have ⟨Hc''⟩ := H c'' (whiskerRight α' Gr) (pullback.snd _ _) ?_ (hα'.whiskerRight Gr) ?_
· exact ⟨IsColimit.precomposeHomEquiv β c'
      (isColimitOfPreserves Gl Hc'').ofIsoColimit (asIso cf).symm⟩
  · ext j
    dsimp [c'']
    simp only [pullback.lift_snd]
  · intro j
    apply IsPullback.of_right _ _ (IsPullback.of_hasPullback _ _)
    · dsimp [α', c'']
      simp only [Category.comp_id, Category.id_comp, Category.assoc, Functor.map_comp,
        pullback.lift_fst]
      rw [← Category.comp_id (Gr.map f)]
      refine ((hc' j).map Gr).paste_vert (IsPullback.of_vert_isIso ⟨?_⟩)
      rw [← adj.unit_naturality]; rw [Category.comp_id]; rw [← Category.assoc]; rw [← Category.id_comp (Gr.map ((Gl.mapCocone c).ι.app j))]
      congr 1
      rw [← cancel_mono (Gr.map (adj.counit.app (F.obj j)))]
      dsimp
      simp only [Category.comp_id, Adjunction.right_triangle_components, Category.id_comp,
        Category.assoc]
    · dsimp [c'']
      simp only [pullback.lift_snd]

Depends on / 依赖: Equifibered, F.rightUnitor.hom, Functor, Functor.associator, Gl.map, Gr.map, HasPullback, IsPullback, IsPullback.of_hasPullback, NatTrans, NatTrans.Equifibered, PreservesColimitsOfSize, adj.counit, adj.leftAdjoint_preservesColimits, adj.rightAdjoint_preservesLimits, adj.unit.app, associator, c.pt, condition, counit
-/
theorem IsUniversalColimit.map_reflective
    {Gl : C ⥤ D} {Gr : D ⥤ C} (adj : Gl ⊣ Gr) [Gr.Full] [Gr.Faithful]
    {F : J ⥤ D} {c : Cocone (F ⋙ Gr)}
    (H : IsUniversalColimit c)
    [forall X (f : X ⟶ Gl.obj c.pt), HasPullback (Gr.map f) (adj.unit.app c.pt)]
    [forall X (f : X ⟶ Gl.obj c.pt), PreservesLimit (cospan (Gr.map f) (adj.unit.app c.pt)) Gl] :
    IsUniversalColimit (Gl.mapCocone c) := by
  have := adj.rightAdjoint_preservesLimits
  have : PreservesColimitsOfSize.{u', v'} Gl := adj.leftAdjoint_preservesColimits
  intro F' c' α f h hα hc'
  have : HasPullback (Gl.map (Gr.map f)) (Gl.map (adj.unit.app c.pt)) :=
    ⟨⟨_, isLimitPullbackConeMapOfIsLimit _ pullback.condition
      (IsPullback.of_hasPullback _ _).isLimit⟩⟩
  let α' := α ≫ (Functor.associator _ _ _).hom ≫ whiskerLeft F adj.counit ≫ F.rightUnitor.hom
  have hα' : NatTrans.Equifibered α' := hα.comp (.of_isIso _)
  have hadj : forall X, Gl.map (adj.unit.app X) = inv (adj.counit.app _) := by
    intro X
    apply IsIso.eq_inv_of_inv_hom_id
    exact adj.left_triangle_components _
  have : forall X, IsIso (Gl.map (adj.unit.app X)) := by
    simp_rw [hadj]
    infer_instance
  have hα'' : forall j, Gl.map (Gr.map <| α'.app j) = adj.counit.app _ ≫ α.app j := by
    intro j
    rw [← cancel_mono (adj.counit.app <| F.obj j)]
    dsimp [α']
    simp only [Category.comp_id, Adjunction.counit_naturality_assoc, Category.id_comp,
      Adjunction.counit_naturality, Category.assoc, Functor.map_comp]
  have hc'' : forall j, α.app j ≫ Gl.map (c.ι.app j) = c'.ι.app j ≫ f := NatTrans.congr_app h
  let β := isoWhiskerLeft F' (asIso adj.counit) ≪≫ F'.rightUnitor
  let c'' : Cocone (F' ⋙ Gr) := by
    refine
    { pt := pullback (Gr.map f) (adj.unit.app _)
      ι := { app := fun j => pullback.lift (Gr.map <| c'.ι.app j) (Gr.map (α'.app j) ≫ c.ι.app j) ?_
             naturality := ?_ } }
    · rw [← Gr.map_comp, ← hc'']
      simp_all [← adj.unit_naturality]
    · intro i j g
      dsimp [α']
      ext
      all_goals simp only [Category.comp_id, Category.id_comp, Category.assoc,
        ← Functor.map_comp, pullback.lift_fst, pullback.lift_snd, ← Functor.map_comp_assoc]
      · congr 1
        exact c'.w _
      · rw [α.naturality_assoc]
        dsimp
        rw [adj.counit_naturality]; rw [← Category.assoc]; rw [Gr.map_comp_assoc]
        congr 1
        exact c.w _
  let cf : (Cocone.precompose β.hom).obj c' ⟶ Gl.mapCocone c'' := by
    refine { hom := pullback.lift ?_ f ?_ ≫ (PreservesPullback.iso _ _ _).inv, w := ?_ }
· exact inv adj.counit.app c'.pt
    · simp [← cancel_mono (adj.counit.app <| Gl.obj c.pt)]
    · intro j
      rw [← Category.assoc]; rw [Iso.comp_inv_eq]
      ext
      all_goals simp only [c'', PreservesPullback.iso_hom_fst, PreservesPullback.iso_hom_snd,
          pullback.lift_fst, pullback.lift_snd, Category.assoc,
          Functor.mapCocone_ι_app, ← Gl.map_comp]
      · dsimp [β]
        simp only [IsIso.comp_inv_eq, adj.counit_naturality, Category.comp_id]
      · rw [Gl.map_comp, hα'', Category.assoc, hc'']
        dsimp [β]
        rw [Category.comp_id]; rw [Category.assoc]
  have :
      cf.hom ≫ (PreservesPullback.iso _ _ _).hom ≫ pullback.fst _ _ ≫ adj.counit.app _ = 𝟙 _ := by
    simp only [cf, IsIso.inv_hom_id, Iso.inv_hom_id_assoc, Category.assoc,
      pullback.lift_fst_assoc]
  have : IsIso cf := by
    apply @Cocone.cocone_iso_of_hom_iso (i := ?_)
    rw [← IsIso.eq_comp_inv] at this
    rw [this]
    infer_instance
  have ⟨Hc''⟩ := H c'' (whiskerRight α' Gr) (pullback.snd _ _) ?_ (hα'.whiskerRight Gr) ?_
· exact ⟨IsColimit.precomposeHomEquiv β c'
      (isColimitOfPreserves Gl Hc'').ofIsoColimit (asIso cf).symm⟩
  · ext j
    dsimp [c'']
    simp only [pullback.lift_snd]
  · intro j
    apply IsPullback.of_right _ _ (IsPullback.of_hasPullback _ _)
    · dsimp [α', c'']
      simp only [Category.comp_id, Category.id_comp, Category.assoc, Functor.map_comp,
        pullback.lift_fst]
      rw [← Category.comp_id (Gr.map f)]
      refine ((hc' j).map Gr).paste_vert (IsPullback.of_vert_isIso ⟨?_⟩)
      rw [← adj.unit_naturality]; rw [Category.comp_id]; rw [← Category.assoc]; rw [← Category.id_comp (Gr.map ((Gl.mapCocone c).ι.app j))]
      congr 1
      rw [← cancel_mono (Gr.map (adj.counit.app (F.obj j)))]
      dsimp
      simp only [Category.comp_id, Adjunction.right_triangle_components, Category.id_comp,
        Category.assoc]
    · dsimp [c'']
      simp only [pullback.lift_snd]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsVanKampenColimit.map_reflective` / 定理 `IsVanKampenColimit.map_reflective`

English:
theorem IsVanKampenColimit.map_reflective
  statement: [HasColimitsOfShape J C]
  proof: by
  have := adj.rightAdjoint_preservesLimits
  have : PreservesColimitsOfSize.{u', v'} Gl := adj.leftAdjoint_preservesColimits
  intro F' c' α f h hα
  refine ⟨?_, H.isUniversal.map_reflective adj c' α f h hα⟩
  intro ⟨hc'⟩ j
  let α' := α ≫ (Functor.associator _ _ _).hom ≫ whiskerLeft F adj.counit ≫ F.rightUnitor.hom
  have hα' : NatTrans.Equifibered α' := hα.comp (.of_isIso _)
  have hα'' : forall j, Gl.map (Gr.map <| α'.app j) = adj.counit.app _ ≫ α.app j := by
    intro j
    rw [← cancel_mono (adj.counit.app <| F.obj j)]
    dsimp [α']
    simp only [Category.comp_id, Adjunction.counit_naturality_assoc, Category.id_comp,
      Adjunction.counit_naturality, Category.assoc, Functor.map_comp]
  let β := isoWhiskerLeft F' (asIso adj.counit) ≪≫ F'.rightUnitor
  let hl := (IsColimit.precomposeHomEquiv β c').symm hc'
  let hr := isColimitOfPreserves Gl (colimit.isColimit <| F' ⋙ Gr)
  have : α.app j = β.inv.app _ ≫ Gl.map (Gr.map <| α'.app j) := by
    rw [hα'']
    simp [β]
  rw [this]
  have : f = (hl.coconePointUniqueUpToIso hr).hom ≫
    Gl.map (colimit.desc _ ⟨_, whiskerRight α' Gr ≫ c.2⟩) := by
    symm
    convert!
      @IsColimit.coconePointUniqueUpToIso_hom_desc _ _ _ _ ((F' ⋙ Gr) ⋙ Gl)
        (Gl.mapCocone ⟨_, (whiskerRight α' Gr ≫ c.2 :)⟩) _ _ hl hr using 2
    · apply hr.hom_ext
      intro j
      rw [hr.fac]; rw [Functor.mapCocone_ι_app]; rw [← Gl.map_comp]; rw [colimit.cocone_ι]; rw [colimit.ι_desc]
      rfl
    · clear_value α'
      apply hl.hom_ext
      intro j
      rw [hl.fac]
      dsimp [β]
      simp only [Category.comp_id, hα'', Category.assoc, Gl.map_comp]
      congr 1
      exact (NatTrans.congr_app h j).symm
  rw [this]
  have := ((H (colimit.cocone <| F' ⋙ Gr) (whiskerRight α' Gr)
    (colimit.desc _ ⟨_, whiskerRight α' Gr ≫ c.2⟩) ?_ (hα'.whiskerRight Gr)).mp
    ⟨(getColimitCocone <| F' ⋙ Gr).2⟩ j).map Gl
  · convert! IsPullback.paste_vert _ this
    refine IsPullback.of_vert_isIso ⟨?_⟩
    rw [← IsIso.inv_comp_eq]; rw [← Category.assoc]; rw [NatIso.inv_inv_app]
    exact IsColimit.comp_coconePointUniqueUpToIso_hom hl hr _
  · clear_value α'
    ext j
    simp

中文:
定理 IsVanKampenColimit.map_reflective
  结论: [有形状余极限 J C]
  证明: by
  have := adj.rightAdjoint_preservesLimits
  have : PreservesColimitsOfSize.{u', v'} Gl := adj.leftAdjoint_preservesColimits
  intro F' c' α f h hα
  refine ⟨?_, H.isUniversal.map_reflective adj c' α f h hα⟩
  intro ⟨hc'⟩ j
  let α' := α ≫ (Functor.associator _ _ _).hom ≫ whiskerLeft F adj.counit ≫ F.rightUnitor.hom
  have hα' : NatTrans.Equifibered α' := hα.comp (.of_isIso _)
  have hα'' : forall j, Gl.map (Gr.map <| α'.app j) = adj.counit.app _ ≫ α.app j := by
    intro j
    rw [← cancel_mono (adj.counit.app <| F.obj j)]
    dsimp [α']
    simp only [Category.comp_id, Adjunction.counit_naturality_assoc, Category.id_comp,
      Adjunction.counit_naturality, Category.assoc, Functor.map_comp]
  let β := isoWhiskerLeft F' (asIso adj.counit) ≪≫ F'.rightUnitor
  let hl := (IsColimit.precomposeHomEquiv β c').symm hc'
  let hr := isColimitOfPreserves Gl (colimit.isColimit <| F' ⋙ Gr)
  have : α.app j = β.inv.app _ ≫ Gl.map (Gr.map <| α'.app j) := by
    rw [hα'']
    simp [β]
  rw [this]
  have : f = (hl.coconePointUniqueUpToIso hr).hom ≫
    Gl.map (colimit.desc _ ⟨_, whiskerRight α' Gr ≫ c.2⟩) := by
    symm
    convert!
      @IsColimit.coconePointUniqueUpToIso_hom_desc _ _ _ _ ((F' ⋙ Gr) ⋙ Gl)
        (Gl.mapCocone ⟨_, (whiskerRight α' Gr ≫ c.2 :)⟩) _ _ hl hr using 2
    · apply hr.hom_ext
      intro j
      rw [hr.fac]; rw [Functor.mapCocone_ι_app]; rw [← Gl.map_comp]; rw [colimit.cocone_ι]; rw [colimit.ι_desc]
      rfl
    · clear_value α'
      apply hl.hom_ext
      intro j
      rw [hl.fac]
      dsimp [β]
      simp only [Category.comp_id, hα'', Category.assoc, Gl.map_comp]
      congr 1
      exact (NatTrans.congr_app h j).symm
  rw [this]
  have := ((H (colimit.cocone <| F' ⋙ Gr) (whiskerRight α' Gr)
    (colimit.desc _ ⟨_, whiskerRight α' Gr ≫ c.2⟩) ?_ (hα'.whiskerRight Gr)).mp
    ⟨(getColimitCocone <| F' ⋙ Gr).2⟩ j).map Gl
  · convert! IsPullback.paste_vert _ this
    refine IsPullback.of_vert_isIso ⟨?_⟩
    rw [← IsIso.inv_comp_eq]; rw [← Category.assoc]; rw [NatIso.inv_inv_app]
    exact IsColimit.comp_coconePointUniqueUpToIso_hom hl hr _
  · clear_value α'
    ext j
    simp

Depends on / 依赖: Equifibered, F.rightUnitor.hom, Functor, Functor.associator, Gl.map, Gr.map, H.isUniversal.map_reflective, NatTrans, NatTrans.Equifibered, PreservesColimitsOfSize, adj.counit, adj.counit.app, adj.leftAdjoint_preservesColimits, adj.rightAdjoint_preservesLimits, associator, cancel_mono, counit, isUniversal, leftAdjoint_preservesColimits, map_reflective
-/
theorem IsVanKampenColimit.map_reflective [HasColimitsOfShape J C]
    {Gl : C ⥤ D} {Gr : D ⥤ C} (adj : Gl ⊣ Gr) [Gr.Full] [Gr.Faithful]
    {F : J ⥤ D} {c : Cocone (F ⋙ Gr)} (H : IsVanKampenColimit c)
    [forall X (f : X ⟶ Gl.obj c.pt), HasPullback (Gr.map f) (adj.unit.app c.pt)]
    [forall X (f : X ⟶ Gl.obj c.pt), PreservesLimit (cospan (Gr.map f) (adj.unit.app c.pt)) Gl]
    [forall X i (f : X ⟶ c.pt), PreservesLimit (cospan f (c.ι.app i)) Gl] :
    IsVanKampenColimit (Gl.mapCocone c) := by
  have := adj.rightAdjoint_preservesLimits
  have : PreservesColimitsOfSize.{u', v'} Gl := adj.leftAdjoint_preservesColimits
  intro F' c' α f h hα
  refine ⟨?_, H.isUniversal.map_reflective adj c' α f h hα⟩
  intro ⟨hc'⟩ j
  let α' := α ≫ (Functor.associator _ _ _).hom ≫ whiskerLeft F adj.counit ≫ F.rightUnitor.hom
  have hα' : NatTrans.Equifibered α' := hα.comp (.of_isIso _)
  have hα'' : forall j, Gl.map (Gr.map <| α'.app j) = adj.counit.app _ ≫ α.app j := by
    intro j
    rw [← cancel_mono (adj.counit.app <| F.obj j)]
    dsimp [α']
    simp only [Category.comp_id, Adjunction.counit_naturality_assoc, Category.id_comp,
      Adjunction.counit_naturality, Category.assoc, Functor.map_comp]
  let β := isoWhiskerLeft F' (asIso adj.counit) ≪≫ F'.rightUnitor
  let hl := (IsColimit.precomposeHomEquiv β c').symm hc'
  let hr := isColimitOfPreserves Gl (colimit.isColimit <| F' ⋙ Gr)
  have : α.app j = β.inv.app _ ≫ Gl.map (Gr.map <| α'.app j) := by
    rw [hα'']
    simp [β]
  rw [this]
  have : f = (hl.coconePointUniqueUpToIso hr).hom ≫
    Gl.map (colimit.desc _ ⟨_, whiskerRight α' Gr ≫ c.2⟩) := by
    symm
    convert!
      @IsColimit.coconePointUniqueUpToIso_hom_desc _ _ _ _ ((F' ⋙ Gr) ⋙ Gl)
        (Gl.mapCocone ⟨_, (whiskerRight α' Gr ≫ c.2 :)⟩) _ _ hl hr using 2
    · apply hr.hom_ext
      intro j
      rw [hr.fac]; rw [Functor.mapCocone_ι_app]; rw [← Gl.map_comp]; rw [colimit.cocone_ι]; rw [colimit.ι_desc]
      rfl
    · clear_value α'
      apply hl.hom_ext
      intro j
      rw [hl.fac]
      dsimp [β]
      simp only [Category.comp_id, hα'', Category.assoc, Gl.map_comp]
      congr 1
      exact (NatTrans.congr_app h j).symm
  rw [this]
  have := ((H (colimit.cocone <| F' ⋙ Gr) (whiskerRight α' Gr)
    (colimit.desc _ ⟨_, whiskerRight α' Gr ≫ c.2⟩) ?_ (hα'.whiskerRight Gr)).mp
    ⟨(getColimitCocone <| F' ⋙ Gr).2⟩ j).map Gl
  · convert! IsPullback.paste_vert _ this
    refine IsPullback.of_vert_isIso ⟨?_⟩
    rw [← IsIso.inv_comp_eq]; rw [← Category.assoc]; rw [NatIso.inv_inv_app]
    exact IsColimit.comp_coconePointUniqueUpToIso_hom hl hr _
  · clear_value α'
    ext j
    simp

end reflective

section Initial

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `hasStrictInitial_of_isUniversal` / 定理 `hasStrictInitial_of_isUniversal`

English:
theorem hasStrictInitial_of_isUniversal
  statement: [HasInitial C]
  proof: hasStrictInitialObjects_of_initial_is_strict
    (by
      intro A f
      suffices IsColimit (BinaryCofan.mk (𝟙 A) (𝟙 A)) by
        obtain ⟨l, h₁, h₂⟩ := Limits.BinaryCofan.IsColimit.desc' this (f ≫ initial.to A) (𝟙 A)
        rcases (Category.id_comp _).symm.trans h₂ with rfl
        exact ⟨⟨_, ((Category.id_comp _).symm.trans h₁).symm, initialIsInitial.hom_ext _ _⟩⟩
      refine (H (BinaryCofan.mk (𝟙 _) (𝟙 _)) (mapPair f f) f (by ext ⟨⟨⟩⟩ <;> simp)
        (.of_discrete _) ?_).some
      rintro ⟨⟨⟩⟩ <;> dsimp <;>
        exact IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩)

中文:
定理 hasStrictInitial_of_isUniversal
  结论: [HasInitial C]
  证明: hasStrictInitialObjects_of_initial_is_strict
    (by
      intro A f
      suffices IsColimit (BinaryCofan.mk (𝟙 A) (𝟙 A)) by
        obtain ⟨l, h₁, h₂⟩ := Limits.BinaryCofan.IsColimit.desc' this (f ≫ initial.to A) (𝟙 A)
        rcases (Category.id_comp _).symm.trans h₂ with rfl
        exact ⟨⟨_, ((Category.id_comp _).symm.trans h₁).symm, initialIsInitial.hom_ext _ _⟩⟩
      refine (H (BinaryCofan.mk (𝟙 _) (𝟙 _)) (mapPair f f) f (by ext ⟨⟨⟩⟩ <;> simp)
        (.of_discrete _) ?_).some
      rintro ⟨⟨⟩⟩ <;> dsimp <;>
        exact IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩)

Depends on / 依赖: BinaryCofan, BinaryCofan.mk, Category, Category.id_comp, IsColimit, IsPullback, IsPullback.of_horiz_isIso, Limits, Limits.BinaryCofan.IsColimit.desc, hasStrictInitialObjects_of_initial_is_strict, hom_ext, id_comp, initial, initial.to, initialIsInitial, initialIsInitial.hom_ext, mapPair, of_discrete, of_horiz_isIso, symm.trans
-/
theorem hasStrictInitial_of_isUniversal [HasInitial C]
    (H : IsUniversalColimit (BinaryCofan.mk (𝟙 (⊥_ C)) (𝟙 (⊥_ C)))) : HasStrictInitialObjects C :=
  hasStrictInitialObjects_of_initial_is_strict
    (by
      intro A f
      suffices IsColimit (BinaryCofan.mk (𝟙 A) (𝟙 A)) by
        obtain ⟨l, h₁, h₂⟩ := Limits.BinaryCofan.IsColimit.desc' this (f ≫ initial.to A) (𝟙 A)
        rcases (Category.id_comp _).symm.trans h₂ with rfl
        exact ⟨⟨_, ((Category.id_comp _).symm.trans h₁).symm, initialIsInitial.hom_ext _ _⟩⟩
      refine (H (BinaryCofan.mk (𝟙 _) (𝟙 _)) (mapPair f f) f (by ext ⟨⟨⟩⟩ <;> simp)
        (.of_discrete _) ?_).some
      rintro ⟨⟨⟩⟩ <;> dsimp <;>
        exact IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩)

/--
theorem `isVanKampenColimit_of_isEmpty` / 定理 `isVanKampenColimit_of_isEmpty`

English:
theorem isVanKampenColimit_of_isEmpty
  statement: [HasStrictInitialObjects C] [IsEmpty J] {F : J ⥤ C}
  proof: by
  have : IsInitial c.pt := by
    have := (IsColimit.precomposeInvEquiv (Functor.uniqueFromEmpty _) _).symm
      (hc.whiskerEquivalence (equivalenceOfIsEmpty (Discrete PEmpty.{1}) J))
    exact IsColimit.ofIsoColimit this (Cocone.ext (Iso.refl c.pt) (fun {X} => isEmptyElim X))
  replace this := IsInitial.isVanKampenColimit this
  apply (IsVanKampenColimit.whiskerEquivalence_iff
    (equivalenceOfIsEmpty (Discrete PEmpty.{1}) J)).mp
  exact (this.precompose_isIso (Functor.uniqueFromEmpty
    ((equivalenceOfIsEmpty (Discrete PEmpty.{1}) J).functor ⋙ F)).hom).of_iso
    (Cocone.ext (Iso.refl _) (by simp))

中文:
定理 isVanKampenColimit_of_isEmpty
  结论: [有StrictInitialObjects C] [是空 J] {F : J ⥤ C}
  证明: by
  have : IsInitial c.pt := by
    have := (IsColimit.precomposeInvEquiv (Functor.uniqueFromEmpty _) _).symm
      (hc.whiskerEquivalence (equivalenceOfIsEmpty (Discrete PEmpty.{1}) J))
    exact IsColimit.ofIsoColimit this (Cocone.ext (Iso.refl c.pt) (fun {X} => isEmptyElim X))
  replace this := IsInitial.isVanKampenColimit this
  apply (IsVanKampenColimit.whiskerEquivalence_iff
    (equivalenceOfIsEmpty (Discrete PEmpty.{1}) J)).mp
  exact (this.precompose_isIso (Functor.uniqueFromEmpty
    ((equivalenceOfIsEmpty (Discrete PEmpty.{1}) J).functor ⋙ F)).hom).of_iso
    (Cocone.ext (Iso.refl _) (by simp))

Depends on / 依赖: Cocone, Cocone.ext, Discre, Discrete, Functor, Functor.uniqueFromEmpty, IsColimit, IsColimit.ofIsoColimit, IsColimit.precomposeInvEquiv, IsInitial, IsInitial.isVanKampenColimit, IsVanKampenColimit, IsVanKampenColimit.whiskerEquivalence_iff, Iso.refl, PEmpty, c.pt, equivalenceOfIsEmpty, hc.whiskerEquivalence, isEmptyElim, isVanKampenColimit
-/
theorem isVanKampenColimit_of_isEmpty [HasStrictInitialObjects C] [IsEmpty J] {F : J ⥤ C}
    (c : Cocone F) (hc : IsColimit c) : IsVanKampenColimit c := by
  have : IsInitial c.pt := by
    have := (IsColimit.precomposeInvEquiv (Functor.uniqueFromEmpty _) _).symm
      (hc.whiskerEquivalence (equivalenceOfIsEmpty (Discrete PEmpty.{1}) J))
    exact IsColimit.ofIsoColimit this (Cocone.ext (Iso.refl c.pt) (fun {X} => isEmptyElim X))
  replace this := IsInitial.isVanKampenColimit this
  apply (IsVanKampenColimit.whiskerEquivalence_iff
    (equivalenceOfIsEmpty (Discrete PEmpty.{1}) J)).mp
  exact (this.precompose_isIso (Functor.uniqueFromEmpty
    ((equivalenceOfIsEmpty (Discrete PEmpty.{1}) J).functor ⋙ F)).hom).of_iso
    (Cocone.ext (Iso.refl _) (by simp))

end Initial

section BinaryCoproduct

variable {X Y : C}

/--
theorem `BinaryCofan.isVanKampen_iff` / 定理 `BinaryCofan.isVanKampen_iff`

English:
theorem BinaryCofan.isVanKampen_iff
  given: (c : BinaryCofan X Y)
  proof: by
  constructor
  · introv H hαX hαY
    rw [H c' (mapPair αX αY) f (by ext ⟨⟨⟩⟩ <;> dsimp <;> assumption) (.of_discrete _)]
    constructor
    · intro H
      exact ⟨H _, H _⟩
    · rintro H ⟨⟨⟩⟩
      exacts [H.1, H.2]
  · introv H F' hα h
    let X' := F'.obj ⟨WalkingPair.left⟩
    let Y' := F'.obj ⟨WalkingPair.right⟩
    have : F' = pair X' Y' := by
      apply Functor.hext
      · rintro ⟨⟨⟩⟩ <;> rfl
      · rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩ <;> simp [X', Y']
    clear_value X' Y'
    subst this
    change BinaryCofan X' Y' at c'
    rw [H c' _ _ _ (NatTrans.congr_app hα ⟨WalkingPair.left⟩)
        (NatTrans.congr_app hα ⟨WalkingPair.right⟩)]
    constructor
    · rintro H ⟨⟨⟩⟩
      exacts [H.1, H.2]
    · intro H
      exact ⟨H _, H _⟩

中文:
定理 BinaryCofan.isVanKampen_iff
  条件: (c : BinaryCofan X Y)
  证明: by
  constructor
  · introv H hαX hαY
    rw [H c' (mapPair αX αY) f (by ext ⟨⟨⟩⟩ <;> dsimp <;> assumption) (.of_discrete _)]
    constructor
    · intro H
      exact ⟨H _, H _⟩
    · rintro H ⟨⟨⟩⟩
      exacts [H.1, H.2]
  · introv H F' hα h
    let X' := F'.obj ⟨WalkingPair.left⟩
    let Y' := F'.obj ⟨WalkingPair.right⟩
    have : F' = pair X' Y' := by
      apply Functor.hext
      · rintro ⟨⟨⟩⟩ <;> rfl
      · rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩ <;> simp [X', Y']
    clear_value X' Y'
    subst this
    change BinaryCofan X' Y' at c'
    rw [H c' _ _ _ (NatTrans.congr_app hα ⟨WalkingPair.left⟩)
        (NatTrans.congr_app hα ⟨WalkingPair.right⟩)]
    constructor
    · rintro H ⟨⟨⟩⟩
      exacts [H.1, H.2]
    · intro H
      exact ⟨H _, H _⟩

Depends on / 依赖: BinaryCofan, Functor, Functor.hext, NatTrans, NatTrans.congr_app, WalkingPair, WalkingPair.left, WalkingPair.right, clear_value, congr_app, exacts, introv, mapPair, of_discrete
-/
theorem BinaryCofan.isVanKampen_iff (c : BinaryCofan X Y) :
    IsVanKampenColimit c ↔
      forall {X' Y' : C} (c' : BinaryCofan X' Y') (αX : X' ⟶ X) (αY : Y' ⟶ Y) (f : c'.pt ⟶ c.pt)
        (_ : αX ≫ c.inl = c'.inl ≫ f) (_ : αY ≫ c.inr = c'.inr ≫ f),
        Nonempty (IsColimit c') ↔ IsPullback c'.inl αX f c.inl ∧ IsPullback c'.inr αY f c.inr := by
  constructor
  · introv H hαX hαY
    rw [H c' (mapPair αX αY) f (by ext ⟨⟨⟩⟩ <;> dsimp <;> assumption) (.of_discrete _)]
    constructor
    · intro H
      exact ⟨H _, H _⟩
    · rintro H ⟨⟨⟩⟩
      exacts [H.1, H.2]
  · introv H F' hα h
    let X' := F'.obj ⟨WalkingPair.left⟩
    let Y' := F'.obj ⟨WalkingPair.right⟩
    have : F' = pair X' Y' := by
      apply Functor.hext
      · rintro ⟨⟨⟩⟩ <;> rfl
      · rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩ <;> simp [X', Y']
    clear_value X' Y'
    subst this
    change BinaryCofan X' Y' at c'
    rw [H c' _ _ _ (NatTrans.congr_app hα ⟨WalkingPair.left⟩)
        (NatTrans.congr_app hα ⟨WalkingPair.right⟩)]
    constructor
    · rintro H ⟨⟨⟩⟩
      exacts [H.1, H.2]
    · intro H
      exact ⟨H _, H _⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `BinaryCofan.isVanKampen_mk` / 定理 `BinaryCofan.isVanKampen_mk`

English:
theorem BinaryCofan.isVanKampen_mk
  statement: {X Y : C} (c : BinaryCofan X Y)
  proof: by
  rw [BinaryCofan.isVanKampen_iff]
  introv hX hY
  constructor
  · rintro ⟨h⟩
    let e := h.coconePointUniqueUpToIso (colimits _ _)
    obtain ⟨hl, hr⟩ := h₁ αX αY (e.inv ≫ f) (by simp [e, hX]) (by simp [e, hY])
    constructor
    · rw [← Category.id_comp αX, ← Iso.hom_inv_id_assoc e f]
      have : IsIso (𝟙 X') := inferInstance
      have : c'.inl ≫ e.hom = 𝟙 X' ≫ (cofans X' Y').inl := by
        dsimp [e]
        simp
      exact (IsPullback.of_vert_isIso ⟨this⟩).paste_vert hl
    · rw [← Category.id_comp αY, ← Iso.hom_inv_id_assoc e f]
      have : IsIso (𝟙 Y') := inferInstance
      have : c'.inr ≫ e.hom = 𝟙 Y' ≫ (cofans X' Y').inr := by
        dsimp [e]
        simp
      exact (IsPullback.of_vert_isIso ⟨this⟩).paste_vert hr
  · rintro ⟨H₁, H₂⟩
refine ⟨IsColimit.ofIsoColimit ?_ (isoBinaryCofanMk _).symm⟩
    let e₁ : X' ≅ _ := H₁.isLimit.conePointUniqueUpToIso (limits _ _)
    let e₂ : Y' ≅ _ := H₂.isLimit.conePointUniqueUpToIso (limits _ _)
    have he₁ : c'.inl = e₁.hom ≫ (cones f c.inl).fst := by simp [e₁]
    have he₂ : c'.inr = e₂.hom ≫ (cones f c.inr).fst := by simp [e₂]
    rw [he₁]; rw [he₂]
    exact (BinaryCofan.mk _ _).isColimitCompRightIso e₂.hom
      ((BinaryCofan.mk _ _).isColimitCompLeftIso e₁.hom (h₂ f))

中文:
定理 BinaryCofan.isVanKampen_mk
  结论: {X Y : C} (c : BinaryCofan X Y)
  证明: by
  rw [BinaryCofan.isVanKampen_iff]
  introv hX hY
  constructor
  · rintro ⟨h⟩
    let e := h.coconePointUniqueUpToIso (colimits _ _)
    obtain ⟨hl, hr⟩ := h₁ αX αY (e.inv ≫ f) (by simp [e, hX]) (by simp [e, hY])
    constructor
    · rw [← Category.id_comp αX, ← Iso.hom_inv_id_assoc e f]
      have : IsIso (𝟙 X') := inferInstance
      have : c'.inl ≫ e.hom = 𝟙 X' ≫ (cofans X' Y').inl := by
        dsimp [e]
        simp
      exact (IsPullback.of_vert_isIso ⟨this⟩).paste_vert hl
    · rw [← Category.id_comp αY, ← Iso.hom_inv_id_assoc e f]
      have : IsIso (𝟙 Y') := inferInstance
      have : c'.inr ≫ e.hom = 𝟙 Y' ≫ (cofans X' Y').inr := by
        dsimp [e]
        simp
      exact (IsPullback.of_vert_isIso ⟨this⟩).paste_vert hr
  · rintro ⟨H₁, H₂⟩
refine ⟨IsColimit.ofIsoColimit ?_ (isoBinaryCofanMk _).symm⟩
    let e₁ : X' ≅ _ := H₁.isLimit.conePointUniqueUpToIso (limits _ _)
    let e₂ : Y' ≅ _ := H₂.isLimit.conePointUniqueUpToIso (limits _ _)
    have he₁ : c'.inl = e₁.hom ≫ (cones f c.inl).fst := by simp [e₁]
    have he₂ : c'.inr = e₂.hom ≫ (cones f c.inr).fst := by simp [e₂]
    rw [he₁]; rw [he₂]
    exact (BinaryCofan.mk _ _).isColimitCompRightIso e₂.hom
      ((BinaryCofan.mk _ _).isColimitCompLeftIso e₁.hom (h₂ f))

Depends on / 依赖: BinaryCofan, BinaryCofan.isVanKampen_iff, Category, Category.id_comp, IsPullback, IsPullback.of_vert_isIso, Iso.hom_inv_id_assoc, coconePointUniqueUpToIso, cofans, colimits, e.hom, e.inv, h.coconePointUniqueUpToIso, hom_inv_id_assoc, id_comp, introv, isVanKampen_iff, of_vert_isIso, paste_vert
-/
theorem BinaryCofan.isVanKampen_mk {X Y : C} (c : BinaryCofan X Y)
    (cofans : forall X Y : C, BinaryCofan X Y) (colimits : forall X Y, IsColimit (cofans X Y))
    (cones : forall {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), PullbackCone f g)
    (limits : forall {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), IsLimit (cones f g))
    (h₁ : forall {X' Y' : C} (αX : X' ⟶ X) (αY : Y' ⟶ Y) (f : (cofans X' Y').pt ⟶ c.pt)
      (_ : αX ≫ c.inl = (cofans X' Y').inl ≫ f) (_ : αY ≫ c.inr = (cofans X' Y').inr ≫ f),
      IsPullback (cofans X' Y').inl αX f c.inl ∧ IsPullback (cofans X' Y').inr αY f c.inr)
    (h₂ : forall {Z : C} (f : Z ⟶ c.pt),
      IsColimit (BinaryCofan.mk (cones f c.inl).fst (cones f c.inr).fst)) :
    IsVanKampenColimit c := by
  rw [BinaryCofan.isVanKampen_iff]
  introv hX hY
  constructor
  · rintro ⟨h⟩
    let e := h.coconePointUniqueUpToIso (colimits _ _)
    obtain ⟨hl, hr⟩ := h₁ αX αY (e.inv ≫ f) (by simp [e, hX]) (by simp [e, hY])
    constructor
    · rw [← Category.id_comp αX, ← Iso.hom_inv_id_assoc e f]
      have : IsIso (𝟙 X') := inferInstance
      have : c'.inl ≫ e.hom = 𝟙 X' ≫ (cofans X' Y').inl := by
        dsimp [e]
        simp
      exact (IsPullback.of_vert_isIso ⟨this⟩).paste_vert hl
    · rw [← Category.id_comp αY, ← Iso.hom_inv_id_assoc e f]
      have : IsIso (𝟙 Y') := inferInstance
      have : c'.inr ≫ e.hom = 𝟙 Y' ≫ (cofans X' Y').inr := by
        dsimp [e]
        simp
      exact (IsPullback.of_vert_isIso ⟨this⟩).paste_vert hr
  · rintro ⟨H₁, H₂⟩
refine ⟨IsColimit.ofIsoColimit ?_ (isoBinaryCofanMk _).symm⟩
    let e₁ : X' ≅ _ := H₁.isLimit.conePointUniqueUpToIso (limits _ _)
    let e₂ : Y' ≅ _ := H₂.isLimit.conePointUniqueUpToIso (limits _ _)
    have he₁ : c'.inl = e₁.hom ≫ (cones f c.inl).fst := by simp [e₁]
    have he₂ : c'.inr = e₂.hom ≫ (cones f c.inr).fst := by simp [e₂]
    rw [he₁]; rw [he₂]
    exact (BinaryCofan.mk _ _).isColimitCompRightIso e₂.hom
      ((BinaryCofan.mk _ _).isColimitCompLeftIso e₁.hom (h₂ f))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `BinaryCofan.mono_inr_of_isVanKampen` / 定理 `BinaryCofan.mono_inr_of_isVanKampen`

English:
theorem BinaryCofan.mono_inr_of_isVanKampen
  statement: [HasInitial C] {X Y : C} {c : BinaryCofan X Y}
  proof: by
  refine PullbackCone.mono_of_isLimitMkIdId _ (IsPullback.isLimit ?_)
  refine (h (BinaryCofan.mk (initial.to Y) (𝟙 Y)) (mapPair (initial.to X) (𝟙 Y)) c.inr ?_
      (.of_discrete _)).mp ⟨?_⟩ ⟨WalkingPair.right⟩
  · ext ⟨⟨⟩⟩ <;> simp
  · exact ((BinaryCofan.isColimit_iff_isIso_inr initialIsInitial _).mpr (by
      dsimp
      infer_instance)).some

中文:
定理 BinaryCofan.mono_inr_of_isVanKampen
  结论: [HasInitial C] {X Y : C} {c : BinaryCofan X Y}
  证明: by
  refine PullbackCone.mono_of_isLimitMkIdId _ (IsPullback.isLimit ?_)
  refine (h (BinaryCofan.mk (initial.to Y) (𝟙 Y)) (mapPair (initial.to X) (𝟙 Y)) c.inr ?_
      (.of_discrete _)).mp ⟨?_⟩ ⟨WalkingPair.right⟩
  · ext ⟨⟨⟩⟩ <;> simp
  · exact ((BinaryCofan.isColimit_iff_isIso_inr initialIsInitial _).mpr (by
      dsimp
      infer_instance)).some

Depends on / 依赖: BinaryCofan, BinaryCofan.isColimit_iff_isIso_inr, BinaryCofan.mk, IsPullback, IsPullback.isLimit, PullbackCone, PullbackCone.mono_of_isLimitMkIdId, WalkingPair, WalkingPair.right, c.inr, infer_instance, initial, initial.to, initialIsInitial, isColimit_iff_isIso_inr, isLimit, mapPair, mono_of_isLimitMkIdId, of_discrete
-/
theorem BinaryCofan.mono_inr_of_isVanKampen [HasInitial C] {X Y : C} {c : BinaryCofan X Y}
    (h : IsVanKampenColimit c) : Mono c.inr := by
  refine PullbackCone.mono_of_isLimitMkIdId _ (IsPullback.isLimit ?_)
  refine (h (BinaryCofan.mk (initial.to Y) (𝟙 Y)) (mapPair (initial.to X) (𝟙 Y)) c.inr ?_
      (.of_discrete _)).mp ⟨?_⟩ ⟨WalkingPair.right⟩
  · ext ⟨⟨⟩⟩ <;> simp
  · exact ((BinaryCofan.isColimit_iff_isIso_inr initialIsInitial _).mpr (by
      dsimp
      infer_instance)).some

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `BinaryCofan.isPullback_initial_to_of_isVanKampen` / 定理 `BinaryCofan.isPullback_initial_to_of_isVanKampen`

English:
theorem BinaryCofan.isPullback_initial_to_of_isVanKampen
  statement: [HasInitial C] {c : BinaryCofan X Y}
  proof: by
  refine ((h (BinaryCofan.mk (initial.to Y) (𝟙 Y)) (mapPair (initial.to X) (𝟙 Y)) c.inr ?_
      (.of_discrete _)).mp ⟨?_⟩ ⟨WalkingPair.left⟩).flip
  · ext ⟨⟨⟩⟩ <;> simp
  · exact ((BinaryCofan.isColimit_iff_isIso_inr initialIsInitial _).mpr (by
      dsimp
      infer_instance)).some

中文:
定理 BinaryCofan.isPullback_initial_to_of_isVanKampen
  结论: [HasInitial C] {c : BinaryCofan X Y}
  证明: by
  refine ((h (BinaryCofan.mk (initial.to Y) (𝟙 Y)) (mapPair (initial.to X) (𝟙 Y)) c.inr ?_
      (.of_discrete _)).mp ⟨?_⟩ ⟨WalkingPair.left⟩).flip
  · ext ⟨⟨⟩⟩ <;> simp
  · exact ((BinaryCofan.isColimit_iff_isIso_inr initialIsInitial _).mpr (by
      dsimp
      infer_instance)).some

Depends on / 依赖: BinaryCofan, BinaryCofan.isColimit_iff_isIso_inr, BinaryCofan.mk, WalkingPair, WalkingPair.left, c.inr, infer_instance, initial, initial.to, initialIsInitial, isColimit_iff_isIso_inr, mapPair, of_discrete
-/
theorem BinaryCofan.isPullback_initial_to_of_isVanKampen [HasInitial C] {c : BinaryCofan X Y}
    (h : IsVanKampenColimit c) : IsPullback (initial.to _) (initial.to _) c.inl c.inr := by
  refine ((h (BinaryCofan.mk (initial.to Y) (𝟙 Y)) (mapPair (initial.to X) (𝟙 Y)) c.inr ?_
      (.of_discrete _)).mp ⟨?_⟩ ⟨WalkingPair.left⟩).flip
  · ext ⟨⟨⟩⟩ <;> simp
  · exact ((BinaryCofan.isColimit_iff_isIso_inr initialIsInitial _).mpr (by
      dsimp
      infer_instance)).some

end BinaryCoproduct

section FiniteCoproducts

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `isUniversalColimit_extendCofan` / 定理 `isUniversalColimit_extendCofan`

English:
theorem isUniversalColimit_extendCofan
  statement: {n : Nat} (f : Fin (n + 1) -> C)
  proof: by
  intro F c α i e hα H
  let F' : Fin (n + 1) -> C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor F' := by
    apply Functor.hext
    · exact fun i => rfl
    · rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
      simp [F']
  have t₁' := @t₁ (Discrete.functor (fun j => F.obj ⟨j.succ⟩))
    (Cofan.mk (pullback c₂.inr i) fun j => pullback.lift (α.app _ ≫ c₁.inj _) (c.ι.app _) ?_)
    (Discrete.natTrans fun i => α.app _) (pullback.fst _ _) ?_ (.of_discrete _) ?_
  rotate_left
  · simpa only [Functor.const_obj_obj, pair_obj_right, Discrete.functor_obj, Category.assoc,
      extendCofan_pt, Functor.const_obj_obj, NatTrans.comp_app, extendCofan_ι_app,
      Fin.cases_succ, Functor.const_map_app] using! congr_app e ⟨j.succ⟩
  · ext j
    dsimp
    simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, Cofan.inj]
  · intro j
    simp only [pair_obj_right, Functor.const_obj_obj, Discrete.functor_obj,
      Cofan.mk_pt, Cofan.mk_ι_app, Discrete.natTrans_app]
    refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback (BinaryCofan.inr c₂) i).flip
    · simp only [Functor.const_obj_obj, pair_obj_right, limit.lift_π,
        PullbackCone.mk_pt, PullbackCone.mk_π_app]
      exact H _
    · simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, Cofan.inj]
  obtain ⟨H₁⟩ := t₁'
  have t₂' := @t₂ (pair (F.obj ⟨0⟩) (pullback c₂.inr i))
    (BinaryCofan.mk (c.ι.app ⟨0⟩) (pullback.snd _ _)) (mapPair (α.app _) (pullback.fst _ _)) i ?_
    (.of_discrete _) ?_
  rotate_left
  · ext ⟨⟨⟩⟩
    · simpa [mapPair] using! congr_app e ⟨0⟩
    · simpa using! pullback.condition
  · rintro ⟨⟨⟩⟩
    · simp only [pair_obj_right, Functor.const_obj_obj, pair_obj_left, BinaryCofan.mk_pt,
        BinaryCofan.ι_app_left, BinaryCofan.mk_inl, mapPair_left]
      exact H ⟨0⟩
    · simp only [pair_obj_right, Functor.const_obj_obj, BinaryCofan.mk_pt, BinaryCofan.ι_app_right,
        BinaryCofan.mk_inr, mapPair_right]
      exact (IsPullback.of_hasPullback (BinaryCofan.inr c₂) i).flip
  obtain ⟨H₂⟩ := t₂'
  clear_value F'
  subst this
  refine ⟨IsColimit.ofIsoColimit (extendCofanIsColimit
    (fun i => (Discrete.functor F').obj ⟨i⟩) H₁ H₂) <| Cocone.ext (Iso.refl _) ?_⟩
  dsimp
  rintro ⟨j⟩
  simp only [limit.lift_π, PullbackCone.mk_pt,
    PullbackCone.mk_π_app, Category.comp_id]
  induction j using Fin.inductionOn
  · simp only [Fin.cases_zero]
  · simp only [Fin.cases_succ]

中文:
定理 isUniversalColimit_extendCofan
  结论: {n : 自然数} (f : 有限集 (n + 1) -> C)
  证明: by
  intro F c α i e hα H
  let F' : Fin (n + 1) -> C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor F' := by
    apply Functor.hext
    · exact fun i => rfl
    · rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
      simp [F']
  have t₁' := @t₁ (Discrete.functor (fun j => F.obj ⟨j.succ⟩))
    (Cofan.mk (pullback c₂.inr i) fun j => pullback.lift (α.app _ ≫ c₁.inj _) (c.ι.app _) ?_)
    (Discrete.natTrans fun i => α.app _) (pullback.fst _ _) ?_ (.of_discrete _) ?_
  rotate_left
  · simpa only [Functor.const_obj_obj, pair_obj_right, Discrete.functor_obj, Category.assoc,
      extendCofan_pt, Functor.const_obj_obj, NatTrans.comp_app, extendCofan_ι_app,
      Fin.cases_succ, Functor.const_map_app] using! congr_app e ⟨j.succ⟩
  · ext j
    dsimp
    simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, Cofan.inj]
  · intro j
    simp only [pair_obj_right, Functor.const_obj_obj, Discrete.functor_obj,
      Cofan.mk_pt, Cofan.mk_ι_app, Discrete.natTrans_app]
    refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback (BinaryCofan.inr c₂) i).flip
    · simp only [Functor.const_obj_obj, pair_obj_right, limit.lift_π,
        PullbackCone.mk_pt, PullbackCone.mk_π_app]
      exact H _
    · simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, Cofan.inj]
  obtain ⟨H₁⟩ := t₁'
  have t₂' := @t₂ (pair (F.obj ⟨0⟩) (pullback c₂.inr i))
    (BinaryCofan.mk (c.ι.app ⟨0⟩) (pullback.snd _ _)) (mapPair (α.app _) (pullback.fst _ _)) i ?_
    (.of_discrete _) ?_
  rotate_left
  · ext ⟨⟨⟩⟩
    · simpa [mapPair] using! congr_app e ⟨0⟩
    · simpa using! pullback.condition
  · rintro ⟨⟨⟩⟩
    · simp only [pair_obj_right, Functor.const_obj_obj, pair_obj_left, BinaryCofan.mk_pt,
        BinaryCofan.ι_app_left, BinaryCofan.mk_inl, mapPair_left]
      exact H ⟨0⟩
    · simp only [pair_obj_right, Functor.const_obj_obj, BinaryCofan.mk_pt, BinaryCofan.ι_app_right,
        BinaryCofan.mk_inr, mapPair_right]
      exact (IsPullback.of_hasPullback (BinaryCofan.inr c₂) i).flip
  obtain ⟨H₂⟩ := t₂'
  clear_value F'
  subst this
  refine ⟨IsColimit.ofIsoColimit (extendCofanIsColimit
    (fun i => (Discrete.functor F').obj ⟨i⟩) H₁ H₂) <| Cocone.ext (Iso.refl _) ?_⟩
  dsimp
  rintro ⟨j⟩
  simp only [limit.lift_π, PullbackCone.mk_pt,
    PullbackCone.mk_π_app, Category.comp_id]
  induction j using Fin.inductionOn
  · simp only [Fin.cases_zero]
  · simp only [Fin.cases_succ]

Depends on / 依赖: Cofan.mk, Discrete, Discrete.fun, Discrete.functor, Discrete.mk, Discrete.natTrans, F.obj, Functor, Functor.const_obj_obj, Functor.hext, const_obj_obj, functor, j.succ, natTrans, of_discrete, pair_obj_right, pullback, pullback.fst, pullback.lift, rotate_left
-/
theorem isUniversalColimit_extendCofan {n : Nat} (f : Fin (n + 1) -> C)
    {c₁ : Cofan fun i : Fin n => f i.succ} {c₂ : BinaryCofan (f 0) c₁.pt}
    (t₁ : IsUniversalColimit c₁) (t₂ : IsUniversalColimit c₂)
    [forall {Z} (i : Z ⟶ c₂.pt), HasPullback c₂.inr i] :
    IsUniversalColimit (extendCofan c₁ c₂) := by
  intro F c α i e hα H
  let F' : Fin (n + 1) -> C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor F' := by
    apply Functor.hext
    · exact fun i => rfl
    · rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
      simp [F']
  have t₁' := @t₁ (Discrete.functor (fun j => F.obj ⟨j.succ⟩))
    (Cofan.mk (pullback c₂.inr i) fun j => pullback.lift (α.app _ ≫ c₁.inj _) (c.ι.app _) ?_)
    (Discrete.natTrans fun i => α.app _) (pullback.fst _ _) ?_ (.of_discrete _) ?_
  rotate_left
  · simpa only [Functor.const_obj_obj, pair_obj_right, Discrete.functor_obj, Category.assoc,
      extendCofan_pt, Functor.const_obj_obj, NatTrans.comp_app, extendCofan_ι_app,
      Fin.cases_succ, Functor.const_map_app] using! congr_app e ⟨j.succ⟩
  · ext j
    dsimp
    simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, Cofan.inj]
  · intro j
    simp only [pair_obj_right, Functor.const_obj_obj, Discrete.functor_obj,
      Cofan.mk_pt, Cofan.mk_ι_app, Discrete.natTrans_app]
    refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback (BinaryCofan.inr c₂) i).flip
    · simp only [Functor.const_obj_obj, pair_obj_right, limit.lift_π,
        PullbackCone.mk_pt, PullbackCone.mk_π_app]
      exact H _
    · simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, Cofan.inj]
  obtain ⟨H₁⟩ := t₁'
  have t₂' := @t₂ (pair (F.obj ⟨0⟩) (pullback c₂.inr i))
    (BinaryCofan.mk (c.ι.app ⟨0⟩) (pullback.snd _ _)) (mapPair (α.app _) (pullback.fst _ _)) i ?_
    (.of_discrete _) ?_
  rotate_left
  · ext ⟨⟨⟩⟩
    · simpa [mapPair] using! congr_app e ⟨0⟩
    · simpa using! pullback.condition
  · rintro ⟨⟨⟩⟩
    · simp only [pair_obj_right, Functor.const_obj_obj, pair_obj_left, BinaryCofan.mk_pt,
        BinaryCofan.ι_app_left, BinaryCofan.mk_inl, mapPair_left]
      exact H ⟨0⟩
    · simp only [pair_obj_right, Functor.const_obj_obj, BinaryCofan.mk_pt, BinaryCofan.ι_app_right,
        BinaryCofan.mk_inr, mapPair_right]
      exact (IsPullback.of_hasPullback (BinaryCofan.inr c₂) i).flip
  obtain ⟨H₂⟩ := t₂'
  clear_value F'
  subst this
  refine ⟨IsColimit.ofIsoColimit (extendCofanIsColimit
    (fun i => (Discrete.functor F').obj ⟨i⟩) H₁ H₂) <| Cocone.ext (Iso.refl _) ?_⟩
  dsimp
  rintro ⟨j⟩
  simp only [limit.lift_π, PullbackCone.mk_pt,
    PullbackCone.mk_π_app, Category.comp_id]
  induction j using Fin.inductionOn
  · simp only [Fin.cases_zero]
  · simp only [Fin.cases_succ]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `isVanKampenColimit_extendCofan` / 定理 `isVanKampenColimit_extendCofan`

English:
theorem isVanKampenColimit_extendCofan
  statement: {n : Nat} (f : Fin (n + 1) -> C)
  proof: by
  intro F c α i e hα
  refine ⟨?_, isUniversalColimit_extendCofan f t₁.isUniversal t₂.isUniversal c α i e hα⟩
  intro ⟨Hc⟩ ⟨j⟩
  have t₂' := (@t₂ (pair (F.obj ⟨0⟩) (∐ fun (j : Fin n) => F.obj ⟨j.succ⟩))
    (BinaryCofan.mk (P := c.pt) (c.ι.app _) (Sigma.desc fun b => c.ι.app _))
    (mapPair (α.app _) (Sigma.desc fun b => α.app _ ≫ c₁.inj _)) i ?_ (.of_discrete _)).mp ⟨?_⟩
  rotate_left
  · ext ⟨⟨⟩⟩
    · simpa only [pair_obj_left, Functor.const_obj_obj, pair_obj_right, Discrete.functor_obj,
        NatTrans.comp_app, mapPair_left, BinaryCofan.ι_app_left, BinaryCofan.mk_pt,
        BinaryCofan.mk_inl, Functor.const_map_app, extendCofan_pt,
        extendCofan_ι_app, Fin.cases_zero] using! congr_app e ⟨0⟩
    · dsimp
      ext j
      simpa only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_pt, Cofan.mk_ι_app,
        Category.assoc, extendCofan_pt, Functor.const_obj_obj, NatTrans.comp_app, extendCofan_ι_app,
        Fin.cases_succ, Functor.const_map_app] using! congr_app e ⟨j.succ⟩
  · let F' : Fin (n + 1) -> C := F.obj ∘ Discrete.mk
    have : F = Discrete.functor F' := by
      apply Functor.hext
      · exact fun i => rfl
      · rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
        simp [F']
    clear_value F'
    subst this
    apply BinaryCofan.IsColimit.mk _ (fun {T} f₁ f₂ => Hc.desc (Cofan.mk T (Fin.cases f₁
      (fun i => Sigma.ι (fun (j : Fin n) => (Discrete.functor F').obj ⟨j.succ⟩) _ ≫ f₂))))
    · intro T f₁ f₂
      simp only [Discrete.functor_obj, pair_obj_left, BinaryCofan.mk_pt, Functor.const_obj_obj,
        BinaryCofan.mk_inl, IsColimit.fac, Cofan.mk_pt, Cofan.mk_ι_app,
        Fin.cases_zero]
    · intro T f₁ f₂
      simp only [Discrete.functor_obj, pair_obj_right, BinaryCofan.mk_pt, Functor.const_obj_obj,
        BinaryCofan.mk_inr]
      ext j
      simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_pt,
        Cofan.mk_ι_app, IsColimit.fac, Fin.cases_succ]
    · intro T f₁ f₂ f₃ m₁ m₂
      simp only [Discrete.functor_obj_eq_as, pair_obj_left, BinaryCofan.mk_pt, const_obj_obj,
        BinaryCofan.mk_inl, pair_obj_right, BinaryCofan.mk_inr] at m₁ m₂ ⊢
      refine Hc.uniq (Cofan.mk T (Fin.cases f₁
        (fun i => Sigma.ι (fun (j : Fin n) => (Discrete.functor F').obj ⟨j.succ⟩) _ ≫ f₂))) _ ?_
      intro ⟨j⟩
      simp only [Discrete.functor_obj, Cofan.mk_pt, Cofan.mk_ι_app]
      induction j using Fin.inductionOn
      · simp only [Fin.cases_zero, m₁]
      · simp only [← m₂, colimit.ι_desc_assoc, Discrete.functor_obj,
          Cofan.mk_pt, Cofan.mk_ι_app, Fin.cases_succ]
  induction j using Fin.inductionOn with
  | zero => exact t₂' ⟨WalkingPair.left⟩
  | succ j _ =>
    have t₁' := (@t₁ (Discrete.functor (fun j => F.obj ⟨j.succ⟩)) (Cofan.mk _ _) (Discrete.natTrans
      fun i => α.app _) (Sigma.desc (fun j => α.app _ ≫ c₁.inj _)) ?_
      (.of_discrete _)).mp ⟨coproductIsCoproduct _⟩ ⟨j⟩
    rotate_left
    · ext ⟨j⟩
      dsimp
      rw [colimit.ι_desc]
      rfl
    simpa [Functor.const_obj_obj, Discrete.functor_obj, extendCofan_pt, extendCofan_ι_app,
      Fin.cases_succ, BinaryCofan.mk_pt, colimit.cocone_x, Cofan.mk_pt, Cofan.mk_ι_app,
      BinaryCofan.ι_app_right, BinaryCofan.mk_inr, colimit.ι_desc,
      Discrete.natTrans_app] using! t₁'.paste_horiz (t₂' ⟨WalkingPair.right⟩)

中文:
定理 isVanKampenColimit_extendCofan
  结论: {n : 自然数} (f : 有限集 (n + 1) -> C)
  证明: by
  intro F c α i e hα
  refine ⟨?_, isUniversalColimit_extendCofan f t₁.isUniversal t₂.isUniversal c α i e hα⟩
  intro ⟨Hc⟩ ⟨j⟩
  have t₂' := (@t₂ (pair (F.obj ⟨0⟩) (∐ fun (j : Fin n) => F.obj ⟨j.succ⟩))
    (BinaryCofan.mk (P := c.pt) (c.ι.app _) (Sigma.desc fun b => c.ι.app _))
    (mapPair (α.app _) (Sigma.desc fun b => α.app _ ≫ c₁.inj _)) i ?_ (.of_discrete _)).mp ⟨?_⟩
  rotate_left
  · ext ⟨⟨⟩⟩
    · simpa only [pair_obj_left, Functor.const_obj_obj, pair_obj_right, Discrete.functor_obj,
        NatTrans.comp_app, mapPair_left, BinaryCofan.ι_app_left, BinaryCofan.mk_pt,
        BinaryCofan.mk_inl, Functor.const_map_app, extendCofan_pt,
        extendCofan_ι_app, Fin.cases_zero] using! congr_app e ⟨0⟩
    · dsimp
      ext j
      simpa only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_pt, Cofan.mk_ι_app,
        Category.assoc, extendCofan_pt, Functor.const_obj_obj, NatTrans.comp_app, extendCofan_ι_app,
        Fin.cases_succ, Functor.const_map_app] using! congr_app e ⟨j.succ⟩
  · let F' : Fin (n + 1) -> C := F.obj ∘ Discrete.mk
    have : F = Discrete.functor F' := by
      apply Functor.hext
      · exact fun i => rfl
      · rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
        simp [F']
    clear_value F'
    subst this
    apply BinaryCofan.IsColimit.mk _ (fun {T} f₁ f₂ => Hc.desc (Cofan.mk T (Fin.cases f₁
      (fun i => Sigma.ι (fun (j : Fin n) => (Discrete.functor F').obj ⟨j.succ⟩) _ ≫ f₂))))
    · intro T f₁ f₂
      simp only [Discrete.functor_obj, pair_obj_left, BinaryCofan.mk_pt, Functor.const_obj_obj,
        BinaryCofan.mk_inl, IsColimit.fac, Cofan.mk_pt, Cofan.mk_ι_app,
        Fin.cases_zero]
    · intro T f₁ f₂
      simp only [Discrete.functor_obj, pair_obj_right, BinaryCofan.mk_pt, Functor.const_obj_obj,
        BinaryCofan.mk_inr]
      ext j
      simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_pt,
        Cofan.mk_ι_app, IsColimit.fac, Fin.cases_succ]
    · intro T f₁ f₂ f₃ m₁ m₂
      simp only [Discrete.functor_obj_eq_as, pair_obj_left, BinaryCofan.mk_pt, const_obj_obj,
        BinaryCofan.mk_inl, pair_obj_right, BinaryCofan.mk_inr] at m₁ m₂ ⊢
      refine Hc.uniq (Cofan.mk T (Fin.cases f₁
        (fun i => Sigma.ι (fun (j : Fin n) => (Discrete.functor F').obj ⟨j.succ⟩) _ ≫ f₂))) _ ?_
      intro ⟨j⟩
      simp only [Discrete.functor_obj, Cofan.mk_pt, Cofan.mk_ι_app]
      induction j using Fin.inductionOn
      · simp only [Fin.cases_zero, m₁]
      · simp only [← m₂, colimit.ι_desc_assoc, Discrete.functor_obj,
          Cofan.mk_pt, Cofan.mk_ι_app, Fin.cases_succ]
  induction j using Fin.inductionOn with
  | zero => exact t₂' ⟨WalkingPair.left⟩
  | succ j _ =>
    have t₁' := (@t₁ (Discrete.functor (fun j => F.obj ⟨j.succ⟩)) (Cofan.mk _ _) (Discrete.natTrans
      fun i => α.app _) (Sigma.desc (fun j => α.app _ ≫ c₁.inj _)) ?_
      (.of_discrete _)).mp ⟨coproductIsCoproduct _⟩ ⟨j⟩
    rotate_left
    · ext ⟨j⟩
      dsimp
      rw [colimit.ι_desc]
      rfl
    simpa [Functor.const_obj_obj, Discrete.functor_obj, extendCofan_pt, extendCofan_ι_app,
      Fin.cases_succ, BinaryCofan.mk_pt, colimit.cocone_x, Cofan.mk_pt, Cofan.mk_ι_app,
      BinaryCofan.ι_app_right, BinaryCofan.mk_inr, colimit.ι_desc,
      Discrete.natTrans_app] using! t₁'.paste_horiz (t₂' ⟨WalkingPair.right⟩)

Depends on / 依赖: BinaryCofan, BinaryCofan.mk, Discrete, Discrete.functor_obj, F.obj, Functor, Functor.const_obj_obj, NatTrans, NatTrans.comp_app, Sigma.desc, c.pt, comp_app, const_obj_obj, functor_obj, isUniversal, isUniversalColimit_extendCofan, j.succ, mapPair, of_discrete, pair_obj_left
-/
theorem isVanKampenColimit_extendCofan {n : Nat} (f : Fin (n + 1) -> C)
    {c₁ : Cofan fun i : Fin n => f i.succ} {c₂ : BinaryCofan (f 0) c₁.pt}
    (t₁ : IsVanKampenColimit c₁) (t₂ : IsVanKampenColimit c₂)
    [forall {Z} (i : Z ⟶ c₂.pt), HasPullback c₂.inr i]
    [HasFiniteCoproducts C] :
    IsVanKampenColimit (extendCofan c₁ c₂) := by
  intro F c α i e hα
  refine ⟨?_, isUniversalColimit_extendCofan f t₁.isUniversal t₂.isUniversal c α i e hα⟩
  intro ⟨Hc⟩ ⟨j⟩
  have t₂' := (@t₂ (pair (F.obj ⟨0⟩) (∐ fun (j : Fin n) => F.obj ⟨j.succ⟩))
    (BinaryCofan.mk (P := c.pt) (c.ι.app _) (Sigma.desc fun b => c.ι.app _))
    (mapPair (α.app _) (Sigma.desc fun b => α.app _ ≫ c₁.inj _)) i ?_ (.of_discrete _)).mp ⟨?_⟩
  rotate_left
  · ext ⟨⟨⟩⟩
    · simpa only [pair_obj_left, Functor.const_obj_obj, pair_obj_right, Discrete.functor_obj,
        NatTrans.comp_app, mapPair_left, BinaryCofan.ι_app_left, BinaryCofan.mk_pt,
        BinaryCofan.mk_inl, Functor.const_map_app, extendCofan_pt,
        extendCofan_ι_app, Fin.cases_zero] using! congr_app e ⟨0⟩
    · dsimp
      ext j
      simpa only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_pt, Cofan.mk_ι_app,
        Category.assoc, extendCofan_pt, Functor.const_obj_obj, NatTrans.comp_app, extendCofan_ι_app,
        Fin.cases_succ, Functor.const_map_app] using! congr_app e ⟨j.succ⟩
  · let F' : Fin (n + 1) -> C := F.obj ∘ Discrete.mk
    have : F = Discrete.functor F' := by
      apply Functor.hext
      · exact fun i => rfl
      · rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
        simp [F']
    clear_value F'
    subst this
    apply BinaryCofan.IsColimit.mk _ (fun {T} f₁ f₂ => Hc.desc (Cofan.mk T (Fin.cases f₁
      (fun i => Sigma.ι (fun (j : Fin n) => (Discrete.functor F').obj ⟨j.succ⟩) _ ≫ f₂))))
    · intro T f₁ f₂
      simp only [Discrete.functor_obj, pair_obj_left, BinaryCofan.mk_pt, Functor.const_obj_obj,
        BinaryCofan.mk_inl, IsColimit.fac, Cofan.mk_pt, Cofan.mk_ι_app,
        Fin.cases_zero]
    · intro T f₁ f₂
      simp only [Discrete.functor_obj, pair_obj_right, BinaryCofan.mk_pt, Functor.const_obj_obj,
        BinaryCofan.mk_inr]
      ext j
      simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_pt,
        Cofan.mk_ι_app, IsColimit.fac, Fin.cases_succ]
    · intro T f₁ f₂ f₃ m₁ m₂
      simp only [Discrete.functor_obj_eq_as, pair_obj_left, BinaryCofan.mk_pt, const_obj_obj,
        BinaryCofan.mk_inl, pair_obj_right, BinaryCofan.mk_inr] at m₁ m₂ ⊢
      refine Hc.uniq (Cofan.mk T (Fin.cases f₁
        (fun i => Sigma.ι (fun (j : Fin n) => (Discrete.functor F').obj ⟨j.succ⟩) _ ≫ f₂))) _ ?_
      intro ⟨j⟩
      simp only [Discrete.functor_obj, Cofan.mk_pt, Cofan.mk_ι_app]
      induction j using Fin.inductionOn
      · simp only [Fin.cases_zero, m₁]
      · simp only [← m₂, colimit.ι_desc_assoc, Discrete.functor_obj,
          Cofan.mk_pt, Cofan.mk_ι_app, Fin.cases_succ]
  induction j using Fin.inductionOn with
  | zero => exact t₂' ⟨WalkingPair.left⟩
  | succ j _ =>
    have t₁' := (@t₁ (Discrete.functor (fun j => F.obj ⟨j.succ⟩)) (Cofan.mk _ _) (Discrete.natTrans
      fun i => α.app _) (Sigma.desc (fun j => α.app _ ≫ c₁.inj _)) ?_
      (.of_discrete _)).mp ⟨coproductIsCoproduct _⟩ ⟨j⟩
    rotate_left
    · ext ⟨j⟩
      dsimp
      rw [colimit.ι_desc]
      rfl
    simpa [Functor.const_obj_obj, Discrete.functor_obj, extendCofan_pt, extendCofan_ι_app,
      Fin.cases_succ, BinaryCofan.mk_pt, colimit.cocone_x, Cofan.mk_pt, Cofan.mk_ι_app,
      BinaryCofan.ι_app_right, BinaryCofan.mk_inr, colimit.ι_desc,
      Discrete.natTrans_app] using! t₁'.paste_horiz (t₂' ⟨WalkingPair.right⟩)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `isPullback_of_cofan_isVanKampen` / 定理 `isPullback_of_cofan_isVanKampen`

English:
theorem isPullback_of_cofan_isVanKampen
  statement: [HasInitial C] {ι : Type*} {X : ι -> C}
  proof: by
  refine (hc (Cofan.mk (X i) (f := fun k => if k = i then X i else ⊥_ C)
    (fun k => if h : k = i then (eqToHom <| if_pos h) else (eqToHom <| if_neg h) ≫ initial.to _))
    (Discrete.natTrans (fun k => if h : k.1 = i then (eqToHom <| (if_pos h).trans
(congr_arg X h.symm)) else (eqToHom if_neg h) ≫ initial.to _))
    (c.inj i) ?_ (.of_discrete _)).mp ⟨?_⟩ ⟨j⟩
  · ext ⟨k⟩
    simp only [Discrete.functor_obj, Functor.const_obj_obj, NatTrans.comp_app,
      Discrete.natTrans_app, Cofan.mk_pt, Cofan.mk_ι_app, Functor.const_map_app]
    split
    · subst ‹k = i›; rfl
    · simp
  · refine Cofan.IsColimit.mk _ (fun t => (eqToHom (if_pos rfl).symm) ≫ t.inj i) ?_ ?_
    · intro t j
      simp only [Cofan.mk_pt, cofan_mk_inj]
      split
      · subst ‹j = i›; simp
      · rw [Category.assoc, ← IsIso.eq_inv_comp]
        exact initialIsInitial.hom_ext _ _
    · intro t m hm
      simp [← hm i]

中文:
定理 isPullback_of_cofan_isVanKampen
  结论: [HasInitial C] {ι : 类型} {X : ι -> C}
  证明: by
  refine (hc (Cofan.mk (X i) (f := fun k => if k = i then X i else ⊥_ C)
    (fun k => if h : k = i then (eqToHom <| if_pos h) else (eqToHom <| if_neg h) ≫ initial.to _))
    (Discrete.natTrans (fun k => if h : k.1 = i then (eqToHom <| (if_pos h).trans
(congr_arg X h.symm)) else (eqToHom if_neg h) ≫ initial.to _))
    (c.inj i) ?_ (.of_discrete _)).mp ⟨?_⟩ ⟨j⟩
  · ext ⟨k⟩
    simp only [Discrete.functor_obj, Functor.const_obj_obj, NatTrans.comp_app,
      Discrete.natTrans_app, Cofan.mk_pt, Cofan.mk_ι_app, Functor.const_map_app]
    split
    · subst ‹k = i›; rfl
    · simp
  · refine Cofan.IsColimit.mk _ (fun t => (eqToHom (if_pos rfl).symm) ≫ t.inj i) ?_ ?_
    · intro t j
      simp only [Cofan.mk_pt, cofan_mk_inj]
      split
      · subst ‹j = i›; simp
      · rw [Category.assoc, ← IsIso.eq_inv_comp]
        exact initialIsInitial.hom_ext _ _
    · intro t m hm
      simp [← hm i]
-/
theorem isPullback_of_cofan_isVanKampen [HasInitial C] {ι : Type*} {X : ι -> C}
    {c : Cofan X} (hc : IsVanKampenColimit c) (i j : ι) [DecidableEq ι] :
    IsPullback (P := (if j = i then X i else ⊥_ C))
      (if h : j = i then eqToHom (if_pos h) else eqToHom (if_neg h) ≫ initial.to (X i))
      (if h : j = i then eqToHom ((if_pos h).trans (congr_arg X h.symm))
        else eqToHom (if_neg h) ≫ initial.to (X j))
      (Cofan.inj c i) (Cofan.inj c j) := by
  refine (hc (Cofan.mk (X i) (f := fun k => if k = i then X i else ⊥_ C)
    (fun k => if h : k = i then (eqToHom <| if_pos h) else (eqToHom <| if_neg h) ≫ initial.to _))
    (Discrete.natTrans (fun k => if h : k.1 = i then (eqToHom <| (if_pos h).trans
(congr_arg X h.symm)) else (eqToHom if_neg h) ≫ initial.to _))
    (c.inj i) ?_ (.of_discrete _)).mp ⟨?_⟩ ⟨j⟩
  · ext ⟨k⟩
    simp only [Discrete.functor_obj, Functor.const_obj_obj, NatTrans.comp_app,
      Discrete.natTrans_app, Cofan.mk_pt, Cofan.mk_ι_app, Functor.const_map_app]
    split
    · subst ‹k = i›; rfl
    · simp
  · refine Cofan.IsColimit.mk _ (fun t => (eqToHom (if_pos rfl).symm) ≫ t.inj i) ?_ ?_
    · intro t j
      simp only [Cofan.mk_pt, cofan_mk_inj]
      split
      · subst ‹j = i›; simp
      · rw [Category.assoc, ← IsIso.eq_inv_comp]
        exact initialIsInitial.hom_ext _ _
    · intro t m hm
      simp [← hm i]

/--
theorem `isPullback_initial_to_of_cofan_isVanKampen` / 定理 `isPullback_initial_to_of_cofan_isVanKampen`

English:
theorem isPullback_initial_to_of_cofan_isVanKampen
  statement: [HasInitial C] {ι : Type*} {F : Discrete ι ⥤ C}
  proof: by
  classical
  let f : ι -> C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun i => rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  have : forall i, Subsingleton (⊥_ C ⟶ (Discrete.functor f).obj i) := inferInstance
  convert! isPullback_of_cofan_isVanKampen hc i.as j.as
  exact (if_neg (mt Discrete.ext hi.symm)).symm

中文:
定理 isPullback_initial_to_of_cofan_isVanKampen
  结论: [HasInitial C] {ι : 类型} {F : 离散 ι ⥤ C}
  证明: by
  classical
  let f : ι -> C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun i => rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  have : forall i, Subsingleton (⊥_ C ⟶ (Discrete.functor f).obj i) := inferInstance
  convert! isPullback_of_cofan_isVanKampen hc i.as j.as
  exact (if_neg (mt Discrete.ext hi.symm)).symm

Depends on / 依赖: Discrete, Discrete.ext, Discrete.functor, Discrete.mk, F.obj, Functor, Functor.hext, Subsingleton, classical, clear_value, convert, functor, hi.symm, i.as, if_neg, isPullback_of_cofan_isVanKampen, j.as
-/
theorem isPullback_initial_to_of_cofan_isVanKampen [HasInitial C] {ι : Type*} {F : Discrete ι ⥤ C}
    {c : Cocone F} (hc : IsVanKampenColimit c) (i j : Discrete ι) (hi : i != j) :
    IsPullback (initial.to _) (initial.to _) (c.ι.app i) (c.ι.app j) := by
  classical
  let f : ι -> C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun i => rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  have : forall i, Subsingleton (⊥_ C ⟶ (Discrete.functor f).obj i) := inferInstance
  convert! isPullback_of_cofan_isVanKampen hc i.as j.as
  exact (if_neg (mt Discrete.ext hi.symm)).symm

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mono_of_cofan_isVanKampen` / 定理 `mono_of_cofan_isVanKampen`

English:
theorem mono_of_cofan_isVanKampen
  statement: [HasInitial C] {ι : Type*} {F : Discrete ι ⥤ C}
  proof: by
  classical
  let f : ι -> C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun i => rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  refine PullbackCone.mono_of_isLimitMkIdId _ (IsPullback.isLimit ?_)
  nth_rw 1 [← Category.id_comp (c.ι.app i)]
  convert! IsPullback.paste_vert _ (isPullback_of_cofan_isVanKampen hc i.as i.as)
  swap
  · exact (eqToHom (if_pos rfl).symm)
  · simp
  · exact IsPullback.of_vert_isIso ⟨by simp⟩

中文:
定理 mono_of_cofan_isVanKampen
  结论: [HasInitial C] {ι : 类型} {F : 离散 ι ⥤ C}
  证明: by
  classical
  let f : ι -> C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun i => rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  refine PullbackCone.mono_of_isLimitMkIdId _ (IsPullback.isLimit ?_)
  nth_rw 1 [← Category.id_comp (c.ι.app i)]
  convert! IsPullback.paste_vert _ (isPullback_of_cofan_isVanKampen hc i.as i.as)
  swap
  · exact (eqToHom (if_pos rfl).symm)
  · simp
  · exact IsPullback.of_vert_isIso ⟨by simp⟩

Depends on / 依赖: Category, Category.id_comp, Discrete, Discrete.functor, Discrete.mk, F.obj, Functor, Functor.hext, IsPullback, IsPullback.isLimit, IsPullback.of_vert_isIso, IsPullback.paste_vert, PullbackCone, PullbackCone.mono_of_isLimitMkIdId, classical, clear_value, convert, eqToHom, functor, i.as
-/
theorem mono_of_cofan_isVanKampen [HasInitial C] {ι : Type*} {F : Discrete ι ⥤ C}
    {c : Cocone F} (hc : IsVanKampenColimit c) (i : Discrete ι) : Mono (c.ι.app i) := by
  classical
  let f : ι -> C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun i => rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  refine PullbackCone.mono_of_isLimitMkIdId _ (IsPullback.isLimit ?_)
  nth_rw 1 [← Category.id_comp (c.ι.app i)]
  convert! IsPullback.paste_vert _ (isPullback_of_cofan_isVanKampen hc i.as i.as)
  swap
  · exact (eqToHom (if_pos rfl).symm)
  · simp
  · exact IsPullback.of_vert_isIso ⟨by simp⟩

end FiniteCoproducts

section CoproductsPullback

variable {ι ι' : Type*} {S : C}
variable {B : C} {X : ι -> C} {a : Cofan X} (hau : IsUniversalColimit a) (f : forall i, X i ⟶ S)
  (u : a.pt ⟶ S) (v : B ⟶ S)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
include hau in
/--
lemma `IsUniversalColimit.nonempty_isColimit_of_pullbackCone_left` / 引理 `IsUniversalColimit.nonempty_isColimit_of_pullbackCone_left`

English:
lemma IsUniversalColimit.nonempty_isColimit_of_pullbackCone_left
  proof: by
  let iso : d ≅ (Cofan.mk _ fun i : ι => PullbackCone.IsLimit.lift ht
      (s i).fst ((s i).snd ≫ a.inj i) (by simp [hu, (s i).condition])) :=
Cofan.ext e fun p => PullbackCone.IsLimit.hom_ext ht (by simp [he₁]) (by simp [he₂])
  rw [(IsColimit.equivIsoColimit iso).nonempty_congr]
  refine hau _ (Discrete.natTrans fun i => (s i.as).snd) t.snd ?_ (.of_discrete _) fun j => ?_
  · ext; simp [Cofan.inj]
  · simp only [Discrete.functor_obj_eq_as, Cofan.mk_pt, Functor.const_obj_obj, Cofan.mk_ι_app,
      Discrete.natTrans_app]
    rw [← Cofan.inj]
    refine IsPullback.of_right ?_ (by simp) (IsPullback.of_isLimit ht)
    simpa [hu] using (IsPullback.of_isLimit (hs j.1))

中文:
引理 IsUniversalColimit.nonempty_isColimit_of_pullbackCone_left
  证明: by
  let iso : d ≅ (Cofan.mk _ fun i : ι => PullbackCone.IsLimit.lift ht
      (s i).fst ((s i).snd ≫ a.inj i) (by simp [hu, (s i).condition])) :=
Cofan.ext e fun p => PullbackCone.IsLimit.hom_ext ht (by simp [he₁]) (by simp [he₂])
  rw [(IsColimit.equivIsoColimit iso).nonempty_congr]
  refine hau _ (Discrete.natTrans fun i => (s i.as).snd) t.snd ?_ (.of_discrete _) fun j => ?_
  · ext; simp [Cofan.inj]
  · simp only [Discrete.functor_obj_eq_as, Cofan.mk_pt, Functor.const_obj_obj, Cofan.mk_ι_app,
      Discrete.natTrans_app]
    rw [← Cofan.inj]
    refine IsPullback.of_right ?_ (by simp) (IsPullback.of_isLimit ht)
    simpa [hu] using (IsPullback.of_isLimit (hs j.1))

Depends on / 依赖: Cofan.ext, Cofan.mk, Discrete, Discrete.natTrans, IsColimit, IsColimit.equivIsoColimit, IsLimit, Nonempty, PullbackCone, PullbackCone.IsLimit.hom_ext, PullbackCone.IsLimit.lift, a.inj, cat_disch, condition, d.inj, e.hom, equivIsoColimit, hom_ext, natTrans, nonempty_congr
-/
lemma IsUniversalColimit.nonempty_isColimit_of_pullbackCone_left
    (s : forall i, PullbackCone v (f i)) (hs : forall i, IsLimit (s i))
    (t : PullbackCone v u) (ht : IsLimit t) (d : Cofan (fun i : ι => (s i).pt)) (e : d.pt ≅ t.pt)
    (hu : forall i, a.inj i ≫ u = f i := by cat_disch)
    (he₁ : forall i, d.inj i ≫ e.hom ≫ t.fst = (s i).fst := by cat_disch)
    (he₂ : forall i, d.inj i ≫ e.hom ≫ t.snd = (s i).snd ≫ a.inj i := by cat_disch) :
    Nonempty (IsColimit d) := by
  let iso : d ≅ (Cofan.mk _ fun i : ι => PullbackCone.IsLimit.lift ht
      (s i).fst ((s i).snd ≫ a.inj i) (by simp [hu, (s i).condition])) :=
Cofan.ext e fun p => PullbackCone.IsLimit.hom_ext ht (by simp [he₁]) (by simp [he₂])
  rw [(IsColimit.equivIsoColimit iso).nonempty_congr]
  refine hau _ (Discrete.natTrans fun i => (s i.as).snd) t.snd ?_ (.of_discrete _) fun j => ?_
  · ext; simp [Cofan.inj]
  · simp only [Discrete.functor_obj_eq_as, Cofan.mk_pt, Functor.const_obj_obj, Cofan.mk_ι_app,
      Discrete.natTrans_app]
    rw [← Cofan.inj]
    refine IsPullback.of_right ?_ (by simp) (IsPullback.of_isLimit ht)
    simpa [hu] using (IsPullback.of_isLimit (hs j.1))

section

variable {P : ι -> C} (q₁ : forall i, P i ⟶ B) (q₂ : forall i, P i ⟶ X i)
  (hP : forall i, IsPullback (q₁ i) (q₂ i) v (f i))

include hau hP in
/--
lemma `IsUniversalColimit.nonempty_isColimit_of_isPullback_left` / 引理 `IsUniversalColimit.nonempty_isColimit_of_isPullback_left`

English:
lemma IsUniversalColimit.nonempty_isColimit_of_isPullback_left
  proof: hau.nonempty_isColimit_of_pullbackCone_left f u v (fun i => (hP i).cone)
    (fun i => (hP i).isLimit) h.cone h.isLimit d e

中文:
引理 IsUniversalColimit.nonempty_isColimit_of_isPullback_left
  证明: hau.nonempty_isColimit_of_pullbackCone_left f u v (fun i => (hP i).cone)
    (fun i => (hP i).isLimit) h.cone h.isLimit d e

Depends on / 依赖: IsColimit, Nonempty, a.inj, cat_disch, d.inj, e.hom, h.cone, h.isLimit, hau.nonempty_isColimit_of_pullbackCone_left, isLimit, nonempty_isColimit_of_pullbackCone_left
-/
lemma IsUniversalColimit.nonempty_isColimit_of_isPullback_left
    {Z : C} {p₁ : Z ⟶ B} {p₂ : Z ⟶ a.pt} (h : IsPullback p₁ p₂ v u)
    (d : Cofan P) (e : d.pt ≅ Z)
    (hu : forall i, a.inj i ≫ u = f i := by cat_disch)
    (he₁ : forall i, d.inj i ≫ e.hom ≫ p₁ = q₁ i := by cat_disch)
    (he₂ : forall i, d.inj i ≫ e.hom ≫ p₂ = q₂ i ≫ a.inj i := by cat_disch) :
    Nonempty (IsColimit d) :=
  hau.nonempty_isColimit_of_pullbackCone_left f u v (fun i => (hP i).cone)
    (fun i => (hP i).isLimit) h.cone h.isLimit d e

set_option backward.isDefEq.respectTransparency false in
include hau hP in
/--
lemma `IsUniversalColimit.isPullback_of_isColimit_left` / 引理 `IsUniversalColimit.isPullback_of_isColimit_left`

English:
lemma IsUniversalColimit.isPullback_of_isColimit_left
  statement: {d : Cofan P} (hd : IsColimit d)
  proof: by
  let c : Cofan P := Cofan.mk (pullback v u)
    fun i => pullback.lift (q₁ i) (q₂ i ≫ a.inj i) (by simp [(hP i).w, hu])
  obtain ⟨hc⟩ := hau.nonempty_isColimit_of_isPullback_left f u
    v q₁ q₂ hP (IsPullback.of_hasPullback _ _) c (Iso.refl _)
  refine (IsPullback.of_hasPullback v u).of_iso
      ?_ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · exact hc.coconePointUniqueUpToIso hd
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i => ?_
    simpa [Cofan.inj, Cofan.IsColimit.desc] using! pullback.lift_fst _ _ _
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i => ?_
    simpa [Cofan.inj, Cofan.IsColimit.desc] using! pullback.lift_snd _ _ _

中文:
引理 IsUniversalColimit.isPullback_of_isColimit_left
  结论: {d : Cofan P} (hd : 是余极限 d)
  证明: by
  let c : Cofan P := Cofan.mk (pullback v u)
    fun i => pullback.lift (q₁ i) (q₂ i ≫ a.inj i) (by simp [(hP i).w, hu])
  obtain ⟨hc⟩ := hau.nonempty_isColimit_of_isPullback_left f u
    v q₁ q₂ hP (IsPullback.of_hasPullback _ _) c (Iso.refl _)
  refine (IsPullback.of_hasPullback v u).of_iso
      ?_ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · exact hc.coconePointUniqueUpToIso hd
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i => ?_
    simpa [Cofan.inj, Cofan.IsColimit.desc] using! pullback.lift_fst _ _ _
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i => ?_
    simpa [Cofan.inj, Cofan.IsColimit.desc] using! pullback.lift_snd _ _ _

Depends on / 依赖: Cofan.IsColimit.desc, Cofan.mk, HasPullback, IsColimit, IsPullback, IsPullback.of_hasPullback, Iso.refl, a.inj, cat_disch, coconePointUni, hau.nonempty_isColimit_of_isPullback_left, hc.coconePointUni, nonempty_isColimit_of_isPullback_left, of_hasPullback, of_iso, pullback, pullback.lift
-/
lemma IsUniversalColimit.isPullback_of_isColimit_left {d : Cofan P} (hd : IsColimit d)
    (hu : forall i, a.inj i ≫ u = f i := by cat_disch)
    [HasPullback v u] :
    IsPullback (Cofan.IsColimit.desc hd q₁) (Cofan.IsColimit.desc hd (q₂ · ≫ a.inj _))
      v u := by
  let c : Cofan P := Cofan.mk (pullback v u)
    fun i => pullback.lift (q₁ i) (q₂ i ≫ a.inj i) (by simp [(hP i).w, hu])
  obtain ⟨hc⟩ := hau.nonempty_isColimit_of_isPullback_left f u
    v q₁ q₂ hP (IsPullback.of_hasPullback _ _) c (Iso.refl _)
  refine (IsPullback.of_hasPullback v u).of_iso
      ?_ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · exact hc.coconePointUniqueUpToIso hd
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i => ?_
    simpa [Cofan.inj, Cofan.IsColimit.desc] using! pullback.lift_fst _ _ _
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i => ?_
    simpa [Cofan.inj, Cofan.IsColimit.desc] using! pullback.lift_snd _ _ _

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
include hau in
/--
lemma `IsUniversalColimit.nonempty_isColimit_of_pullbackCone_right` / 引理 `IsUniversalColimit.nonempty_isColimit_of_pullbackCone_right`

English:
lemma IsUniversalColimit.nonempty_isColimit_of_pullbackCone_right
  proof: by
  let iso : d ≅ (Cofan.mk _ fun i : ι => PullbackCone.IsLimit.lift ht
      ((s i).fst ≫ a.inj i) ((s i).snd) (by simp [hu, (s i).condition])) :=
Cofan.ext e fun p => PullbackCone.IsLimit.hom_ext ht (by simp [he₁]) (by simp [he₂])
  rw [(IsColimit.equivIsoColimit iso).nonempty_congr]
  refine hau _ (Discrete.natTrans fun i => (s i.as).fst) t.fst ?_ (.of_discrete _) fun j => ?_
  · ext; simp [Cofan.inj]
  · simp only [Discrete.functor_obj_eq_as, Cofan.mk_pt, Functor.const_obj_obj, Cofan.mk_ι_app,
      Discrete.natTrans_app]
    rw [← Cofan.inj]
    refine IsPullback.of_right ?_ (by simp) (IsPullback.of_isLimit ht).flip
    simpa [hu] using (IsPullback.of_isLimit (hs j.1)).flip

中文:
引理 IsUniversalColimit.nonempty_isColimit_of_pullbackCone_right
  证明: by
  let iso : d ≅ (Cofan.mk _ fun i : ι => PullbackCone.IsLimit.lift ht
      ((s i).fst ≫ a.inj i) ((s i).snd) (by simp [hu, (s i).condition])) :=
Cofan.ext e fun p => PullbackCone.IsLimit.hom_ext ht (by simp [he₁]) (by simp [he₂])
  rw [(IsColimit.equivIsoColimit iso).nonempty_congr]
  refine hau _ (Discrete.natTrans fun i => (s i.as).fst) t.fst ?_ (.of_discrete _) fun j => ?_
  · ext; simp [Cofan.inj]
  · simp only [Discrete.functor_obj_eq_as, Cofan.mk_pt, Functor.const_obj_obj, Cofan.mk_ι_app,
      Discrete.natTrans_app]
    rw [← Cofan.inj]
    refine IsPullback.of_right ?_ (by simp) (IsPullback.of_isLimit ht).flip
    simpa [hu] using (IsPullback.of_isLimit (hs j.1)).flip

Depends on / 依赖: Cofan.ext, Cofan.mk, Discrete, Discrete.natTran, IsColimit, IsColimit.equivIsoColimit, IsLimit, Nonempty, PullbackCone, PullbackCone.IsLimit.hom_ext, PullbackCone.IsLimit.lift, a.inj, cat_disch, condition, d.inj, e.hom, equivIsoColimit, hom_ext, natTran, nonempty_congr
-/
lemma IsUniversalColimit.nonempty_isColimit_of_pullbackCone_right
    (s : forall i, PullbackCone (f i) v) (hs : forall i, IsLimit (s i))
    (t : PullbackCone u v) (ht : IsLimit t) (d : Cofan (fun i : ι => (s i).pt)) (e : d.pt ≅ t.pt)
    (hu : forall i, a.inj i ≫ u = f i := by cat_disch)
    (he₁ : forall i, d.inj i ≫ e.hom ≫ t.fst = (s i).fst ≫ a.inj i := by cat_disch)
    (he₂ : forall i, d.inj i ≫ e.hom ≫ t.snd = (s i).snd := by cat_disch) :
    Nonempty (IsColimit d) := by
  let iso : d ≅ (Cofan.mk _ fun i : ι => PullbackCone.IsLimit.lift ht
      ((s i).fst ≫ a.inj i) ((s i).snd) (by simp [hu, (s i).condition])) :=
Cofan.ext e fun p => PullbackCone.IsLimit.hom_ext ht (by simp [he₁]) (by simp [he₂])
  rw [(IsColimit.equivIsoColimit iso).nonempty_congr]
  refine hau _ (Discrete.natTrans fun i => (s i.as).fst) t.fst ?_ (.of_discrete _) fun j => ?_
  · ext; simp [Cofan.inj]
  · simp only [Discrete.functor_obj_eq_as, Cofan.mk_pt, Functor.const_obj_obj, Cofan.mk_ι_app,
      Discrete.natTrans_app]
    rw [← Cofan.inj]
    refine IsPullback.of_right ?_ (by simp) (IsPullback.of_isLimit ht).flip
    simpa [hu] using (IsPullback.of_isLimit (hs j.1)).flip

section

variable {P : ι -> C} (q₁ : forall i, P i ⟶ X i) (q₂ : forall i, P i ⟶ B)
  (hP : forall i, IsPullback (q₁ i) (q₂ i) (f i) v)

include hau hP in
/--
lemma `IsUniversalColimit.nonempty_isColimit_of_isPullback_right` / 引理 `IsUniversalColimit.nonempty_isColimit_of_isPullback_right`

English:
lemma IsUniversalColimit.nonempty_isColimit_of_isPullback_right
  proof: hau.nonempty_isColimit_of_pullbackCone_right f u v (fun i => (hP i).cone)
    (fun i => (hP i).isLimit) h.cone h.isLimit d e

中文:
引理 IsUniversalColimit.nonempty_isColimit_of_isPullback_right
  证明: hau.nonempty_isColimit_of_pullbackCone_right f u v (fun i => (hP i).cone)
    (fun i => (hP i).isLimit) h.cone h.isLimit d e

Depends on / 依赖: IsColimit, Nonempty, a.inj, cat_disch, d.inj, e.hom, h.cone, h.isLimit, hau.nonempty_isColimit_of_pullbackCone_right, isLimit, nonempty_isColimit_of_pullbackCone_right
-/
lemma IsUniversalColimit.nonempty_isColimit_of_isPullback_right
    {Z : C} {p₁ : Z ⟶ a.pt} {p₂ : Z ⟶ B} (h : IsPullback p₁ p₂ u v)
    (d : Cofan P) (e : d.pt ≅ Z)
    (hu : forall i, a.inj i ≫ u = f i := by cat_disch)
    (he₁ : forall i, d.inj i ≫ e.hom ≫ p₁ = q₁ i ≫ a.inj i := by cat_disch)
    (he₂ : forall i, d.inj i ≫ e.hom ≫ p₂ = q₂ i := by cat_disch) :
    Nonempty (IsColimit d) :=
  hau.nonempty_isColimit_of_pullbackCone_right f u v (fun i => (hP i).cone)
    (fun i => (hP i).isLimit) h.cone h.isLimit d e

set_option backward.isDefEq.respectTransparency false in
include hau hP in
/--
lemma `IsUniversalColimit.isPullback_of_isColimit_right` / 引理 `IsUniversalColimit.isPullback_of_isColimit_right`

English:
lemma IsUniversalColimit.isPullback_of_isColimit_right
  statement: {d : Cofan P} (hd : IsColimit d)
  proof: by
  let c : Cofan P := Cofan.mk (pullback u v)
    fun i => pullback.lift (q₁ i ≫ a.inj i) (q₂ i) (by simp [(hP i).w, hu])
  obtain ⟨hc⟩ := hau.nonempty_isColimit_of_isPullback_right f u
    v q₁ q₂ hP (IsPullback.of_hasPullback _ _) c (Iso.refl _)
  refine (IsPullback.of_hasPullback u v).of_iso
      ?_ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · exact hc.coconePointUniqueUpToIso hd
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i => ?_
    simpa [Cofan.inj, Cofan.IsColimit.desc] using! pullback.lift_fst _ _ _
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i => ?_
    simpa [Cofan.inj, Cofan.IsColimit.desc] using! pullback.lift_snd _ _ _

中文:
引理 IsUniversalColimit.isPullback_of_isColimit_right
  结论: {d : Cofan P} (hd : 是余极限 d)
  证明: by
  let c : Cofan P := Cofan.mk (pullback u v)
    fun i => pullback.lift (q₁ i ≫ a.inj i) (q₂ i) (by simp [(hP i).w, hu])
  obtain ⟨hc⟩ := hau.nonempty_isColimit_of_isPullback_right f u
    v q₁ q₂ hP (IsPullback.of_hasPullback _ _) c (Iso.refl _)
  refine (IsPullback.of_hasPullback u v).of_iso
      ?_ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · exact hc.coconePointUniqueUpToIso hd
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i => ?_
    simpa [Cofan.inj, Cofan.IsColimit.desc] using! pullback.lift_fst _ _ _
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i => ?_
    simpa [Cofan.inj, Cofan.IsColimit.desc] using! pullback.lift_snd _ _ _

Depends on / 依赖: Cofan.IsColimit.desc, Cofan.mk, HasPullback, IsColimit, IsPullback, IsPullback.of_hasPullback, Iso.refl, a.inj, cat_disch, coconePointUn, hau.nonempty_isColimit_of_isPullback_right, hc.coconePointUn, nonempty_isColimit_of_isPullback_right, of_hasPullback, of_iso, pullback, pullback.lift
-/
lemma IsUniversalColimit.isPullback_of_isColimit_right {d : Cofan P} (hd : IsColimit d)
    (hu : forall i, a.inj i ≫ u = f i := by cat_disch)
    [HasPullback u v] :
    IsPullback (Cofan.IsColimit.desc hd (q₁ · ≫ a.inj _)) (Cofan.IsColimit.desc hd q₂)
      u v := by
  let c : Cofan P := Cofan.mk (pullback u v)
    fun i => pullback.lift (q₁ i ≫ a.inj i) (q₂ i) (by simp [(hP i).w, hu])
  obtain ⟨hc⟩ := hau.nonempty_isColimit_of_isPullback_right f u
    v q₁ q₂ hP (IsPullback.of_hasPullback _ _) c (Iso.refl _)
  refine (IsPullback.of_hasPullback u v).of_iso
      ?_ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · exact hc.coconePointUniqueUpToIso hd
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i => ?_
    simpa [Cofan.inj, Cofan.IsColimit.desc] using! pullback.lift_fst _ _ _
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i => ?_
    simpa [Cofan.inj, Cofan.IsColimit.desc] using! pullback.lift_snd _ _ _

end

variable {Y : ι' -> C} {b : Cofan Y} (hbu : IsUniversalColimit b)
  (f : forall i, X i ⟶ S) (g : forall i, Y i ⟶ S) (u : a.pt ⟶ S) (v : b.pt ⟶ S)
  [forall i, HasPullback (f i) v]

set_option backward.isDefEq.respectTransparency false in
include hau hbu in
/--
lemma `IsUniversalColimit.nonempty_isColimit_prod_of_pullbackCone` / 引理 `IsUniversalColimit.nonempty_isColimit_prod_of_pullbackCone`

English:
lemma IsUniversalColimit.nonempty_isColimit_prod_of_pullbackCone
  proof: by
  let c (i : ι) : Cofan (fun j : ι' => (s i j).pt) :=
    Cofan.mk (pullback (f i) v) fun j => pullback.lift (s i j).fst ((s i j).snd ≫ b.inj j)
      (by simp [hv, (s i j).condition])
  let c' : Cofan (fun i : ι => (c i).pt) :=
    Cofan.mk t.pt fun i =>
      PullbackCone.IsLimit.lift ht (pullback.fst _ _ ≫ a.inj i) (pullback.snd _ _)
      (by simp [hu, pullback.condition])
  let iso : d ≅ Cofan.mk c'.pt fun p : ι × ι' => (c p.1).inj p.2 ≫ c'.inj _ := by
refine Cofan.ext e fun p => PullbackCone.IsLimit.hom_ext ht ?_ ?_
    · simp [c', c, he₁]
    · simp [c', c, he₂]
  rw [(IsColimit.equivIsoColimit iso).nonempty_congr]
  refine ⟨Cofan.IsColimit.prod c (fun i => Nonempty.some ?_) c' (Nonempty.some ?_)⟩
  · exact hbu.nonempty_isColimit_of_pullbackCone_left _ v _ _ (hs i) (pullback.cone _ _)
      (pullback.isLimit _ _) _ (Iso.refl _)
  · exact hau.nonempty_isColimit_of_pullbackCone_right _ u _ _ (fun _ => pullback.isLimit _ _)
      t ht _ (Iso.refl _)

include hau hbu in

中文:
引理 IsUniversalColimit.nonempty_isColimit_prod_of_pullbackCone
  证明: by
  let c (i : ι) : Cofan (fun j : ι' => (s i j).pt) :=
    Cofan.mk (pullback (f i) v) fun j => pullback.lift (s i j).fst ((s i j).snd ≫ b.inj j)
      (by simp [hv, (s i j).condition])
  let c' : Cofan (fun i : ι => (c i).pt) :=
    Cofan.mk t.pt fun i =>
      PullbackCone.IsLimit.lift ht (pullback.fst _ _ ≫ a.inj i) (pullback.snd _ _)
      (by simp [hu, pullback.condition])
  let iso : d ≅ Cofan.mk c'.pt fun p : ι × ι' => (c p.1).inj p.2 ≫ c'.inj _ := by
refine Cofan.ext e fun p => PullbackCone.IsLimit.hom_ext ht ?_ ?_
    · simp [c', c, he₁]
    · simp [c', c, he₂]
  rw [(IsColimit.equivIsoColimit iso).nonempty_congr]
  refine ⟨Cofan.IsColimit.prod c (fun i => Nonempty.some ?_) c' (Nonempty.some ?_)⟩
  · exact hbu.nonempty_isColimit_of_pullbackCone_left _ v _ _ (hs i) (pullback.cone _ _)
      (pullback.isLimit _ _) _ (Iso.refl _)
  · exact hau.nonempty_isColimit_of_pullbackCone_right _ u _ _ (fun _ => pullback.isLimit _ _)
      t ht _ (Iso.refl _)

include hau hbu in

Depends on / 依赖: Cofan.mk, IsColimit, Nonempty, a.inj, b.inj, cat_disch, condition, d.inj, e.hom, pullback, pullback.lift, t.fst, t.snd
-/
lemma IsUniversalColimit.nonempty_isColimit_prod_of_pullbackCone
    (s : forall (i : ι) (j : ι'), PullbackCone (f i) (g j))
    (hs : forall i j, IsLimit (s i j)) (t : PullbackCone u v) (ht : IsLimit t)
    {d : Cofan (fun p : ι × ι' => (s p.1 p.2).pt)} (e : d.pt ≅ t.pt)
    (hu : forall i, a.inj i ≫ u = f i := by cat_disch)
    (hv : forall i, b.inj i ≫ v = g i := by cat_disch)
    (he₁ : forall i j, d.inj (i, j) ≫ e.hom ≫ t.fst = (s _ _).fst ≫ a.inj _ := by cat_disch)
    (he₂ : forall i j, d.inj (i, j) ≫ e.hom ≫ t.snd = (s _ _).snd ≫ b.inj _ := by cat_disch) :
    Nonempty (IsColimit d) := by
  let c (i : ι) : Cofan (fun j : ι' => (s i j).pt) :=
    Cofan.mk (pullback (f i) v) fun j => pullback.lift (s i j).fst ((s i j).snd ≫ b.inj j)
      (by simp [hv, (s i j).condition])
  let c' : Cofan (fun i : ι => (c i).pt) :=
    Cofan.mk t.pt fun i =>
      PullbackCone.IsLimit.lift ht (pullback.fst _ _ ≫ a.inj i) (pullback.snd _ _)
      (by simp [hu, pullback.condition])
  let iso : d ≅ Cofan.mk c'.pt fun p : ι × ι' => (c p.1).inj p.2 ≫ c'.inj _ := by
refine Cofan.ext e fun p => PullbackCone.IsLimit.hom_ext ht ?_ ?_
    · simp [c', c, he₁]
    · simp [c', c, he₂]
  rw [(IsColimit.equivIsoColimit iso).nonempty_congr]
  refine ⟨Cofan.IsColimit.prod c (fun i => Nonempty.some ?_) c' (Nonempty.some ?_)⟩
  · exact hbu.nonempty_isColimit_of_pullbackCone_left _ v _ _ (hs i) (pullback.cone _ _)
      (pullback.isLimit _ _) _ (Iso.refl _)
  · exact hau.nonempty_isColimit_of_pullbackCone_right _ u _ _ (fun _ => pullback.isLimit _ _)
      t ht _ (Iso.refl _)

include hau hbu in
/--
lemma `IsUniversalColimit.nonempty_isColimit_prod_of_isPullback` / 引理 `IsUniversalColimit.nonempty_isColimit_prod_of_isPullback`

English:
lemma IsUniversalColimit.nonempty_isColimit_prod_of_isPullback
  proof: IsUniversalColimit.nonempty_isColimit_prod_of_pullbackCone hau hbu f g u v
    (fun i j => (hP i j).cone) (fun i j => (hP i j).isLimit) h.cone h.isLimit e

中文:
引理 IsUniversalColimit.nonempty_isColimit_prod_of_isPullback
  证明: IsUniversalColimit.nonempty_isColimit_prod_of_pullbackCone hau hbu f g u v
    (fun i j => (hP i j).cone) (fun i j => (hP i j).isLimit) h.cone h.isLimit e

Depends on / 依赖: IsColimit, IsUniversalColimit, IsUniversalColimit.nonempty_isColimit_prod_of_pullbackCone, Nonempty, Projective, Projective.hasLiftingProperty_of_isZero, a.inj, b.inj, cat_disch, d.inj, e.hom, h.cone, h.isLimit, hasLiftingProperty_of_isZero, isLimit, isZero_zero, nonempty_isColimit_prod_of_pullbackCone
-/
lemma IsUniversalColimit.nonempty_isColimit_prod_of_isPullback
    {P : ι × ι' -> C} {q₁ : forall i j, P (i, j) ⟶ X i} {q₂ : forall i j, P (i, j) ⟶ Y j}
    (hP : forall i j, IsPullback (q₁ i j) (q₂ i j) (f i) (g j))
    {Z : C} {p₁ : Z ⟶ a.pt} {p₂ : Z ⟶ b.pt} (h : IsPullback p₁ p₂ u v)
    {d : Cofan P} (e : d.pt ≅ Z)
    (hu : forall i, a.inj i ≫ u = f i := by cat_disch)
    (hv : forall i, b.inj i ≫ v = g i := by cat_disch)
    (he₁ : forall i j, d.inj (i, j) ≫ e.hom ≫ p₁ = q₁ _ _ ≫ a.inj _ := by cat_disch)
    (he₂ : forall i j, d.inj (i, j) ≫ e.hom ≫ p₂ = q₂ _ _ ≫ b.inj _ := by cat_disch) :
    Nonempty (IsColimit d) :=
  IsUniversalColimit.nonempty_isColimit_prod_of_pullbackCone hau hbu f g u v
    (fun i j => (hP i j).cone) (fun i j => (hP i j).isLimit) h.cone h.isLimit e

set_option backward.isDefEq.respectTransparency false in
include hau hbu in
/--
lemma `IsUniversalColimit.isPullback_prod_of_isColimit` / 引理 `IsUniversalColimit.isPullback_prod_of_isColimit`

English:
lemma IsUniversalColimit.isPullback_prod_of_isColimit
  statement: [HasPullback u v]
  proof: by
  let c : Cofan P := Cofan.mk (pullback u v)
    fun p => pullback.lift (q₁ p.1 p.2 ≫ a.inj p.1) (q₂ p.1 p.2 ≫ b.inj _)
      (by simp [(hP p.1 p.2).w, hu, hv])
  obtain ⟨hc⟩ := hau.nonempty_isColimit_prod_of_isPullback hbu f g u
    v hP (IsPullback.of_hasPullback _ _) (d := c) (Iso.refl _)
  refine (IsPullback.of_hasPullback u v).of_iso
      ?_ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · exact hc.coconePointUniqueUpToIso hd
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i => ?_
    simpa [Cofan.inj, Cofan.IsColimit.desc] using! pullback.lift_fst _ _ _
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i => ?_
    simpa [Cofan.inj, Cofan.IsColimit.desc] using! pullback.lift_snd _ _ _

中文:
引理 IsUniversalColimit.isPullback_prod_of_isColimit
  结论: [HasPullback u v]
  证明: by
  let c : Cofan P := Cofan.mk (pullback u v)
    fun p => pullback.lift (q₁ p.1 p.2 ≫ a.inj p.1) (q₂ p.1 p.2 ≫ b.inj _)
      (by simp [(hP p.1 p.2).w, hu, hv])
  obtain ⟨hc⟩ := hau.nonempty_isColimit_prod_of_isPullback hbu f g u
    v hP (IsPullback.of_hasPullback _ _) (d := c) (Iso.refl _)
  refine (IsPullback.of_hasPullback u v).of_iso
      ?_ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · exact hc.coconePointUniqueUpToIso hd
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i => ?_
    simpa [Cofan.inj, Cofan.IsColimit.desc] using! pullback.lift_fst _ _ _
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i => ?_
    simpa [Cofan.inj, Cofan.IsColimit.desc] using! pullback.lift_snd _ _ _

Depends on / 依赖: Cofan.IsColimit.desc, Cofan.mk, IsColimit, IsPullback, IsPullback.of, IsPullback.of_hasPullback, Iso.refl, a.inj, b.inj, cat_disch, hau.nonempty_isColimit_prod_of_isPullback, nonempty_isColimit_prod_of_isPullback, of_hasPullback, pullback, pullback.lift
-/
lemma IsUniversalColimit.isPullback_prod_of_isColimit [HasPullback u v]
    {P : ι × ι' -> C} {q₁ : forall i j, P (i, j) ⟶ X i} {q₂ : forall i j, P (i, j) ⟶ Y j}
    (hP : forall i j, IsPullback (q₁ i j) (q₂ i j) (f i) (g j)) (d : Cofan P) (hd : IsColimit d)
    (hu : forall i, a.inj i ≫ u = f i := by cat_disch)
    (hv : forall i, b.inj i ≫ v = g i := by cat_disch) :
    IsPullback
      (Cofan.IsColimit.desc hd (fun p => q₁ p.1 p.2 ≫ a.inj _))
      (Cofan.IsColimit.desc hd (fun p => q₂ p.1 p.2 ≫ b.inj _)) u v := by
  let c : Cofan P := Cofan.mk (pullback u v)
    fun p => pullback.lift (q₁ p.1 p.2 ≫ a.inj p.1) (q₂ p.1 p.2 ≫ b.inj _)
      (by simp [(hP p.1 p.2).w, hu, hv])
  obtain ⟨hc⟩ := hau.nonempty_isColimit_prod_of_isPullback hbu f g u
    v hP (IsPullback.of_hasPullback _ _) (d := c) (Iso.refl _)
  refine (IsPullback.of_hasPullback u v).of_iso
      ?_ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · exact hc.coconePointUniqueUpToIso hd
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i => ?_
    simpa [Cofan.inj, Cofan.IsColimit.desc] using! pullback.lift_fst _ _ _
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i => ?_
    simpa [Cofan.inj, Cofan.IsColimit.desc] using! pullback.lift_snd _ _ _

end CoproductsPullback

end CategoryTheory
