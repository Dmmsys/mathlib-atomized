/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.GradedObject.Associator
public import Mathlib.CategoryTheory.GradedObject.Single
/-!
# The left and right unitors

Given a bifunctor `F : C ⥤ D ⥤ D`, an object `X : C` such that `F.obj X ≅ 𝟭 D` and a
map `p : I × J → J` such that `hp : ∀ (j : J), p ⟨0, j⟩ = j`,
we define an isomorphism of `J`-graded objects for any `Y : GradedObject J D`.
`mapBifunctorLeftUnitor F X e p hp Y : mapBifunctorMapObj F p ((single₀ I).obj X) Y ≅ Y`.
Under similar assumptions, we also obtain a right unitor isomorphism
`mapBifunctorMapObj F p X ((single₀ I).obj Y) ≅ X`. Finally,
the lemma `mapBifunctor_triangle` promotes a triangle identity involving functors
to a triangle identity for the induced functors on graded objects.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace GradedObject

section LeftUnitor

variable {C D I J : Type*} [Category* C] [Category* D]
  [Zero I] [DecidableEq I] [HasInitial C]
  (F : C ⥤ D ⥤ D) (X : C) (e : F.obj X ≅ 𝟭 D)
  [forall (Y : D), PreservesColimit (Functor.empty.{0} C) (F.flip.obj Y)]
  (p : I × J -> J) (hp : forall (j : J), p ⟨0, j⟩ = j)
  (Y Y' : GradedObject J D) (φ : Y ⟶ Y')

/-- Given `F : C ⥤ D ⥤ D`, `X : C`, `e : F.obj X ≅ 𝟭 D` and `Y : GradedObject J D`,
this is the isomorphism `((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y a ≅ Y a.2`
when `a : I × J` is such that `a.1 = 0`. -/
@[simps!]
/--
Definition of `mapBifunctorObjSingle₀ObjIso` / `mapBifunctorObjSingle₀ObjIso` 的定义

English:
definition mapBifunctorObjSingle₀ObjIso
  signature: (a : I × J) (ha : a.1 = 0)
  body: (F.mapIso (singleObjApplyIsoOfEq _ X _ ha)).app _ ≪≫ e.app (Y a.2)

中文:
定义 mapBifunctorObjSingle₀ObjIso
  签名: (a : I × J) (ha : a.1 = 0)
  定义体: (F.mapIso (singleObjApplyIsoOfEq _ X _ ha)).app _ ≪≫ e.app (Y a.2)

Depends on / 依赖: F.mapIso, e.app, mapIso, singleObjApplyIsoOfEq
-/
noncomputable def mapBifunctorObjSingle₀ObjIso (a : I × J) (ha : a.1 = 0) :
    ((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y a ≅ Y a.2 :=
  (F.mapIso (singleObjApplyIsoOfEq _ X _ ha)).app _ ≪≫ e.app (Y a.2)

/--
Definition of `mapBifunctorObjSingle₀ObjIsInitial` / `mapBifunctorObjSingle₀ObjIsInitial` 的定义

English:
definition mapBifunctorObjSingle₀ObjIsInitial
  signature: (a : I × J) (ha : a.1 != 0)
  body: IsInitial.isInitialObj (F.flip.obj (Y a.2)) _ (isInitialSingleObjApply _ _ _ ha)

中文:
定义 mapBifunctorObjSingle₀ObjIsInitial
  签名: (a : I × J) (ha : a.1 != 0)
  定义体: IsInitial.isInitialObj (F.flip.obj (Y a.2)) _ (isInitialSingleObjApply _ _ _ ha)

Depends on / 依赖: F.flip.obj, IsInitial, IsInitial.isInitialObj, isInitialObj, isInitialSingleObjApply
-/
noncomputable def mapBifunctorObjSingle₀ObjIsInitial (a : I × J) (ha : a.1 != 0) :
    IsInitial (((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y a) :=
  IsInitial.isInitialObj (F.flip.obj (Y a.2)) _ (isInitialSingleObjApply _ _ _ ha)

/--
Definition of `mapBifunctorLeftUnitorCofan` / `mapBifunctorLeftUnitorCofan` 的定义

English:
definition mapBifunctorLeftUnitorCofan
  signature: (hp : forall (j : J), p ⟨0, j⟩ = j) (Y) (j : J)
  body: CofanMapObjFun.mk _ _ _ (Y j) (fun a ha =>
    if ha : a.1 = 0 then
      (mapBifunctorObjSingle₀ObjIso F X e Y a ha).hom ≫ eqToHom (by aesop)
    else
      (mapBifunctorObjSingle₀ObjIsInitial F X Y a ha).to _)

中文:
定义 mapBifunctorLeftUnitorCofan
  签名: (hp : 对任意 (j : J), p ⟨0, j⟩ = j) (Y) (j : J)
  定义体: CofanMapObjFun.mk _ _ _ (Y j) (fun a ha =>
    if ha : a.1 = 0 then
      (mapBifunctorObjSingle₀ObjIso F X e Y a ha).hom ≫ eqToHom (by aesop)
    else
      (mapBifunctorObjSingle₀ObjIsInitial F X Y a ha).to _)

Depends on / 依赖: CofanMapObjFun, CofanMapObjFun.mk, eqToHom
-/
noncomputable def mapBifunctorLeftUnitorCofan (hp : forall (j : J), p ⟨0, j⟩ = j) (Y) (j : J) :
    (((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y).CofanMapObjFun p j :=
  CofanMapObjFun.mk _ _ _ (Y j) (fun a ha =>
    if ha : a.1 = 0 then
      (mapBifunctorObjSingle₀ObjIso F X e Y a ha).hom ≫ eqToHom (by aesop)
    else
      (mapBifunctorObjSingle₀ObjIsInitial F X Y a ha).to _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp, reassoc]
/--
lemma `mapBifunctorLeftUnitorCofan_inj` / 引理 `mapBifunctorLeftUnitorCofan_inj`

English:
lemma mapBifunctorLeftUnitorCofan_inj
  given: (j : J)
  proof: by
  simp [mapBifunctorLeftUnitorCofan]

中文:
引理 mapBifunctorLeftUnitorCofan_inj
  条件: (j : J)
  证明: by
  simp [mapBifunctorLeftUnitorCofan]

Depends on / 依赖: mapBifunctorLeftUnitorCofan
-/
lemma mapBifunctorLeftUnitorCofan_inj (j : J) :
    (mapBifunctorLeftUnitorCofan F X e p hp Y j).inj ⟨⟨0, j⟩, hp j⟩ =
      (F.map (singleObjApplyIso (0 : I) X).hom).app (Y j) ≫ e.hom.app (Y j) := by
  simp [mapBifunctorLeftUnitorCofan]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mapBifunctorLeftUnitorCofanIsColimit` / `mapBifunctorLeftUnitorCofanIsColimit` 的定义

English:
definition mapBifunctorLeftUnitorCofanIsColimit
  signature: (j : J)
  body: Cofan.IsColimit.mk _
    (fun s => e.inv.app (Y j) ≫
      (F.map (singleObjApplyIso (0 : I) X).inv).app (Y j) ≫ s.inj ⟨⟨0, j⟩, hp j⟩)
    (fun s => by
      rintro ⟨⟨i, j'⟩, h⟩
      by_cases hi : i = 0
      · subst hi
        simp only [Set.mem_preimage, hp, Set.mem_singleton_iff] at h
        su

中文:
定义 mapBifunctorLeftUnitorCofanIsColimit
  签名: (j : J)
  定义体: Cofan.IsColimit.mk _
    (fun s => e.inv.app (Y j) ≫
      (F.map (singleObjApplyIso (0 : I) X).inv).app (Y j) ≫ s.inj ⟨⟨0, j⟩, hp j⟩)
    (fun s => by
      rintro ⟨⟨i, j'⟩, h⟩
      by_cases hi : i = 0
      · subst hi
        simp only [Set.mem_preimage, hp, Set.mem_singleton_iff] at h
        su

Depends on / 依赖: Cofan.IsColimit.mk, F.map, Hom.id, IsColimit, IsInitial, IsInitial.hom_ext, Set.mem_preimage, Set.mem_singleton_iff, WidePushoutShape, e.inv.app, hom_ext, mem_preimage, mem_singleton_iff, s.inj, singleObjApplyIso
-/
noncomputable def mapBifunctorLeftUnitorCofanIsColimit (j : J) :
    IsColimit (mapBifunctorLeftUnitorCofan F X e p hp Y j) :=
  Cofan.IsColimit.mk _
    (fun s => e.inv.app (Y j) ≫
      (F.map (singleObjApplyIso (0 : I) X).inv).app (Y j) ≫ s.inj ⟨⟨0, j⟩, hp j⟩)
    (fun s => by
      rintro ⟨⟨i, j'⟩, h⟩
      by_cases hi : i = 0
      · subst hi
        simp only [Set.mem_preimage, hp, Set.mem_singleton_iff] at h
        subst h
        simp
      · apply IsInitial.hom_ext
        exact mapBifunctorObjSingle₀ObjIsInitial _ _ _ _ hi)
    (fun s m hm => by simp [← hm ⟨⟨0, j⟩, hp j⟩])

include e hp in
/--
lemma `mapBifunctorLeftUnitor_hasMap` / 引理 `mapBifunctorLeftUnitor_hasMap`

English:
lemma mapBifunctorLeftUnitor_hasMap
  proof: CofanMapObjFun.hasMap _ _ _ (mapBifunctorLeftUnitorCofanIsColimit F X e p hp Y)

中文:
引理 mapBifunctorLeftUnitor_hasMap
  证明: CofanMapObjFun.hasMap _ _ _ (mapBifunctorLeftUnitorCofanIsColimit F X e p hp Y)

Depends on / 依赖: CofanMapObjFun, CofanMapObjFun.hasMap, hasMap, mapBifunctorLeftUnitorCofanIsColimit
-/
lemma mapBifunctorLeftUnitor_hasMap :
    HasMap (((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y) p :=
  CofanMapObjFun.hasMap _ _ _ (mapBifunctorLeftUnitorCofanIsColimit F X e p hp Y)

variable [HasMap (((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y) p]
  [HasMap (((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y') p]

/--
Definition of `mapBifunctorLeftUnitor` / `mapBifunctorLeftUnitor` 的定义

English:
definition mapBifunctorLeftUnitor
  signature: : mapBifunctorMapObj F p ((single₀ I).obj X) Y ≅ Y
  body: isoMk _ _ (fun j => (CofanMapObjFun.iso
    (mapBifunctorLeftUnitorCofanIsColimit F X e p hp Y j)).symm)

中文:
定义 mapBifunctorLeftUnitor
  签名: : mapBifunctorMapObj F p ((single₀ I).obj X) Y ≅ Y
  定义体: isoMk _ _ (fun j => (CofanMapObjFun.iso
    (mapBifunctorLeftUnitorCofanIsColimit F X e p hp Y j)).symm)

Depends on / 依赖: CofanMapObjFun, CofanMapObjFun.iso, mapBifunctorLeftUnitorCofanIsColimit
-/
noncomputable def mapBifunctorLeftUnitor : mapBifunctorMapObj F p ((single₀ I).obj X) Y ≅ Y :=
  isoMk _ _ (fun j => (CofanMapObjFun.iso
    (mapBifunctorLeftUnitorCofanIsColimit F X e p hp Y j)).symm)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `ι_mapBifunctorLeftUnitor_hom_apply` / 引理 `ι_mapBifunctorLeftUnitor_hom_apply`

English:
lemma ι_mapBifunctorLeftUnitor_hom_apply
  given: (j : J)
  proof: by
  dsimp [mapBifunctorLeftUnitor]
  erw [CofanMapObjFun.ιMapObj_iso_inv]
  rw [mapBifunctorLeftUnitorCofan_inj]

中文:
引理 ι_mapBifunctorLeftUnitor_hom_apply
  条件: (j : J)
  证明: by
  dsimp [mapBifunctorLeftUnitor]
  erw [CofanMapObjFun.ιMapObj_iso_inv]
  rw [mapBifunctorLeftUnitorCofan_inj]

Depends on / 依赖: CofanMapObjFun, mapBifunctorLeftUnitor, mapBifunctorLeftUnitorCofan_inj
-/
lemma ι_mapBifunctorLeftUnitor_hom_apply (j : J) :
    ιMapBifunctorMapObj F p ((single₀ I).obj X) Y 0 j j (hp j) ≫
      (mapBifunctorLeftUnitor F X e p hp Y).hom j =
      (F.map (singleObjApplyIso (0 : I) X).hom).app _ ≫ e.hom.app (Y j) := by
  dsimp [mapBifunctorLeftUnitor]
  erw [CofanMapObjFun.ιMapObj_iso_inv]
  rw [mapBifunctorLeftUnitorCofan_inj]

/--
lemma `mapBifunctorLeftUnitor_inv_apply` / 引理 `mapBifunctorLeftUnitor_inv_apply`

English:
lemma mapBifunctorLeftUnitor_inv_apply
  given: (j : J)
  proof: rfl

中文:
引理 mapBifunctorLeftUnitor_inv_apply
  条件: (j : J)
  证明: rfl
-/
lemma mapBifunctorLeftUnitor_inv_apply (j : J) :
    (mapBifunctorLeftUnitor F X e p hp Y).inv j =
      e.inv.app (Y j) ≫ (F.map (singleObjApplyIso (0 : I) X).inv).app (Y j) ≫
      ιMapBifunctorMapObj F p ((single₀ I).obj X) Y 0 j j (hp j) := rfl

variable {Y Y'}

@[reassoc]
/--
lemma `mapBifunctorLeftUnitor_inv_naturality` / 引理 `mapBifunctorLeftUnitor_inv_naturality`

English:
lemma mapBifunctorLeftUnitor_inv_naturality
  proof: by
  ext j
  dsimp
  rw [mapBifunctorLeftUnitor_inv_apply]; rw [mapBifunctorLeftUnitor_inv_apply]; rw [assoc]; rw [assoc]; rw [ι_mapBifunctorMapMap]
  dsimp
  rw [Functor.map_id]; rw [NatTrans.id_app]; rw [id_comp]; rw [← NatTrans.naturality_assoc]; rw [← NatTrans.naturality_assoc]
  rfl

@[reassoc]

中文:
引理 mapBifunctorLeftUnitor_inv_naturality
  证明: by
  ext j
  dsimp
  rw [mapBifunctorLeftUnitor_inv_apply]; rw [mapBifunctorLeftUnitor_inv_apply]; rw [assoc]; rw [assoc]; rw [ι_mapBifunctorMapMap]
  dsimp
  rw [Functor.map_id]; rw [NatTrans.id_app]; rw [id_comp]; rw [← NatTrans.naturality_assoc]; rw [← NatTrans.naturality_assoc]
  rfl

@[reassoc]

Depends on / 依赖: Functor, Functor.map_id, NatTrans, NatTrans.id_app, NatTrans.naturality_assoc, id_app, id_comp, mapBifunctorLeftUnitor_inv_apply, map_id, naturality_assoc
-/
lemma mapBifunctorLeftUnitor_inv_naturality :
    φ ≫ (mapBifunctorLeftUnitor F X e p hp Y').inv =
      (mapBifunctorLeftUnitor F X e p hp Y).inv ≫ mapBifunctorMapMap F p (𝟙 _) φ := by
  ext j
  dsimp
  rw [mapBifunctorLeftUnitor_inv_apply]; rw [mapBifunctorLeftUnitor_inv_apply]; rw [assoc]; rw [assoc]; rw [ι_mapBifunctorMapMap]
  dsimp
  rw [Functor.map_id]; rw [NatTrans.id_app]; rw [id_comp]; rw [← NatTrans.naturality_assoc]; rw [← NatTrans.naturality_assoc]
  rfl

@[reassoc]
/--
lemma `mapBifunctorLeftUnitor_naturality` / 引理 `mapBifunctorLeftUnitor_naturality`

English:
lemma mapBifunctorLeftUnitor_naturality
  proof: by
  rw [← cancel_mono (mapBifunctorLeftUnitor F X e p hp Y').inv]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [mapBifunctorLeftUnitor_inv_naturality]; rw [Iso.hom_inv_id_assoc]

中文:
引理 mapBifunctorLeftUnitor_naturality
  证明: by
  rw [← cancel_mono (mapBifunctorLeftUnitor F X e p hp Y').inv]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [mapBifunctorLeftUnitor_inv_naturality]; rw [Iso.hom_inv_id_assoc]

Depends on / 依赖: Iso.hom_inv_id, Iso.hom_inv_id_assoc, cancel_mono, comp_id, hom_inv_id, hom_inv_id_assoc, mapBifunctorLeftUnitor, mapBifunctorLeftUnitor_inv_naturality
-/
lemma mapBifunctorLeftUnitor_naturality :
    mapBifunctorMapMap F p (𝟙 _) φ ≫ (mapBifunctorLeftUnitor F X e p hp Y').hom =
      (mapBifunctorLeftUnitor F X e p hp Y).hom ≫ φ := by
  rw [← cancel_mono (mapBifunctorLeftUnitor F X e p hp Y').inv]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [mapBifunctorLeftUnitor_inv_naturality]; rw [Iso.hom_inv_id_assoc]

end LeftUnitor

section RightUnitor

variable {C D I J : Type*} [Category* C] [Category* D]
  [Zero I] [DecidableEq I] [HasInitial C]
  (F : D ⥤ C ⥤ D) (Y : C) (e : F.flip.obj Y ≅ 𝟭 D)
  [forall (X : D), PreservesColimit (Functor.empty.{0} C) (F.obj X)]
  (p : J × I -> J)
  (hp : forall (j : J), p ⟨j, 0⟩ = j) (X X' : GradedObject J D) (φ : X ⟶ X')

/-- Given `F : D ⥤ C ⥤ D`, `Y : C`, `e : F.flip.obj X ≅ 𝟭 D` and `X : GradedObject J D`,
this is the isomorphism `((mapBifunctor F J I).obj X).obj ((single₀ I).obj Y) a ≅ Y a.2`
when `a : J × I` is such that `a.2 = 0`. -/
@[simps!]
/--
Definition of `mapBifunctorObjObjSingle₀Iso` / `mapBifunctorObjObjSingle₀Iso` 的定义

English:
definition mapBifunctorObjObjSingle₀Iso
  signature: (a : J × I) (ha : a.2 = 0)
  body: Functor.mapIso _ (singleObjApplyIsoOfEq _ Y _ ha) ≪≫ e.app (X a.1)

中文:
定义 mapBifunctorObjObjSingle₀Iso
  签名: (a : J × I) (ha : a.2 = 0)
  定义体: Functor.mapIso _ (singleObjApplyIsoOfEq _ Y _ ha) ≪≫ e.app (X a.1)

Depends on / 依赖: Functor, Functor.mapIso, e.app, mapIso, singleObjApplyIsoOfEq
-/
noncomputable def mapBifunctorObjObjSingle₀Iso (a : J × I) (ha : a.2 = 0) :
    ((mapBifunctor F J I).obj X).obj ((single₀ I).obj Y) a ≅ X a.1 :=
  Functor.mapIso _ (singleObjApplyIsoOfEq _ Y _ ha) ≪≫ e.app (X a.1)

/--
Definition of `mapBifunctorObjObjSingle₀IsInitial` / `mapBifunctorObjObjSingle₀IsInitial` 的定义

English:
definition mapBifunctorObjObjSingle₀IsInitial
  signature: (a : J × I) (ha : a.2 != 0)
  body: IsInitial.isInitialObj (F.obj (X a.1)) _ (isInitialSingleObjApply _ _ _ ha)

中文:
定义 mapBifunctorObjObjSingle₀IsInitial
  签名: (a : J × I) (ha : a.2 != 0)
  定义体: IsInitial.isInitialObj (F.obj (X a.1)) _ (isInitialSingleObjApply _ _ _ ha)

Depends on / 依赖: F.obj, IsInitial, IsInitial.isInitialObj, isInitialObj, isInitialSingleObjApply
-/
noncomputable def mapBifunctorObjObjSingle₀IsInitial (a : J × I) (ha : a.2 != 0) :
    IsInitial (((mapBifunctor F J I).obj X).obj ((single₀ I).obj Y) a) :=
  IsInitial.isInitialObj (F.obj (X a.1)) _ (isInitialSingleObjApply _ _ _ ha)

/--
Definition of `mapBifunctorRightUnitorCofan` / `mapBifunctorRightUnitorCofan` 的定义

English:
definition mapBifunctorRightUnitorCofan
  signature: (hp : forall (j : J), p ⟨j, 0⟩ = j) (X) (j : J)
  body: CofanMapObjFun.mk _ _ _ (X j) (fun a ha =>
    if ha : a.2 = 0 then
      (mapBifunctorObjObjSingle₀Iso F Y e X a ha).hom ≫ eqToHom (by aesop)
    else
      (mapBifunctorObjObjSingle₀IsInitial F Y X a ha).to _)

中文:
定义 mapBifunctorRightUnitorCofan
  签名: (hp : 对任意 (j : J), p ⟨j, 0⟩ = j) (X) (j : J)
  定义体: CofanMapObjFun.mk _ _ _ (X j) (fun a ha =>
    if ha : a.2 = 0 then
      (mapBifunctorObjObjSingle₀Iso F Y e X a ha).hom ≫ eqToHom (by aesop)
    else
      (mapBifunctorObjObjSingle₀IsInitial F Y X a ha).to _)

Depends on / 依赖: CofanMapObjFun, CofanMapObjFun.mk, eqToHom
-/
noncomputable def mapBifunctorRightUnitorCofan (hp : forall (j : J), p ⟨j, 0⟩ = j) (X) (j : J) :
    (((mapBifunctor F J I).obj X).obj ((single₀ I).obj Y)).CofanMapObjFun p j :=
  CofanMapObjFun.mk _ _ _ (X j) (fun a ha =>
    if ha : a.2 = 0 then
      (mapBifunctorObjObjSingle₀Iso F Y e X a ha).hom ≫ eqToHom (by aesop)
    else
      (mapBifunctorObjObjSingle₀IsInitial F Y X a ha).to _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp, reassoc]
/--
lemma `mapBifunctorRightUnitorCofan_inj` / 引理 `mapBifunctorRightUnitorCofan_inj`

English:
lemma mapBifunctorRightUnitorCofan_inj
  given: (j : J)
  proof: by
  simp [mapBifunctorRightUnitorCofan]

中文:
引理 mapBifunctorRightUnitorCofan_inj
  条件: (j : J)
  证明: by
  simp [mapBifunctorRightUnitorCofan]

Depends on / 依赖: mapBifunctorRightUnitorCofan
-/
lemma mapBifunctorRightUnitorCofan_inj (j : J) :
    (mapBifunctorRightUnitorCofan F Y e p hp X j).inj ⟨⟨j, 0⟩, hp j⟩ =
      (F.obj (X j)).map (singleObjApplyIso (0 : I) Y).hom ≫ e.hom.app (X j) := by
  simp [mapBifunctorRightUnitorCofan]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mapBifunctorRightUnitorCofanIsColimit` / `mapBifunctorRightUnitorCofanIsColimit` 的定义

English:
definition mapBifunctorRightUnitorCofanIsColimit
  signature: (j : J)
  body: Cofan.IsColimit.mk _
    (fun s => e.inv.app (X j) ≫
      (F.obj (X j)).map (singleObjApplyIso (0 : I) Y).inv ≫ s.inj ⟨⟨j, 0⟩, hp j⟩)
    (fun s => by
      rintro ⟨⟨j', i⟩, h⟩
      by_cases hi : i = 0
      · subst hi
        simp only [Set.mem_preimage, hp, Set.mem_singleton_iff] at h
        su

中文:
定义 mapBifunctorRightUnitorCofanIsColimit
  签名: (j : J)
  定义体: Cofan.IsColimit.mk _
    (fun s => e.inv.app (X j) ≫
      (F.obj (X j)).map (singleObjApplyIso (0 : I) Y).inv ≫ s.inj ⟨⟨j, 0⟩, hp j⟩)
    (fun s => by
      rintro ⟨⟨j', i⟩, h⟩
      by_cases hi : i = 0
      · subst hi
        simp only [Set.mem_preimage, hp, Set.mem_singleton_iff] at h
        su

Depends on / 依赖: Cofan.IsColimit.mk, F.obj, Functor, Functor.map_comp_assoc, Functor.map_id, IsColimit, IsInitial, IsInitial.hom_ext, Iso.hom_inv_id, Iso.hom_inv_id_app_assoc, Set.mem_preimage, Set.mem_singleton_iff, e.inv.app, hom_ext, hom_inv_id, hom_inv_id_app_assoc, id_comp, mapBifunctorRightUnitorCofan_inj, map_comp_assoc, map_id
-/
noncomputable def mapBifunctorRightUnitorCofanIsColimit (j : J) :
    IsColimit (mapBifunctorRightUnitorCofan F Y e p hp X j) :=
  Cofan.IsColimit.mk _
    (fun s => e.inv.app (X j) ≫
      (F.obj (X j)).map (singleObjApplyIso (0 : I) Y).inv ≫ s.inj ⟨⟨j, 0⟩, hp j⟩)
    (fun s => by
      rintro ⟨⟨j', i⟩, h⟩
      by_cases hi : i = 0
      · subst hi
        simp only [Set.mem_preimage, hp, Set.mem_singleton_iff] at h
        subst h
        rw [mapBifunctorRightUnitorCofan_inj]; rw [assoc]; rw [Iso.hom_inv_id_app_assoc]; rw [← Functor.map_comp_assoc]; rw [Iso.hom_inv_id]; rw [Functor.map_id]; rw [id_comp]
      · apply IsInitial.hom_ext
        exact mapBifunctorObjObjSingle₀IsInitial _ _ _ _ hi)
    (fun s m hm => by
      rw [← hm ⟨⟨j]; rw [0⟩]; rw [hp j⟩]; rw [mapBifunctorRightUnitorCofan_inj]; rw [assoc]; rw [← Functor.map_comp_assoc]; rw [Iso.inv_hom_id]; rw [Functor.map_id]; rw [id_comp]; rw [Iso.inv_hom_id_app_assoc])

include e hp in
/--
lemma `mapBifunctorRightUnitor_hasMap` / 引理 `mapBifunctorRightUnitor_hasMap`

English:
lemma mapBifunctorRightUnitor_hasMap
  proof: CofanMapObjFun.hasMap _ _ _ (mapBifunctorRightUnitorCofanIsColimit F Y e p hp X)

中文:
引理 mapBifunctorRightUnitor_hasMap
  证明: CofanMapObjFun.hasMap _ _ _ (mapBifunctorRightUnitorCofanIsColimit F Y e p hp X)

Depends on / 依赖: CofanMapObjFun, CofanMapObjFun.hasMap, hasMap, mapBifunctorRightUnitorCofanIsColimit
-/
lemma mapBifunctorRightUnitor_hasMap :
    HasMap (((mapBifunctor F J I).obj X).obj ((single₀ I).obj Y)) p :=
  CofanMapObjFun.hasMap _ _ _ (mapBifunctorRightUnitorCofanIsColimit F Y e p hp X)

variable [HasMap (((mapBifunctor F J I).obj X).obj ((single₀ I).obj Y)) p]
  [HasMap (((mapBifunctor F J I).obj X').obj ((single₀ I).obj Y)) p]

/--
Definition of `mapBifunctorRightUnitor` / `mapBifunctorRightUnitor` 的定义

English:
definition mapBifunctorRightUnitor
  signature: : mapBifunctorMapObj F p X ((single₀ I).obj Y) ≅ X
  body: isoMk _ _ (fun j => (CofanMapObjFun.iso
    (mapBifunctorRightUnitorCofanIsColimit F Y e p hp X j)).symm)

中文:
定义 mapBifunctorRightUnitor
  签名: : mapBifunctorMapObj F p X ((single₀ I).obj Y) ≅ X
  定义体: isoMk _ _ (fun j => (CofanMapObjFun.iso
    (mapBifunctorRightUnitorCofanIsColimit F Y e p hp X j)).symm)

Depends on / 依赖: CofanMapObjFun, CofanMapObjFun.iso, mapBifunctorRightUnitorCofanIsColimit
-/
noncomputable def mapBifunctorRightUnitor : mapBifunctorMapObj F p X ((single₀ I).obj Y) ≅ X :=
  isoMk _ _ (fun j => (CofanMapObjFun.iso
    (mapBifunctorRightUnitorCofanIsColimit F Y e p hp X j)).symm)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `ι_mapBifunctorRightUnitor_hom_apply` / 引理 `ι_mapBifunctorRightUnitor_hom_apply`

English:
lemma ι_mapBifunctorRightUnitor_hom_apply
  given: (j : J)
  proof: by
  dsimp [mapBifunctorRightUnitor]
  erw [CofanMapObjFun.ιMapObj_iso_inv]
  rw [mapBifunctorRightUnitorCofan_inj]

中文:
引理 ι_mapBifunctorRightUnitor_hom_apply
  条件: (j : J)
  证明: by
  dsimp [mapBifunctorRightUnitor]
  erw [CofanMapObjFun.ιMapObj_iso_inv]
  rw [mapBifunctorRightUnitorCofan_inj]

Depends on / 依赖: CofanMapObjFun, mapBifunctorRightUnitor, mapBifunctorRightUnitorCofan_inj
-/
lemma ι_mapBifunctorRightUnitor_hom_apply (j : J) :
    ιMapBifunctorMapObj F p X ((single₀ I).obj Y) j 0 j (hp j) ≫
        (mapBifunctorRightUnitor F Y e p hp X).hom j =
      (F.obj (X j)).map (singleObjApplyIso (0 : I) Y).hom ≫ e.hom.app (X j) := by
  dsimp [mapBifunctorRightUnitor]
  erw [CofanMapObjFun.ιMapObj_iso_inv]
  rw [mapBifunctorRightUnitorCofan_inj]

/--
lemma `mapBifunctorRightUnitor_inv_apply` / 引理 `mapBifunctorRightUnitor_inv_apply`

English:
lemma mapBifunctorRightUnitor_inv_apply
  given: (j : J)
  proof: rfl

中文:
引理 mapBifunctorRightUnitor_inv_apply
  条件: (j : J)
  证明: rfl
-/
lemma mapBifunctorRightUnitor_inv_apply (j : J) :
    (mapBifunctorRightUnitor F Y e p hp X).inv j =
      e.inv.app (X j) ≫ (F.obj (X j)).map (singleObjApplyIso (0 : I) Y).inv ≫
        ιMapBifunctorMapObj F p X ((single₀ I).obj Y) j 0 j (hp j) := rfl

variable {Y}

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `mapBifunctorRightUnitor_inv_naturality` / 引理 `mapBifunctorRightUnitor_inv_naturality`

English:
lemma mapBifunctorRightUnitor_inv_naturality
  proof: by
  ext j
  dsimp
  rw [mapBifunctorRightUnitor_inv_apply]; rw [mapBifunctorRightUnitor_inv_apply]; rw [assoc]; rw [assoc]; rw [ι_mapBifunctorMapMap]
  dsimp
  rw [Functor.map_id]; rw [id_comp]; rw [NatTrans.naturality_assoc]
  erw [← NatTrans.naturality_assoc e.inv]
  rfl

@[reassoc]

中文:
引理 mapBifunctorRightUnitor_inv_naturality
  证明: by
  ext j
  dsimp
  rw [mapBifunctorRightUnitor_inv_apply]; rw [mapBifunctorRightUnitor_inv_apply]; rw [assoc]; rw [assoc]; rw [ι_mapBifunctorMapMap]
  dsimp
  rw [Functor.map_id]; rw [id_comp]; rw [NatTrans.naturality_assoc]
  erw [← NatTrans.naturality_assoc e.inv]
  rfl

@[reassoc]

Depends on / 依赖: Functor, Functor.map_id, NatTrans, NatTrans.naturality_assoc, e.inv, id_comp, mapBifunctorRightUnitor_inv_apply, map_id, naturality_assoc
-/
lemma mapBifunctorRightUnitor_inv_naturality :
    φ ≫ (mapBifunctorRightUnitor F Y e p hp X').inv =
      (mapBifunctorRightUnitor F Y e p hp X).inv ≫ mapBifunctorMapMap F p φ (𝟙 _) := by
  ext j
  dsimp
  rw [mapBifunctorRightUnitor_inv_apply]; rw [mapBifunctorRightUnitor_inv_apply]; rw [assoc]; rw [assoc]; rw [ι_mapBifunctorMapMap]
  dsimp
  rw [Functor.map_id]; rw [id_comp]; rw [NatTrans.naturality_assoc]
  erw [← NatTrans.naturality_assoc e.inv]
  rfl

@[reassoc]
/--
lemma `mapBifunctorRightUnitor_naturality` / 引理 `mapBifunctorRightUnitor_naturality`

English:
lemma mapBifunctorRightUnitor_naturality
  proof: by
  rw [← cancel_mono (mapBifunctorRightUnitor F Y e p hp X').inv]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [mapBifunctorRightUnitor_inv_naturality]; rw [Iso.hom_inv_id_assoc]

中文:
引理 mapBifunctorRightUnitor_naturality
  证明: by
  rw [← cancel_mono (mapBifunctorRightUnitor F Y e p hp X').inv]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [mapBifunctorRightUnitor_inv_naturality]; rw [Iso.hom_inv_id_assoc]

Depends on / 依赖: Iso.hom_inv_id, Iso.hom_inv_id_assoc, cancel_mono, comp_id, hom_inv_id, hom_inv_id_assoc, mapBifunctorRightUnitor, mapBifunctorRightUnitor_inv_naturality
-/
lemma mapBifunctorRightUnitor_naturality :
    mapBifunctorMapMap F p φ (𝟙 _) ≫ (mapBifunctorRightUnitor F Y e p hp X').hom =
      (mapBifunctorRightUnitor F Y e p hp X).hom ≫ φ := by
  rw [← cancel_mono (mapBifunctorRightUnitor F Y e p hp X').inv]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [mapBifunctorRightUnitor_inv_naturality]; rw [Iso.hom_inv_id_assoc]

end RightUnitor

section

variable {I₁ I₂ I₃ J : Type*} [Zero I₂]

/--
Definition of `TriangleIndexData` / `TriangleIndexData` 的定义

English:
structure TriangleIndexData
  parameters: (r : I₁ × I₂ × I₃ -> J) (π : I₁ × I₃ -> J)
  axioms and operations (6):
    - p₁₂ : I₁ × I₂ -> I₁
    - hp₁₂((i : I₁ × I₂ × I₃)) : π ⟨p₁₂ ⟨i.1, i.2.1⟩, i.2.2⟩ = r i
    - p₂₃ : I₂ × I₃ -> I₃
    - hp₂₃((i : I₁ × I₂ × I₃)) : π ⟨i.1, p₂₃ i.2⟩ = r i
    - h₁((i₁ : I₁)) : p₁₂ (i₁, 0) = i₁
    - h₃((i₃ : I₃)) : p₂₃ (0, i₃) = i₃

中文:
结构 TriangleIndexData
  参数: (r : I₁ × I₂ × I₃ -> J) (π : I₁ × I₃ -> J)
  公理与运算 (6 个):
    - p₁₂ : I₁ × I₂ -> I₁
    - hp₁₂((i : I₁ × I₂ × I₃)) : π ⟨p₁₂ ⟨i.1, i.2.1⟩, i.2.2⟩ = r i
    - p₂₃ : I₂ × I₃ -> I₃
    - hp₂₃((i : I₁ × I₂ × I₃)) : π ⟨i.1, p₂₃ i.2⟩ = r i
    - h₁((i₁ : I₁)) : p₁₂ (i₁, 0) = i₁
    - h₃((i₃ : I₃)) : p₂₃ (0, i₃) = i₃
-/
structure TriangleIndexData (r : I₁ × I₂ × I₃ -> J) (π : I₁ × I₃ -> J) where
  /-- a map `I₁ × I₂ → I₁` -/
  p₁₂ : I₁ × I₂ -> I₁
  hp₁₂ (i : I₁ × I₂ × I₃) : π ⟨p₁₂ ⟨i.1, i.2.1⟩, i.2.2⟩ = r i
  /-- a map `I₂ × I₃ → I₃` -/
  p₂₃ : I₂ × I₃ -> I₃
  hp₂₃ (i : I₁ × I₂ × I₃) : π ⟨i.1, p₂₃ i.2⟩ = r i
  h₁ (i₁ : I₁) : p₁₂ (i₁, 0) = i₁
  h₃ (i₃ : I₃) : p₂₃ (0, i₃) = i₃

variable {r : I₁ × I₂ × I₃ -> J} {π : I₁ × I₃ -> J} (τ : TriangleIndexData r π)
include τ

namespace TriangleIndexData

attribute [simp] h₁ h₃

/--
lemma `r_zero` / 引理 `r_zero`

English:
lemma r_zero
  given: (i₁ : I₁) (i₃ : I₃)
  statement: r ⟨i₁, 0, i₃⟩ = π ⟨i₁, i₃⟩
  proof: by
  rw [← τ.hp₂₃]; rw [τ.h₃ i₃]

中文:
引理 r_zero
  条件: (i₁ : I₁) (i₃ : I₃)
  结论: r ⟨i₁, 0, i₃⟩ = π ⟨i₁, i₃⟩
  证明: by
  rw [← τ.hp₂₃]; rw [τ.h₃ i₃]
-/
lemma r_zero (i₁ : I₁) (i₃ : I₃) : r ⟨i₁, 0, i₃⟩ = π ⟨i₁, i₃⟩ := by
  rw [← τ.hp₂₃]; rw [τ.h₃ i₃]

/-- The `BifunctorComp₁₂IndexData r` attached to a `TriangleIndexData r π`. -/
@[reducible]
/--
Definition of `ρ₁₂` / `ρ₁₂` 的定义

English:
definition ρ₁₂
  signature: : BifunctorComp₁₂IndexData r where
  body: I₁
  p := τ.p₁₂
  q := π
  hpq := τ.hp₁₂

中文:
定义 ρ₁₂
  签名: : BifunctorComp₁₂IndexData r where
  定义体: I₁
  p := τ.p₁₂
  q := π
  hpq := τ.hp₁₂
-/
def ρ₁₂ : BifunctorComp₁₂IndexData r where
  I₁₂ := I₁
  p := τ.p₁₂
  q := π
  hpq := τ.hp₁₂

/-- The `BifunctorComp₂₃IndexData r` attached to a `TriangleIndexData r π`. -/
@[reducible]
/--
Definition of `ρ₂₃` / `ρ₂₃` 的定义

English:
definition ρ₂₃
  signature: : BifunctorComp₂₃IndexData r where
  body: I₃
  p := τ.p₂₃
  q := π
  hpq := τ.hp₂₃

中文:
定义 ρ₂₃
  签名: : BifunctorComp₂₃IndexData r where
  定义体: I₃
  p := τ.p₂₃
  q := π
  hpq := τ.hp₂₃
-/
def ρ₂₃ : BifunctorComp₂₃IndexData r where
  I₂₃ := I₃
  p := τ.p₂₃
  q := π
  hpq := τ.hp₂₃

end TriangleIndexData

end

section Triangle

variable {C₁ C₂ C₃ D I₁ I₂ I₃ J : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* D]
  [Zero I₂] [DecidableEq I₂] [HasInitial C₂]
  {F₁ : C₁ ⥤ C₂ ⥤ C₁} {F₂ : C₂ ⥤ C₃ ⥤ C₃} {G : C₁ ⥤ C₃ ⥤ D}
  (associator : bifunctorComp₁₂ F₁ G ≅ bifunctorComp₂₃ G F₂)
  (X₂ : C₂) (e₁ : F₁.flip.obj X₂ ≅ 𝟭 C₁) (e₂ : F₂.obj X₂ ≅ 𝟭 C₃)
  [forall (X₁ : C₁), PreservesColimit (Functor.empty.{0} C₂) (F₁.obj X₁)]
  [forall (X₃ : C₃), PreservesColimit (Functor.empty.{0} C₂) (F₂.flip.obj X₃)]
  {r : I₁ × I₂ × I₃ -> J} {π : I₁ × I₃ -> J}
  (τ : TriangleIndexData r π)
  (X₁ : GradedObject I₁ C₁) (X₃ : GradedObject I₃ C₃)
  [HasMap (((mapBifunctor F₁ I₁ I₂).obj X₁).obj ((single₀ I₂).obj X₂)) τ.p₁₂]
  [HasMap (((mapBifunctor G I₁ I₃).obj
    (mapBifunctorMapObj F₁ τ.p₁₂ X₁ ((single₀ I₂).obj X₂))).obj X₃) π]
  [HasMap (((mapBifunctor F₂ I₂ I₃).obj ((single₀ I₂).obj X₂)).obj X₃) τ.p₂₃]
  [HasMap (((mapBifunctor G I₁ I₃).obj X₁).obj
      (mapBifunctorMapObj F₂ τ.p₂₃ ((single₀ I₂).obj X₂) X₃)) π]
  [HasGoodTrifunctor₁₂Obj F₁ G τ.ρ₁₂ X₁ ((single₀ I₂).obj X₂) X₃]
  [HasGoodTrifunctor₂₃Obj G F₂ τ.ρ₂₃ X₁ ((single₀ I₂).obj X₂) X₃]
  [HasMap (((mapBifunctor G I₁ I₃).obj X₁).obj X₃) π]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mapBifunctor_triangle` / 引理 `mapBifunctor_triangle`

English:
lemma mapBifunctor_triangle
  proof: by
  rw [← cancel_epi ((mapBifunctorMapMap G π
    (mapBifunctorRightUnitor F₁ X₂ e₁ τ.p₁₂ τ.h₁ X₁).inv (𝟙 X₃)))]
  ext j i₁ i₃ hj
  simp only [categoryOfGradedObjects_comp, ι_mapBifunctorMapMap_assoc,
    mapBifunctorRightUnitor_inv_apply, Functor.id_obj, Functor.map_comp,
    NatTrans.comp_app, ca

中文:
引理 mapBifunctor_triangle
  证明: by
  rw [← cancel_epi ((mapBifunctorMapMap G π
    (mapBifunctorRightUnitor F₁ X₂ e₁ τ.p₁₂ τ.h₁ X₁).inv (𝟙 X₃)))]
  ext j i₁ i₃ hj
  simp only [categoryOfGradedObjects_comp, ι_mapBifunctorMapMap_assoc,
    mapBifunctorRightUnitor_inv_apply, Functor.id_obj, Functor.map_comp,
    NatTrans.comp_app, ca

Depends on / 依赖: Functor, Functor.id_obj, Functor.map_comp, Functor.map_id, NatTrans, NatTrans.comp_app, cancel_epi, categoryOfGradedObjects_comp, categoryOfGradedObjects_id, comp_app, id_comp, id_obj, mapBifunctorMapMap, mapBifunctorRightUnitor, mapBifunctorRightUnitor_inv_apply, map_comp, map_id, r_zero
-/
lemma mapBifunctor_triangle
    (triangle : forall (X₁ : C₁) (X₃ : C₃), ((associator.hom.app X₁).app X₂).app X₃ ≫
    (G.obj X₁).map (e₂.hom.app X₃) = (G.map (e₁.hom.app X₁)).app X₃) :
    (mapBifunctorAssociator associator τ.ρ₁₂ τ.ρ₂₃ X₁ ((single₀ I₂).obj X₂) X₃).hom ≫
    mapBifunctorMapMap G π (𝟙 X₁) (mapBifunctorLeftUnitor F₂ X₂ e₂ τ.p₂₃ τ.h₃ X₃).hom =
      mapBifunctorMapMap G π (mapBifunctorRightUnitor F₁ X₂ e₁ τ.p₁₂ τ.h₁ X₁).hom (𝟙 X₃) := by
  rw [← cancel_epi ((mapBifunctorMapMap G π
    (mapBifunctorRightUnitor F₁ X₂ e₁ τ.p₁₂ τ.h₁ X₁).inv (𝟙 X₃)))]
  ext j i₁ i₃ hj
  simp only [categoryOfGradedObjects_comp, ι_mapBifunctorMapMap_assoc,
    mapBifunctorRightUnitor_inv_apply, Functor.id_obj, Functor.map_comp,
    NatTrans.comp_app, categoryOfGradedObjects_id, Functor.map_id, id_comp, assoc,
    ι_mapBifunctorMapMap]
  congr 2
  rw [← ιMapBifunctor₁₂BifunctorMapObj_eq_assoc F₁ G τ.ρ₁₂ _ _ _ i₁ 0 i₃ j
    (by rw [τ.r_zero]; rw [hj]) i₁ (by simp), ι_mapBifunctorAssociator_hom_assoc,
    ιMapBifunctorBifunctor₂₃MapObj_eq_assoc G F₂ τ.ρ₂₃ _ _ _ i₁ 0 i₃ j
    (by rw [τ.r_zero, hj]) i₃ (by simp), ι_mapBifunctorMapMap]
  dsimp
  rw [Functor.map_id]; rw [NatTrans.id_app]; rw [id_comp]; rw [← Functor.map_comp_assoc]; rw [← NatTrans.comp_app_assoc]; rw [← Functor.map_comp]; rw [ι_mapBifunctorLeftUnitor_hom_apply F₂ X₂ e₂ τ.p₂₃ τ.h₃ X₃ i₃]; rw [ι_mapBifunctorRightUnitor_hom_apply F₁ X₂ e₁ τ.p₁₂ τ.h₁ X₁ i₁]
  dsimp
  simp only [Functor.map_comp, NatTrans.comp_app, ← triangle (X₁ i₁) (X₃ i₃), ← assoc]
  congr 2
  symm
  apply NatTrans.naturality_app (associator.hom.app (X₁ i₁))

end Triangle

end GradedObject

end CategoryTheory
