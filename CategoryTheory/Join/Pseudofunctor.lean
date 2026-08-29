/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Join.Basic
public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!
# Pseudofunctoriality of categorical joins

In this file, we promote the join construction to two pseudofunctors
`Join.pseudofunctorLeft` and `Join.pseudofunctorRight`, expressing its pseudofunctoriality in
each variable.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Join

open Bicategory CategoryTheory.Functor

-- The proof gets too slow if we put it in a single `pseudofunctor` constructor,
-- so we break down the component proofs for the pseudofunctors over several lemmas.

section
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]


variable (A) in
/--
Definition of `mapCompRight` / `mapCompRight` 的定义

English:
definition mapCompRight
  signature: (F : B ⥤ C) (G : C ⥤ D)
  body: mapIsoWhiskerRight (Functor.leftUnitor _).symm _ ≪≫ mapPairComp (𝟭 A) F (𝟭 A) G

中文:
定义 mapCompRight
  签名: (F : B ⥤ C) (G : C ⥤ D)
  定义体: mapIsoWhiskerRight (Functor.leftUnitor _).symm _ ≪≫ mapPairComp (𝟭 A) F (𝟭 A) G

Depends on / 依赖: Functor, Functor.leftUnitor, leftUnitor, mapIsoWhiskerRight, mapPairComp
-/
def mapCompRight (F : B ⥤ C) (G : C ⥤ D) :
    mapPair (𝟭 A) (F ⋙ G) ≅ mapPair (𝟭 A) F ⋙ mapPair (𝟭 A) G :=
  mapIsoWhiskerRight (Functor.leftUnitor _).symm _ ≪≫ mapPairComp (𝟭 A) F (𝟭 A) G

variable (D) in
/--
Definition of `mapCompLeft` / `mapCompLeft` 的定义

English:
definition mapCompLeft
  signature: (F : A ⥤ B) (G : B ⥤ C)
  body: mapIsoWhiskerLeft _ (Functor.leftUnitor _).symm ≪≫ mapPairComp F (𝟭 D) G (𝟭 D)

#adaptation_note

中文:
定义 mapCompLeft
  签名: (F : A ⥤ B) (G : B ⥤ C)
  定义体: mapIsoWhiskerLeft _ (Functor.leftUnitor _).symm ≪≫ mapPairComp F (𝟭 D) G (𝟭 D)

#adaptation_note

Depends on / 依赖: Functor, Functor.leftUnitor, leftUnitor, mapIsoWhiskerLeft, mapPairComp
-/
def mapCompLeft (F : A ⥤ B) (G : B ⥤ C) :
    mapPair (F ⋙ G) (𝟭 D) ≅ mapPair F (𝟭 D) ⋙ mapPair G (𝟭 D) :=
  mapIsoWhiskerLeft _ (Functor.leftUnitor _).symm ≪≫ mapPairComp F (𝟭 D) G (𝟭 D)

#adaptation_note
/--
`mapIsoWhiskerRight`'s `simps` theorems were formulated in simp normal form under
`respectTransparency.types true`. We use `respectTransparency.types false` here because these
lemmas fail to match without this annotation.
Suggested way forward: Decide what the correct signatures of the `mapIsoWhiskerRight` lemmas
are, then update this proof accordingly.
-/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable (A) in
@[reassoc]
/--
lemma `mapWhiskerLeft_whiskerLeft` / 引理 `mapWhiskerLeft_whiskerLeft`

English:
lemma mapWhiskerLeft_whiskerLeft
  given: (F : B ⥤ C) {G H : C ⥤ D} (η : G ⟶ H)
  proof: by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

#adaptation_note

中文:
引理 mapWhiskerLeft_whiskerLeft
  条件: (F : B ⥤ C) {G H : C ⥤ D} (η : G ⟶ H)
  证明: by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

#adaptation_note

Depends on / 依赖: mapCompRight, natTrans_ext
-/
lemma mapWhiskerLeft_whiskerLeft (F : B ⥤ C) {G H : C ⥤ D} (η : G ⟶ H) :
    mapWhiskerLeft _ (whiskerLeft F η) =
    (mapCompRight A F G).hom ≫ whiskerLeft (mapPair (𝟭 A) F) (mapWhiskerLeft _ η) ≫
      (mapCompRight A F H).inv := by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

#adaptation_note
/--
`mapIsoWhiskerLeft`'s `simps` theorems were formulated in simp normal form under
`respectTransparency.types true`. We use `respectTransparency.types false` here because these
lemmas fail to match without this annotation.
Suggested way forward: Decide what the correct signatures of the `mapIsoWhiskerLeft` lemmas
are, then update this proof accordingly.
-/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable (D) in
@[reassoc]
/--
lemma `mapWhiskerRight_whiskerLeft` / 引理 `mapWhiskerRight_whiskerLeft`

English:
lemma mapWhiskerRight_whiskerLeft
  given: (F : A ⥤ B) {G H : B ⥤ C} (η : G ⟶ H)
  proof: by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

中文:
引理 mapWhiskerRight_whiskerLeft
  条件: (F : A ⥤ B) {G H : B ⥤ C} (η : G ⟶ H)
  证明: by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

Depends on / 依赖: mapCompLeft, natTrans_ext
-/
lemma mapWhiskerRight_whiskerLeft (F : A ⥤ B) {G H : B ⥤ C} (η : G ⟶ H) :
    mapWhiskerRight (whiskerLeft F η) (𝟭 D) =
    (mapCompLeft D F G).hom ≫ whiskerLeft (mapPair F (𝟭 D)) (mapWhiskerRight η _) ≫
      (mapCompLeft D F H).inv := by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (A) in
@[reassoc]
/--
lemma `mapWhiskerLeft_whiskerRight` / 引理 `mapWhiskerLeft_whiskerRight`

English:
lemma mapWhiskerLeft_whiskerRight
  given: {F G : B ⥤ C} (η : F ⟶ G) (H : C ⥤ D)
  proof: by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

中文:
引理 mapWhiskerLeft_whiskerRight
  条件: {F G : B ⥤ C} (η : F ⟶ G) (H : C ⥤ D)
  证明: by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

Depends on / 依赖: mapCompRight, natTrans_ext
-/
lemma mapWhiskerLeft_whiskerRight {F G : B ⥤ C} (η : F ⟶ G) (H : C ⥤ D) :
    mapWhiskerLeft _ (whiskerRight η H) =
    (mapCompRight A F H).hom ≫ whiskerRight (mapWhiskerLeft _ η) (mapPair (𝟭 A) H) ≫
      (mapCompRight A G H).inv := by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (D) in
@[reassoc]
/--
lemma `mapWhiskerRight_whiskerRight` / 引理 `mapWhiskerRight_whiskerRight`

English:
lemma mapWhiskerRight_whiskerRight
  given: {F G : A ⥤ B} (η : F ⟶ G) (H : B ⥤ C)
  proof: by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

中文:
引理 mapWhiskerRight_whiskerRight
  条件: {F G : A ⥤ B} (η : F ⟶ G) (H : B ⥤ C)
  证明: by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

Depends on / 依赖: mapCompLeft, natTrans_ext
-/
lemma mapWhiskerRight_whiskerRight {F G : A ⥤ B} (η : F ⟶ G) (H : B ⥤ C) :
    mapWhiskerRight (whiskerRight η H) _ =
    (mapCompLeft D F H).hom ≫ whiskerRight (mapWhiskerRight η _) (mapPair H (𝟭 D)) ≫
      (mapCompLeft D G H).inv := by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

variable {E : Type*} [Category* E]

set_option backward.defeqAttrib.useBackward true in
variable (A) in
@[reassoc]
/--
lemma `mapWhiskerLeft_associator_hom` / 引理 `mapWhiskerLeft_associator_hom`

English:
lemma mapWhiskerLeft_associator_hom
  given: (F : B ⥤ C) (G : C ⥤ D) (H : D ⥤ E)
  proof: by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

中文:
引理 mapWhiskerLeft_associator_hom
  条件: (F : B ⥤ C) (G : C ⥤ D) (H : D ⥤ E)
  证明: by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

Depends on / 依赖: mapCompRight, natTrans_ext
-/
lemma mapWhiskerLeft_associator_hom (F : B ⥤ C) (G : C ⥤ D) (H : D ⥤ E) :
    mapWhiskerLeft _ (F.associator G H).hom =
      (mapCompRight A (F ⋙ G) H).hom ≫ whiskerRight (mapCompRight A F G).hom (mapPair (𝟭 A) H) ≫
      ((mapPair (𝟭 A) F).associator (mapPair (𝟭 A) G) (mapPair (𝟭 A) H)).hom ≫
      whiskerLeft (mapPair (𝟭 A) F) (mapCompRight A G H).inv ≫ (mapCompRight A F (G ⋙ H)).inv := by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

set_option backward.defeqAttrib.useBackward true in
variable (E) in
/--
lemma `mapWhiskerRight_associator_hom` / 引理 `mapWhiskerRight_associator_hom`

English:
lemma mapWhiskerRight_associator_hom
  given: (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D)
  proof: by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

中文:
引理 mapWhiskerRight_associator_hom
  条件: (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D)
  证明: by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

Depends on / 依赖: mapCompLeft, natTrans_ext
-/
lemma mapWhiskerRight_associator_hom (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) :
    mapWhiskerRight (F.associator G H).hom _ =
    (mapCompLeft E (F ⋙ G) H).hom ≫ whiskerRight (mapCompLeft E F G).hom (mapPair H (𝟭 E)) ≫
      ((mapPair F (𝟭 E)).associator (mapPair G (𝟭 E)) (mapPair H (𝟭 E))).hom ≫
      whiskerLeft (mapPair F (𝟭 E)) (mapCompLeft E G H).inv ≫ (mapCompLeft E F (G ⋙ H)).inv := by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

set_option backward.defeqAttrib.useBackward true in
variable (A) in
/--
lemma `mapWhiskerLeft_leftUnitor_hom` / 引理 `mapWhiskerLeft_leftUnitor_hom`

English:
lemma mapWhiskerLeft_leftUnitor_hom
  given: (F : B ⥤ C)
  proof: by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

中文:
引理 mapWhiskerLeft_leftUnitor_hom
  条件: (F : B ⥤ C)
  证明: by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

Depends on / 依赖: mapCompRight, natTrans_ext
-/
lemma mapWhiskerLeft_leftUnitor_hom (F : B ⥤ C) :
    mapWhiskerLeft _ F.leftUnitor.hom =
    (mapCompRight A (𝟭 _) F).hom ≫ whiskerRight mapPairId.hom (mapPair _ F) ≫
      (mapPair _ F).leftUnitor.hom := by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

set_option backward.defeqAttrib.useBackward true in
variable (C) in
/--
lemma `mapWhiskerRight_leftUnitor_hom` / 引理 `mapWhiskerRight_leftUnitor_hom`

English:
lemma mapWhiskerRight_leftUnitor_hom
  given: (F : A ⥤ B)
  proof: by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

中文:
引理 mapWhiskerRight_leftUnitor_hom
  条件: (F : A ⥤ B)
  证明: by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

Depends on / 依赖: mapCompLeft, natTrans_ext
-/
lemma mapWhiskerRight_leftUnitor_hom (F : A ⥤ B) :
    mapWhiskerRight F.leftUnitor.hom (𝟭 C) =
    (mapCompLeft C (𝟭 A) F).hom ≫ whiskerRight mapPairId.hom (mapPair F (𝟭 C)) ≫
      (mapPair F (𝟭 C)).leftUnitor.hom := by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

set_option backward.defeqAttrib.useBackward true in
variable (A) in
/--
lemma `mapWhiskerLeft_rightUnitor_hom` / 引理 `mapWhiskerLeft_rightUnitor_hom`

English:
lemma mapWhiskerLeft_rightUnitor_hom
  given: (F : B ⥤ C)
  proof: by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

中文:
引理 mapWhiskerLeft_rightUnitor_hom
  条件: (F : B ⥤ C)
  证明: by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

Depends on / 依赖: mapCompRight, natTrans_ext
-/
lemma mapWhiskerLeft_rightUnitor_hom (F : B ⥤ C) :
    mapWhiskerLeft _ F.rightUnitor.hom =
    (mapCompRight A F (𝟭 C)).hom ≫ whiskerLeft (mapPair _ F) mapPairId.hom ≫
      (mapPair (𝟭 A) _).rightUnitor.hom := by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

set_option backward.defeqAttrib.useBackward true in
variable (C) in
/--
lemma `mapWhiskerRight_rightUnitor_hom` / 引理 `mapWhiskerRight_rightUnitor_hom`

English:
lemma mapWhiskerRight_rightUnitor_hom
  given: (F : A ⥤ B)
  proof: by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

中文:
引理 mapWhiskerRight_rightUnitor_hom
  条件: (F : A ⥤ B)
  证明: by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

Depends on / 依赖: mapCompLeft, natTrans_ext
-/
lemma mapWhiskerRight_rightUnitor_hom (F : A ⥤ B) :
    mapWhiskerRight F.rightUnitor.hom _ =
    (mapCompLeft C F (𝟭 B)).hom ≫ whiskerLeft (mapPair F _) mapPairId.hom ≫
      (mapPair _ (𝟭 C)).rightUnitor.hom := by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

end

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The pseudofunctor sending `D` to `C ⋆ D`. -/
@[simps!]
/--
Definition of `pseudofunctorRight` / `pseudofunctorRight` 的定义

English:
definition pseudofunctorRight
  signature: (C : Type u₁) [Category.{v₁} C]
  body: Cat.of (C ⋆ D)
  map F := (mapPair (𝟭 C) F.toFunctor).toCatHom
  map₂ f := (mapWhiskerLeft (𝟭 C) f.toNatTrans).toCatHom₂
  mapId D := Cat.Hom.isoMk mapPairId
mapComp F G := Cat.Hom.isoMk mapCompRight C F.toFunctor G.toFunctor
  map₂_whisker_left := by intros; exact congr($(mapWhiskerLeft_whiskerLeft C _ _).toCatHom₂)
  map₂_whisker_right := by intros; exact congr($(mapWhiskerLeft_whiskerRight C _ _).toCatHom₂)
  map₂_associator := by intros; exact congr($(mapWhiskerLeft_associator_hom C _ _ _).toCatHom₂)
  map₂_left_unitor := by intros; exact congr($(mapWhiskerLeft_leftUnitor_hom C _).toCatHom₂)
  map₂_right_unitor := by intros; exact congr($(mapWhiskerLeft_rightUnitor_hom C _).toCatHom₂)

#adaptation_note

中文:
定义 pseudofunctorRight
  签名: (C : 类型u₁) [范畴.{v₁} C]
  定义体: Cat.of (C ⋆ D)
  map F := (mapPair (𝟭 C) F.toFunctor).toCatHom
  map₂ f := (mapWhiskerLeft (𝟭 C) f.toNatTrans).toCatHom₂
  mapId D := Cat.Hom.isoMk mapPairId
mapComp F G := Cat.Hom.isoMk mapCompRight C F.toFunctor G.toFunctor
  map₂_whisker_left := by intros; exact congr($(mapWhiskerLeft_whiskerLeft C _ _).toCatHom₂)
  map₂_whisker_right := by intros; exact congr($(mapWhiskerLeft_whiskerRight C _ _).toCatHom₂)
  map₂_associator := by intros; exact congr($(mapWhiskerLeft_associator_hom C _ _ _).toCatHom₂)
  map₂_left_unitor := by intros; exact congr($(mapWhiskerLeft_leftUnitor_hom C _).toCatHom₂)
  map₂_right_unitor := by intros; exact congr($(mapWhiskerLeft_rightUnitor_hom C _).toCatHom₂)

#adaptation_note

Depends on / 依赖: Cat.of
-/
def pseudofunctorRight (C : Type u₁) [Category.{v₁} C] :
    Pseudofunctor Cat.{v₂, u₂} Cat.{max v₁ v₂, max u₁ u₂} where
  obj D := Cat.of (C ⋆ D)
  map F := (mapPair (𝟭 C) F.toFunctor).toCatHom
  map₂ f := (mapWhiskerLeft (𝟭 C) f.toNatTrans).toCatHom₂
  mapId D := Cat.Hom.isoMk mapPairId
mapComp F G := Cat.Hom.isoMk mapCompRight C F.toFunctor G.toFunctor
  map₂_whisker_left := by intros; exact congr($(mapWhiskerLeft_whiskerLeft C _ _).toCatHom₂)
  map₂_whisker_right := by intros; exact congr($(mapWhiskerLeft_whiskerRight C _ _).toCatHom₂)
  map₂_associator := by intros; exact congr($(mapWhiskerLeft_associator_hom C _ _ _).toCatHom₂)
  map₂_left_unitor := by intros; exact congr($(mapWhiskerLeft_leftUnitor_hom C _).toCatHom₂)
  map₂_right_unitor := by intros; exact congr($(mapWhiskerLeft_rightUnitor_hom C _).toCatHom₂)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The pseudofunctor sending `C` to `C ⋆ D`. -/
@[simps!]
/--
Definition of `pseudofunctorLeft` / `pseudofunctorLeft` 的定义

English:
definition pseudofunctorLeft
  signature: (D : Type u₂) [Category.{v₂} D]
  body: Cat.of (C ⋆ D)
  map F := (mapPair F.toFunctor (𝟭 D)).toCatHom
  map₂ := (mapWhiskerRight ·.toNatTrans _ |>.toCatHom₂)
mapId D := Cat.Hom.isoMk mapPairId
mapComp _ _ := Cat.Hom.isoMk mapCompLeft D _ _
  map₂_whisker_left := by intros; exact congr($(mapWhiskerRight_whiskerLeft D _ _).toCatHom₂)
  map₂_whisker_right := by intros; exact congr($(mapWhiskerRight_whiskerRight D _ _).toCatHom₂)
  map₂_associator := by intros; exact congr($(mapWhiskerRight_associator_hom D _ _ _).toCatHom₂)
  map₂_left_unitor := by intros; exact congr($(mapWhiskerRight_leftUnitor_hom D _).toCatHom₂)
  map₂_right_unitor := by intros; exact congr($(mapWhiskerRight_rightUnitor_hom D _).toCatHom₂)

中文:
定义 pseudofunctorLeft
  签名: (D : 类型u₂) [范畴.{v₂} D]
  定义体: Cat.of (C ⋆ D)
  map F := (mapPair F.toFunctor (𝟭 D)).toCatHom
  map₂ := (mapWhiskerRight ·.toNatTrans _ |>.toCatHom₂)
mapId D := Cat.Hom.isoMk mapPairId
mapComp _ _ := Cat.Hom.isoMk mapCompLeft D _ _
  map₂_whisker_left := by intros; exact congr($(mapWhiskerRight_whiskerLeft D _ _).toCatHom₂)
  map₂_whisker_right := by intros; exact congr($(mapWhiskerRight_whiskerRight D _ _).toCatHom₂)
  map₂_associator := by intros; exact congr($(mapWhiskerRight_associator_hom D _ _ _).toCatHom₂)
  map₂_left_unitor := by intros; exact congr($(mapWhiskerRight_leftUnitor_hom D _).toCatHom₂)
  map₂_right_unitor := by intros; exact congr($(mapWhiskerRight_rightUnitor_hom D _).toCatHom₂)

Depends on / 依赖: Cat.of
-/
def pseudofunctorLeft (D : Type u₂) [Category.{v₂} D] :
    Pseudofunctor Cat.{v₁, u₁} Cat.{max v₁ v₂, max u₁ u₂} where
  obj C := Cat.of (C ⋆ D)
  map F := (mapPair F.toFunctor (𝟭 D)).toCatHom
  map₂ := (mapWhiskerRight ·.toNatTrans _ |>.toCatHom₂)
mapId D := Cat.Hom.isoMk mapPairId
mapComp _ _ := Cat.Hom.isoMk mapCompLeft D _ _
  map₂_whisker_left := by intros; exact congr($(mapWhiskerRight_whiskerLeft D _ _).toCatHom₂)
  map₂_whisker_right := by intros; exact congr($(mapWhiskerRight_whiskerRight D _ _).toCatHom₂)
  map₂_associator := by intros; exact congr($(mapWhiskerRight_associator_hom D _ _ _).toCatHom₂)
  map₂_left_unitor := by intros; exact congr($(mapWhiskerRight_leftUnitor_hom D _).toCatHom₂)
  map₂_right_unitor := by intros; exact congr($(mapWhiskerRight_rightUnitor_hom D _).toCatHom₂)

end CategoryTheory.Join
