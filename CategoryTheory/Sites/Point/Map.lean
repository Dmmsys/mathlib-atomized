/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered

/-!
# The image of a point by a cocontinuous functor

Let `F : C ⥤ D` be a cocontinuous functor between sites `(C, J)` and `(D, K)`.
Let `Φ` be a point of `(C, J)`. In this file, we define a point `Φ.map F K`
of `(D, K)` and show that there are natural isomorphisms
`(Φ.map F K).presheafFiber ≅ (Functor.whiskeringLeft _ _ A).obj F.op ⋙ Φ.presheafFiber`
and `(Φ.map F K).sheafFiber ≅ F.sheafPushforwardContinuous A J K ⋙ Φ.sheafFiber`
(the latter is defined only if `F` is also continuous).

-/

@[expose] public section

universe w v'' v' v u'' u' u

namespace CategoryTheory

open Limits Opposite

namespace GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} (Φ : Point.{w} J) (F : C ⥤ D)
  (K : GrothendieckTopology D) [F.IsCocontinuous J K]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `map_aux` / 引理 `map_aux`

English:
lemma map_aux
  given: ⦃X
  statement: D⦄ (R : Sieve X) (hR : R in K X)
  proof: by
  obtain ⟨U, u⟩ := u
  dsimp at f ⊢
  obtain ⟨V, g, hg, v, rfl⟩ :=
    Φ.jointly_surjective _ (F.cover_lift J K (K.pullback_stable f hR)) u
  exact ⟨_, F.map g ≫ f, hg, Φ.fiber.elementsMk _ v, ⟨g, rfl⟩, 𝟙 _, by simp⟩

中文:
引理 map_aux
  条件: ⦃X
  结论: D⦄ (R : 筛 X) (hR : R in K X)
  证明: by
  obtain ⟨U, u⟩ := u
  dsimp at f ⊢
  obtain ⟨V, g, hg, v, rfl⟩ :=
    Φ.jointly_surjective _ (F.cover_lift J K (K.pullback_stable f hR)) u
  exact ⟨_, F.map g ≫ f, hg, Φ.fiber.elementsMk _ v, ⟨g, rfl⟩, 𝟙 _, by simp⟩

Depends on / 依赖: F.cover_lift, F.map, K.pullback_stable, cover_lift, elementsMk, fiber.elementsMk, jointly_surjective, pullback_stable
-/
lemma map_aux ⦃X : D⦄ (R : Sieve X) (hR : R in K X)
    ⦃u : Φ.fiber.Elements⦄ (f : (CategoryOfElements.π Φ.fiber ⋙ F).obj u ⟶ X) :
    exists (Y : D) (g : Y ⟶ X) (_ : R.arrows g) (v : Φ.fiber.Elements)
      (q : v ⟶ u) (a : F.obj v.fst ⟶ Y), a ≫ g = F.map q.1 ≫ f := by
  obtain ⟨U, u⟩ := u
  dsimp at f ⊢
  obtain ⟨V, g, hg, v, rfl⟩ :=
    Φ.jointly_surjective _ (F.cover_lift J K (K.pullback_stable f hR)) u
  exact ⟨_, F.map g ≫ f, hg, Φ.fiber.elementsMk _ v, ⟨g, rfl⟩, 𝟙 _, by simp⟩

variable [LocallySmall.{w} D]

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : Point.{w} K
  body: Point.ofIsCofiltered.{w} (CategoryOfElements.π Φ.fiber ⋙ F) (Φ.map_aux F K)

中文:
定义 map
  签名: : Point.{w} K
  定义体: Point.ofIsCofiltered.{w} (CategoryOfElements.π Φ.fiber ⋙ F) (Φ.map_aux F K)

Depends on / 依赖: CategoryOfElements, Point.ofIsCofiltered, map_aux, ofIsCofiltered
-/
noncomputable def map : Point.{w} K :=
  Point.ofIsCofiltered.{w} (CategoryOfElements.π Φ.fiber ⋙ F) (Φ.map_aux F K)

variable {A : Type u''} [Category.{v''} A] [HasColimitsOfSize.{w, w} A]

/--
Definition of `toPresheafFiberMap` / `toPresheafFiberMap` 的定义

English:
definition toPresheafFiberMap
  signature: (P : Dᵒᵖ ⥤ A) (X : C) (x : Φ.fiber.obj X)
  body: toPresheafFiberOfIsCofiltered _ (Φ.map_aux F K) (Φ.fiber.elementsMk X x) P

@[reassoc (attr := simp)]

中文:
定义 toPresheafFiberMap
  签名: (P : Dᵒᵖ ⥤ A) (X : C) (x : Φ.fiber.obj X)
  定义体: toPresheafFiberOfIsCofiltered _ (Φ.map_aux F K) (Φ.fiber.elementsMk X x) P

@[reassoc (attr := simp)]

Depends on / 依赖: elementsMk, fiber.elementsMk, map_aux, toPresheafFiberOfIsCofiltered
-/
noncomputable def toPresheafFiberMap (P : Dᵒᵖ ⥤ A) (X : C) (x : Φ.fiber.obj X) :
    P.obj (op (F.obj X)) ⟶ (Φ.map F K).presheafFiber.obj P :=
  toPresheafFiberOfIsCofiltered _ (Φ.map_aux F K) (Φ.fiber.elementsMk X x) P

@[reassoc (attr := simp)]
/--
lemma `toPresheafFiberMap_w` / 引理 `toPresheafFiberMap_w`

English:
lemma toPresheafFiberMap_w
  statement: {X Y : C} (f : X ⟶ Y)
  proof: toPresheafFiberOfIsCofiltered_w _ (Φ.map_aux F K)
    (V := ⟨X, x⟩) (U := ⟨Y, Φ.fiber.map f x⟩) ⟨f, rfl⟩ P

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
引理 toPresheafFiberMap_w
  结论: {X Y : C} (f : X ⟶ Y)
  证明: toPresheafFiberOfIsCofiltered_w _ (Φ.map_aux F K)
    (V := ⟨X, x⟩) (U := ⟨Y, Φ.fiber.map f x⟩) ⟨f, rfl⟩ P

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: fiber.map, map_aux, toPresheafFiberOfIsCofiltered_w
-/
lemma toPresheafFiberMap_w {X Y : C} (f : X ⟶ Y)
    (x : Φ.fiber.obj X) (P : Dᵒᵖ ⥤ A) :
    P.map (F.map f).op ≫ Φ.toPresheafFiberMap F K P X x =
      Φ.toPresheafFiberMap F K P Y (Φ.fiber.map f x) :=
  toPresheafFiberOfIsCofiltered_w _ (Φ.map_aux F K)
    (V := ⟨X, x⟩) (U := ⟨Y, Φ.fiber.map f x⟩) ⟨f, rfl⟩ P

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `toPresheafFiberMap_naturality` / 引理 `toPresheafFiberMap_naturality`

English:
lemma toPresheafFiberMap_naturality
  given: {P Q : Dᵒᵖ ⥤ A} (g : P ⟶ Q) (X : C) (x : Φ.fiber.obj X)
  proof: toPresheafFiberOfIsCofiltered_naturality _ _ _ _

中文:
引理 toPresheafFiberMap_naturality
  条件: {P Q : Dᵒᵖ ⥤ A} (g : P ⟶ Q) (X : C) (x : Φ.fiber.obj X)
  证明: toPresheafFiberOfIsCofiltered_naturality _ _ _ _

Depends on / 依赖: toPresheafFiberOfIsCofiltered_naturality
-/
lemma toPresheafFiberMap_naturality {P Q : Dᵒᵖ ⥤ A} (g : P ⟶ Q) (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiberMap F K P X x ≫ (Φ.map F K).presheafFiber.map g =
      g.app _ ≫ Φ.toPresheafFiberMap F K Q X x :=
  toPresheafFiberOfIsCofiltered_naturality _ _ _ _

set_option backward.defeqAttrib.useBackward true in
/-- Given a cocontinuous functor `F : C ⥤ D` between sites `(C, J)` and `(D, K)`,
`P` a presheaf on `D`, this is the (colimit) cocone which expresses
`(Φ.map F K).presheafFiber.obj P` as a colimit of `P.obj (op (F.obj X))`
for `X : C`, `x : Φ.fiber.obj X`. -/
@[simps]
/--
Definition of `presheafFiberMapCocone` / `presheafFiberMapCocone` 的定义

English:
definition presheafFiberMapCocone
  signature: (P : Dᵒᵖ ⥤ A)
  body: (Φ.map F K).presheafFiber.obj P
  ι.app x := Φ.toPresheafFiberMap F K P x.unop.1 x.unop.2

中文:
定义 presheafFiberMapCocone
  签名: (P : Dᵒᵖ ⥤ A)
  定义体: (Φ.map F K).presheafFiber.obj P
  ι.app x := Φ.toPresheafFiberMap F K P x.unop.1 x.unop.2

Depends on / 依赖: presheafFiber, presheafFiber.obj
-/
noncomputable def presheafFiberMapCocone (P : Dᵒᵖ ⥤ A) :
    Cocone ((CategoryOfElements.π Φ.fiber).op ⋙ F.op ⋙ P) where
  pt := (Φ.map F K).presheafFiber.obj P
  ι.app x := Φ.toPresheafFiberMap F K P x.unop.1 x.unop.2

/--
Definition of `isColimitPresheafFiberMapCocone` / `isColimitPresheafFiberMapCocone` 的定义

English:
definition isColimitPresheafFiberMapCocone
  signature: (P : Dᵒᵖ ⥤ A)
  body: isColimitPresheafFiberOfIsCofilteredCocone.{w} _ (Φ.map_aux F K) P

@[ext]

中文:
定义 isColimitPresheafFiberMapCocone
  签名: (P : Dᵒᵖ ⥤ A)
  定义体: isColimitPresheafFiberOfIsCofilteredCocone.{w} _ (Φ.map_aux F K) P

@[ext]

Depends on / 依赖: isColimitPresheafFiberOfIsCofilteredCocone, map_aux
-/
noncomputable def isColimitPresheafFiberMapCocone (P : Dᵒᵖ ⥤ A) :
    IsColimit (Φ.presheafFiberMapCocone F K P) :=
  isColimitPresheafFiberOfIsCofilteredCocone.{w} _ (Φ.map_aux F K) P

@[ext]
/--
lemma `presheafFiberMap_hom_ext` / 引理 `presheafFiberMap_hom_ext`

English:
lemma presheafFiberMap_hom_ext
  statement: {P : Dᵒᵖ ⥤ A} {T : A}
  proof: (Φ.isColimitPresheafFiberMapCocone F K P).hom_ext (fun _ => h _ _)

中文:
引理 presheafFiberMap_hom_ext
  结论: {P : Dᵒᵖ ⥤ A} {T : A}
  证明: (Φ.isColimitPresheafFiberMapCocone F K P).hom_ext (fun _ => h _ _)

Depends on / 依赖: hom_ext, isColimitPresheafFiberMapCocone
-/
lemma presheafFiberMap_hom_ext {P : Dᵒᵖ ⥤ A} {T : A}
    {f g : (Φ.map F K).presheafFiber.obj P ⟶ T}
    (h : forall (X : C) (x : Φ.fiber.obj X),
      Φ.toPresheafFiberMap F K P X x ≫ f = Φ.toPresheafFiberMap F K P X x ≫ g) :
    f = g :=
  (Φ.isColimitPresheafFiberMapCocone F K P).hom_ext (fun _ => h _ _)

/--
Definition of `presheafFiberMapObjIso` / `presheafFiberMapObjIso` 的定义

English:
definition presheafFiberMapObjIso
  signature: (P : Dᵒᵖ ⥤ A)
  body: IsColimit.coconePointUniqueUpToIso (Φ.isColimitPresheafFiberMapCocone F K P)
    (Φ.isColimitPresheafFiberCocone (F.op ⋙ P))

@[reassoc (attr := simp)]

中文:
定义 presheafFiberMapObjIso
  签名: (P : Dᵒᵖ ⥤ A)
  定义体: IsColimit.coconePointUniqueUpToIso (Φ.isColimitPresheafFiberMapCocone F K P)
    (Φ.isColimitPresheafFiberCocone (F.op ⋙ P))

@[reassoc (attr := simp)]

Depends on / 依赖: F.op, IsColimit, IsColimit.coconePointUniqueUpToIso, coconePointUniqueUpToIso, isColimitPresheafFiberCocone, isColimitPresheafFiberMapCocone
-/
noncomputable def presheafFiberMapObjIso (P : Dᵒᵖ ⥤ A) :
    (Φ.map F K).presheafFiber.obj P ≅ Φ.presheafFiber.obj (F.op ⋙ P) :=
  IsColimit.coconePointUniqueUpToIso (Φ.isColimitPresheafFiberMapCocone F K P)
    (Φ.isColimitPresheafFiberCocone (F.op ⋙ P))

@[reassoc (attr := simp)]
/--
lemma `toPresheafFiberMap_presheafFiberMapObjIso_hom` / 引理 `toPresheafFiberMap_presheafFiberMapObjIso_hom`

English:
lemma toPresheafFiberMap_presheafFiberMapObjIso_hom
  given: (P : Dᵒᵖ ⥤ A) (X : C) (x : Φ.fiber.obj X)
  proof: IsColimit.comp_coconePointUniqueUpToIso_hom
    (Φ.isColimitPresheafFiberMapCocone F K P) _ ⟨X, x⟩

中文:
引理 toPresheafFiberMap_presheafFiberMapObjIso_hom
  条件: (P : Dᵒᵖ ⥤ A) (X : C) (x : Φ.fiber.obj X)
  证明: IsColimit.comp_coconePointUniqueUpToIso_hom
    (Φ.isColimitPresheafFiberMapCocone F K P) _ ⟨X, x⟩

Depends on / 依赖: IsColimit, IsColimit.comp_coconePointUniqueUpToIso_hom, comp_coconePointUniqueUpToIso_hom, isColimitPresheafFiberMapCocone
-/
lemma toPresheafFiberMap_presheafFiberMapObjIso_hom (P : Dᵒᵖ ⥤ A) (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiberMap F K P X x ≫ (Φ.presheafFiberMapObjIso F K P).hom =
      Φ.toPresheafFiber X x (F.op ⋙ P) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (Φ.isColimitPresheafFiberMapCocone F K P) _ ⟨X, x⟩

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `toPresheafFiber_presheafFiberMapObjIso_inv` / 引理 `toPresheafFiber_presheafFiberMapObjIso_inv`

English:
lemma toPresheafFiber_presheafFiberMapObjIso_inv
  given: (P : Dᵒᵖ ⥤ A) (X : C) (x : Φ.fiber.obj X)
  proof: by
  simpa [-toPresheafFiberMap_presheafFiberMapObjIso_hom] using
    (Φ.toPresheafFiberMap_presheafFiberMapObjIso_hom F K ..).symm =≫
      (Φ.presheafFiberMapObjIso F K P).inv

中文:
引理 toPresheafFiber_presheafFiberMapObjIso_inv
  条件: (P : Dᵒᵖ ⥤ A) (X : C) (x : Φ.fiber.obj X)
  证明: by
  simpa [-toPresheafFiberMap_presheafFiberMapObjIso_hom] using
    (Φ.toPresheafFiberMap_presheafFiberMapObjIso_hom F K ..).symm =≫
      (Φ.presheafFiberMapObjIso F K P).inv

Depends on / 依赖: presheafFiberMapObjIso, toPresheafFiberMap_presheafFiberMapObjIso_hom
-/
lemma toPresheafFiber_presheafFiberMapObjIso_inv (P : Dᵒᵖ ⥤ A) (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x (F.op ⋙ P) ≫ (Φ.presheafFiberMapObjIso F K P).inv =
      Φ.toPresheafFiberMap F K P X x := by
  simpa [-toPresheafFiberMap_presheafFiberMapObjIso_hom] using
    (Φ.toPresheafFiberMap_presheafFiberMapObjIso_hom F K ..).symm =≫
      (Φ.presheafFiberMapObjIso F K P).inv

set_option backward.isDefEq.respectTransparency false in
variable (A) in
/-- Relation between the fiber functors on presheaves for the points `Φ.map F K`
and `Φ` when `F : C ⥤ D` is a cocontinuous functor between sites `(C, J)` and `(D, K)`. -/
@[simps!]
/--
Definition of `presheafFiberMapIso` / `presheafFiberMapIso` 的定义

English:
definition presheafFiberMapIso
  signature: :
  body: NatIso.ofComponents (Φ.presheafFiberMapObjIso F K)

中文:
定义 presheafFiberMapIso
  签名: :
  定义体: NatIso.ofComponents (Φ.presheafFiberMapObjIso F K)

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents, presheafFiberMapObjIso
-/
noncomputable def presheafFiberMapIso :
    (Φ.map F K).presheafFiber ≅
      (Functor.whiskeringLeft _ _ A).obj F.op ⋙ Φ.presheafFiber :=
  NatIso.ofComponents (Φ.presheafFiberMapObjIso F K)

variable (A) in
/--
Definition of `sheafFiberMapIso` / `sheafFiberMapIso` 的定义

English:
definition sheafFiberMapIso
  signature: [Functor.IsContinuous F J K]
  body: Functor.isoWhiskerLeft (sheafToPresheaf K A) (Φ.presheafFiberMapIso F K A) ≪≫
    (Functor.associator ..).symm ≪≫
    Functor.isoWhiskerRight (F.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm _ ≪≫
    Functor.associator ..

中文:
定义 sheafFiberMapIso
  签名: [函子.是连续 F J K]
  定义体: Functor.isoWhiskerLeft (sheafToPresheaf K A) (Φ.presheafFiberMapIso F K A) ≪≫
    (Functor.associator ..).symm ≪≫
    Functor.isoWhiskerRight (F.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm _ ≪≫
    Functor.associator ..

Depends on / 依赖: F.sheafPushforwardContinuousCompSheafToPresheafIso, Functor, Functor.associator, Functor.isoWhiskerLeft, Functor.isoWhiskerRight, associator, isoWhiskerLeft, isoWhiskerRight, presheafFiberMapIso, sheafPushforwardContinuousCompSheafToPresheafIso, sheafToPresheaf
-/
noncomputable def sheafFiberMapIso [Functor.IsContinuous F J K] :
    (Φ.map F K).sheafFiber ≅
      F.sheafPushforwardContinuous A J K ⋙ Φ.sheafFiber :=
  Functor.isoWhiskerLeft (sheafToPresheaf K A) (Φ.presheafFiberMapIso F K A) ≪≫
    (Functor.associator ..).symm ≪≫
    Functor.isoWhiskerRight (F.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm _ ≪≫
    Functor.associator ..

end GrothendieckTopology.Point

end CategoryTheory
