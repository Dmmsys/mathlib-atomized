/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Points of a site

Let `C` be a category equipped with a Grothendieck topology `J`. In this file,
we define the notion of point of the site `(C, J)`, as a
structure `GrothendieckTopology.Point`. Such a `Φ : J.Point` consists
in a functor `Φ.fiber : C ⥤ Type w` such that the category `Φ.fiber.Elements`
is cofiltered (and initially small) and such that if `x : Φ.fiber.obj X`
and `R` is a covering sieve of `X`, then `x` belongs to the image
of some `y : Φ.fiber.obj Y` by a morphism `f : Y ⟶ X` which belongs to `R`.
(This definition is essentially the definition of a fiber functor on a site
from SGA 4 IV 6.3.)

The fact that `Φ.fiber.Elementsᵒᵖ` is filtered allows to define
`Φ.presheafFiber : (Cᵒᵖ ⥤ A) ⥤ A` by taking the filtering colimit
of the evaluation functors at `op X` when `(X : C, x : F.obj X)` varies in
`Φ.fiber.Elementsᵒᵖ`. We define `Φ.sheafFiber : Sheaf J A ⥤ A` as the
restriction of `Φ.presheafFiber` to the full subcategory of sheaves.

Under certain assumptions, we show that if `A` is concrete and
`P ⟶ Q` is a locally bijective morphism between presheaves,
then the induced morphism on fibers is a bijection. It follows
that not only `Φ.sheafFiber : Sheaf J A ⥤ A` is the restriction of
`Φ.presheafFiber` but it may also be thought as a localization
of this functor with respect to the class of morphisms `J.W`.
In particular, the fiber of a presheaf identifies to the fiber of
its associated sheaf.

Under suitable assumptions on the target category `A`, we show that
both `Φ.presheafFiber` and `Φ.sheafFiber` commute with finite limits
and with arbitrary colimits. (The commutation of `Φ.sheafFiber` with colimits
is obtained in the file `Mathlib/CategoryTheory/Sites/Point/Skyscraper.lean`.)

-/

@[expose] public section

universe w' w v v' v'' u u' u''

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C]

namespace GrothendieckTopology

variable (J : GrothendieckTopology C)

/--
Definition of `Point` / `Point` 的定义

English:
structure Point
  parameters: where
  axioms and operations (4):
    - fiber : C ⥤ Type w
    - isCofiltered : IsCofiltered fiber.Elements  [default: by infer_instance]
    - initiallySmall : InitiallySmall.{w} fiber.Elements  [default: by infer_instance]
    - jointly_surjective({X : C} (R : Sieve X) (h : R in J X) (x : fiber.obj X)) : exists (Y : C) (f : Y ⟶ X) (_ : R f) (y : fiber.obj Y), fiber.map f y = x

中文:
结构 Point
  参数: where
  公理与运算 (4 个):
    - fiber : C ⥤ Type w
    - isCofiltered : IsCofiltered fiber.Elements  [默认: by infer_instance]
    - initiallySmall : InitiallySmall.{w} fiber.Elements  [默认: by infer_instance]
    - jointly_surjective({X : C} (R : Sieve X) (h : R in J X) (x : fiber.obj X)) : 存在 (Y : C) (f : Y ⟶ X) (_ : R f) (y : fiber.obj Y), fiber.map f y = x

Depends on / 依赖: Elements, InitiallySmall, fiber.Elements, fiber.map, fiber.obj, infer_instance, initiallySmall, jointly_surjective
-/
structure Point where
  /-- the fiber functor on the underlying category of the site -/
  fiber : C ⥤ Type w
  isCofiltered : IsCofiltered fiber.Elements := by infer_instance
  initiallySmall : InitiallySmall.{w} fiber.Elements := by infer_instance
  jointly_surjective {X : C} (R : Sieve X) (h : R in J X) (x : fiber.obj X) :
    exists (Y : C) (f : Y ⟶ X) (_ : R f) (y : fiber.obj Y), fiber.map f y = x

namespace Point

attribute [instance] initiallySmall isCofiltered

variable {J} (Φ : Point.{w} J) {A : Type u'} [Category.{v'} A]
  {B : Type u''} [Category.{v''} B]
  [HasColimitsOfSize.{w, w} A] [HasColimitsOfSize.{w, w} B]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasColimitsOfShape Φ.fiber.Elementsᵒᵖ A
  body: hasColimitsOfShape_of_finallySmall _ _

中文:
实例 :
  签名: HasColimitsOfShape Φ.fiber.Elementsᵒᵖ A
  定义体: hasColimitsOfShape_of_finallySmall _ _

Depends on / 依赖: hasColimitsOfShape_of_finallySmall
-/
instance : HasColimitsOfShape Φ.fiber.Elementsᵒᵖ A :=
  hasColimitsOfShape_of_finallySmall _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSifted Φ.fiber.Elementsᵒᵖ
  body: IsFiltered.isSifted

中文:
实例 :
  签名: IsSifted Φ.fiber.Elementsᵒᵖ
  定义体: IsFiltered.isSifted

Depends on / 依赖: IsFiltered, IsFiltered.isSifted, isSifted
-/
instance : IsSifted Φ.fiber.Elementsᵒᵖ := IsFiltered.isSifted

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LocallySmall.{w}
  signature: C] [AB5OfSize.{w, w} A] [HasFiniteLimits A] :
  body: hasExactColimitsOfShape_of_final _
    (FinallySmall.fromFilteredFinalModel Φ.fiber.Elementsᵒᵖ)

中文:
实例 [LocallySmall.{w}
  签名: C] [AB5OfSize.{w, w} A] [HasFiniteLimits A] :
  定义体: hasExactColimitsOfShape_of_final _
    (FinallySmall.fromFilteredFinalModel Φ.fiber.Elementsᵒᵖ)

Depends on / 依赖: FinallySmall, FinallySmall.fromFilteredFinalModel, fiber.Elements, fromFilteredFinalModel, hasExactColimitsOfShape_of_final
-/
instance [LocallySmall.{w} C] [AB5OfSize.{w, w} A] [HasFiniteLimits A] :
    HasExactColimitsOfShape Φ.fiber.Elementsᵒᵖ A :=
  hasExactColimitsOfShape_of_final _
    (FinallySmall.fromFilteredFinalModel Φ.fiber.Elementsᵒᵖ)

/--
Definition of `presheafFiber` / `presheafFiber` 的定义

English:
definition presheafFiber
  signature: : (Cᵒᵖ ⥤ A) ⥤ A
  body: (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π Φ.fiber).op ⋙ colim

中文:
定义 presheafFiber
  签名: : (Cᵒᵖ ⥤ A) ⥤ A
  定义体: (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π Φ.fiber).op ⋙ colim

Depends on / 依赖: CategoryOfElements, Functor, Functor.whiskeringLeft, whiskeringLeft
-/
noncomputable def presheafFiber : (Cᵒᵖ ⥤ A) ⥤ A :=
  (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π Φ.fiber).op ⋙ colim

/--
Definition of `toPresheafFiber` / `toPresheafFiber` 的定义

English:
definition toPresheafFiber
  signature: (X : C) (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ A)
  body: colimit.ι ((CategoryOfElements.π Φ.fiber).op ⋙ P) (op ⟨X, x⟩)

@[ext]

中文:
定义 toPresheafFiber
  签名: (X : C) (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ A)
  定义体: colimit.ι ((CategoryOfElements.π Φ.fiber).op ⋙ P) (op ⟨X, x⟩)

@[ext]

Depends on / 依赖: CategoryOfElements, colimit
-/
noncomputable def toPresheafFiber (X : C) (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ A) :
    P.obj (op X) ⟶ Φ.presheafFiber.obj P :=
  colimit.ι ((CategoryOfElements.π Φ.fiber).op ⋙ P) (op ⟨X, x⟩)

@[ext]
/--
lemma `presheafFiber_hom_ext` / 引理 `presheafFiber_hom_ext`

English:
lemma presheafFiber_hom_ext
  proof: colimit.hom_ext (by rintro ⟨⟨X, x⟩⟩; exact h X x)

中文:
引理 presheafFiber_hom_ext
  证明: colimit.hom_ext (by rintro ⟨⟨X, x⟩⟩; exact h X x)

Depends on / 依赖: colimit, colimit.hom_ext, hom_ext
-/
lemma presheafFiber_hom_ext
    {P : Cᵒᵖ ⥤ A} {T : A} {f g : Φ.presheafFiber.obj P ⟶ T}
    (h : forall (X : C) (x : Φ.fiber.obj X), Φ.toPresheafFiber X x P ≫ f =
      Φ.toPresheafFiber X x P ≫ g) : f = g :=
  colimit.hom_ext (by rintro ⟨⟨X, x⟩⟩; exact h X x)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a point `Φ` of a site `(C, J)`, `X : C` and `x : Φ.fiber.obj X`,
this is the map `P.obj (op X) ⟶ Φ.presheafFiber.obj P` for any `P : Cᵒᵖ ⥤ A`
as a natural transformation. -/
@[simps]
/--
Definition of `toPresheafFiberNatTrans` / `toPresheafFiberNatTrans` 的定义

English:
definition toPresheafFiberNatTrans
  signature: (X : C) (x : Φ.fiber.obj X)
  body: Φ.toPresheafFiber X x
  naturality _ _ f := by simp [presheafFiber, toPresheafFiber]

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
定义 toPresheafFiberNatTrans
  签名: (X : C) (x : Φ.fiber.obj X)
  定义体: Φ.toPresheafFiber X x
  naturality _ _ f := by simp [presheafFiber, toPresheafFiber]

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: toPresheafFiber
-/
noncomputable def toPresheafFiberNatTrans (X : C) (x : Φ.fiber.obj X) :
    (evaluation Cᵒᵖ A).obj (op X) ⟶ Φ.presheafFiber where
  app := Φ.toPresheafFiber X x
  naturality _ _ f := by simp [presheafFiber, toPresheafFiber]

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `toPresheafFiber_w` / 引理 `toPresheafFiber_w`

English:
lemma toPresheafFiber_w
  given: {X Y : C} (f : X ⟶ Y) (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ A)
  proof: colimit.w ((CategoryOfElements.π Φ.fiber).op ⋙ P)
      (CategoryOfElements.homMk ⟨X, x⟩ ⟨Y, Φ.fiber.map f x⟩ f rfl).op

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
引理 toPresheafFiber_w
  条件: {X Y : C} (f : X ⟶ Y) (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ A)
  证明: colimit.w ((CategoryOfElements.π Φ.fiber).op ⋙ P)
      (CategoryOfElements.homMk ⟨X, x⟩ ⟨Y, Φ.fiber.map f x⟩ f rfl).op

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: CategoryOfElements, CategoryOfElements.homMk, colimit, colimit.w, fiber.map
-/
lemma toPresheafFiber_w {X Y : C} (f : X ⟶ Y) (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ A) :
    P.map f.op ≫ Φ.toPresheafFiber X x P =
      Φ.toPresheafFiber Y (Φ.fiber.map f x) P :=
  colimit.w ((CategoryOfElements.π Φ.fiber).op ⋙ P)
      (CategoryOfElements.homMk ⟨X, x⟩ ⟨Y, Φ.fiber.map f x⟩ f rfl).op

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `toPresheafFiber_naturality` / 引理 `toPresheafFiber_naturality`

English:
lemma toPresheafFiber_naturality
  given: {P Q : Cᵒᵖ ⥤ A} (g : P ⟶ Q) (X : C) (x : Φ.fiber.obj X)
  proof: ((Φ.toPresheafFiberNatTrans X x).naturality g).symm

中文:
引理 toPresheafFiber_naturality
  条件: {P Q : Cᵒᵖ ⥤ A} (g : P ⟶ Q) (X : C) (x : Φ.fiber.obj X)
  证明: ((Φ.toPresheafFiberNatTrans X x).naturality g).symm

Depends on / 依赖: naturality, toPresheafFiberNatTrans
-/
lemma toPresheafFiber_naturality {P Q : Cᵒᵖ ⥤ A} (g : P ⟶ Q) (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x P ≫ Φ.presheafFiber.map g =
      g.app (op X) ≫ Φ.toPresheafFiber X x Q :=
  ((Φ.toPresheafFiberNatTrans X x).naturality g).symm

set_option backward.defeqAttrib.useBackward true in
/-- The (colimit) cocone which defines the fiber of a presheaf. -/
@[simps]
/--
Definition of `presheafFiberCocone` / `presheafFiberCocone` 的定义

English:
definition presheafFiberCocone
  signature: (P : Cᵒᵖ ⥤ A)
  body: Φ.presheafFiber.obj P
  ι.app x := Φ.toPresheafFiber x.unop.1 x.unop.2 P

中文:
定义 presheafFiberCocone
  签名: (P : Cᵒᵖ ⥤ A)
  定义体: Φ.presheafFiber.obj P
  ι.app x := Φ.toPresheafFiber x.unop.1 x.unop.2 P

Depends on / 依赖: presheafFiber, presheafFiber.obj
-/
noncomputable def presheafFiberCocone (P : Cᵒᵖ ⥤ A) :
    Cocone ((CategoryOfElements.π Φ.fiber).op ⋙ P) where
  pt := Φ.presheafFiber.obj P
  ι.app x := Φ.toPresheafFiber x.unop.1 x.unop.2 P

/--
Definition of `isColimitPresheafFiberCocone` / `isColimitPresheafFiberCocone` 的定义

English:
definition isColimitPresheafFiberCocone
  signature: (P : Cᵒᵖ ⥤ A)
  body: colimit.isColimit _

中文:
定义 isColimitPresheafFiberCocone
  签名: (P : Cᵒᵖ ⥤ A)
  定义体: colimit.isColimit _

Depends on / 依赖: colimit, colimit.isColimit, isColimit
-/
noncomputable def isColimitPresheafFiberCocone (P : Cᵒᵖ ⥤ A) :
    IsColimit (Φ.presheafFiberCocone P) :=
  colimit.isColimit _

/--
Definition of `shrinkYonedaCompPresheafFiberIso` / `shrinkYonedaCompPresheafFiberIso` 的定义

English:
definition shrinkYonedaCompPresheafFiberIso
  signature: [LocallySmall.{w} C]
  body: Functor.Elements.shrinkYonedaCompWhiskeringLeftObjπCompColimIso _

中文:
定义 shrinkYonedaCompPresheafFiberIso
  签名: [LocallySmall.{w} C]
  定义体: Functor.Elements.shrinkYonedaCompWhiskeringLeftObjπCompColimIso _

Depends on / 依赖: Elements, Functor, Functor.Elements.shrinkYonedaCompWhiskeringLeftObj
-/
noncomputable def shrinkYonedaCompPresheafFiberIso [LocallySmall.{w} C] :
    shrinkYoneda.{w} ⋙ Φ.presheafFiber ≅ Φ.fiber :=
  Functor.Elements.shrinkYonedaCompWhiskeringLeftObjπCompColimIso _

/--
lemma `shrinkYonedaCompPresheafFiberIso_inv_app_toPresheafFiber` / 引理 `shrinkYonedaCompPresheafFiberIso_inv_app_toPresheafFiber`

English:
lemma shrinkYonedaCompPresheafFiberIso_inv_app_toPresheafFiber
  proof: Functor.Elements.shrinkYonedaCompWhiskeringLeftObjπCompColimIso_inv_app_apply
    _ (Functor.elementsMk (Φ.fiber) _ x)

中文:
引理 shrinkYonedaCompPresheafFiberIso_inv_app_toPresheafFiber
  证明: Functor.Elements.shrinkYonedaCompWhiskeringLeftObjπCompColimIso_inv_app_apply
    _ (Functor.elementsMk (Φ.fiber) _ x)

Depends on / 依赖: Elements, Functor, Functor.Elements.shrinkYonedaCompWhiskeringLeftObj, Functor.elementsMk, elementsMk
-/
lemma shrinkYonedaCompPresheafFiberIso_inv_app_toPresheafFiber
    [LocallySmall.{w} C] {X : C} (x : Φ.fiber.obj X) :
    Φ.shrinkYonedaCompPresheafFiberIso.inv.app X x =
    Φ.toPresheafFiber X x (shrinkYoneda.{w}.obj X)
      (shrinkYonedaObjObjEquiv.symm (𝟙 X)) :=
  Functor.Elements.shrinkYonedaCompWhiskeringLeftObjπCompColimIso_inv_app_apply
    _ (Functor.elementsMk (Φ.fiber) _ x)

/--
lemma `presheafFiber_map_shrinkYoneda_map_shrinkYonedaCompPresheafFiberIso_inv_app` / 引理 `presheafFiber_map_shrinkYoneda_map_shrinkYonedaCompPresheafFiberIso_inv_app`

English:
lemma presheafFiber_map_shrinkYoneda_map_shrinkYonedaCompPresheafFiberIso_inv_app
  proof: by
  rw [shrinkYonedaCompPresheafFiberIso_inv_app_toPresheafFiber]
  refine (Φ.toPresheafFiber_naturality_apply (shrinkYoneda.{w}.map f) _ x
    (shrinkYonedaObjObjEquiv.symm (𝟙 X))).trans (congr_arg _ ?_)
  simpa using shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w} (𝟙 _) f

中文:
引理 presheafFiber_map_shrinkYoneda_map_shrinkYonedaCompPresheafFiberIso_inv_app
  证明: by
  rw [shrinkYonedaCompPresheafFiberIso_inv_app_toPresheafFiber]
  refine (Φ.toPresheafFiber_naturality_apply (shrinkYoneda.{w}.map f) _ x
    (shrinkYonedaObjObjEquiv.symm (𝟙 X))).trans (congr_arg _ ?_)
  simpa using shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w} (𝟙 _) f

Depends on / 依赖: congr_arg, shrinkYoneda, shrinkYonedaCompPresheafFiberIso_inv_app_toPresheafFiber, shrinkYonedaObjObjEquiv, shrinkYonedaObjObjEquiv.symm, shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm, toPresheafFiber_naturality_apply
-/
lemma presheafFiber_map_shrinkYoneda_map_shrinkYonedaCompPresheafFiberIso_inv_app
    [LocallySmall.{w} C] {X Y : C} (f : X ⟶ Y) (x : Φ.fiber.obj X) :
    Φ.presheafFiber.map (shrinkYoneda.{w}.map f)
      (Φ.shrinkYonedaCompPresheafFiberIso.inv.app X x) =
    Φ.toPresheafFiber X x (shrinkYoneda.{w}.obj Y)
      (shrinkYonedaObjObjEquiv.symm f) := by
  rw [shrinkYonedaCompPresheafFiberIso_inv_app_toPresheafFiber]
  refine (Φ.toPresheafFiber_naturality_apply (shrinkYoneda.{w}.map f) _ x
    (shrinkYonedaObjObjEquiv.symm (𝟙 X))).trans (congr_arg _ ?_)
  simpa using shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w} (𝟙 _) f

section

variable {P : Cᵒᵖ ⥤ A} {T : A}
  (φ : forall (X : C) (_ : Φ.fiber.obj X), P.obj (op X) ⟶ T)
  (hφ : forall ⦃X Y : C⦄ (f : X ⟶ Y) (x : Φ.fiber.obj X),
    P.map f.op ≫ φ X x = φ Y (Φ.fiber.map f x) := by cat_disch)

set_option backward.defeqAttrib.useBackward true in
set_option backward.privateInPublic true in
/--
Definition of `presheafFiberDesc` / `presheafFiberDesc` 的定义

English:
definition presheafFiberDesc
  signature: :
  body: colimit.desc _ (Cocone.mk _ { app x := φ x.unop.1 x.unop.2 })

中文:
定义 presheafFiberDesc
  签名: :
  定义体: colimit.desc _ (Cocone.mk _ { app x := φ x.unop.1 x.unop.2 })

Depends on / 依赖: Cocone, Cocone.mk, colimit, colimit.desc, x.unop
-/
noncomputable def presheafFiberDesc :
    Φ.presheafFiber.obj P ⟶ T :=
  colimit.desc _ (Cocone.mk _ { app x := φ x.unop.1 x.unop.2 })

set_option backward.privateInPublic true in
@[reassoc (attr := simp)]
/--
lemma `toPresheafFiber_presheafFiberDesc` / 引理 `toPresheafFiber_presheafFiberDesc`

English:
lemma toPresheafFiber_presheafFiberDesc
  given: (X : C) (x : Φ.fiber.obj X)
  proof: colimit.ι_desc _ _

中文:
引理 toPresheafFiber_presheafFiberDesc
  条件: (X : C) (x : Φ.fiber.obj X)
  证明: colimit.ι_desc _ _

Depends on / 依赖: colimit
-/
lemma toPresheafFiber_presheafFiberDesc (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x P ≫ Φ.presheafFiberDesc φ hφ = φ X x :=
  colimit.ι_desc _ _

end

variable {FC : A -> A -> Type*} {CC : A -> Type w'}
  [forall (X Y : A), FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory.{w'} A FC]

section

variable {P Q : Cᵒᵖ ⥤ A}

variable [PreservesFilteredColimitsOfSize.{w, w} (forget A)] [LocallySmall.{w} C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimitsOfShape Φ.fiber.Elementsᵒᵖ (forget A)
  body: Functor.Final.preservesColimitsOfShape_of_final (FinallySmall.fromFilteredFinalModel.{w} _) _

中文:
实例 :
  签名: PreservesColimitsOfShape Φ.fiber.Elementsᵒᵖ (forget A)
  定义体: Functor.Final.preservesColimitsOfShape_of_final (FinallySmall.fromFilteredFinalModel.{w} _) _

Depends on / 依赖: FinallySmall, FinallySmall.fromFilteredFinalModel, Functor, Functor.Final.preservesColimitsOfShape_of_final, fromFilteredFinalModel, preservesColimitsOfShape_of_final
-/
instance : PreservesColimitsOfShape Φ.fiber.Elementsᵒᵖ (forget A) :=
  Functor.Final.preservesColimitsOfShape_of_final (FinallySmall.fromFilteredFinalModel.{w} _) _

/--
lemma `toPresheafFiber_jointly_surjective` / 引理 `toPresheafFiber_jointly_surjective`

English:
lemma toPresheafFiber_jointly_surjective
  given: (p : ToType (Φ.presheafFiber.obj P))
  proof: by
  obtain ⟨⟨X, x⟩, z, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget A)
      (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ P))) p
  exact ⟨X, x, z, rfl⟩

中文:
引理 toPresheafFiber_jointly_surjective
  条件: (p : ToType (Φ.presheafFiber.obj P))
  证明: by
  obtain ⟨⟨X, x⟩, z, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget A)
      (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ P))) p
  exact ⟨X, x, z, rfl⟩

Depends on / 依赖: CategoryOfElements, Types.jointly_surjective_of_isColimit, colimit, colimit.isColimit, forget, isColimit, isColimitOfPreserves, jointly_surjective_of_isColimit
-/
lemma toPresheafFiber_jointly_surjective (p : ToType (Φ.presheafFiber.obj P)) :
    exists (X : C) (x : Φ.fiber.obj X) (z : ToType (P.obj (op X))),
      Φ.toPresheafFiber X x P z = p := by
  obtain ⟨⟨X, x⟩, z, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget A)
      (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ P))) p
  exact ⟨X, x, z, rfl⟩

/--
lemma `toPresheafFiber_jointly_surjective₂` / 引理 `toPresheafFiber_jointly_surjective₂`

English:
lemma toPresheafFiber_jointly_surjective₂
  given: (p₁ p₂ : ToType (Φ.presheafFiber.obj P))
  proof: by
  obtain ⟨⟨X, x⟩, z₁, z₂, rfl, rfl⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂
    (isColimitOfPreserves (forget A)
      (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ P))) p₁ p₂
  exact ⟨X, x, z₁, z₂, rfl, rfl⟩

中文:
引理 toPresheafFiber_jointly_surjective₂
  条件: (p₁ p₂ : ToType (Φ.presheafFiber.obj P))
  证明: by
  obtain ⟨⟨X, x⟩, z₁, z₂, rfl, rfl⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂
    (isColimitOfPreserves (forget A)
      (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ P))) p₁ p₂
  exact ⟨X, x, z₁, z₂, rfl, rfl⟩

Depends on / 依赖: CategoryOfElements, FilteredColimit, Types.FilteredColimit.jointly_surjective_of_isColimit, colimit, colimit.isColimit, forget, isColimit, isColimitOfPreserves
-/
lemma toPresheafFiber_jointly_surjective₂ (p₁ p₂ : ToType (Φ.presheafFiber.obj P)) :
    exists (X : C) (x : Φ.fiber.obj X) (z₁ z₂ : ToType (P.obj (op X))),
      Φ.toPresheafFiber X x P z₁ = p₁ ∧ Φ.toPresheafFiber X x P z₂ = p₂ := by
  obtain ⟨⟨X, x⟩, z₁, z₂, rfl, rfl⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂
    (isColimitOfPreserves (forget A)
      (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ P))) p₁ p₂
  exact ⟨X, x, z₁, z₂, rfl, rfl⟩

/--
lemma `toPresheafFiber_eq_iff'` / 引理 `toPresheafFiber_eq_iff'`

English:
lemma toPresheafFiber_eq_iff'
  given: (X : C) (x : Φ.fiber.obj X) (z₁ z₂ : ToType (P.obj (op X)))
  proof: by
  refine ((colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ P)).eq_iff' ..).trans ?_
  constructor
  · rintro ⟨⟨Y, y⟩, ⟨f, hf⟩, hf'⟩
    exact ⟨Y, f, y, hf, hf'⟩
  · rintro ⟨Y, f, y, hf, hf'⟩
    exact ⟨⟨Y, y⟩, ⟨f, hf⟩, hf'⟩

中文:
引理 toPresheafFiber_eq_iff'
  条件: (X : C) (x : Φ.fiber.obj X) (z₁ z₂ : ToType (P.obj (op X)))
  证明: by
  refine ((colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ P)).eq_iff' ..).trans ?_
  constructor
  · rintro ⟨⟨Y, y⟩, ⟨f, hf⟩, hf'⟩
    exact ⟨Y, f, y, hf, hf'⟩
  · rintro ⟨Y, f, y, hf, hf'⟩
    exact ⟨⟨Y, y⟩, ⟨f, hf⟩, hf'⟩

Depends on / 依赖: CategoryOfElements, colimit, colimit.isColimit, eq_iff, isColimit
-/
lemma toPresheafFiber_eq_iff' (X : C) (x : Φ.fiber.obj X) (z₁ z₂ : ToType (P.obj (op X))) :
    Φ.toPresheafFiber X x P z₁ = Φ.toPresheafFiber X x P z₂ ↔
      exists (Y : C) (f : Y ⟶ X) (y : Φ.fiber.obj Y), Φ.fiber.map f y = x ∧
        P.map f.op z₁ = P.map f.op z₂ := by
  refine ((colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ P)).eq_iff' ..).trans ?_
  constructor
  · rintro ⟨⟨Y, y⟩, ⟨f, hf⟩, hf'⟩
    exact ⟨Y, f, y, hf, hf'⟩
  · rintro ⟨Y, f, y, hf, hf'⟩
    exact ⟨⟨Y, y⟩, ⟨f, hf⟩, hf'⟩

variable (f : P ⟶ Q)

/--
lemma `toPresheafFiber_map_surjective` / 引理 `toPresheafFiber_map_surjective`

English:
lemma toPresheafFiber_map_surjective
  given: [Presheaf.IsLocallySurjective J f]
  proof: by
  intro p
  obtain ⟨X, x, z, rfl⟩ := Φ.toPresheafFiber_jointly_surjective p
  obtain ⟨Y, g, ⟨t, ht⟩, y, rfl⟩ := Φ.jointly_surjective _ (Presheaf.imageSieve_mem J f z) x
  exact ⟨Φ.toPresheafFiber Y y P t, by simp [← toPresheafFiber_w, ← ht]⟩

中文:
引理 toPresheafFiber_map_surjective
  条件: [Presheaf.IsLocallySurjective J f]
  证明: by
  intro p
  obtain ⟨X, x, z, rfl⟩ := Φ.toPresheafFiber_jointly_surjective p
  obtain ⟨Y, g, ⟨t, ht⟩, y, rfl⟩ := Φ.jointly_surjective _ (Presheaf.imageSieve_mem J f z) x
  exact ⟨Φ.toPresheafFiber Y y P t, by simp [← toPresheafFiber_w, ← ht]⟩

Depends on / 依赖: Presheaf, Presheaf.imageSieve_mem, imageSieve_mem, jointly_surjective, toPresheafFiber, toPresheafFiber_jointly_surjective, toPresheafFiber_w
-/
lemma toPresheafFiber_map_surjective [Presheaf.IsLocallySurjective J f] :
    Function.Surjective (Φ.presheafFiber.map f) := by
  intro p
  obtain ⟨X, x, z, rfl⟩ := Φ.toPresheafFiber_jointly_surjective p
  obtain ⟨Y, g, ⟨t, ht⟩, y, rfl⟩ := Φ.jointly_surjective _ (Presheaf.imageSieve_mem J f z) x
  exact ⟨Φ.toPresheafFiber Y y P t, by simp [← toPresheafFiber_w, ← ht]⟩

/--
lemma `toPresheafFiber_map_injective` / 引理 `toPresheafFiber_map_injective`

English:
lemma toPresheafFiber_map_injective
  given: [Presheaf.IsLocallyInjective J f]
  proof: by
  suffices forall (X : C) (x : Φ.fiber.obj X) (p₁ p₂ : ToType (P.obj (op X)))
      (hp : f.app _ p₁ = f.app _ p₂), Φ.toPresheafFiber X x P p₁ = Φ.toPresheafFiber X x P p₂ by
    rintro q₁ q₂ h
    obtain ⟨X, x, p₁, p₂, rfl, rfl⟩ := Φ.toPresheafFiber_jointly_surjective₂ q₁ q₂
    simp only [toPre

中文:
引理 toPresheafFiber_map_injective
  条件: [Presheaf.IsLocallyInjective J f]
  证明: by
  suffices forall (X : C) (x : Φ.fiber.obj X) (p₁ p₂ : ToType (P.obj (op X)))
      (hp : f.app _ p₁ = f.app _ p₂), Φ.toPresheafFiber X x P p₁ = Φ.toPresheafFiber X x P p₂ by
    rintro q₁ q₂ h
    obtain ⟨X, x, p₁, p₂, rfl, rfl⟩ := Φ.toPresheafFiber_jointly_surjective₂ q₁ q₂
    simp only [toPre

Depends on / 依赖: NatTrans, NatTrans.naturality_apply, P.obj, ToType, f.app, fiber.obj, jointly_su, naturality_apply, toPresheafFiber, toPresheafFiber_eq_iff, toPresheafFiber_naturality_apply
-/
lemma toPresheafFiber_map_injective [Presheaf.IsLocallyInjective J f] :
    Function.Injective (Φ.presheafFiber.map f) := by
  suffices forall (X : C) (x : Φ.fiber.obj X) (p₁ p₂ : ToType (P.obj (op X)))
      (hp : f.app _ p₁ = f.app _ p₂), Φ.toPresheafFiber X x P p₁ = Φ.toPresheafFiber X x P p₂ by
    rintro q₁ q₂ h
    obtain ⟨X, x, p₁, p₂, rfl, rfl⟩ := Φ.toPresheafFiber_jointly_surjective₂ q₁ q₂
    simp only [toPresheafFiber_naturality_apply, toPresheafFiber_eq_iff'] at h
    obtain ⟨Y, g, y, rfl, h⟩ := h
    simp only [← NatTrans.naturality_apply] at h
    simpa using this _ y _ _ h
  intro X x p₁ p₂ h
  obtain ⟨Y, g, hg, y, rfl⟩ := Φ.jointly_surjective _ (Presheaf.equalizerSieve_mem J f _ _ h) x
  simp_all [← toPresheafFiber_w_apply]

/--
lemma `toPresheafFiber_map_bijective` / 引理 `toPresheafFiber_map_bijective`

English:
lemma toPresheafFiber_map_bijective
  proof: ⟨Φ.toPresheafFiber_map_injective f, Φ.toPresheafFiber_map_surjective f⟩

中文:
引理 toPresheafFiber_map_bijective
  证明: ⟨Φ.toPresheafFiber_map_injective f, Φ.toPresheafFiber_map_surjective f⟩

Depends on / 依赖: toPresheafFiber_map_injective, toPresheafFiber_map_surjective
-/
lemma toPresheafFiber_map_bijective
    [Presheaf.IsLocallyInjective J f] [Presheaf.IsLocallySurjective J f] :
    Function.Bijective (Φ.presheafFiber.map f) :=
  ⟨Φ.toPresheafFiber_map_injective f, Φ.toPresheafFiber_map_surjective f⟩

/--
lemma `W_isInvertedBy_presheafFiber'` / 引理 `W_isInvertedBy_presheafFiber'`

English:
lemma W_isInvertedBy_presheafFiber'
  proof: by
  intro P Q f hf
  obtain ⟨_, _⟩ := (J.W_iff_isLocallyBijective f).1 hf
  rw [← isIso_iff_of_reflects_iso _ (forget A)]; rw [isIso_iff_bijective]
  exact Φ.toPresheafFiber_map_bijective f

中文:
引理 W_isInvertedBy_presheafFiber'
  证明: by
  intro P Q f hf
  obtain ⟨_, _⟩ := (J.W_iff_isLocallyBijective f).1 hf
  rw [← isIso_iff_of_reflects_iso _ (forget A)]; rw [isIso_iff_bijective]
  exact Φ.toPresheafFiber_map_bijective f

Depends on / 依赖: J.W_iff_isLocallyBijective, W_iff_isLocallyBijective, forget, isIso_iff_bijective, isIso_iff_of_reflects_iso, toPresheafFiber_map_bijective
-/
lemma W_isInvertedBy_presheafFiber'
    [J.WEqualsLocallyBijective A] [(forget A).ReflectsIsomorphisms] :
    J.W.IsInvertedBy (Φ.presheafFiber (A := A)) := by
  intro P Q f hf
  obtain ⟨_, _⟩ := (J.W_iff_isLocallyBijective f).1 hf
  rw [← isIso_iff_of_reflects_iso _ (forget A)]; rw [isIso_iff_bijective]
  exact Φ.toPresheafFiber_map_bijective f

end

/--
Definition of `sheafFiber` / `sheafFiber` 的定义

English:
definition sheafFiber
  signature: : Sheaf J A ⥤ A
  body: sheafToPresheaf J A ⋙ Φ.presheafFiber

中文:
定义 sheafFiber
  签名: : Sheaf J A ⥤ A
  定义体: sheafToPresheaf J A ⋙ Φ.presheafFiber

Depends on / 依赖: presheafFiber, sheafToPresheaf
-/
noncomputable def sheafFiber : Sheaf J A ⥤ A :=
  sheafToPresheaf J A ⋙ Φ.presheafFiber

/--
Definition of `sheafToPresheafCompPresheafFiberIso` / `sheafToPresheafCompPresheafFiberIso` 的定义

English:
definition sheafToPresheafCompPresheafFiberIso
  signature: :
  body: Iso.refl _

中文:
定义 sheafToPresheafCompPresheafFiberIso
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
noncomputable def sheafToPresheafCompPresheafFiberIso :
    sheafToPresheaf J A ⋙ Φ.presheafFiber ≅ Φ.sheafFiber :=
  Iso.refl _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LocallySmall.{w}
  signature: C] [HasFiniteLimits A] [AB5OfSize.{w, w} A] :
  body: comp_preservesFiniteLimits _ _

中文:
实例 [LocallySmall.{w}
  签名: C] [HasFiniteLimits A] [AB5OfSize.{w, w} A] :
  定义体: comp_preservesFiniteLimits _ _
-/
instance [LocallySmall.{w} C] [HasFiniteLimits A] [AB5OfSize.{w, w} A] :
    PreservesFiniteLimits (Φ.presheafFiber (A := A)) :=
  comp_preservesFiniteLimits _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LocallySmall.{w}
  signature: C] [HasFiniteLimits A] [AB5OfSize.{w, w} A] :
  body: comp_preservesFiniteLimits _ _

中文:
实例 [LocallySmall.{w}
  签名: C] [HasFiniteLimits A] [AB5OfSize.{w, w} A] :
  定义体: comp_preservesFiniteLimits _ _
-/
instance [LocallySmall.{w} C] [HasFiniteLimits A] [AB5OfSize.{w, w} A] :
    PreservesFiniteLimits (Φ.sheafFiber (A := A)) :=
  comp_preservesFiniteLimits _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimitsOfSize.{w, w} (Φ.presheafFiber (A := A))
  body: by
    dsimp [presheafFiber]
    infer_instance

中文:
实例 :
  签名: PreservesColimitsOfSize.{w, w} (Φ.presheafFiber (A := A))
  定义体: by
    dsimp [presheafFiber]
    infer_instance
-/
instance : PreservesColimitsOfSize.{w, w} (Φ.presheafFiber (A := A)) where
  preservesColimitsOfShape := by
    dsimp [presheafFiber]
    infer_instance

section

variable [LocallySmall.{w} C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteLimits Φ.fiber
  body: preservesFiniteLimits_of_natIso Φ.shrinkYonedaCompPresheafFiberIso

中文:
实例 :
  签名: PreservesFiniteLimits Φ.fiber
  定义体: preservesFiniteLimits_of_natIso Φ.shrinkYonedaCompPresheafFiberIso

Depends on / 依赖: preservesFiniteLimits_of_natIso, shrinkYonedaCompPresheafFiberIso
-/
instance : PreservesFiniteLimits Φ.fiber :=
  preservesFiniteLimits_of_natIso Φ.shrinkYonedaCompPresheafFiberIso

/--
Definition of `isTerminalFiberObj` / `isTerminalFiberObj` 的定义

English:
definition isTerminalFiberObj
  signature: (T : C) (hT : IsTerminal T)
  body: IsTerminal.isTerminalObj _ _ hT

中文:
定义 isTerminalFiberObj
  签名: (T : C) (hT : IsTerminal T)
  定义体: IsTerminal.isTerminalObj _ _ hT

Depends on / 依赖: IsTerminal, IsTerminal.isTerminalObj, isTerminalObj
-/
noncomputable def isTerminalFiberObj (T : C) (hT : IsTerminal T) :
    IsTerminal (Φ.fiber.obj T) :=
  IsTerminal.isTerminalObj _ _ hT

/-- The fiber of the terminal object contains a unique element. -/
@[instance_reducible]
/--
Definition of `uniqueFiberObj` / `uniqueFiberObj` 的定义

English:
definition uniqueFiberObj
  signature: (T : C) (hT : IsTerminal T)
  body: Types.isTerminalEquivUnique _ (Φ.isTerminalFiberObj T hT)

中文:
定义 uniqueFiberObj
  签名: (T : C) (hT : IsTerminal T)
  定义体: Types.isTerminalEquivUnique _ (Φ.isTerminalFiberObj T hT)

Depends on / 依赖: Types.isTerminalEquivUnique, isTerminalEquivUnique, isTerminalFiberObj
-/
noncomputable def uniqueFiberObj (T : C) (hT : IsTerminal T) :
    Unique (Φ.fiber.obj T) :=
  Types.isTerminalEquivUnique _ (Φ.isTerminalFiberObj T hT)

/--
lemma `fiber_map_injective_of_mono` / 引理 `fiber_map_injective_of_mono`

English:
lemma fiber_map_injective_of_mono
  given: {U T : C} (f : U ⟶ T) [Mono f]
  proof: by
  rw [← mono_iff_injective]
  infer_instance

中文:
引理 fiber_map_injective_of_mono
  条件: {U T : C} (f : U ⟶ T) [Mono f]
  证明: by
  rw [← mono_iff_injective]
  infer_instance

Depends on / 依赖: infer_instance, mono_iff_injective
-/
lemma fiber_map_injective_of_mono {U T : C} (f : U ⟶ T) [Mono f] :
    Function.Injective (Φ.fiber.map f) := by
  rw [← mono_iff_injective]
  infer_instance

/--
lemma `subsingleton_fiber_obj` / 引理 `subsingleton_fiber_obj`

English:
lemma subsingleton_fiber_obj
  given: {U T : C} (f : U ⟶ T) [Mono f] (hT : IsTerminal T)
  proof: Φ.fiber_map_injective_of_mono f (by
    have := Φ.uniqueFiberObj T hT
    subsingleton)

中文:
引理 subsingleton_fiber_obj
  条件: {U T : C} (f : U ⟶ T) [Mono f] (hT : IsTerminal T)
  证明: Φ.fiber_map_injective_of_mono f (by
    have := Φ.uniqueFiberObj T hT
    subsingleton)

Depends on / 依赖: fiber_map_injective_of_mono, subsingleton, uniqueFiberObj
-/
lemma subsingleton_fiber_obj {U T : C} (f : U ⟶ T) [Mono f] (hT : IsTerminal T) :
    Subsingleton (Φ.fiber.obj U) where
  allEq _ _ := Φ.fiber_map_injective_of_mono f (by
    have := Φ.uniqueFiberObj T hT
    subsingleton)

end

variable (F : A ⥤ B) [LocallySmall.{w} C] [PreservesFilteredColimitsOfSize.{w, w} F]

/--
Definition of `presheafFiberCompIso` / `presheafFiberCompIso` 的定义

English:
definition presheafFiberCompIso
  signature: :
  body: haveI := Functor.Final.preservesColimitsOfShape_of_final
    (FinallySmall.fromFilteredFinalModel.{w} (Φ.fiber.Elementsᵒᵖ)) F
  Functor.isoWhiskerLeft
    ((Functor.whiskeringLeft _ _ _).obj _) (preservesColimitNatIso F).symm

@[reassoc]

中文:
定义 presheafFiberCompIso
  签名: :
  定义体: haveI := Functor.Final.preservesColimitsOfShape_of_final
    (FinallySmall.fromFilteredFinalModel.{w} (Φ.fiber.Elementsᵒᵖ)) F
  Functor.isoWhiskerLeft
    ((Functor.whiskeringLeft _ _ _).obj _) (preservesColimitNatIso F).symm

@[reassoc]

Depends on / 依赖: FinallySmall, FinallySmall.fromFilteredFinalModel, Functor, Functor.Final.preservesColimitsOfShape_of_final, Functor.isoWhiskerLeft, Functor.whiskeringLeft, fiber.Elements, fromFilteredFinalModel, isoWhiskerLeft, preservesColimitNatIso, preservesColimitsOfShape_of_final, whiskeringLeft
-/
noncomputable def presheafFiberCompIso :
    (Functor.whiskeringRight _ _ _).obj F ⋙ Φ.presheafFiber ≅
      Φ.presheafFiber ⋙ F :=
  haveI := Functor.Final.preservesColimitsOfShape_of_final
    (FinallySmall.fromFilteredFinalModel.{w} (Φ.fiber.Elementsᵒᵖ)) F
  Functor.isoWhiskerLeft
    ((Functor.whiskeringLeft _ _ _).obj _) (preservesColimitNatIso F).symm

@[reassoc]
/--
lemma `toPresheafFiber_presheafFiberCompIso_hom_app` / 引理 `toPresheafFiber_presheafFiberCompIso_hom_app`

English:
lemma toPresheafFiber_presheafFiberCompIso_hom_app
  proof: by
  have := Functor.Final.preservesColimitsOfShape_of_final
    (FinallySmall.fromFilteredFinalModel.{w} (Φ.fiber.Elementsᵒᵖ)) F
  simp only [presheafFiberCompIso]
  exact ι_preservesColimitIso_inv F ((CategoryOfElements.π Φ.fiber).op ⋙ P) _

中文:
引理 toPresheafFiber_presheafFiberCompIso_hom_app
  证明: by
  have := Functor.Final.preservesColimitsOfShape_of_final
    (FinallySmall.fromFilteredFinalModel.{w} (Φ.fiber.Elementsᵒᵖ)) F
  simp only [presheafFiberCompIso]
  exact ι_preservesColimitIso_inv F ((CategoryOfElements.π Φ.fiber).op ⋙ P) _

Depends on / 依赖: CategoryOfElements, FinallySmall, FinallySmall.fromFilteredFinalModel, Functor, Functor.Final.preservesColimitsOfShape_of_final, fiber.Elements, fromFilteredFinalModel, preservesColimitsOfShape_of_final, presheafFiberCompIso
-/
lemma toPresheafFiber_presheafFiberCompIso_hom_app
    (X : C) (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ A) :
    Φ.toPresheafFiber X x (P ⋙ F) ≫ (Φ.presheafFiberCompIso F).hom.app P =
      F.map (Φ.toPresheafFiber X x P) := by
  have := Functor.Final.preservesColimitsOfShape_of_final
    (FinallySmall.fromFilteredFinalModel.{w} (Φ.fiber.Elementsᵒᵖ)) F
  simp only [presheafFiberCompIso]
  exact ι_preservesColimitIso_inv F ((CategoryOfElements.π Φ.fiber).op ⋙ P) _

/-- If `Φ` is a point of a site and `F : A ⥤ B` is a functor which preserves
filtered colimits, then taking fibers of sheaves at `Φ` commutes with `F`. -/
@[simps!]
/--
Definition of `sheafFiberCompIso` / `sheafFiberCompIso` 的定义

English:
definition sheafFiberCompIso
  signature: [J.HasSheafCompose F]
  body: Functor.isoWhiskerLeft (sheafToPresheaf J A) (Φ.presheafFiberCompIso F) ≪≫
    (Functor.associator _ _ _).symm

中文:
定义 sheafFiberCompIso
  签名: [J.HasSheafCompose F]
  定义体: Functor.isoWhiskerLeft (sheafToPresheaf J A) (Φ.presheafFiberCompIso F) ≪≫
    (Functor.associator _ _ _).symm

Depends on / 依赖: Functor, Functor.associator, Functor.isoWhiskerLeft, associator, isoWhiskerLeft, presheafFiberCompIso, sheafToPresheaf
-/
noncomputable def sheafFiberCompIso [J.HasSheafCompose F] :
    sheafCompose J F ⋙ Φ.sheafFiber ≅ Φ.sheafFiber ⋙ F :=
  Functor.isoWhiskerLeft (sheafToPresheaf J A) (Φ.presheafFiberCompIso F) ≪≫
    (Functor.associator _ _ _).symm

end Point

end GrothendieckTopology

end CategoryTheory
