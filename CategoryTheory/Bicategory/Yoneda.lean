/-
Copyright (c) 2026 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import Mathlib.CategoryTheory.Bicategory.Opposites

/-!
# 2-Yoneda embedding

In this file we define the bicategorical Yoneda embedding.

-/

@[expose] public section

namespace CategoryTheory

open Bicategory.Opposite Opposite Pseudofunctor StrongTrans

universe w v u

namespace Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/-- Version of `Bicategory.precomposing` viewed in the bicategory `Cat`. -/
@[simps]
/--
Definition of `precomposingCat` / `precomposingCat` 的定义

English:
definition precomposingCat
  signature: (a b c : B)
  body: (precomp c f).toCatHom
  map η := NatTrans.toCatHom₂ ((precomposing a b c).map η)

中文:
定义 precomposingCat
  签名: (a b c : B)
  定义体: (precomp c f).toCatHom
  map η := NatTrans.toCatHom₂ ((precomposing a b c).map η)

Depends on / 依赖: precomp, toCatHom
-/
def precomposingCat (a b c : B) :
    (a ⟶ b) ⥤ (Cat.of (b ⟶ c) ⟶ Cat.of (a ⟶ c)) where
  obj f := (precomp c f).toCatHom
  map η := NatTrans.toCatHom₂ ((precomposing a b c).map η)

/-- Version of `Bicategory.postcomposing` viewed in the bicategory `Cat`. -/
@[simps]
/--
Definition of `postcomposingCat` / `postcomposingCat` 的定义

English:
definition postcomposingCat
  signature: (a b c : B)
  body: (postcomp a f).toCatHom
  map η := NatTrans.toCatHom₂ ((postcomposing a b c).map η)

中文:
定义 postcomposingCat
  签名: (a b c : B)
  定义体: (postcomp a f).toCatHom
  map η := NatTrans.toCatHom₂ ((postcomposing a b c).map η)

Depends on / 依赖: postcomp, toCatHom
-/
def postcomposingCat (a b c : B) : (b ⟶ c) ⥤ (Cat.of (a ⟶ b) ⟶ Cat.of (a ⟶ c)) where
  obj f := (postcomp a f).toCatHom
  map η := NatTrans.toCatHom₂ ((postcomposing a b c).map η)

set_option backward.defeqAttrib.useBackward true in
/-- Left unitor as a 2-isomorphism in `Cat`. -/
@[simps!]
/--
Definition of `leftUnitorNatIsoCat` / `leftUnitorNatIsoCat` 的定义

English:
definition leftUnitorNatIsoCat
  signature: (a b : B)
  body: Cat.Hom.isoMk NatIso.ofComponents (fun_ ·)

中文:
定义 leftUnitorNatIsoCat
  签名: (a b : B)
  定义体: Cat.Hom.isoMk NatIso.ofComponents (fun_ ·)

Depends on / 依赖: Cat.Hom.isoMk, NatIso, NatIso.ofComponents, fun_, ofComponents
-/
def leftUnitorNatIsoCat (a b : B) : (precomposingCat _ _ b).obj (𝟙 a) ≅ 𝟙 (Cat.of (a ⟶ b)) :=
Cat.Hom.isoMk NatIso.ofComponents (fun_ ·)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Right component of the associator as a 2-isomorphism in `Cat`. -/
@[simps!]
/--
Definition of `associatorNatIsoRightCat` / `associatorNatIsoRightCat` 的定义

English:
definition associatorNatIsoRightCat
  signature: {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (d : B)
  body: Cat.Hom.isoMk NatIso.ofComponents (α_ f g ·)

中文:
定义 associatorNatIsoRightCat
  签名: {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (d : B)
  定义体: Cat.Hom.isoMk NatIso.ofComponents (α_ f g ·)

Depends on / 依赖: Cat.Hom.isoMk, NatIso, NatIso.ofComponents, ofComponents
-/
def associatorNatIsoRightCat {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (d : B) :
    (precomposingCat _ _ d).obj (f ≫ g) ≅
      (precomposingCat ..).obj g ≫ (precomposingCat ..).obj f :=
Cat.Hom.isoMk NatIso.ofComponents (α_ f g ·)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Middle component of the associator as a 2-isomorphism in `Cat`. -/
@[simps!]
/--
Definition of `associatorNatIsoMiddleCat` / `associatorNatIsoMiddleCat` 的定义

English:
definition associatorNatIsoMiddleCat
  signature: {a b c d : B} (f : a ⟶ b) (h : c ⟶ d)
  body: Cat.Hom.isoMk NatIso.ofComponents (α_ f · h)

中文:
定义 associatorNatIsoMiddleCat
  签名: {a b c d : B} (f : a ⟶ b) (h : c ⟶ d)
  定义体: Cat.Hom.isoMk NatIso.ofComponents (α_ f · h)

Depends on / 依赖: Cat.Hom.isoMk, NatIso, NatIso.ofComponents, ofComponents
-/
def associatorNatIsoMiddleCat {a b c d : B} (f : a ⟶ b) (h : c ⟶ d) :
    (precomposingCat ..).obj f ≫ (postcomposingCat ..).obj h ≅
      (postcomposingCat ..).obj h ≫ (precomposingCat ..).obj f :=
Cat.Hom.isoMk NatIso.ofComponents (α_ f · h)

set_option backward.defeqAttrib.useBackward true in
/-- Right unitor as a 2-isomorphism in `Cat`. -/
@[simps!]
/--
Definition of `rightUnitorNatIsoCat` / `rightUnitorNatIsoCat` 的定义

English:
definition rightUnitorNatIsoCat
  signature: (a b : B)
  body: Cat.Hom.isoMk NatIso.ofComponents (ρ_ ·)

中文:
定义 rightUnitorNatIsoCat
  签名: (a b : B)
  定义体: Cat.Hom.isoMk NatIso.ofComponents (ρ_ ·)

Depends on / 依赖: Cat.Hom.isoMk, NatIso, NatIso.ofComponents, ofComponents
-/
def rightUnitorNatIsoCat (a b : B) : (postcomposingCat a _ _).obj (𝟙 b) ≅ 𝟙 (Cat.of (a ⟶ b)) :=
Cat.Hom.isoMk NatIso.ofComponents (ρ_ ·)

set_option backward.isDefEq.respectTransparency false in
/-- Left component of the associator as a 2-isomorphism in `Cat`. -/
@[simps!]
/--
Definition of `associatorNatIsoLeftCat` / `associatorNatIsoLeftCat` 的定义

English:
definition associatorNatIsoLeftCat
  signature: (a : B) {b c d : B} (g : b ⟶ c) (h : c ⟶ d)
  body: Cat.Hom.isoMk NatIso.ofComponents (α_ · g h)

中文:
定义 associatorNatIsoLeftCat
  签名: (a : B) {b c d : B} (g : b ⟶ c) (h : c ⟶ d)
  定义体: Cat.Hom.isoMk NatIso.ofComponents (α_ · g h)

Depends on / 依赖: Cat.Hom.isoMk, NatIso, NatIso.ofComponents, ofComponents
-/
def associatorNatIsoLeftCat (a : B) {b c d : B} (g : b ⟶ c) (h : c ⟶ d) :
    (postcomposingCat a ..).obj g ≫ (postcomposingCat ..).obj h ≅
      (postcomposingCat ..).obj (g ≫ h) :=
Cat.Hom.isoMk NatIso.ofComponents (α_ · g h)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The map on objects underlying the Yoneda embedding. It sends an object `x` to
the pseudofunctor defined by:
* Objects: `a ↦ (a ⟶ x)`
* Higher morphisms get sent to the corresponding "precomposing" operation.

This is only used for defining `yoneda`, after which `Bicategory.yoneda.obj` should be preferred. -/
@[simps!]
/--
Definition of `yoneda₀` / `yoneda₀` 的定义

English:
definition yoneda₀
  signature: (x : B)
  body: PrelaxFunctor.mkOfHomFunctors (fun y => Cat.of (unop y ⟶ x))
    (fun a b => unopFunctor a b ⋙ precomposingCat (unop b) (unop a) x)
  mapId a := leftUnitorNatIsoCat (unop a) x
  mapComp f g := associatorNatIsoRightCat g.unop f.unop x

中文:
定义 yoneda₀
  签名: (x : B)
  定义体: PrelaxFunctor.mkOfHomFunctors (fun y => Cat.of (unop y ⟶ x))
    (fun a b => unopFunctor a b ⋙ precomposingCat (unop b) (unop a) x)
  mapId a := leftUnitorNatIsoCat (unop a) x
  mapComp f g := associatorNatIsoRightCat g.unop f.unop x

Depends on / 依赖: Cat.of, PrelaxFunctor, PrelaxFunctor.mkOfHomFunctors, mkOfHomFunctors
-/
def yoneda₀ (x : B) : Pseudofunctor Bᵒᵖ Cat.{w, v} where
  toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors (fun y => Cat.of (unop y ⟶ x))
    (fun a b => unopFunctor a b ⋙ precomposingCat (unop b) (unop a) x)
  mapId a := leftUnitorNatIsoCat (unop a) x
  mapComp f g := associatorNatIsoRightCat g.unop f.unop x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Postcomposing of a 1-morphism seen as a strong transformation between pseudofunctors. -/
@[simps!]
/--
Definition of `postcomp₂` / `postcomp₂` 的定义

English:
definition postcomp₂
  signature: {a b : B} (f : a ⟶ b)
  body: (postcomposingCat (unop x) a b).obj f
  naturality g := associatorNatIsoMiddleCat g.unop f

中文:
定义 postcomp₂
  签名: {a b : B} (f : a ⟶ b)
  定义体: (postcomposingCat (unop x) a b).obj f
  naturality g := associatorNatIsoMiddleCat g.unop f

Depends on / 依赖: postcomposingCat
-/
def postcomp₂ {a b : B} (f : a ⟶ b) : yoneda₀ a ⟶ yoneda₀ b where
  app x := (postcomposingCat (unop x) a b).obj f
  naturality g := associatorNatIsoMiddleCat g.unop f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Postcomposing of `1`-morphisms seen as a functor from `a ⟶ b` to the hom-category of the
corresponding pseudofunctors.

This is an implementation detail, and `Bicategory.yoneda.map` should be preferred. -/
@[simps!]
/--
Definition of `postcomposing₂` / `postcomposing₂` 的定义

English:
definition postcomposing₂
  signature: (a b : B)
  body: postcomp₂
  map η := { as := { app x := (postcomposingCat (unop x) a b).map η } }

中文:
定义 postcomposing₂
  签名: (a b : B)
  定义体: postcomp₂
  map η := { as := { app x := (postcomposingCat (unop x) a b).map η } }
-/
def postcomposing₂ (a b : B) : (a ⟶ b) ⥤ (yoneda₀ a ⟶ yoneda₀ b) where
  obj := postcomp₂
  map η := { as := { app x := (postcomposingCat (unop x) a b).map η } }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Yoneda pseudofunctor from `B` to `Bᵒᵖ ⥤ᵖ Cat`.

It consists of the following:
* On objects: sends `x : B` to the pseudofunctor `Bᵒᵖ ⥤ᵖ Cat` given by
  `a ↦ (a ⟶ x)` on objects and on 1- and 2-morphisms given by "precomposing"
* On 1- and 2-morphisms it is given by "postcomposing" -/
@[simps!]
/--
Definition of `yoneda` / `yoneda` 的定义

English:
definition yoneda
  signature: : B ⥤ᵖ Bᵒᵖ ⥤ᵖ Cat.{w, v} where
  body: PrelaxFunctor.mkOfHomFunctors (yoneda₀ ·) postcomposing₂
  mapId a := isoMk (fun b => rightUnitorNatIsoCat (unop b) a)
  mapComp f g := (isoMk (fun b => associatorNatIsoLeftCat (unop b) f g)).symm

中文:
定义 yoneda
  签名: : B ⥤ᵖ Bᵒᵖ ⥤ᵖ Cat.{w, v} where
  定义体: PrelaxFunctor.mkOfHomFunctors (yoneda₀ ·) postcomposing₂
  mapId a := isoMk (fun b => rightUnitorNatIsoCat (unop b) a)
  mapComp f g := (isoMk (fun b => associatorNatIsoLeftCat (unop b) f g)).symm

Depends on / 依赖: PrelaxFunctor, PrelaxFunctor.mkOfHomFunctors, mkOfHomFunctors
-/
def yoneda : B ⥤ᵖ Bᵒᵖ ⥤ᵖ Cat.{w, v} where
  toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors (yoneda₀ ·) postcomposing₂
  mapId a := isoMk (fun b => rightUnitorNatIsoCat (unop b) a)
  mapComp f g := (isoMk (fun b => associatorNatIsoLeftCat (unop b) f g)).symm

end Bicategory

end CategoryTheory
