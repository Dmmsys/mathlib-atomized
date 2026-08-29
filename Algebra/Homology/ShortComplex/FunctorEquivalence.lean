/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Basic

/-!
# Short complexes in functor categories

In this file, it is shown that if `J` and `C` are two categories (such
that `C` has zero morphisms), then there is an equivalence of categories
`ShortComplex.functorEquivalence J C : ShortComplex (J ⥤ C) ≌ J ⥤ ShortComplex C`.

-/

@[expose] public section

namespace CategoryTheory

open Limits CategoryTheory.Functor

variable (J C : Type*) [Category* J] [Category* C] [HasZeroMorphisms C]

namespace ShortComplex

namespace FunctorEquivalence

attribute [local simp] ShortComplex.Hom.comm₁₂ ShortComplex.Hom.comm₂₃

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The obvious functor `ShortComplex (J ⥤ C) ⥤ J ⥤ ShortComplex C`. -/
@[simps]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : ShortComplex (J ⥤ C) ⥤ J ⥤ ShortComplex C where
  body: { obj := fun j => S.map ((evaluation J C).obj j)
      map := fun f => S.mapNatTrans ((evaluation J C).map f) }
  map φ :=
    { app := fun j => ((evaluation J C).obj j).mapShortComplex.map φ }

中文:
定义 functor
  签名: : ShortComplex (J ⥤ C) ⥤ J ⥤ ShortComplex C where
  定义体: { obj := fun j => S.map ((evaluation J C).obj j)
      map := fun f => S.mapNatTrans ((evaluation J C).map f) }
  map φ :=
    { app := fun j => ((evaluation J C).obj j).mapShortComplex.map φ }

Depends on / 依赖: S.map, S.mapNatTrans, evaluation, inv_hom_id, mapNatTrans, mapShortComplex, mapShortComplex.map
-/
def functor : ShortComplex (J ⥤ C) ⥤ J ⥤ ShortComplex C where
  obj S :=
    { obj := fun j => S.map ((evaluation J C).obj j)
      map := fun f => S.mapNatTrans ((evaluation J C).map f) }
  map φ :=
    { app := fun j => ((evaluation J C).obj j).mapShortComplex.map φ }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The obvious functor `(J ⥤ ShortComplex C) ⥤ ShortComplex (J ⥤ C)`. -/
@[simps]
/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: : (J ⥤ ShortComplex C) ⥤ ShortComplex (J ⥤ C) where
  body: { f := whiskerLeft F π₁Toπ₂
      g := whiskerLeft F π₂Toπ₃
      zero := by cat_disch }
  map φ := Hom.mk (whiskerRight φ π₁) (whiskerRight φ π₂) (whiskerRight φ π₃)
    (by cat_disch) (by cat_disch)

中文:
定义 inverse
  签名: : (J ⥤ ShortComplex C) ⥤ ShortComplex (J ⥤ C) where
  定义体: { f := whiskerLeft F π₁Toπ₂
      g := whiskerLeft F π₂Toπ₃
      zero := by cat_disch }
  map φ := Hom.mk (whiskerRight φ π₁) (whiskerRight φ π₂) (whiskerRight φ π₃)
    (by cat_disch) (by cat_disch)

Depends on / 依赖: Hom.mk, cat_disch, whiskerLeft, whiskerRight
-/
def inverse : (J ⥤ ShortComplex C) ⥤ ShortComplex (J ⥤ C) where
  obj F :=
    { f := whiskerLeft F π₁Toπ₂
      g := whiskerLeft F π₂Toπ₃
      zero := by cat_disch }
  map φ := Hom.mk (whiskerRight φ π₁) (whiskerRight φ π₂) (whiskerRight φ π₃)
    (by cat_disch) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The unit isomorphism of the equivalence
`ShortComplex.functorEquivalence : ShortComplex (J ⥤ C) ≌ J ⥤ ShortComplex C`. -/
@[simps!]
/--
Definition of `unitIso` / `unitIso` 的定义

English:
definition unitIso
  signature: : 𝟭 _ ≅ functor J C ⋙ inverse J C
  body: NatIso.ofComponents (fun _ => isoMk
    (NatIso.ofComponents (fun _ => Iso.refl _) (by simp))
    (NatIso.ofComponents (fun _ => Iso.refl _) (by simp))
    (NatIso.ofComponents (fun _ => Iso.refl _) (by simp))
    (by cat_disch) (by cat_disch)) (by cat_disch)

中文:
定义 unitIso
  签名: : 𝟭 _ ≅ functor J C ⋙ inverse J C
  定义体: NatIso.ofComponents (fun _ => isoMk
    (NatIso.ofComponents (fun _ => Iso.refl _) (by simp))
    (NatIso.ofComponents (fun _ => Iso.refl _) (by simp))
    (NatIso.ofComponents (fun _ => Iso.refl _) (by simp))
    (by cat_disch) (by cat_disch)) (by cat_disch)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, cat_disch, ofComponents
-/
def unitIso : 𝟭 _ ≅ functor J C ⋙ inverse J C :=
  NatIso.ofComponents (fun _ => isoMk
    (NatIso.ofComponents (fun _ => Iso.refl _) (by simp))
    (NatIso.ofComponents (fun _ => Iso.refl _) (by simp))
    (NatIso.ofComponents (fun _ => Iso.refl _) (by simp))
    (by cat_disch) (by cat_disch)) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The counit isomorphism of the equivalence
`ShortComplex.functorEquivalence : ShortComplex (J ⥤ C) ≌ J ⥤ ShortComplex C`. -/
@[simps!]
/--
Definition of `counitIso` / `counitIso` 的定义

English:
definition counitIso
  signature: : inverse J C ⋙ functor J C ≅ 𝟭 _
  body: NatIso.ofComponents (fun _ => NatIso.ofComponents
    (fun _ => isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp)) (by cat_disch)) (by cat_disch)

中文:
定义 counitIso
  签名: : inverse J C ⋙ functor J C ≅ 𝟭 _
  定义体: NatIso.ofComponents (fun _ => NatIso.ofComponents
    (fun _ => isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp)) (by cat_disch)) (by cat_disch)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, cat_disch, ofComponents
-/
def counitIso : inverse J C ⋙ functor J C ≅ 𝟭 _ :=
  NatIso.ofComponents (fun _ => NatIso.ofComponents
    (fun _ => isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp)) (by cat_disch)) (by cat_disch)

end FunctorEquivalence

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The obvious equivalence `ShortComplex (J ⥤ C) ≌ J ⥤ ShortComplex C`. -/
@[simps]
/--
Definition of `functorEquivalence` / `functorEquivalence` 的定义

English:
definition functorEquivalence
  signature: : ShortComplex (J ⥤ C) ≌ J ⥤ ShortComplex C where
  body: FunctorEquivalence.functor J C
  inverse := FunctorEquivalence.inverse J C
  unitIso := FunctorEquivalence.unitIso J C
  counitIso := FunctorEquivalence.counitIso J C

中文:
定义 functorEquivalence
  签名: : ShortComplex (J ⥤ C) ≌ J ⥤ ShortComplex C where
  定义体: FunctorEquivalence.functor J C
  inverse := FunctorEquivalence.inverse J C
  unitIso := FunctorEquivalence.unitIso J C
  counitIso := FunctorEquivalence.counitIso J C

Depends on / 依赖: FunctorEquivalence, FunctorEquivalence.functor, functor, inv_hom_id
-/
def functorEquivalence : ShortComplex (J ⥤ C) ≌ J ⥤ ShortComplex C where
  functor := FunctorEquivalence.functor J C
  inverse := FunctorEquivalence.inverse J C
  unitIso := FunctorEquivalence.unitIso J C
  counitIso := FunctorEquivalence.counitIso J C

end ShortComplex

end CategoryTheory
