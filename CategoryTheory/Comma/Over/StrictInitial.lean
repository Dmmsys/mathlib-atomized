/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial

/-!
# `Over X` when `C` has strict initial objects

In this file we define the canonical equivalence of `Over X` with `Discrete PUnit` when
`C` has strict initial objects. We also provide the variants for `P.Over Q X`
and the dual versions.
-/

@[expose] public section

universe w

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `C` has strict initial objects and `X` is an initial object, the category
`Over X` is equivalent to a point. -/
@[simps, pp_with_univ]
noncomputable
/--
Definition of `overEquivOfIsInitial` / `overEquivOfIsInitial` 的定义

English:
definition overEquivOfIsInitial
  signature: [HasStrictInitialObjects C] (X : C) (h : IsInitial X)
  body: Functor.star _
  inverse := Functor.fromPUnit (.mk (𝟙 X))
  unitIso := NatIso.ofComponents fun A =>
    haveI := h.isIso_to A.hom
    Over.isoMk (asIso A.hom)
  counitIso := Iso.refl _

中文:
定义 overEquivOfIsInitial
  签名: [有StrictInitialObjects C] (X : C) (h : IsInitial X)
  定义体: Functor.star _
  inverse := Functor.fromPUnit (.mk (𝟙 X))
  unitIso := NatIso.ofComponents fun A =>
    haveI := h.isIso_to A.hom
    Over.isoMk (asIso A.hom)
  counitIso := Iso.refl _

Depends on / 依赖: Functor, Functor.star
-/
def overEquivOfIsInitial [HasStrictInitialObjects C] (X : C) (h : IsInitial X) :
    Over X ≌ Discrete PUnit.{w + 1} where
  functor := Functor.star _
  inverse := Functor.fromPUnit (.mk (𝟙 X))
  unitIso := NatIso.ofComponents fun A =>
    haveI := h.isIso_to A.hom
    Over.isoMk (asIso A.hom)
  counitIso := Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `C` has strict terminal objects and `X` is a terminal object, the category
`Under X` is equivalent to a point. -/
@[simps, pp_with_univ]
noncomputable
/--
Definition of `underEquivOfIsTerminal` / `underEquivOfIsTerminal` 的定义

English:
definition underEquivOfIsTerminal
  signature: [HasStrictTerminalObjects C] (X : C) (h : IsTerminal X)
  body: Functor.star _
  inverse := Functor.fromPUnit (.mk (𝟙 X))
  counitIso := Iso.refl _
  unitIso := NatIso.ofComponents fun A =>
    haveI := h.isIso_from A.hom
    Under.isoMk (asIso A.hom).symm

中文:
定义 underEquivOfIsTerminal
  签名: [有StrictTerminalObjects C] (X : C) (h : 是终止 X)
  定义体: Functor.star _
  inverse := Functor.fromPUnit (.mk (𝟙 X))
  counitIso := Iso.refl _
  unitIso := NatIso.ofComponents fun A =>
    haveI := h.isIso_from A.hom
    Under.isoMk (asIso A.hom).symm

Depends on / 依赖: Functor, Functor.star
-/
def underEquivOfIsTerminal [HasStrictTerminalObjects C] (X : C) (h : IsTerminal X) :
    Under X ≌ Discrete PUnit.{w + 1} where
  functor := Functor.star _
  inverse := Functor.fromPUnit (.mk (𝟙 X))
  counitIso := Iso.refl _
  unitIso := NatIso.ofComponents fun A =>
    haveI := h.isIso_from A.hom
    Under.isoMk (asIso A.hom).symm

variable (P Q : MorphismProperty C) [P.ContainsIdentities] [Q.IsMultiplicative] [Q.RespectsIso]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `C` has strict initial objects and `X` is an initial object, the category
`P.Over Q X` is equivalent to a point. -/
@[simps, pp_with_univ]
noncomputable
/--
Definition of `MorphismProperty.overEquivOfIsInitial` / `MorphismProperty.overEquivOfIsInitial` 的定义

English:
definition MorphismProperty.overEquivOfIsInitial
  signature: [HasStrictInitialObjects C] (X : C) (h : IsInitial X)
  body: Functor.star _
  inverse := Functor.fromPUnit (.mk _ (𝟙 X) (P.id_mem _))
  unitIso := NatIso.ofComponents fun A =>
    haveI := h.isIso_to A.hom
    Over.isoMk (asIso A.hom)
  counitIso := Iso.refl _

中文:
定义 MorphismProperty.overEquivOfIsInitial
  签名: [有StrictInitialObjects C] (X : C) (h : IsInitial X)
  定义体: Functor.star _
  inverse := Functor.fromPUnit (.mk _ (𝟙 X) (P.id_mem _))
  unitIso := NatIso.ofComponents fun A =>
    haveI := h.isIso_to A.hom
    Over.isoMk (asIso A.hom)
  counitIso := Iso.refl _

Depends on / 依赖: Functor, Functor.star
-/
def MorphismProperty.overEquivOfIsInitial [HasStrictInitialObjects C] (X : C) (h : IsInitial X) :
    P.Over Q X ≌ Discrete PUnit.{w + 1} where
  functor := Functor.star _
  inverse := Functor.fromPUnit (.mk _ (𝟙 X) (P.id_mem _))
  unitIso := NatIso.ofComponents fun A =>
    haveI := h.isIso_to A.hom
    Over.isoMk (asIso A.hom)
  counitIso := Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/-- If `C` has strict terminal objects and `X` is a terminal object, the category
`P.Under Q X` is equivalent to a point. -/
@[simps, pp_with_univ]
noncomputable
/--
Definition of `MorphismProperty.underEquivOfIsTerminal` / `MorphismProperty.underEquivOfIsTerminal` 的定义

English:
definition MorphismProperty.underEquivOfIsTerminal
  signature: [HasStrictTerminalObjects C] (X : C)
  body: Functor.star _
  inverse := Functor.fromPUnit (.mk _ (𝟙 X) (P.id_mem _))
  counitIso := Iso.refl _
  unitIso := NatIso.ofComponents fun A =>
    haveI := h.isIso_from A.hom
    Under.isoMk (asIso A.hom).symm

中文:
定义 MorphismProperty.underEquivOfIsTerminal
  签名: [有StrictTerminalObjects C] (X : C)
  定义体: Functor.star _
  inverse := Functor.fromPUnit (.mk _ (𝟙 X) (P.id_mem _))
  counitIso := Iso.refl _
  unitIso := NatIso.ofComponents fun A =>
    haveI := h.isIso_from A.hom
    Under.isoMk (asIso A.hom).symm

Depends on / 依赖: Functor, Functor.star
-/
def MorphismProperty.underEquivOfIsTerminal [HasStrictTerminalObjects C] (X : C)
    (h : IsTerminal X) :
    P.Under Q X ≌ Discrete PUnit.{w + 1} where
  functor := Functor.star _
  inverse := Functor.fromPUnit (.mk _ (𝟙 X) (P.id_mem _))
  counitIso := Iso.refl _
  unitIso := NatIso.ofComponents fun A =>
    haveI := h.isIso_from A.hom
    Under.isoMk (asIso A.hom).symm

end CategoryTheory
