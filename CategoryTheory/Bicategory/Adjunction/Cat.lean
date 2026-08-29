/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj

/-!
# Adjunctions in `Cat`

We show that adjunctions in the bicategory `Cat` correspond to
adjunctions between functors in the usual categorical sense.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Bicategory

section

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  {F' : D ⥤ E} {G' : E ⥤ D} (adj' : F' ⊣ G')

namespace Adjunction

attribute [local simp] bicategoricalComp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The adjunction in the bicategorical sense attached to an adjunction between functors. -/
@[simps]
/--
Definition of `toCat` / `toCat` 的定义

English:
definition toCat
  signature: : Bicategory.Adjunction F.toCatHom G.toCatHom where
  body: .ofNatTrans adj.unit
  counit := .ofNatTrans adj.counit

中文:
定义 toCat
  签名: : 双范畴.伴随 F.toCatHom G.toCatHom where
  定义体: .ofNatTrans adj.unit
  counit := .ofNatTrans adj.counit

Depends on / 依赖: adj.unit, ofNatTrans, of_hComp
-/
def toCat : Bicategory.Adjunction F.toCatHom G.toCatHom where
  unit := .ofNatTrans adj.unit
  counit := .ofNatTrans adj.counit

set_option backward.defeqAttrib.useBackward true in
/-- The adjunction of functors corresponding to an adjunction in the bicategory `Cat`. -/
@[simps]
/--
Definition of `ofCat` / `ofCat` 的定义

English:
definition ofCat
  signature: {C D : Cat} {F : C ⟶ D} {G : D ⟶ C}
  body: adj.unit.toNatTrans
  counit := adj.counit.toNatTrans
  left_triangle_components X := by
    simpa using congr($(adj.left_triangle).toNatTrans.app X)
  right_triangle_components X := by
    simpa using congr($(adj.right_triangle).toNatTrans.app X)

@[simp]

中文:
定义 ofCat
  签名: {C D : Cat} {F : C ⟶ D} {G : D ⟶ C}
  定义体: adj.unit.toNatTrans
  counit := adj.counit.toNatTrans
  left_triangle_components X := by
    simpa using congr($(adj.left_triangle).toNatTrans.app X)
  right_triangle_components X := by
    simpa using congr($(adj.right_triangle).toNatTrans.app X)

@[simp]

Depends on / 依赖: adj.unit.toNatTrans, toNatTrans
-/
def ofCat {C D : Cat} {F : C ⟶ D} {G : D ⟶ C}
    (adj : Bicategory.Adjunction F G) :
    F.toFunctor ⊣ G.toFunctor where
  unit := adj.unit.toNatTrans
  counit := adj.counit.toNatTrans
  left_triangle_components X := by
    simpa using congr($(adj.left_triangle).toNatTrans.app X)
  right_triangle_components X := by
    simpa using congr($(adj.right_triangle).toNatTrans.app X)

@[simp]
/--
lemma `toCat_ofCat` / 引理 `toCat_ofCat`

English:
lemma toCat_ofCat
  proof: rfl

@[simp]

中文:
引理 toCat_ofCat
  证明: rfl

@[simp]

Depends on / 依赖: TwoSquare, TwoSquare.hComp, hComp_iff_of_equivalences, whiskerHorizontal_iff
-/
lemma toCat_ofCat
    {C D : Cat} {F : C ⟶ D} {G : D ⟶ C} (adj : Bicategory.Adjunction F G) :
    (Adjunction.ofCat adj).toCat = adj := rfl

@[simp]
/--
lemma `ofCat_toCat` / 引理 `ofCat_toCat`

English:
lemma ofCat_toCat
  proof: rfl

中文:
引理 ofCat_toCat
  证明: rfl
-/
lemma ofCat_toCat :
    Adjunction.ofCat adj.toCat = adj := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `toCat_comp_toCat` / 引理 `toCat_comp_toCat`

English:
lemma toCat_comp_toCat
  statement: adj.toCat.comp adj'.toCat = (adj.comp adj').toCat
  proof: by
  cat_disch

中文:
引理 toCat_comp_toCat
  结论: adj.toCat.comp adj'.toCat = (adj.comp adj').toCat
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma toCat_comp_toCat : adj.toCat.comp adj'.toCat = (adj.comp adj').toCat := by
  cat_disch

end Adjunction

end

namespace Bicategory

@[simp]
/--
lemma `Adjunction.ofCat_id` / 引理 `Adjunction.ofCat_id`

English:
lemma Adjunction.ofCat_id
  given: (C : Cat.{v, u})
  proof: rfl

中文:
引理 伴随.ofCat_id
  条件: (C : Cat.{v, u})
  证明: rfl
-/
lemma Adjunction.ofCat_id (C : Cat.{v, u}) :
    Adjunction.ofCat (Adjunction.id C) = CategoryTheory.Adjunction.id :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `Adjunction.ofCat_comp` / 引理 `Adjunction.ofCat_comp`

English:
lemma Adjunction.ofCat_comp
  statement: {C D E : Cat.{v, u}}
  proof: by
  ext
  simp [bicategoricalComp]

中文:
引理 伴随.ofCat_comp
  结论: {C D E : Cat.{v, u}}
  证明: by
  ext
  simp [bicategoricalComp]

Depends on / 依赖: bicategoricalComp
-/
lemma Adjunction.ofCat_comp {C D E : Cat.{v, u}}
    {F : C ⟶ D} {G : D ⟶ C} (adj : F ⊣ G)
    {F' : D ⟶ E} {G' : E ⟶ D} (adj' : F' ⊣ G') :
    Adjunction.ofCat (adj.comp adj') = (Adjunction.ofCat adj).comp (Adjunction.ofCat adj') := by
  ext
  simp [bicategoricalComp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `toNatTrans_mateEquiv` / 引理 `toNatTrans_mateEquiv`

English:
lemma toNatTrans_mateEquiv
  statement: {C D E F : Cat}
  proof: by
  ext X
  simp [mateEquiv, Adjunction.homEquiv₁, Adjunction.homEquiv₂]

中文:
引理 to自然数Trans_mateEquiv
  结论: {C D E F : Cat}
  证明: by
  ext X
  simp [mateEquiv, Adjunction.homEquiv₁, Adjunction.homEquiv₂]

Depends on / 依赖: Adjunction, Adjunction.homEquiv, mateEquiv
-/
lemma toNatTrans_mateEquiv {C D E F : Cat}
    {G : C ⟶ E} {H : D ⟶ F} {L₁ : C ⟶ D} {R₁ : D ⟶ C} {L₂ : E ⟶ F} {R₂ : F ⟶ E}
    (adj₁ : Bicategory.Adjunction L₁ R₁) (adj₂ : Bicategory.Adjunction L₂ R₂)
    (f : G ≫ L₂ ⟶ L₁ ≫ H) :
    (Bicategory.mateEquiv adj₁ adj₂ f).toNatTrans =
      CategoryTheory.mateEquiv (Adjunction.ofCat adj₁) (Adjunction.ofCat adj₂) f.toNatTrans := by
  ext X
  simp [mateEquiv, Adjunction.homEquiv₁, Adjunction.homEquiv₂]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `toNatTrans_conjugateEquiv` / 引理 `toNatTrans_conjugateEquiv`

English:
lemma toNatTrans_conjugateEquiv
  statement: {C D : Cat}
  proof: by
  dsimp [Bicategory.conjugateEquiv]
  rw [toNatTrans_mateEquiv]
  ext X
  simp [CategoryTheory.conjugateEquiv]

中文:
引理 to自然数Trans_conjugateEquiv
  结论: {C D : Cat}
  证明: by
  dsimp [Bicategory.conjugateEquiv]
  rw [toNatTrans_mateEquiv]
  ext X
  simp [CategoryTheory.conjugateEquiv]

Depends on / 依赖: Bicategory, Bicategory.conjugateEquiv, CategoryTheory, CategoryTheory.conjugateEquiv, conjugateEquiv, toNatTrans_mateEquiv
-/
lemma toNatTrans_conjugateEquiv {C D : Cat}
    {L₁ L₂ : C ⟶ D} {R₁ R₂ : D ⟶ C}
    (adj₁ : Bicategory.Adjunction L₁ R₁) (adj₂ : Bicategory.Adjunction L₂ R₂) (f : L₂ ⟶ L₁) :
    (Bicategory.conjugateEquiv adj₁ adj₂ f).toNatTrans =
      CategoryTheory.conjugateEquiv
        (Adjunction.ofCat adj₁) (Adjunction.ofCat adj₂) f.toNatTrans := by
  dsimp [Bicategory.conjugateEquiv]
  rw [toNatTrans_mateEquiv]
  ext X
  simp [CategoryTheory.conjugateEquiv]

namespace Adj

variable {C₁ C₂ : Adj Cat.{v, u}} (α : C₁ ⟶ C₂)

@[reassoc (attr := simp)]
/--
lemma `left_triangle_components` / 引理 `left_triangle_components`

English:
lemma left_triangle_components
  given: (X : C₁.obj)
  proof: (Adjunction.ofCat α.adj).left_triangle_components _

@[reassoc (attr := simp)]

中文:
引理 left_triangle_components
  条件: (X : C₁.obj)
  证明: (Adjunction.ofCat α.adj).left_triangle_components _

@[reassoc (attr := simp)]

Depends on / 依赖: Adjunction, Adjunction.ofCat, left_triangle_components
-/
lemma left_triangle_components (X : C₁.obj) :
    α.l.toFunctor.map (α.adj.unit.toNatTrans.app X) ≫
      α.adj.counit.toNatTrans.app (α.l.toFunctor.obj X) =
    𝟙 (α.l.toFunctor.obj X) :=
  (Adjunction.ofCat α.adj).left_triangle_components _

@[reassoc (attr := simp)]
/--
lemma `right_triangle_components` / 引理 `right_triangle_components`

English:
lemma right_triangle_components
  given: (X : C₂.obj)
  proof: (Adjunction.ofCat α.adj).right_triangle_components _

#adaptation_note

中文:
引理 right_triangle_components
  条件: (X : C₂.obj)
  证明: (Adjunction.ofCat α.adj).right_triangle_components _

#adaptation_note

Depends on / 依赖: Adjunction, Adjunction.ofCat, right_triangle_components
-/
lemma right_triangle_components (X : C₂.obj) :
    α.adj.unit.toNatTrans.app (α.r.toFunctor.obj X) ≫
       α.r.toFunctor.map (α.adj.counit.toNatTrans.app X) =
    𝟙 (α.r.toFunctor.obj X) :=
  (Adjunction.ofCat α.adj).right_triangle_components _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `unit_naturality` / 引理 `unit_naturality`

English:
lemma unit_naturality
  given: {X Y : C₁.obj} (f : X ⟶ Y)
  proof: (Adjunction.ofCat α.adj).unit_naturality f

#adaptation_note

中文:
引理 unit_naturality
  条件: {X Y : C₁.obj} (f : X ⟶ Y)
  证明: (Adjunction.ofCat α.adj).unit_naturality f

#adaptation_note

Depends on / 依赖: Adjunction, Adjunction.ofCat, unit_naturality
-/
lemma unit_naturality {X Y : C₁.obj} (f : X ⟶ Y) :
    α.adj.unit.toNatTrans.app X ≫ α.r.toFunctor.map (α.l.toFunctor.map f) =
    f ≫ α.adj.unit.toNatTrans.app Y :=
  (Adjunction.ofCat α.adj).unit_naturality f

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `counit_naturality` / 引理 `counit_naturality`

English:
lemma counit_naturality
  given: {X Y : C₂.obj} (f : X ⟶ Y)
  proof: (Adjunction.ofCat α.adj).counit_naturality f

中文:
引理 counit_naturality
  条件: {X Y : C₂.obj} (f : X ⟶ Y)
  证明: (Adjunction.ofCat α.adj).counit_naturality f

Depends on / 依赖: Adjunction, Adjunction.ofCat, counit_naturality
-/
lemma counit_naturality {X Y : C₂.obj} (f : X ⟶ Y) :
    α.l.toFunctor.map (α.r.toFunctor.map f) ≫ α.adj.counit.toNatTrans.app Y =
      α.adj.counit.toNatTrans.app X ≫ f :=
  (Adjunction.ofCat α.adj).counit_naturality f

end Adj

end Bicategory

end CategoryTheory
