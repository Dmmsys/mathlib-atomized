/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Read, Andrew Yang, Dagur Asgeirsson, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
/-!

# Uniqueness of adjoints

This file shows that adjoints are unique up to natural isomorphism.

## Main results

* `Adjunction.leftAdjointUniq` : If `F` and `F'` are both left adjoint to `G`, then they are
  naturally isomorphic.

* `Adjunction.rightAdjointUniq` : If `G` and `G'` are both right adjoint to `F`, then they are
  naturally isomorphic.

-/

@[expose] public section

open CategoryTheory Functor

variable {C D : Type*} [Category* C] [Category* D]

namespace CategoryTheory.Adjunction

attribute [local simp] homEquiv_unit homEquiv_counit

/--
Definition of `leftAdjointUniq` / `leftAdjointUniq` 的定义

English:
definition leftAdjointUniq
  signature: {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
  body: ((conjugateIsoEquiv adj1 adj2).symm (Iso.refl G)).symm

中文:
定义 leftAdjointUniq
  签名: {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
  定义体: ((conjugateIsoEquiv adj1 adj2).symm (Iso.refl G)).symm

Depends on / 依赖: Iso.refl, conjugateIsoEquiv
-/
def leftAdjointUniq {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) : F ≅ F' :=
  ((conjugateIsoEquiv adj1 adj2).symm (Iso.refl G)).symm

set_option backward.defeqAttrib.useBackward true in
/--
theorem `homEquiv_leftAdjointUniq_hom_app` / 定理 `homEquiv_leftAdjointUniq_hom_app`

English:
theorem homEquiv_leftAdjointUniq_hom_app
  statement: {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
  proof: by
  simp [leftAdjointUniq]

中文:
定理 homEquiv_leftAdjointUniq_hom_app
  结论: {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
  证明: by
  simp [leftAdjointUniq]

Depends on / 依赖: leftAdjointUniq
-/
theorem homEquiv_leftAdjointUniq_hom_app {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    (x : C) : adj1.homEquiv _ _ ((leftAdjointUniq adj1 adj2).hom.app x) = adj2.unit.app x := by
  simp [leftAdjointUniq]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
theorem `unit_leftAdjointUniq_hom` / 定理 `unit_leftAdjointUniq_hom`

English:
theorem unit_leftAdjointUniq_hom
  given: {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
  proof: by
  ext x
  rw [NatTrans.comp_app]; rw [← homEquiv_leftAdjointUniq_hom_app adj1 adj2]
  simp

@[reassoc (attr := simp)]

中文:
定理 unit_leftAdjointUniq_hom
  条件: {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
  证明: by
  ext x
  rw [NatTrans.comp_app]; rw [← homEquiv_leftAdjointUniq_hom_app adj1 adj2]
  simp

@[reassoc (attr := simp)]

Depends on / 依赖: NatTrans, NatTrans.comp_app, comp_app, homEquiv_leftAdjointUniq_hom_app
-/
theorem unit_leftAdjointUniq_hom {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) :
    adj1.unit ≫ whiskerRight (leftAdjointUniq adj1 adj2).hom G = adj2.unit := by
  ext x
  rw [NatTrans.comp_app]; rw [← homEquiv_leftAdjointUniq_hom_app adj1 adj2]
  simp

@[reassoc (attr := simp)]
/--
theorem `unit_leftAdjointUniq_hom_app` / 定理 `unit_leftAdjointUniq_hom_app`

English:
theorem unit_leftAdjointUniq_hom_app
  proof: by
  rw [← unit_leftAdjointUniq_hom adj1 adj2]; rfl

中文:
定理 unit_leftAdjointUniq_hom_app
  证明: by
  rw [← unit_leftAdjointUniq_hom adj1 adj2]; rfl

Depends on / 依赖: unit_leftAdjointUniq_hom
-/
theorem unit_leftAdjointUniq_hom_app
    {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (x : C) :
    adj1.unit.app x ≫ G.map ((leftAdjointUniq adj1 adj2).hom.app x) = adj2.unit.app x := by
  rw [← unit_leftAdjointUniq_hom adj1 adj2]; rfl

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
theorem `leftAdjointUniq_hom_counit` / 定理 `leftAdjointUniq_hom_counit`

English:
theorem leftAdjointUniq_hom_counit
  given: {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
  proof: by
  ext x
  simp only [Functor.comp_obj, Functor.id_obj, leftAdjointUniq, Iso.symm_hom,
    conjugateIsoEquiv_symm_apply_inv, Iso.refl_inv, NatTrans.comp_app, whiskerLeft_app,
    conjugateEquiv_symm_apply_app, NatTrans.id_app, Functor.map_id, Category.id_comp,
    Category.assoc]
  rw [← adj1.coun

中文:
定理 leftAdjointUniq_hom_counit
  条件: {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
  证明: by
  ext x
  simp only [Functor.comp_obj, Functor.id_obj, leftAdjointUniq, Iso.symm_hom,
    conjugateIsoEquiv_symm_apply_inv, Iso.refl_inv, NatTrans.comp_app, whiskerLeft_app,
    conjugateEquiv_symm_apply_app, NatTrans.id_app, Functor.map_id, Category.id_comp,
    Category.assoc]
  rw [← adj1.coun

Depends on / 依赖: Category, Category.assoc, Category.id_comp, F.map_comp, Functor, Functor.comp_obj, Functor.id_obj, Functor.map_id, Iso.refl_inv, Iso.symm_hom, NatTrans, NatTrans.comp_app, NatTrans.id_app, adj1.counit_naturality, comp_app, comp_obj, conjugateEquiv_symm_apply_app, conjugateIsoEquiv_symm_apply_inv, counit_naturality, id_app
-/
theorem leftAdjointUniq_hom_counit {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) :
    whiskerLeft G (leftAdjointUniq adj1 adj2).hom ≫ adj2.counit = adj1.counit := by
  ext x
  simp only [Functor.comp_obj, Functor.id_obj, leftAdjointUniq, Iso.symm_hom,
    conjugateIsoEquiv_symm_apply_inv, Iso.refl_inv, NatTrans.comp_app, whiskerLeft_app,
    conjugateEquiv_symm_apply_app, NatTrans.id_app, Functor.map_id, Category.id_comp,
    Category.assoc]
  rw [← adj1.counit_naturality]; rw [← Category.assoc]; rw [← F.map_comp]
  simp

@[reassoc (attr := simp)]
/--
theorem `leftAdjointUniq_hom_app_counit` / 定理 `leftAdjointUniq_hom_app_counit`

English:
theorem leftAdjointUniq_hom_app_counit
  statement: {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
  proof: by
  rw [← leftAdjointUniq_hom_counit adj1 adj2]
  rfl

中文:
定理 leftAdjointUniq_hom_app_counit
  结论: {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
  证明: by
  rw [← leftAdjointUniq_hom_counit adj1 adj2]
  rfl

Depends on / 依赖: leftAdjointUniq_hom_counit
-/
theorem leftAdjointUniq_hom_app_counit {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    (x : D) :
    (leftAdjointUniq adj1 adj2).hom.app (G.obj x) ≫ adj2.counit.app x = adj1.counit.app x := by
  rw [← leftAdjointUniq_hom_counit adj1 adj2]
  rfl

/--
theorem `leftAdjointUniq_inv_app` / 定理 `leftAdjointUniq_inv_app`

English:
theorem leftAdjointUniq_inv_app
  given: {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (x : C)
  proof: rfl

@[reassoc (attr := simp)]

中文:
定理 leftAdjointUniq_inv_app
  条件: {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (x : C)
  证明: rfl

@[reassoc (attr := simp)]
-/
theorem leftAdjointUniq_inv_app {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (x : C) :
    (leftAdjointUniq adj1 adj2).inv.app x = (leftAdjointUniq adj2 adj1).hom.app x :=
  rfl

@[reassoc (attr := simp)]
/--
theorem `leftAdjointUniq_trans` / 定理 `leftAdjointUniq_trans`

English:
theorem leftAdjointUniq_trans
  statement: {F F' F'' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
  proof: by
  simp [leftAdjointUniq]

@[reassoc (attr := simp)]

中文:
定理 leftAdjointUniq_trans
  结论: {F F' F'' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
  证明: by
  simp [leftAdjointUniq]

@[reassoc (attr := simp)]

Depends on / 依赖: leftAdjointUniq
-/
theorem leftAdjointUniq_trans {F F' F'' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    (adj3 : F'' ⊣ G) :
    (leftAdjointUniq adj1 adj2).hom ≫ (leftAdjointUniq adj2 adj3).hom =
      (leftAdjointUniq adj1 adj3).hom := by
  simp [leftAdjointUniq]

@[reassoc (attr := simp)]
/--
theorem `leftAdjointUniq_trans_app` / 定理 `leftAdjointUniq_trans_app`

English:
theorem leftAdjointUniq_trans_app
  statement: {F F' F'' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
  proof: by
  rw [← leftAdjointUniq_trans adj1 adj2 adj3]
  rfl

@[simp]

中文:
定理 leftAdjointUniq_trans_app
  结论: {F F' F'' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
  证明: by
  rw [← leftAdjointUniq_trans adj1 adj2 adj3]
  rfl

@[simp]

Depends on / 依赖: leftAdjointUniq_trans
-/
theorem leftAdjointUniq_trans_app {F F' F'' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    (adj3 : F'' ⊣ G) (x : C) :
    (leftAdjointUniq adj1 adj2).hom.app x ≫ (leftAdjointUniq adj2 adj3).hom.app x =
      (leftAdjointUniq adj1 adj3).hom.app x := by
  rw [← leftAdjointUniq_trans adj1 adj2 adj3]
  rfl

@[simp]
/--
theorem `leftAdjointUniq_refl` / 定理 `leftAdjointUniq_refl`

English:
theorem leftAdjointUniq_refl
  given: {F : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G)
  proof: by
  simp [leftAdjointUniq]

中文:
定理 leftAdjointUniq_refl
  条件: {F : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G)
  证明: by
  simp [leftAdjointUniq]

Depends on / 依赖: leftAdjointUniq
-/
theorem leftAdjointUniq_refl {F : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) :
    (leftAdjointUniq adj1 adj1).hom = 𝟙 _ := by
  simp [leftAdjointUniq]

/--
Definition of `rightAdjointUniq` / `rightAdjointUniq` 的定义

English:
definition rightAdjointUniq
  signature: {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
  body: conjugateIsoEquiv adj1 adj2 (Iso.refl _)

中文:
定义 rightAdjointUniq
  签名: {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
  定义体: conjugateIsoEquiv adj1 adj2 (Iso.refl _)

Depends on / 依赖: Iso.refl, conjugateIsoEquiv
-/
def rightAdjointUniq {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') : G ≅ G' :=
  conjugateIsoEquiv adj1 adj2 (Iso.refl _)

/--
theorem `homEquiv_symm_rightAdjointUniq_hom_app` / 定理 `homEquiv_symm_rightAdjointUniq_hom_app`

English:
theorem homEquiv_symm_rightAdjointUniq_hom_app
  statement: {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G)
  proof: by
  simp [rightAdjointUniq]

中文:
定理 homEquiv_symm_rightAdjointUniq_hom_app
  结论: {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G)
  证明: by
  simp [rightAdjointUniq]

Depends on / 依赖: rightAdjointUniq
-/
theorem homEquiv_symm_rightAdjointUniq_hom_app {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G)
    (adj2 : F ⊣ G') (x : D) :
    (adj2.homEquiv _ _).symm ((rightAdjointUniq adj1 adj2).hom.app x) = adj1.counit.app x := by
  simp [rightAdjointUniq]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
theorem `unit_rightAdjointUniq_hom_app` / 定理 `unit_rightAdjointUniq_hom_app`

English:
theorem unit_rightAdjointUniq_hom_app
  statement: {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
  proof: by
  simp only [Functor.id_obj, Functor.comp_obj, rightAdjointUniq, conjugateIsoEquiv_apply_hom,
    Iso.refl_hom, conjugateEquiv_apply_app, NatTrans.id_app, Functor.map_id, Category.id_comp]
  rw [← adj2.unit_naturality_assoc]; rw [← G'.map_comp]
  simp

@[reassoc (attr := simp)]

中文:
定理 unit_rightAdjointUniq_hom_app
  结论: {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
  证明: by
  simp only [Functor.id_obj, Functor.comp_obj, rightAdjointUniq, conjugateIsoEquiv_apply_hom,
    Iso.refl_hom, conjugateEquiv_apply_app, NatTrans.id_app, Functor.map_id, Category.id_comp]
  rw [← adj2.unit_naturality_assoc]; rw [← G'.map_comp]
  simp

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.id_comp, Functor, Functor.comp_obj, Functor.id_obj, Functor.map_id, Iso.refl_hom, NatTrans, NatTrans.id_app, adj2.unit_naturality_assoc, comp_obj, conjugateEquiv_apply_app, conjugateIsoEquiv_apply_hom, id_app, id_comp, id_obj, map_comp, map_id, refl_hom, rightAdjointUniq
-/
theorem unit_rightAdjointUniq_hom_app {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
    (x : C) : adj1.unit.app x ≫ (rightAdjointUniq adj1 adj2).hom.app (F.obj x) =
      adj2.unit.app x := by
  simp only [Functor.id_obj, Functor.comp_obj, rightAdjointUniq, conjugateIsoEquiv_apply_hom,
    Iso.refl_hom, conjugateEquiv_apply_app, NatTrans.id_app, Functor.map_id, Category.id_comp]
  rw [← adj2.unit_naturality_assoc]; rw [← G'.map_comp]
  simp

@[reassoc (attr := simp)]
/--
theorem `unit_rightAdjointUniq_hom` / 定理 `unit_rightAdjointUniq_hom`

English:
theorem unit_rightAdjointUniq_hom
  given: {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
  proof: by
  ext x
  simp

@[reassoc (attr := simp)]

中文:
定理 unit_rightAdjointUniq_hom
  条件: {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
  证明: by
  ext x
  simp

@[reassoc (attr := simp)]
-/
theorem unit_rightAdjointUniq_hom {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') :
    adj1.unit ≫ whiskerLeft F (rightAdjointUniq adj1 adj2).hom = adj2.unit := by
  ext x
  simp

@[reassoc (attr := simp)]
/--
theorem `rightAdjointUniq_hom_app_counit` / 定理 `rightAdjointUniq_hom_app_counit`

English:
theorem rightAdjointUniq_hom_app_counit
  statement: {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
  proof: by
  simp [rightAdjointUniq]

@[reassoc (attr := simp)]

中文:
定理 rightAdjointUniq_hom_app_counit
  结论: {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
  证明: by
  simp [rightAdjointUniq]

@[reassoc (attr := simp)]

Depends on / 依赖: rightAdjointUniq
-/
theorem rightAdjointUniq_hom_app_counit {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
    (x : D) :
    F.map ((rightAdjointUniq adj1 adj2).hom.app x) ≫ adj2.counit.app x = adj1.counit.app x := by
  simp [rightAdjointUniq]

@[reassoc (attr := simp)]
/--
theorem `rightAdjointUniq_hom_counit` / 定理 `rightAdjointUniq_hom_counit`

English:
theorem rightAdjointUniq_hom_counit
  given: {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
  proof: by
  ext
  simp

中文:
定理 rightAdjointUniq_hom_counit
  条件: {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
  证明: by
  ext
  simp
-/
theorem rightAdjointUniq_hom_counit {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') :
    whiskerRight (rightAdjointUniq adj1 adj2).hom F ≫ adj2.counit = adj1.counit := by
  ext
  simp

/--
theorem `rightAdjointUniq_inv_app` / 定理 `rightAdjointUniq_inv_app`

English:
theorem rightAdjointUniq_inv_app
  statement: {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
  proof: rfl

@[reassoc (attr := simp)]

中文:
定理 rightAdjointUniq_inv_app
  结论: {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
  证明: rfl

@[reassoc (attr := simp)]
-/
theorem rightAdjointUniq_inv_app {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
    (x : D) : (rightAdjointUniq adj1 adj2).inv.app x = (rightAdjointUniq adj2 adj1).hom.app x :=
  rfl

@[reassoc (attr := simp)]
/--
theorem `rightAdjointUniq_trans` / 定理 `rightAdjointUniq_trans`

English:
theorem rightAdjointUniq_trans
  statement: {F : C ⥤ D} {G G' G'' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
  proof: by
  simp [rightAdjointUniq]

@[reassoc (attr := simp)]

中文:
定理 rightAdjointUniq_trans
  结论: {F : C ⥤ D} {G G' G'' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
  证明: by
  simp [rightAdjointUniq]

@[reassoc (attr := simp)]

Depends on / 依赖: rightAdjointUniq
-/
theorem rightAdjointUniq_trans {F : C ⥤ D} {G G' G'' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
    (adj3 : F ⊣ G'') :
    (rightAdjointUniq adj1 adj2).hom ≫ (rightAdjointUniq adj2 adj3).hom =
      (rightAdjointUniq adj1 adj3).hom := by
  simp [rightAdjointUniq]

@[reassoc (attr := simp)]
/--
theorem `rightAdjointUniq_trans_app` / 定理 `rightAdjointUniq_trans_app`

English:
theorem rightAdjointUniq_trans_app
  statement: {F : C ⥤ D} {G G' G'' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
  proof: by
  rw [← rightAdjointUniq_trans adj1 adj2 adj3]
  rfl


@[simp]

中文:
定理 rightAdjointUniq_trans_app
  结论: {F : C ⥤ D} {G G' G'' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
  证明: by
  rw [← rightAdjointUniq_trans adj1 adj2 adj3]
  rfl


@[simp]

Depends on / 依赖: rightAdjointUniq_trans
-/
theorem rightAdjointUniq_trans_app {F : C ⥤ D} {G G' G'' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
    (adj3 : F ⊣ G'') (x : D) :
    (rightAdjointUniq adj1 adj2).hom.app x ≫ (rightAdjointUniq adj2 adj3).hom.app x =
      (rightAdjointUniq adj1 adj3).hom.app x := by
  rw [← rightAdjointUniq_trans adj1 adj2 adj3]
  rfl


@[simp]
/--
theorem `rightAdjointUniq_refl` / 定理 `rightAdjointUniq_refl`

English:
theorem rightAdjointUniq_refl
  given: {F : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G)
  proof: by
  delta rightAdjointUniq
  simp

中文:
定理 rightAdjointUniq_refl
  条件: {F : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G)
  证明: by
  delta rightAdjointUniq
  simp

Depends on / 依赖: rightAdjointUniq
-/
theorem rightAdjointUniq_refl {F : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) :
    (rightAdjointUniq adj1 adj1).hom = 𝟙 _ := by
  delta rightAdjointUniq
  simp

end Adjunction

end CategoryTheory
