/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Category.Grp.Yoneda

/-!
# The Yoneda embedding for preadditive categories

The Yoneda embedding for preadditive categories sends an object `Y` to the presheaf sending an
object `X` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End Y`-module
structure.

We also show that this presheaf is additive and that it is compatible with the normal Yoneda
embedding in the expected way and deduce that the preadditive Yoneda embedding is fully faithful.

## TODO
* The Yoneda embedding is additive itself

-/

@[expose] public section


universe v u u₁

open CategoryTheory.Preadditive Opposite CategoryTheory.Limits CategoryTheory.Functor

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The Yoneda embedding for preadditive categories sends an object `Y` to the presheaf sending an
object `X` to the `End Y`-module of morphisms `X ⟶ Y`.
-/
@[simps]
/--
Definition of `preadditiveYonedaObj` / `preadditiveYonedaObj` 的定义

English:
definition preadditiveYonedaObj
  signature: (Y : C)
  body: ModuleCat.of _ (X.unop ⟶ Y)
  map f := ModuleCat.ofHom
    { toFun := fun g => f.unop ≫ g
      map_add' := fun _ _ => comp_add _ _ _ _ _ _
map_smul' := fun _ _ => Eq.symm Category.assoc _ _ _ }

中文:
定义 preadditiveYonedaObj
  签名: (Y : C)
  定义体: ModuleCat.of _ (X.unop ⟶ Y)
  map f := ModuleCat.ofHom
    { toFun := fun g => f.unop ≫ g
      map_add' := fun _ _ => comp_add _ _ _ _ _ _
map_smul' := fun _ _ => Eq.symm Category.assoc _ _ _ }

Depends on / 依赖: ModuleCat, ModuleCat.of, X.unop
-/
def preadditiveYonedaObj (Y : C) : Cᵒᵖ ⥤ ModuleCat.{v} (End Y) where
  obj X := ModuleCat.of _ (X.unop ⟶ Y)
  map f := ModuleCat.ofHom
    { toFun := fun g => f.unop ≫ g
      map_add' := fun _ _ => comp_add _ _ _ _ _ _
map_smul' := fun _ _ => Eq.symm Category.assoc _ _ _ }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Yoneda embedding for preadditive categories sends an object `Y` to the presheaf sending an
object `X` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End Y`-module
structure, see `preadditiveYonedaObj`.
-/
@[simps obj]
/--
Definition of `preadditiveYoneda` / `preadditiveYoneda` 的定义

English:
definition preadditiveYoneda
  signature: : C ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{v} where
  body: preadditiveYonedaObj Y ⋙ forget₂ _ _
  map f :=
    { app := fun _ => AddCommGrpCat.ofHom
        { toFun := fun g => g ≫ f
          map_zero' := Limits.zero_comp
          map_add' := fun _ _ => add_comp _ _ _ _ _ _ }
      naturality := fun _ _ _ => AddCommGrpCat.ext fun _ => Category.assoc _ _ _

中文:
定义 preadditiveYoneda
  签名: : C ⥤ Cᵒᵖ ⥤ 加法交换群范畴.{v} where
  定义体: preadditiveYonedaObj Y ⋙ forget₂ _ _
  map f :=
    { app := fun _ => AddCommGrpCat.ofHom
        { toFun := fun g => g ≫ f
          map_zero' := Limits.zero_comp
          map_add' := fun _ _ => add_comp _ _ _ _ _ _ }
      naturality := fun _ _ _ => AddCommGrpCat.ext fun _ => Category.assoc _ _ _

Depends on / 依赖: preadditiveYonedaObj
-/
def preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj Y := preadditiveYonedaObj Y ⋙ forget₂ _ _
  map f :=
    { app := fun _ => AddCommGrpCat.ofHom
        { toFun := fun g => g ≫ f
          map_zero' := Limits.zero_comp
          map_add' := fun _ _ => add_comp _ _ _ _ _ _ }
      naturality := fun _ _ _ => AddCommGrpCat.ext fun _ => Category.assoc _ _ _ }

/-- The Yoneda embedding for preadditive categories sends an object `X` to the copresheaf sending an
object `Y` to the `End X`-module of morphisms `X ⟶ Y`.
-/
@[simps]
/--
Definition of `preadditiveCoyonedaObj` / `preadditiveCoyonedaObj` 的定义

English:
definition preadditiveCoyonedaObj
  signature: (X : C)
  body: ModuleCat.of _ (X ⟶ Y)
  map f := ModuleCat.ofHom
    { toFun := fun g => g ≫ f
      map_add' := fun _ _ => add_comp _ _ _ _ _ _
      map_smul' := fun _ _ => Category.assoc _ _ _ }

中文:
定义 preadditiveCoyonedaObj
  签名: (X : C)
  定义体: ModuleCat.of _ (X ⟶ Y)
  map f := ModuleCat.ofHom
    { toFun := fun g => g ≫ f
      map_add' := fun _ _ => add_comp _ _ _ _ _ _
      map_smul' := fun _ _ => Category.assoc _ _ _ }

Depends on / 依赖: ModuleCat, ModuleCat.of
-/
def preadditiveCoyonedaObj (X : C) : C ⥤ ModuleCat.{v} (End X)ᵐᵒᵖ where
  obj Y := ModuleCat.of _ (X ⟶ Y)
  map f := ModuleCat.ofHom
    { toFun := fun g => g ≫ f
      map_add' := fun _ _ => add_comp _ _ _ _ _ _
      map_smul' := fun _ _ => Category.assoc _ _ _ }

set_option backward.isDefEq.respectTransparency.types false in
/-- The Yoneda embedding for preadditive categories sends an object `X` to the copresheaf sending an
object `Y` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End X`-module
structure, see `preadditiveCoyonedaObj`.
-/
@[simps obj]
/--
Definition of `preadditiveCoyoneda` / `preadditiveCoyoneda` 的定义

English:
definition preadditiveCoyoneda
  signature: : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat.{v} where
  body: preadditiveCoyonedaObj (unop X) ⋙ forget₂ _ _
  map f :=
    { app := fun _ => AddCommGrpCat.ofHom
        { toFun := fun g => f.unop ≫ g
          map_zero' := Limits.comp_zero
          map_add' := fun _ _ => comp_add _ _ _ _ _ _ }
      naturality := fun _ _ _ =>
AddCommGrpCat.ext fun _ => Eq.sym

中文:
定义 preadditiveCoyoneda
  签名: : Cᵒᵖ ⥤ C ⥤ 加法交换群范畴.{v} where
  定义体: preadditiveCoyonedaObj (unop X) ⋙ forget₂ _ _
  map f :=
    { app := fun _ => AddCommGrpCat.ofHom
        { toFun := fun g => f.unop ≫ g
          map_zero' := Limits.comp_zero
          map_add' := fun _ _ => comp_add _ _ _ _ _ _ }
      naturality := fun _ _ _ =>
AddCommGrpCat.ext fun _ => Eq.sym

Depends on / 依赖: preadditiveCoyonedaObj
-/
def preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat.{v} where
  obj X := preadditiveCoyonedaObj (unop X) ⋙ forget₂ _ _
  map f :=
    { app := fun _ => AddCommGrpCat.ofHom
        { toFun := fun g => f.unop ≫ g
          map_zero' := Limits.comp_zero
          map_add' := fun _ _ => comp_add _ _ _ _ _ _ }
      naturality := fun _ _ _ =>
AddCommGrpCat.ext fun _ => Eq.symm Category.assoc _ _ _ }

/--
Instance `additive_yonedaObj` / 实例 `additive_yonedaObj`

English:
instance additive_yonedaObj
  signature: (X : C)

中文:
实例 additive_yonedaObj
  签名: (X : C)
-/
instance additive_yonedaObj (X : C) : Functor.Additive (preadditiveYonedaObj X) where

set_option backward.defeqAttrib.useBackward true in
/--
Instance `additive_yonedaObj'` / 实例 `additive_yonedaObj'`

English:
instance additive_yonedaObj'
  signature: (X : C)

中文:
实例 additive_yonedaObj'
  签名: (X : C)
-/
instance additive_yonedaObj' (X : C) : Functor.Additive (preadditiveYoneda.obj X) where

/--
Instance `additive_coyonedaObj` / 实例 `additive_coyonedaObj`

English:
instance additive_coyonedaObj
  signature: (X : C)

中文:
实例 additive_coyonedaObj
  签名: (X : C)
-/
instance additive_coyonedaObj (X : C) : Functor.Additive (preadditiveCoyonedaObj X) where

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `additive_coyonedaObj'` / 实例 `additive_coyonedaObj'`

English:
instance additive_coyonedaObj'
  signature: (X : Cᵒᵖ)

中文:
实例 additive_coyonedaObj'
  签名: (X : Cᵒᵖ)
-/
instance additive_coyonedaObj' (X : Cᵒᵖ) : Functor.Additive (preadditiveCoyoneda.obj X) where

/-- Composing the preadditive yoneda embedding with the forgetful functor yields the regular
Yoneda embedding.
-/
@[simp]
/--
theorem `whiskering_preadditiveYoneda` / 定理 `whiskering_preadditiveYoneda`

English:
theorem whiskering_preadditiveYoneda
  proof: rfl

中文:
定理 whiskering_preadditiveYoneda
  证明: rfl
-/
theorem whiskering_preadditiveYoneda :
    preadditiveYoneda ⋙
        (whiskeringRight Cᵒᵖ AddCommGrpCat (Type v)).obj (forget AddCommGrpCat) =
      yoneda :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Composing the preadditive yoneda embedding with the forgetful functor yields the regular
Yoneda embedding.
-/
@[simp]
/--
theorem `whiskering_preadditiveCoyoneda` / 定理 `whiskering_preadditiveCoyoneda`

English:
theorem whiskering_preadditiveCoyoneda
  proof: rfl

中文:
定理 whiskering_preadditiveCoyoneda
  证明: rfl
-/
theorem whiskering_preadditiveCoyoneda :
    preadditiveCoyoneda ⋙
        (whiskeringRight C AddCommGrpCat (Type v)).obj (forget AddCommGrpCat) =
      coyoneda :=
  rfl

/--
Instance `full_preadditiveYoneda` / 实例 `full_preadditiveYoneda`

English:
instance full_preadditiveYoneda
  signature: : (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGrpCat).Full
  body: let _ : Functor.Full (preadditiveYoneda ⋙
      (whiskeringRight Cᵒᵖ AddCommGrpCat (Type v)).obj (forget AddCommGrpCat)) :=
    Yoneda.yoneda_full
  Functor.Full.of_comp_faithful preadditiveYoneda
    ((whiskeringRight Cᵒᵖ AddCommGrpCat (Type v)).obj (forget AddCommGrpCat))

中文:
实例 full_preadditiveYoneda
  签名: : (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ 加法交换群范畴).满
  定义体: let _ : Functor.Full (preadditiveYoneda ⋙
      (whiskeringRight Cᵒᵖ AddCommGrpCat (Type v)).obj (forget AddCommGrpCat)) :=
    Yoneda.yoneda_full
  Functor.Full.of_comp_faithful preadditiveYoneda
    ((whiskeringRight Cᵒᵖ AddCommGrpCat (Type v)).obj (forget AddCommGrpCat))

Depends on / 依赖: AddCommGrpCat, Functor, Functor.Full, Functor.Full.of_comp_faithful, Yoneda, Yoneda.yoneda_full, forget, of_comp_faithful, preadditiveYoneda, whiskeringRight, yoneda_full
-/
instance full_preadditiveYoneda : (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGrpCat).Full :=
  let _ : Functor.Full (preadditiveYoneda ⋙
      (whiskeringRight Cᵒᵖ AddCommGrpCat (Type v)).obj (forget AddCommGrpCat)) :=
    Yoneda.yoneda_full
  Functor.Full.of_comp_faithful preadditiveYoneda
    ((whiskeringRight Cᵒᵖ AddCommGrpCat (Type v)).obj (forget AddCommGrpCat))

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `full_preadditiveCoyoneda` / 实例 `full_preadditiveCoyoneda`

English:
instance full_preadditiveCoyoneda
  signature: : (preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat).Full
  body: let _ : Functor.Full (preadditiveCoyoneda ⋙
      (whiskeringRight C AddCommGrpCat (Type v)).obj (forget AddCommGrpCat)) :=
    Coyoneda.coyoneda_full
  Functor.Full.of_comp_faithful preadditiveCoyoneda
    ((whiskeringRight C AddCommGrpCat (Type v)).obj (forget AddCommGrpCat))

中文:
实例 full_preadditiveCoyoneda
  签名: : (preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ 加法交换群范畴).满
  定义体: let _ : Functor.Full (preadditiveCoyoneda ⋙
      (whiskeringRight C AddCommGrpCat (Type v)).obj (forget AddCommGrpCat)) :=
    Coyoneda.coyoneda_full
  Functor.Full.of_comp_faithful preadditiveCoyoneda
    ((whiskeringRight C AddCommGrpCat (Type v)).obj (forget AddCommGrpCat))

Depends on / 依赖: AddCommGrpCat, Coyoneda, Coyoneda.coyoneda_full, Functor, Functor.Full, Functor.Full.of_comp_faithful, coyoneda_full, forget, of_comp_faithful, preadditiveCoyoneda, whiskeringRight
-/
instance full_preadditiveCoyoneda : (preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat).Full :=
  let _ : Functor.Full (preadditiveCoyoneda ⋙
      (whiskeringRight C AddCommGrpCat (Type v)).obj (forget AddCommGrpCat)) :=
    Coyoneda.coyoneda_full
  Functor.Full.of_comp_faithful preadditiveCoyoneda
    ((whiskeringRight C AddCommGrpCat (Type v)).obj (forget AddCommGrpCat))

/--
Instance `faithful_preadditiveYoneda` / 实例 `faithful_preadditiveYoneda`

English:
instance faithful_preadditiveYoneda
  signature: : (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGrpCat).Faithful
  body: Functor.Faithful.of_comp_eq whiskering_preadditiveYoneda

中文:
实例 faithful_preadditiveYoneda
  签名: : (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ 加法交换群范畴).忠实
  定义体: Functor.Faithful.of_comp_eq whiskering_preadditiveYoneda

Depends on / 依赖: Faithful, Functor, Functor.Faithful.of_comp_eq, of_comp_eq, whiskering_preadditiveYoneda
-/
instance faithful_preadditiveYoneda : (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGrpCat).Faithful :=
  Functor.Faithful.of_comp_eq whiskering_preadditiveYoneda

/--
Instance `faithful_preadditiveCoyoneda` / 实例 `faithful_preadditiveCoyoneda`

English:
instance faithful_preadditiveCoyoneda
  signature: :
  body: Functor.Faithful.of_comp_eq whiskering_preadditiveCoyoneda

中文:
实例 faithful_preadditiveCoyoneda
  签名: :
  定义体: Functor.Faithful.of_comp_eq whiskering_preadditiveCoyoneda

Depends on / 依赖: Faithful, Functor, Functor.Faithful.of_comp_eq, of_comp_eq, whiskering_preadditiveCoyoneda
-/
instance faithful_preadditiveCoyoneda :
    (preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat).Faithful :=
  Functor.Faithful.of_comp_eq whiskering_preadditiveCoyoneda

section

variable {D : Type u₁} [Category.{v} D] [Preadditive D] (F : C ⥤ D) [F.Additive]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation `preadditiveYoneda.obj X ⟶ F.op ⋙ preadditiveYoneda.obj (F.obj X)`
when `F : C ⥤ D` is an additive functor between preadditive categories and `X : C`. -/
@[simps]
/--
Definition of `preadditiveYonedaMap` / `preadditiveYonedaMap` 的定义

English:
definition preadditiveYonedaMap
  signature: (X : C)
  body: AddCommGrpCat.ofHom F.mapAddHom

中文:
定义 preadditiveYonedaMap
  签名: (X : C)
  定义体: AddCommGrpCat.ofHom F.mapAddHom

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.ofHom, F.mapAddHom, mapAddHom
-/
def preadditiveYonedaMap (X : C) :
    preadditiveYoneda.obj X ⟶ F.op ⋙ preadditiveYoneda.obj (F.obj X) where
  app Y := AddCommGrpCat.ofHom F.mapAddHom

end

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `_root_.AddCommGrpCat.preadditiveCoyonedaIso` / `_root_.AddCommGrpCat.preadditiveCoyonedaIso` 的定义

English:
definition _root_.AddCommGrpCat.preadditiveCoyonedaIso
  signature: : preadditiveCoyoneda ≅ AddCommGrpCat.coyoneda
  body: NatIso.ofComponents fun X => NatIso.ofComponents fun Y => AddCommGrpCat.homAddEquiv.toAddCommGrpIso

中文:
定义 _root_.加法交换群范畴.preadditiveCoyonedaIso
  签名: : preadditiveCoyoneda ≅ 加法交换群范畴.coyoneda
  定义体: NatIso.ofComponents fun X => NatIso.ofComponents fun Y => AddCommGrpCat.homAddEquiv.toAddCommGrpIso

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.homAddEquiv.toAddCommGrpIso, NatIso, NatIso.ofComponents, homAddEquiv, ofComponents, toAddCommGrpIso
-/
def _root_.AddCommGrpCat.preadditiveCoyonedaIso : preadditiveCoyoneda ≅ AddCommGrpCat.coyoneda :=
  NatIso.ofComponents fun X => NatIso.ofComponents fun Y => AddCommGrpCat.homAddEquiv.toAddCommGrpIso

end CategoryTheory
