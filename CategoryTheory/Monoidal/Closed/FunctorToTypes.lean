/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Functor.FunctorHom
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Functors to Type are closed.

Show that `C ⥤ Type max w v u` is monoidal closed for `C` a category in `Type u` with morphisms in
`Type v`, and `w` an arbitrary universe.

## TODO
It should be shown that `C ⥤ Type max w v u` is Cartesian closed.

-/

@[expose] public section


universe w v' v u u'

open CategoryTheory Functor MonoidalCategory

namespace CategoryTheory.FunctorToTypes

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

variable (F : C ⥤ Type (max w v u))

/-- When `F G H : C ⥤ Type max w v u`, we have `(G ⟶ F.functorHom H) ≃ (F ⊗ G ⟶ H)`. -/
@[simps! apply_app symm_apply_app]
/--
Definition of `functorHomEquiv` / `functorHomEquiv` 的定义

English:
definition functorHomEquiv
  signature: (G H : C ⥤ Type (max w v u))
  body: (Functor.functorHomEquiv F H G).trans (homObjEquiv F H G)

中文:
定义 functorHomEquiv
  签名: (G H : C ⥤ 类型 (最大值 w v u))
  定义体: (Functor.functorHomEquiv F H G).trans (homObjEquiv F H G)

Depends on / 依赖: Functor, Functor.functorHomEquiv, functorHomEquiv, homObjEquiv
-/
def functorHomEquiv (G H : C ⥤ Type (max w v u)) : (G ⟶ F.functorHom H) ≃ (F otimes G ⟶ H) :=
  (Functor.functorHomEquiv F H G).trans (homObjEquiv F H G)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A right adjoint of `tensorLeft F`. -/
@[simps! obj_obj obj_map map_app]
/--
Definition of `rightAdj` / `rightAdj` 的定义

English:
definition rightAdj
  signature: : (C ⥤ Type (max w v u)) ⥤ C ⥤ Type (max w v u) where
  body: F.functorHom G
  map f := { app X := ↾fun a => {
    app d b := a.app d b ≫ f.app d
    naturality g h := by
      have := a.naturality g h
      change (F.map g ≫ a.app _ (h ≫ g)) ≫ _ = _
      aesop }}

@[deprecated "Use `(rightAdj F).map instead" (since := "2026-04-08")] alias rightAdj_map := rig

中文:
定义 rightAdj
  签名: : (C ⥤ 类型 (最大值 w v u)) ⥤ C ⥤ 类型 (最大值 w v u) where
  定义体: F.functorHom G
  map f := { app X := ↾fun a => {
    app d b := a.app d b ≫ f.app d
    naturality g h := by
      have := a.naturality g h
      change (F.map g ≫ a.app _ (h ≫ g)) ≫ _ = _
      aesop }}

@[deprecated "Use `(rightAdj F).map instead" (since := "2026-04-08")] alias rightAdj_map := rig

Depends on / 依赖: F.functorHom, functorHom
-/
def rightAdj : (C ⥤ Type (max w v u)) ⥤ C ⥤ Type (max w v u) where
  obj G := F.functorHom G
  map f := { app X := ↾fun a => {
    app d b := a.app d b ≫ f.app d
    naturality g h := by
      have := a.naturality g h
      change (F.map g ≫ a.app _ (h ≫ g)) ≫ _ = _
      aesop }}

@[deprecated "Use `(rightAdj F).map instead" (since := "2026-04-08")] alias rightAdj_map := rightAdj

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [local simp] types_tensorObj_def in
/--
Definition of `adj` / `adj` 的定义

English:
definition adj
  signature: : tensorLeft F ⊣ rightAdj F where
  body: {
    app := fun G => (functorHomEquiv F G _).2 (𝟙 _)
    naturality := fun G H f => by
      ext
      dsimp
      ext
      apply Prod.ext
      · rfl
      · simp }
  counit := { app := fun G => functorHomEquiv F _ G (𝟙 _) }

中文:
定义 adj
  签名: : tensorLeft F ⊣ rightAdj F where
  定义体: {
    app := fun G => (functorHomEquiv F G _).2 (𝟙 _)
    naturality := fun G H f => by
      ext
      dsimp
      ext
      apply Prod.ext
      · rfl
      · simp }
  counit := { app := fun G => functorHomEquiv F _ G (𝟙 _) }

Depends on / 依赖: Extensive, FinitaryPreExtensive, FinitaryPreExtensive.hasPullbacks_of_is_coproduct, Presieve, Presieve.Extensive.arrows_nonempty_isColimit, arrows_nonempty_isColimit, hasPullbacks_of_is_coproduct
-/
def adj : tensorLeft F ⊣ rightAdj F where
  unit := {
    app := fun G => (functorHomEquiv F G _).2 (𝟙 _)
    naturality := fun G H f => by
      ext
      dsimp
      ext
      apply Prod.ext
      · rfl
      · simp }
  counit := { app := fun G => functorHomEquiv F _ G (𝟙 _) }

/--
Instance `closed` / 实例 `closed`

English:
instance closed
  signature: : Closed F where
  body: rightAdj F
  adj := adj F

中文:
实例 closed
  签名: : 闭 F where
  定义体: rightAdj F
  adj := adj F

Depends on / 依赖: rightAdj
-/
instance closed : Closed F where
  rightAdj := rightAdj F
  adj := adj F

/--
Instance `monoidalClosed` / 实例 `monoidalClosed`

English:
instance monoidalClosed
  signature: : MonoidalClosed (C ⥤ Type (max w v u)) where

中文:
实例 monoidalClosed
  签名: : 幺半群闭 (C ⥤ 类型 (最大值 w v u)) where

Depends on / 依赖: coproductIsCoproduct
-/
instance monoidalClosed : MonoidalClosed (C ⥤ Type (max w v u)) where

end CategoryTheory.FunctorToTypes
