/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Functors from a groupoid into a monoidal closed category form a monoidal closed category.

(Using the pointwise monoidal structure on the functor category.)
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe v u

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace CategoryTheory.Functor

variable {D : Type u} {C : Type*} [Groupoid.{v} D] [Category* C]
  [MonoidalCategory C] [MonoidalClosed C]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `CategoryTheory.Functor.closed`.
The internal hom functor `F ⟶[C] -` -/
@[simps!]
/--
Definition of `closedIhom` / `closedIhom` 的定义

English:
definition closedIhom
  signature: (F : D ⥤ C)
  body: ((whiskeringRight₂ D Cᵒᵖ C C).obj internalHom).obj
    ((Groupoid.invEquivalence D).functor ⋙ F.op)

中文:
定义 closedIhom
  签名: (F : D ⥤ C)
  定义体: ((whiskeringRight₂ D Cᵒᵖ C C).obj internalHom).obj
    ((Groupoid.invEquivalence D).functor ⋙ F.op)

Depends on / 依赖: F.op, Groupoid, Groupoid.invEquivalence, functor, internalHom, invEquivalence
-/
def closedIhom (F : D ⥤ C) : (D ⥤ C) ⥤ D ⥤ C :=
  ((whiskeringRight₂ D Cᵒᵖ C C).obj internalHom).obj
    ((Groupoid.invEquivalence D).functor ⋙ F.op)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `CategoryTheory.Functor.closed`.
The unit for the adjunction `(tensorLeft F) ⊣ (ihom F)`. -/
@[simps]
/--
Definition of `closedUnit` / `closedUnit` 的定义

English:
definition closedUnit
  signature: (F : D ⥤ C)
  body: { app := fun X => (ihom.coev (F.obj X)).app (G.obj X)
    naturality := by
      intro X Y f
      dsimp
      simp only [ihom.coev_naturality, closedIhom_obj_map, Monoidal.tensorObj_map]
      dsimp
      rw [coev_app_comp_pre_app_assoc]; rw [← Functor.map_comp]; rw [tensorHom_def]
      simp }

中文:
定义 closedUnit
  签名: (F : D ⥤ C)
  定义体: { app := fun X => (ihom.coev (F.obj X)).app (G.obj X)
    naturality := by
      intro X Y f
      dsimp
      simp only [ihom.coev_naturality, closedIhom_obj_map, Monoidal.tensorObj_map]
      dsimp
      rw [coev_app_comp_pre_app_assoc]; rw [← Functor.map_comp]; rw [tensorHom_def]
      simp }

Depends on / 依赖: F.obj, Functor, Functor.map_comp, G.obj, Monoidal, Monoidal.tensorObj_map, closedIhom_obj_map, coev_app_comp_pre_app_assoc, coev_naturality, ihom.coev, ihom.coev_naturality, map_comp, naturality, tensorHom_def, tensorObj_map
-/
def closedUnit (F : D ⥤ C) : 𝟭 (D ⥤ C) ⟶ tensorLeft F ⋙ closedIhom F where
  app G :=
  { app := fun X => (ihom.coev (F.obj X)).app (G.obj X)
    naturality := by
      intro X Y f
      dsimp
      simp only [ihom.coev_naturality, closedIhom_obj_map, Monoidal.tensorObj_map]
      dsimp
      rw [coev_app_comp_pre_app_assoc]; rw [← Functor.map_comp]; rw [tensorHom_def]
      simp }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `CategoryTheory.Functor.closed`.
The counit for the adjunction `(tensorLeft F) ⊣ (ihom F)`. -/
@[simps]
/--
Definition of `closedCounit` / `closedCounit` 的定义

English:
definition closedCounit
  signature: (F : D ⥤ C)
  body: { app := fun X => (ihom.ev (F.obj X)).app (G.obj X)
    naturality := by
      intro X Y f
      dsimp
      simp only [closedIhom_obj_map, pre_comm_ihom_map]
      rw [tensorHom_def]
      simp }

中文:
定义 closedCounit
  签名: (F : D ⥤ C)
  定义体: { app := fun X => (ihom.ev (F.obj X)).app (G.obj X)
    naturality := by
      intro X Y f
      dsimp
      simp only [closedIhom_obj_map, pre_comm_ihom_map]
      rw [tensorHom_def]
      simp }

Depends on / 依赖: F.obj, G.obj, closedIhom_obj_map, ihom.ev, naturality, pre_comm_ihom_map, preregular, tensorHom_def
-/
def closedCounit (F : D ⥤ C) : closedIhom F ⋙ tensorLeft F ⟶ 𝟭 (D ⥤ C) where
  app G :=
  { app := fun X => (ihom.ev (F.obj X)).app (G.obj X)
    naturality := by
      intro X Y f
      dsimp
      simp only [closedIhom_obj_map, pre_comm_ihom_map]
      rw [tensorHom_def]
      simp }

set_option backward.isDefEq.respectTransparency false in
/--
Instance `closed` / 实例 `closed`

English:
instance closed
  signature: (F : D ⥤ C)
  body: closedIhom F
  adj :=
    { unit := closedUnit F
      counit := closedCounit F }

中文:
实例 closed
  签名: (F : D ⥤ C)
  定义体: closedIhom F
  adj :=
    { unit := closedUnit F
      counit := closedCounit F }

Depends on / 依赖: closedIhom
-/
instance closed (F : D ⥤ C) : Closed F where
  rightAdj := closedIhom F
  adj :=
    { unit := closedUnit F
      counit := closedCounit F }

/-- If `C` is a monoidal closed category and `D` is a groupoid, then the functor category `D ⥤ C`,
with the pointwise monoidal structure, is monoidal closed. -/
@[simps! closed_adj]
/--
Instance `monoidalClosed` / 实例 `monoidalClosed`

English:
instance monoidalClosed
  signature: : MonoidalClosed (D ⥤ C) where

中文:
实例 monoidalClosed
  签名: : MonoidalClosed (D ⥤ C) where
-/
instance monoidalClosed : MonoidalClosed (D ⥤ C) where

/--
theorem `ihom_map` / 定理 `ihom_map`

English:
theorem ihom_map
  given: (F : D ⥤ C) {G H : D ⥤ C} (f : G ⟶ H)
  statement: (ihom F).map f = (closedIhom F).map f
  proof: rfl

中文:
定理 ihom_map
  条件: (F : D ⥤ C) {G H : D ⥤ C} (f : G ⟶ H)
  结论: (ihom F).map f = (closedIhom F).map f
  证明: rfl
-/
theorem ihom_map (F : D ⥤ C) {G H : D ⥤ C} (f : G ⟶ H) : (ihom F).map f = (closedIhom F).map f :=
  rfl

/--
theorem `ihom_ev_app` / 定理 `ihom_ev_app`

English:
theorem ihom_ev_app
  given: (F G : D ⥤ C)
  statement: (ihom.ev F).app G = (closedCounit F).app G
  proof: rfl

中文:
定理 ihom_ev_app
  条件: (F G : D ⥤ C)
  结论: (ihom.ev F).app G = (closedCounit F).app G
  证明: rfl
-/
theorem ihom_ev_app (F G : D ⥤ C) : (ihom.ev F).app G = (closedCounit F).app G :=
  rfl

/--
theorem `ihom_coev_app` / 定理 `ihom_coev_app`

English:
theorem ihom_coev_app
  given: (F G : D ⥤ C)
  statement: (ihom.coev F).app G = (closedUnit F).app G
  proof: rfl

中文:
定理 ihom_coev_app
  条件: (F G : D ⥤ C)
  结论: (ihom.coev F).app G = (closedUnit F).app G
  证明: rfl
-/
theorem ihom_coev_app (F G : D ⥤ C) : (ihom.coev F).app G = (closedUnit F).app G :=
  rfl

end CategoryTheory.Functor
