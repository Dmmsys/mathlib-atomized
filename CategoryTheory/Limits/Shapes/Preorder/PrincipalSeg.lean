/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Order.InitialSeg
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Cones

/-!
# Cocones associated to principal segments

If `f : α <i β` is a principal segment and `F : β ⥤ C`,
there is a cocone for `f.monotone.functor ⋙ F : α ⥤ C`
the point of which is `F.obj f.top`.

-/

@[expose] public section

open CategoryTheory Category Limits

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- When `f : α <i β` and a functor `F : β ⥤ C`, this is the cocone
for `f.monotone.functor ⋙ F : α ⥤ C` whose point is `F.obj f.top`. -/
@[simps]
/--
Definition of `PrincipalSeg.cocone` / `PrincipalSeg.cocone` 的定义

English:
definition PrincipalSeg.cocone
  signature: {α β : Type*} [PartialOrder α] [PartialOrder β]
  body: F.obj f.top
  ι :=
    { app i := F.map (homOfLE (f.lt_top i).le)
      naturality i j f := by
        dsimp
        rw [← F.map_comp]; rw [comp_id]
        rfl }

中文:
定义 PrincipalSeg.cocone
  签名: {α β : 类型} [PartialOrder α] [PartialOrder β]
  定义体: F.obj f.top
  ι :=
    { app i := F.map (homOfLE (f.lt_top i).le)
      naturality i j f := by
        dsimp
        rw [← F.map_comp]; rw [comp_id]
        rfl }

Depends on / 依赖: F.obj, f.top
-/
def PrincipalSeg.cocone {α β : Type*} [PartialOrder α] [PartialOrder β]
    (f : α <i β) {C : Type*} [Category* C] (F : β ⥤ C) : Cocone (f.monotone.functor ⋙ F) where
  pt := F.obj f.top
  ι :=
    { app i := F.map (homOfLE (f.lt_top i).le)
      naturality i j f := by
        dsimp
        rw [← F.map_comp]; rw [comp_id]
        rfl }
