/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Adhesive.Basic
public import Mathlib.CategoryTheory.Subobject.Basic

/-!

# Subobjects in adhesive categories

## Main Results
- Subobjects in adhesive categories have binary coproducts

-/

@[expose] public section

namespace CategoryTheory.Adhesive

open Limits Subobject

universe v u

variable {C : Type u} [Category.{v} C] [Adhesive C] {X : C}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitBinaryCofan` / `isColimitBinaryCofan` 的定义

English:
definition isColimitBinaryCofan
  signature: (a b : Subobject X)
  body: BinaryCofan.isColimitMk (fun s => (mk_le_of_comm
      (pushout.desc (underlying.map (s.ι.app ⟨WalkingPair.left⟩))
      (underlying.map (s.ι.app ⟨WalkingPair.right⟩))
      (by ext; simp [pullback.condition])) (by cat_disch)).hom)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)

中文:
定义 isColimitBinaryCofan
  签名: (a b : Subobject X)
  定义体: BinaryCofan.isColimitMk (fun s => (mk_le_of_comm
      (pushout.desc (underlying.map (s.ι.app ⟨WalkingPair.left⟩))
      (underlying.map (s.ι.app ⟨WalkingPair.right⟩))
      (by ext; simp [pullback.condition])) (by cat_disch)).hom)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)

Depends on / 依赖: Subobject, Subobject.mk, a.arrow, b.arrow, condition, pullback, pullback.condition, pushout, pushout.desc
-/
noncomputable def isColimitBinaryCofan (a b : Subobject X) :
    IsColimit (BinaryCofan.mk (P := Subobject.mk (pushout.desc a.arrow b.arrow pullback.condition))
      (le_mk_of_comm (pushout.inl _ _) (pushout.inl_desc _ _ _)).hom
      (le_mk_of_comm (pushout.inr _ _) (pushout.inr_desc _ _ _)).hom) :=
  BinaryCofan.isColimitMk (fun s => (mk_le_of_comm
      (pushout.desc (underlying.map (s.ι.app ⟨WalkingPair.left⟩))
      (underlying.map (s.ι.app ⟨WalkingPair.right⟩))
      (by ext; simp [pullback.condition])) (by cat_disch)).hom)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasBinaryCoproducts (Subobject X)
  body: by
    have : HasColimit (pair (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)) :=
      ⟨⟨⟨_, isColimitBinaryCofan (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)⟩⟩⟩
    apply hasColimit_of_iso (diagramIsoPair F)

中文:
实例 :
  签名: HasBinaryCoproducts (Subobject X)
  定义体: by
    have : HasColimit (pair (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)) :=
      ⟨⟨⟨_, isColimitBinaryCofan (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)⟩⟩⟩
    apply hasColimit_of_iso (diagramIsoPair F)

Depends on / 依赖: F.obj, HasColimit, WalkingPair, WalkingPair.left, WalkingPair.right, diagramIsoPair, hasColimit_of_iso, isColimitBinaryCofan
-/
instance : HasBinaryCoproducts (Subobject X) where
  has_colimit F := by
    have : HasColimit (pair (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)) :=
      ⟨⟨⟨_, isColimitBinaryCofan (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)⟩⟩⟩
    apply hasColimit_of_iso (diagramIsoPair F)

end CategoryTheory.Adhesive
