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
/-- Given an object `X` of an adhesive category `C`, the coproduct of two subobjects of `X` is their
  pushout in `C` over their pullback. -/
/-
**CategoryTheory.Adhesive.isColimitBinaryCofan** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Adhesive`。
形式化陈述：isColimitBinaryCofan (a b : Subobject X) : IsColimit (BinaryCofan.mk (P
参数：a b : Subobject X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an object `X` of an adhesive category `C`, the coproduct of two subobjects
 of `X` is their
  pushout in `C` over their pullback.
-/
noncomputable def isColimitBinaryCofan (a b : Subobject X) :
    IsColimit (BinaryCofan.mk (P := Subobject.mk (pushout.desc a.arrow b.arrow pullback.condition))
      (le_mk_of_comm (pushout.inl _ _) (pushout.inl_desc _ _ _)).hom
      (le_mk_of_comm (pushout.inr _ _) (pushout.inr_desc _ _ _)).hom) :=
  BinaryCofan.isColimitMk (fun s ↦ (mk_le_of_comm
      (pushout.desc (underlying.map (s.ι.app ⟨WalkingPair.left⟩))
      (underlying.map (s.ι.app ⟨WalkingPair.right⟩))
      (by ext; simp [pullback.condition])) (by cat_disch)).hom)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
/-
**CategoryTheory.Adhesive.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Adhesive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasBinaryCoproducts (Subobject X) where
  has_colimit F := by
    have : HasColimit (pair (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)) :=
      ⟨⟨⟨_, isColimitBinaryCofan (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)⟩⟩⟩
    apply hasColimit_of_iso (diagramIsoPair F)

end CategoryTheory.Adhesive

