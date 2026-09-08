/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Comma.Presheaf.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Yoneda
public import Mathlib.CategoryTheory.Limits.Over

/-!
# Relative Yoneda preserves certain colimits

In this file we turn the statement `yonedaYonedaColimit` from
`CategoryTheory.Limits.Preserves.Yoneda` from a functor `F : J ⥤ Cᵒᵖ ⥤ Type v` into a statement
about families of presheaves over `A`, i.e., functors `F : J ⥤ Over A`.
-/

@[expose] public section

namespace CategoryTheory

open Category Opposite Limits

universe w v u

variable {C : Type u} [Category.{v} C] {A : Cᵒᵖ ⥤ Type v}
variable {J : Type v} [SmallCategory J] {A : Cᵒᵖ ⥤ Type v} (F : J ⥤ Over A)

-- We introduce some local notation to reduce visual noise in the following proof
local notation "E" => Equivalence.functor (overEquivPresheafCostructuredArrow A)
local notation "E.obj" =>
  Functor.obj (Equivalence.functor (overEquivPresheafCostructuredArrow A))

/-- Naturally in `X`, we have `Hom(YX, colim_i Fi) ≅ colim_i Hom(YX, Fi)`, where `Y` is the
"Yoneda embedding" `CostructuredArrow.toOver yoneda A`. This is a relative version of
`yonedaYonedaColimit`. -/
/-
**CategoryTheory.CostructuredArrow.toOverCompYonedaColimit** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Type
 v} →       [inst_1 : CategoryTheory.SmallCategory J] →         {A : CategoryThe
ory.Functor Cᵒᵖ (Type v)} →           (F : CategoryTheory.Functor J (CategoryThe
ory.Over A)) →             (CategoryTheory.CostructuredArrow.toOver CategoryTheo
ry.yoneda A).op.comp                 (CategoryTheory.yoneda.obj (CategoryTheory.
Limits.colimit F)) ≅               (CategoryTheory.CostructuredArrow.toOver Cate
goryTheory.yoneda A).op.comp                 (CategoryTheory.Limits.colimit (F.c
omp CategoryTheory.yoneda))
参数：Type v；F : CategoryTheory.Functor J (CategoryTheory.Over A)；CategoryTheory.Co
structuredArrow.toOver CategoryTheory.yoneda A；CategoryTheory.yoneda.obj (Catego
ryTheory.Limits.colimit F)；CategoryTheory.CostructuredArrow.toOver CategoryTheor
y.yoneda A；CategoryTheory.Limits.colimit (F.comp CategoryTheory.yoneda)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Naturally in `X`, we have `Hom(YX, colim_i Fi) ≅ colim_i Hom(YX, Fi)`, where `Y`
 is the
"Yoneda embedding" `CostructuredArrow.toOver yoneda A`. This is a relative versi
on of
`yonedaYonedaColimit`.
-/
noncomputable def CostructuredArrow.toOverCompYonedaColimit :
    (CostructuredArrow.toOver yoneda A).op ⋙ yoneda.obj (colimit F) ≅
    (CostructuredArrow.toOver yoneda A).op ⋙ colimit (F ⋙ yoneda) := calc
  (CostructuredArrow.toOver yoneda A).op ⋙ yoneda.obj (colimit F)
    ≅ yoneda.op ⋙ yoneda.obj (E.obj (colimit F)) :=
        CostructuredArrow.toOverCompYoneda A _
  _ ≅ yoneda.op ⋙ yoneda.obj (colimit (F ⋙ E)) :=
        Functor.isoWhiskerLeft yoneda.op (yoneda.mapIso (preservesColimitIso E F))
  _ ≅ yoneda.op ⋙ colimit ((F ⋙ E) ⋙ yoneda) :=
        yonedaYonedaColimit _
  _ ≅ yoneda.op ⋙ ((F ⋙ E) ⋙ yoneda).flip ⋙ colim :=
        Functor.isoWhiskerLeft _ (colimitIsoFlipCompColim _)
  _ ≅ (yoneda.op ⋙ coyoneda ⋙ (Functor.whiskeringLeft _ _ _).obj E) ⋙
          (Functor.whiskeringLeft _ _ _).obj F ⋙ colim :=
        Iso.refl _
  _ ≅ (CostructuredArrow.toOver yoneda A).op ⋙ coyoneda ⋙
          (Functor.whiskeringLeft _ _ _).obj F ⋙ colim :=
        Functor.isoWhiskerRight (CostructuredArrow.toOverCompCoyoneda _).symm _
  _ ≅ (CostructuredArrow.toOver yoneda A).op ⋙ (F ⋙ yoneda).flip ⋙ colim :=
        Iso.refl _
  _ ≅ (CostructuredArrow.toOver yoneda A).op ⋙ colimit (F ⋙ yoneda) :=
      Functor.isoWhiskerLeft _ (colimitIsoFlipCompColim _).symm

end CategoryTheory

