/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Join.Basic
public import Mathlib.CategoryTheory.Opposites

/-!
# Opposites of joins of categories

This file constructs the canonical equivalence of categories `(C ⋆ D)ᵒᵖ ≌ Dᵒᵖ ⋆ Cᵒᵖ`.
This equivalence is characterized in both directions.

-/

@[expose] public section

namespace CategoryTheory.Join
open Opposite CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence `(C ⋆ D)ᵒᵖ ≌ Dᵒᵖ ⋆ Cᵒᵖ` induced by `Join.opEquivFunctor` and
`Join.opEquivInverse`. -/
/-
**CategoryTheory.Join.opEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Join`。
形式化陈述：opEquiv : (C ⋆ D)ᵒᵖ ≌ Dᵒᵖ ⋆ Cᵒᵖ where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `(C ⋆ D)ᵒᵖ ≌ Dᵒᵖ ⋆ Cᵒᵖ` induced by `Join.opEquivFunctor` and
`Join.opEquivInverse`.
-/
def opEquiv : (C ⋆ D)ᵒᵖ ≌ Dᵒᵖ ⋆ Cᵒᵖ where
  functor := Functor.leftOp <|
    Join.mkFunctor (inclRight _ _).rightOp (inclLeft _ _).rightOp { app _ := (edge _ _).op }
  inverse := Join.mkFunctor (inclRight _ _).op (inclLeft _ _).op { app _ := (edge _ _).op }
  unitIso := NatIso.ofComponents
    (fun
      | op (left _) => Iso.refl _
      | op (right _) => Iso.refl _)
    (@fun
      | op (left _), op (left _), _ => by cat_disch
      | op (right _), op (left _), _ => by cat_disch
      | op (right _), op (right _), _ => by cat_disch)
  counitIso := NatIso.ofComponents
    (fun
      | left _ => Iso.refl _
      | right _ => Iso.refl _)
  functor_unitIso_comp
    | op (left _) => by cat_disch
    | op (right _) => by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
variable {C} in
@[simp]
/-
**CategoryTheory.Join.opEquiv_functor_obj_op_left** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Join`。
形式化陈述：opEquiv_functor_obj_op_left (c : C) : (opEquiv C D).functor.obj (op <| lef
t c) = right (op c)
参数：c : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma opEquiv_functor_obj_op_left (c : C) :
    (opEquiv C D).functor.obj (op <| left c) = right (op c) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {D} in
@[simp]
/-
**CategoryTheory.Join.opEquiv_functor_obj_op_right** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Join`。
形式化陈述：opEquiv_functor_obj_op_right (d : D) : (opEquiv C D).functor.obj (op <| ri
ght d) = left (op d)
参数：d : D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma opEquiv_functor_obj_op_right (d : D) :
    (opEquiv C D).functor.obj (op <| right d) = left (op d) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {C} in
@[simp]
/-
**CategoryTheory.Join.opEquiv_functor_map_op_inclLeft** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Join`。
形式化陈述：opEquiv_functor_map_op_inclLeft {c c' : C} (f : c ⟶ c') : (opEquiv C D).fu
nctor.map (op <| (inclLeft C D).map f) = (inclRight _ _).map (op f)
参数：f : c ⟶ c'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma opEquiv_functor_map_op_inclLeft {c c' : C} (f : c ⟶ c') :
    (opEquiv C D).functor.map (op <| (inclLeft C D).map f) = (inclRight _ _).map (op f) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {D} in
@[simp]
/-
**CategoryTheory.Join.opEquiv_functor_map_op_inclRight** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Join`。
形式化陈述：opEquiv_functor_map_op_inclRight {d d' : D} (f : d ⟶ d') : (opEquiv C D).f
unctor.map (op <| (inclRight C D).map f) = (inclLeft _ _).map (op f)
参数：f : d ⟶ d'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma opEquiv_functor_map_op_inclRight {d d' : D} (f : d ⟶ d') :
    (opEquiv C D).functor.map (op <| (inclRight C D).map f) = (inclLeft _ _).map (op f) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {C D} in
/-
**CategoryTheory.Join.opEquiv_functor_map_op_edge** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Join`。
形式化陈述：opEquiv_functor_map_op_edge (c : C) (d : D) : (opEquiv C D).functor.map (o
p <| edge c d) = edge (op d) (op c)
参数：c : C；d : D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma opEquiv_functor_map_op_edge (c : C) (d : D) :
    (opEquiv C D).functor.map (op <| edge c d) = edge (op d) (op c) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Characterize (up to a rightOp) the action of the left inclusion on `Join.opEquivFunctor`. -/
@[simps!]
/-
**CategoryTheory.Join.InclLeftCompRightOpOpEquivFunctor** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Join`。
形式化陈述：InclLeftCompRightOpOpEquivFunctor : inclLeft C D ⋙ (opEquiv C D).functor.r
ightOp ≅ (inclRight _ _).rightOp
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Characterize (up to a rightOp) the action of the left inclusion on `Join.opEquiv
Functor`.
-/
def InclLeftCompRightOpOpEquivFunctor :
    inclLeft C D ⋙ (opEquiv C D).functor.rightOp ≅ (inclRight _ _).rightOp :=
  isoWhiskerLeft _ (leftOpRightOpIso _) ≪≫ mkFunctorLeft _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- Characterize (up to a rightOp) the action of the right inclusion on `Join.opEquivFunctor`. -/
@[simps!]
/-
**CategoryTheory.Join.InclRightCompRightOpOpEquivFunctor** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Join`。
形式化陈述：InclRightCompRightOpOpEquivFunctor : inclRight C D ⋙ (opEquiv C D).functor
.rightOp ≅ (inclLeft _ _).rightOp
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Characterize (up to a rightOp) the action of the right inclusion on `Join.opEqui
vFunctor`.
-/
def InclRightCompRightOpOpEquivFunctor :
    inclRight C D ⋙ (opEquiv C D).functor.rightOp ≅ (inclLeft _ _).rightOp :=
  isoWhiskerLeft _ (leftOpRightOpIso _) ≪≫ mkFunctorRight _ _ _

set_option backward.isDefEq.respectTransparency.types false in
variable {D} in
@[simp]
/-
**CategoryTheory.Join.opEquiv_inverse_obj_left_op** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Join`。
形式化陈述：opEquiv_inverse_obj_left_op (d : D) : (opEquiv C D).inverse.obj (left <| o
p d) = op (right d)
参数：d : D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma opEquiv_inverse_obj_left_op (d : D) :
    (opEquiv C D).inverse.obj (left <| op d) = op (right d) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {C} in
@[simp]
/-
**CategoryTheory.Join.opEquiv_inverse_obj_right_op** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Join`。
形式化陈述：opEquiv_inverse_obj_right_op (c : C) : (opEquiv C D).inverse.obj (right <|
 op c) = op (left c)
参数：c : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma opEquiv_inverse_obj_right_op (c : C) :
    (opEquiv C D).inverse.obj (right <| op c) = op (left c) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {D} in
@[simp]
/-
**CategoryTheory.Join.opEquiv_inverse_map_inclLeft_op** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Join`。
形式化陈述：opEquiv_inverse_map_inclLeft_op {d d' : D} (f : d ⟶ d') : (opEquiv C D).in
verse.map ((inclLeft Dᵒᵖ Cᵒᵖ).map f.op) = op ((inclRight _ _).map f)
参数：f : d ⟶ d'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma opEquiv_inverse_map_inclLeft_op {d d' : D} (f : d ⟶ d') :
    (opEquiv C D).inverse.map ((inclLeft Dᵒᵖ Cᵒᵖ).map f.op) = op ((inclRight _ _).map f) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {D} in
@[simp]
/-
**CategoryTheory.Join.opEquiv_inverse_map_inclRight_op** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Join`。
形式化陈述：opEquiv_inverse_map_inclRight_op {c c' : C} (f : c ⟶ c') : (opEquiv C D).i
nverse.map ((inclRight Dᵒᵖ Cᵒᵖ).map f.op) = op ((inclLeft _ _).map f)
参数：f : c ⟶ c'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma opEquiv_inverse_map_inclRight_op {c c' : C} (f : c ⟶ c') :
    (opEquiv C D).inverse.map ((inclRight Dᵒᵖ Cᵒᵖ).map f.op) = op ((inclLeft _ _).map f) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {C D} in
@[simp]
/-
**CategoryTheory.Join.opEquiv_inverse_map_edge_op** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Join`。
形式化陈述：opEquiv_inverse_map_edge_op (c : C) (d : D) : (opEquiv C D).inverse.map (e
dge (op d) (op c)) = op (edge c d)
参数：c : C；d : D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma opEquiv_inverse_map_edge_op (c : C) (d : D) :
    (opEquiv C D).inverse.map (edge (op d) (op c)) = op (edge c d) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Characterize `Join.opEquivInverse` with respect to the left inclusion -/
/-
**CategoryTheory.Join.inclLeftCompOpEquivInverse** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Join`。
形式化陈述：inclLeftCompOpEquivInverse : Join.inclLeft Dᵒᵖ Cᵒᵖ ⋙ (opEquiv C D).inverse
 ≅ (inclRight _ _).op
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Characterize `Join.opEquivInverse` with respect to the left inclusion
-/
def inclLeftCompOpEquivInverse :
    Join.inclLeft Dᵒᵖ Cᵒᵖ ⋙ (opEquiv C D).inverse ≅ (inclRight _ _).op :=
  Join.mkFunctorLeft _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- Characterize `Join.opEquivInverse` with respect to the right inclusion -/
/-
**CategoryTheory.Join.inclRightCompOpEquivInverse** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Join`。
形式化陈述：inclRightCompOpEquivInverse : Join.inclRight Dᵒᵖ Cᵒᵖ ⋙ (opEquiv C D).inver
se ≅ (inclLeft _ _).op
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Characterize `Join.opEquivInverse` with respect to the right inclusion
-/
def inclRightCompOpEquivInverse :
    Join.inclRight Dᵒᵖ Cᵒᵖ ⋙ (opEquiv C D).inverse ≅ (inclLeft _ _).op :=
  Join.mkFunctorRight _ _ _

set_option backward.isDefEq.respectTransparency.types false in
variable {D} in
@[simp]
/-
**CategoryTheory.Join.inclLeftCompOpEquivInverse_hom_app_op** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Join`。
形式化陈述：inclLeftCompOpEquivInverse_hom_app_op (d : D) : (inclLeftCompOpEquivInvers
e C D).hom.app (op d) = 𝟙 (op <| right d)
参数：d : D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inclLeftCompOpEquivInverse_hom_app_op (d : D) :
    (inclLeftCompOpEquivInverse C D).hom.app (op d) = 𝟙 (op <| right d) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {C} in
@[simp]
/-
**CategoryTheory.Join.inclRightCompOpEquivInverse_hom_app_op** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Join`。
形式化陈述：inclRightCompOpEquivInverse_hom_app_op (c : C) : (inclRightCompOpEquivInve
rse C D).hom.app (op c) = 𝟙 (op <| left c)
参数：c : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inclRightCompOpEquivInverse_hom_app_op (c : C) :
    (inclRightCompOpEquivInverse C D).hom.app (op c) = 𝟙 (op <| left c) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {D} in
@[simp]
/-
**CategoryTheory.Join.inclLeftCompOpEquivInverse_inv_app_op** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Join`。
形式化陈述：inclLeftCompOpEquivInverse_inv_app_op (d : D) : (inclLeftCompOpEquivInvers
e C D).inv.app (op d) = 𝟙 (op <| right d)
参数：d : D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inclLeftCompOpEquivInverse_inv_app_op (d : D) :
    (inclLeftCompOpEquivInverse C D).inv.app (op d) = 𝟙 (op <| right d) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {C} in
@[simp]
/-
**CategoryTheory.Join.inclRightCompOpEquivInverse_inv_app_op** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Join`。
形式化陈述：inclRightCompOpEquivInverse_inv_app_op (c : C) : (inclRightCompOpEquivInve
rse C D).inv.app (op c) = 𝟙 (op <| left c)
参数：c : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inclRightCompOpEquivInverse_inv_app_op (c : C) :
    (inclRightCompOpEquivInverse C D).inv.app (op c) = 𝟙 (op <| left c) :=
  rfl

end CategoryTheory.Join

