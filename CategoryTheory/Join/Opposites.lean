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
/--
Definition of `opEquiv` / `opEquiv` 的定义

English:
definition opEquiv
  signature: : (C ⋆ D)ᵒᵖ ≌ Dᵒᵖ ⋆ Cᵒᵖ where
  body: Functor.leftOp
    Join.mkFunctor (inclRight _ _).rightOp (inclLeft _ _).rightOp { app _ := (edge _ _).op }
  inverse := Join.mkFunctor (inclRight _ _).op (inclLeft _ _).op { app _ := (edge _ _).op }
  unitIso := NatIso.ofComponents
    (fun
      | op (left _) => Iso.refl _
      | op (right _) => 

中文:
定义 opEquiv
  签名: : (C ⋆ D)ᵒᵖ ≌ Dᵒᵖ ⋆ Cᵒᵖ where
  定义体: Functor.leftOp
    Join.mkFunctor (inclRight _ _).rightOp (inclLeft _ _).rightOp { app _ := (edge _ _).op }
  inverse := Join.mkFunctor (inclRight _ _).op (inclLeft _ _).op { app _ := (edge _ _).op }
  unitIso := NatIso.ofComponents
    (fun
      | op (left _) => Iso.refl _
      | op (right _) => 

Depends on / 依赖: Functor, Functor.leftOp, leftOp
-/
def opEquiv : (C ⋆ D)ᵒᵖ ≌ Dᵒᵖ ⋆ Cᵒᵖ where
functor := Functor.leftOp
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
/--
lemma `opEquiv_functor_obj_op_left` / 引理 `opEquiv_functor_obj_op_left`

English:
lemma opEquiv_functor_obj_op_left
  given: (c : C)
  proof: rfl

中文:
引理 opEquiv_functor_obj_op_left
  条件: (c : C)
  证明: rfl
-/
lemma opEquiv_functor_obj_op_left (c : C) :
    (opEquiv C D).functor.obj (op <| left c) = right (op c) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {D} in
@[simp]
/--
lemma `opEquiv_functor_obj_op_right` / 引理 `opEquiv_functor_obj_op_right`

English:
lemma opEquiv_functor_obj_op_right
  given: (d : D)
  proof: rfl

中文:
引理 opEquiv_functor_obj_op_right
  条件: (d : D)
  证明: rfl
-/
lemma opEquiv_functor_obj_op_right (d : D) :
    (opEquiv C D).functor.obj (op <| right d) = left (op d) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {C} in
@[simp]
/--
lemma `opEquiv_functor_map_op_inclLeft` / 引理 `opEquiv_functor_map_op_inclLeft`

English:
lemma opEquiv_functor_map_op_inclLeft
  given: {c c' : C} (f : c ⟶ c')
  proof: rfl

中文:
引理 opEquiv_functor_map_op_inclLeft
  条件: {c c' : C} (f : c ⟶ c')
  证明: rfl
-/
lemma opEquiv_functor_map_op_inclLeft {c c' : C} (f : c ⟶ c') :
    (opEquiv C D).functor.map (op <| (inclLeft C D).map f) = (inclRight _ _).map (op f) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {D} in
@[simp]
/--
lemma `opEquiv_functor_map_op_inclRight` / 引理 `opEquiv_functor_map_op_inclRight`

English:
lemma opEquiv_functor_map_op_inclRight
  given: {d d' : D} (f : d ⟶ d')
  proof: rfl

中文:
引理 opEquiv_functor_map_op_inclRight
  条件: {d d' : D} (f : d ⟶ d')
  证明: rfl
-/
lemma opEquiv_functor_map_op_inclRight {d d' : D} (f : d ⟶ d') :
    (opEquiv C D).functor.map (op <| (inclRight C D).map f) = (inclLeft _ _).map (op f) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {C D} in
/--
lemma `opEquiv_functor_map_op_edge` / 引理 `opEquiv_functor_map_op_edge`

English:
lemma opEquiv_functor_map_op_edge
  given: (c : C) (d : D)
  proof: rfl

中文:
引理 opEquiv_functor_map_op_edge
  条件: (c : C) (d : D)
  证明: rfl
-/
lemma opEquiv_functor_map_op_edge (c : C) (d : D) :
    (opEquiv C D).functor.map (op <| edge c d) = edge (op d) (op c) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Characterize (up to a rightOp) the action of the left inclusion on `Join.opEquivFunctor`. -/
@[simps!]
/--
Definition of `InclLeftCompRightOpOpEquivFunctor` / `InclLeftCompRightOpOpEquivFunctor` 的定义

English:
definition InclLeftCompRightOpOpEquivFunctor
  signature: :
  body: isoWhiskerLeft _ (leftOpRightOpIso _) ≪≫ mkFunctorLeft _ _ _

中文:
定义 InclLeftCompRightOpOpEquivFunctor
  签名: :
  定义体: isoWhiskerLeft _ (leftOpRightOpIso _) ≪≫ mkFunctorLeft _ _ _

Depends on / 依赖: isoWhiskerLeft, leftOpRightOpIso, mkFunctorLeft
-/
def InclLeftCompRightOpOpEquivFunctor :
    inclLeft C D ⋙ (opEquiv C D).functor.rightOp ≅ (inclRight _ _).rightOp :=
  isoWhiskerLeft _ (leftOpRightOpIso _) ≪≫ mkFunctorLeft _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- Characterize (up to a rightOp) the action of the right inclusion on `Join.opEquivFunctor`. -/
@[simps!]
/--
Definition of `InclRightCompRightOpOpEquivFunctor` / `InclRightCompRightOpOpEquivFunctor` 的定义

English:
definition InclRightCompRightOpOpEquivFunctor
  signature: :
  body: isoWhiskerLeft _ (leftOpRightOpIso _) ≪≫ mkFunctorRight _ _ _

中文:
定义 InclRightCompRightOpOpEquivFunctor
  签名: :
  定义体: isoWhiskerLeft _ (leftOpRightOpIso _) ≪≫ mkFunctorRight _ _ _

Depends on / 依赖: isoWhiskerLeft, leftOpRightOpIso, mkFunctorRight
-/
def InclRightCompRightOpOpEquivFunctor :
    inclRight C D ⋙ (opEquiv C D).functor.rightOp ≅ (inclLeft _ _).rightOp :=
  isoWhiskerLeft _ (leftOpRightOpIso _) ≪≫ mkFunctorRight _ _ _

set_option backward.isDefEq.respectTransparency.types false in
variable {D} in
@[simp]
/--
lemma `opEquiv_inverse_obj_left_op` / 引理 `opEquiv_inverse_obj_left_op`

English:
lemma opEquiv_inverse_obj_left_op
  given: (d : D)
  proof: rfl

中文:
引理 opEquiv_inverse_obj_left_op
  条件: (d : D)
  证明: rfl
-/
lemma opEquiv_inverse_obj_left_op (d : D) :
    (opEquiv C D).inverse.obj (left <| op d) = op (right d) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {C} in
@[simp]
/--
lemma `opEquiv_inverse_obj_right_op` / 引理 `opEquiv_inverse_obj_right_op`

English:
lemma opEquiv_inverse_obj_right_op
  given: (c : C)
  proof: rfl

中文:
引理 opEquiv_inverse_obj_right_op
  条件: (c : C)
  证明: rfl
-/
lemma opEquiv_inverse_obj_right_op (c : C) :
    (opEquiv C D).inverse.obj (right <| op c) = op (left c) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {D} in
@[simp]
/--
lemma `opEquiv_inverse_map_inclLeft_op` / 引理 `opEquiv_inverse_map_inclLeft_op`

English:
lemma opEquiv_inverse_map_inclLeft_op
  given: {d d' : D} (f : d ⟶ d')
  proof: rfl

中文:
引理 opEquiv_inverse_map_inclLeft_op
  条件: {d d' : D} (f : d ⟶ d')
  证明: rfl
-/
lemma opEquiv_inverse_map_inclLeft_op {d d' : D} (f : d ⟶ d') :
    (opEquiv C D).inverse.map ((inclLeft Dᵒᵖ Cᵒᵖ).map f.op) = op ((inclRight _ _).map f) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {D} in
@[simp]
/--
lemma `opEquiv_inverse_map_inclRight_op` / 引理 `opEquiv_inverse_map_inclRight_op`

English:
lemma opEquiv_inverse_map_inclRight_op
  given: {c c' : C} (f : c ⟶ c')
  proof: rfl

中文:
引理 opEquiv_inverse_map_inclRight_op
  条件: {c c' : C} (f : c ⟶ c')
  证明: rfl
-/
lemma opEquiv_inverse_map_inclRight_op {c c' : C} (f : c ⟶ c') :
    (opEquiv C D).inverse.map ((inclRight Dᵒᵖ Cᵒᵖ).map f.op) = op ((inclLeft _ _).map f) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {C D} in
@[simp]
/--
lemma `opEquiv_inverse_map_edge_op` / 引理 `opEquiv_inverse_map_edge_op`

English:
lemma opEquiv_inverse_map_edge_op
  given: (c : C) (d : D)
  proof: rfl

中文:
引理 opEquiv_inverse_map_edge_op
  条件: (c : C) (d : D)
  证明: rfl
-/
lemma opEquiv_inverse_map_edge_op (c : C) (d : D) :
    (opEquiv C D).inverse.map (edge (op d) (op c)) = op (edge c d) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `inclLeftCompOpEquivInverse` / `inclLeftCompOpEquivInverse` 的定义

English:
definition inclLeftCompOpEquivInverse
  signature: :
  body: Join.mkFunctorLeft _ _ _

中文:
定义 inclLeftCompOpEquivInverse
  签名: :
  定义体: Join.mkFunctorLeft _ _ _

Depends on / 依赖: Join.mkFunctorLeft, mkFunctorLeft
-/
def inclLeftCompOpEquivInverse :
    Join.inclLeft Dᵒᵖ Cᵒᵖ ⋙ (opEquiv C D).inverse ≅ (inclRight _ _).op :=
  Join.mkFunctorLeft _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `inclRightCompOpEquivInverse` / `inclRightCompOpEquivInverse` 的定义

English:
definition inclRightCompOpEquivInverse
  signature: :
  body: Join.mkFunctorRight _ _ _

中文:
定义 inclRightCompOpEquivInverse
  签名: :
  定义体: Join.mkFunctorRight _ _ _

Depends on / 依赖: Join.mkFunctorRight, mkFunctorRight
-/
def inclRightCompOpEquivInverse :
    Join.inclRight Dᵒᵖ Cᵒᵖ ⋙ (opEquiv C D).inverse ≅ (inclLeft _ _).op :=
  Join.mkFunctorRight _ _ _

set_option backward.isDefEq.respectTransparency.types false in
variable {D} in
@[simp]
/--
lemma `inclLeftCompOpEquivInverse_hom_app_op` / 引理 `inclLeftCompOpEquivInverse_hom_app_op`

English:
lemma inclLeftCompOpEquivInverse_hom_app_op
  given: (d : D)
  proof: rfl

中文:
引理 inclLeftCompOpEquivInverse_hom_app_op
  条件: (d : D)
  证明: rfl
-/
lemma inclLeftCompOpEquivInverse_hom_app_op (d : D) :
    (inclLeftCompOpEquivInverse C D).hom.app (op d) = 𝟙 (op <| right d) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {C} in
@[simp]
/--
lemma `inclRightCompOpEquivInverse_hom_app_op` / 引理 `inclRightCompOpEquivInverse_hom_app_op`

English:
lemma inclRightCompOpEquivInverse_hom_app_op
  given: (c : C)
  proof: rfl

中文:
引理 inclRightCompOpEquivInverse_hom_app_op
  条件: (c : C)
  证明: rfl
-/
lemma inclRightCompOpEquivInverse_hom_app_op (c : C) :
    (inclRightCompOpEquivInverse C D).hom.app (op c) = 𝟙 (op <| left c) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {D} in
@[simp]
/--
lemma `inclLeftCompOpEquivInverse_inv_app_op` / 引理 `inclLeftCompOpEquivInverse_inv_app_op`

English:
lemma inclLeftCompOpEquivInverse_inv_app_op
  given: (d : D)
  proof: rfl

中文:
引理 inclLeftCompOpEquivInverse_inv_app_op
  条件: (d : D)
  证明: rfl
-/
lemma inclLeftCompOpEquivInverse_inv_app_op (d : D) :
    (inclLeftCompOpEquivInverse C D).inv.app (op d) = 𝟙 (op <| right d) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {C} in
@[simp]
/--
lemma `inclRightCompOpEquivInverse_inv_app_op` / 引理 `inclRightCompOpEquivInverse_inv_app_op`

English:
lemma inclRightCompOpEquivInverse_inv_app_op
  given: (c : C)
  proof: rfl

中文:
引理 inclRightCompOpEquivInverse_inv_app_op
  条件: (c : C)
  证明: rfl
-/
lemma inclRightCompOpEquivInverse_inv_app_op (c : C) :
    (inclRightCompOpEquivInverse C D).inv.app (op c) = 𝟙 (op <| left c) :=
  rfl

end CategoryTheory.Join
