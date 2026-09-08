/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.GradedObject.Trifunctor

/-!
# The associator for actions of bifunctors on graded objects

Given functors `F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂`, `G : C₁₂ ⥤ C₃ ⥤ C₄`,
`F : C₁ ⥤ C₂₃ ⥤ C₄`, `G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃` equipped with an isomorphism
`associator : bifunctorComp₁₂ F₁₂ G ≅ bifunctorComp₂₃ F G₂₃` (which informally means
that we have natural isomorphisms `G(F₁₂(X₁, X₂), X₃) ≅ F(X₁, G₂₃(X₂, X₃))`),
a map `r : I₁ × I₂ × I₃ → J`, and data `ρ₁₂ : BifunctorComp₁₂IndexData r` and
`ρ₂₃ : BifunctorComp₂₃IndexData r`, then if `X₁ : GradedObject I₁ C₁`,
`X₂ : GradedObject I₂ C₂` and `X₃ : GradedObject I₃ C₃`
satisfy suitable assumptions, we construct an isomorphism
`mapBifunctorAssociator associator ρ₁₂ ρ₂₃ X₁ X₂ X₃` between
`mapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃` and
`mapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃)` in the category
`GradedObject J C₄`.

This construction shall be used in the definition of the monoidal category structure
on graded objects indexed by an additive monoid.

-/

@[expose] public section

namespace CategoryTheory

open Category

namespace GradedObject

variable {C₁ C₂ C₁₂ C₂₃ C₃ C₄ : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄] [Category* C₁₂] [Category* C₂₃]
  {F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂} {G : C₁₂ ⥤ C₃ ⥤ C₄}
  {F : C₁ ⥤ C₂₃ ⥤ C₄} {G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃}
  (associator : bifunctorComp₁₂ F₁₂ G ≅ bifunctorComp₂₃ F G₂₃)
  {I₁ I₂ I₃ J : Type*} {r : I₁ × I₂ × I₃ → J}
  (ρ₁₂ : BifunctorComp₁₂IndexData r) (ρ₂₃ : BifunctorComp₂₃IndexData r)
  (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂) (X₃ : GradedObject I₃ C₃)
  [HasMap (((mapBifunctor F₁₂ I₁ I₂).obj X₁).obj X₂) ρ₁₂.p]
  [HasMap (((mapBifunctor G ρ₁₂.I₁₂ I₃).obj (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂)).obj X₃) ρ₁₂.q]
  [HasMap (((mapBifunctor G₂₃ I₂ I₃).obj X₂).obj X₃) ρ₂₃.p]
  [HasMap (((mapBifunctor F I₁ ρ₂₃.I₂₃).obj X₁).obj (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃)) ρ₂₃.q]
  [H₁₂ : HasGoodTrifunctor₁₂Obj F₁₂ G ρ₁₂ X₁ X₂ X₃]
  [H₂₃ : HasGoodTrifunctor₂₃Obj F G₂₃ ρ₂₃ X₁ X₂ X₃]

/-- Associator isomorphism for the action of bifunctors on graded objects. -/
/-
**CategoryTheory.GradedObject.mapBifunctorAssociator** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.GradedObject`。
形式化陈述：mapBifunctorAssociator : mapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁
₂ ρ₁₂.p X₁ X₂) X₃ ≅ mapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p 
X₂ X₃)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GradedObject.HasGoodTrifunctor₁₂Obj.hasMap`：∀ {C₁ : Type 
u_1} {C₂ : Type u_2} {C₃ : Type u_3} {C₄ : Type u_4} {C₁₂ : Type u_5}   [inst : 
CategoryTheory.Category.{v_1, u_1} C₁] [inst_1 …
· 使用定理 `CategoryTheory.GradedObject.HasGoodTrifunctor₂₃Obj.hasMap`：∀ {C₁ : Type 
u_1} {C₂ : Type u_2} {C₃ : Type u_3} {C₄ : Type u_4} {C₂₃ : Type u_6}   [inst : 
CategoryTheory.Category.{v_1, u_1} C₁] [inst_1 …

--- 原说明 ---
Associator isomorphism for the action of bifunctors on graded objects.
-/
noncomputable def mapBifunctorAssociator :
    mapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ ≅
      mapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) :=
  have := H₁₂.hasMap
  have := H₂₃.hasMap
  (mapBifunctorComp₁₂MapObjIso F₁₂ G ρ₁₂ X₁ X₂ X₃).symm ≪≫
    mapIso ((((mapTrifunctorMapIso associator I₁ I₂ I₃).app X₁).app X₂).app X₃) r ≪≫
    mapBifunctorComp₂₃MapObjIso F G₂₃ ρ₂₃ X₁ X₂ X₃

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp, nolint unusedHavesSuffices)]
/-
**CategoryTheory.GradedObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GradedO
bject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_mapBifunctorAssociator_hom (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) (h : r (i₁, i₂, i₃) = j) :
    ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫
      (mapBifunctorAssociator associator ρ₁₂ ρ₂₃ X₁ X₂ X₃).hom j =
        ((associator.hom.app (X₁ i₁)).app (X₂ i₂)).app (X₃ i₃) ≫
          ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h := by
  dsimp [mapBifunctorAssociator]
  rw [ι_mapBifunctorComp₁₂MapObjIso_inv_assoc, ιMapTrifunctorMapObj,
    ι_mapMap_assoc, mapTrifunctorMapNatTrans_app_app_app]
  erw [ι_mapBifunctorComp₂₃MapObjIso_hom]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.GradedObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GradedO
bject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_mapBifunctorAssociator_inv (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) (h : r (i₁, i₂, i₃) = j) :
    ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫
      (mapBifunctorAssociator associator ρ₁₂ ρ₂₃ X₁ X₂ X₃).inv j =
    ((associator.inv.app (X₁ i₁)).app (X₂ i₂)).app (X₃ i₃) ≫
      ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j h := by
  rw [← cancel_mono ((mapBifunctorAssociator associator ρ₁₂ ρ₂₃ X₁ X₂ X₃).hom j),
    assoc, assoc, Iso.inv_hom_id_eval, comp_id, ι_mapBifunctorAssociator_hom,
    ← NatTrans.comp_app_assoc, ← NatTrans.comp_app, Iso.inv_hom_id_app,
    NatTrans.id_app, NatTrans.id_app, id_comp]

end GradedObject

end CategoryTheory

