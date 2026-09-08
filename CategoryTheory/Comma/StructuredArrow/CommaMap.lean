/-
Copyright (c) 2024 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Structured arrow categories on `Comma.map`

We characterize structured arrow categories on arbitrary instances of `Comma.map` as a
comma category itself.
-/

@[expose] public section

namespace CategoryTheory

namespace StructuredArrow

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {T : Type u₃} [Category.{v₃} T] {L : C ⥤ T} {R : D ⥤ T}
  {C' : Type u₄} [Category.{v₄} C'] {D' : Type u₅} [Category.{v₅} D'] {T' : Type u₆}
  [Category.{v₆} T'] {L' : C' ⥤ T'} {R' : D' ⥤ T'} {F₁ : C ⥤ C'} {F₂ : D ⥤ D'} {F : T ⥤ T'}
  (α : F₁ ⋙ L' ⟶ L ⋙ F) (β : R ⋙ F ⟶ F₂ ⋙ R')

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor establishing the equivalence `StructuredArrow.commaMapEquivalence`. -/
@[simps, implicit_reducible]
/-
**CategoryTheory.StructuredArrow.commaMapEquivalenceFunctor** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.StructuredArrow`。
形式化陈述：commaMapEquivalenceFunctor [IsIso β] (X : Comma L' R') : StructuredArrow X
 (Comma.map α β) ⥤ Comma (map₂ (𝟙 _) α) (map₂ X.hom (inv β)) where obj Y
参数：X : Comma L' R'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor establishing the equivalence `StructuredArrow.commaMapEquivalence`.
-/
def commaMapEquivalenceFunctor [IsIso β] (X : Comma L' R') :
    StructuredArrow X (Comma.map α β) ⥤ Comma (map₂ (𝟙 _) α) (map₂ X.hom (inv β)) where
  obj Y := ⟨mk Y.hom.left, mk Y.hom.right,
    homMk Y.right.hom
      (by simpa only [Functor.const_obj_obj, map₂_obj_left, mk_left, map₂_obj_right, mk_right,
        map₂_obj_hom, mk_hom_eq_self, Category.id_comp, Category.assoc, NatIso.isIso_inv_app,
        Functor.comp_obj, Comma.map_obj_right, Comma.map_obj_left, Comma.map_obj_hom,
        IsIso.hom_inv_id, Category.comp_id] using
        congrFun (congrArg CategoryStruct.comp Y.hom.w) (inv (β.app Y.right.right) :))⟩
  map {Y Z} f := ⟨homMk f.right.left (congrArg CommaMorphism.left (StructuredArrow.w f)),
    homMk f.right.right (congrArg CommaMorphism.right (StructuredArrow.w f)),
    by simp only [map₂_obj_right, mk_right, hom_eq_iff, comp_right,
      map₂_map_right, homMk_right, CommaMorphism.w] ⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The inverse functor establishing the equivalence `StructuredArrow.commaMapEquivalence`. -/
@[simps]
/-
**CategoryTheory.StructuredArrow.commaMapEquivalenceInverse** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.StructuredArrow`。
形式化陈述：commaMapEquivalenceInverse [IsIso β] (X : Comma L' R') : Comma (map₂ (𝟙 _)
 α) (map₂ X.hom (inv β)) ⥤ StructuredArrow X (Comma.map α β) where obj Y
参数：X : Comma L' R'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse functor establishing the equivalence `StructuredArrow.commaMapEquiva
lence`.
-/
def commaMapEquivalenceInverse [IsIso β] (X : Comma L' R') :
    Comma (map₂ (𝟙 _) α) (map₂ X.hom (inv β)) ⥤ StructuredArrow X (Comma.map α β) where
  obj Y := mk (Y := ⟨Y.left.right, Y.right.right, Y.hom.right⟩)
    ⟨by exact Y.left.hom, by exact Y.right.hom, by
      simpa using congrFun (congrArg CategoryStruct.comp (StructuredArrow.w Y.hom))
        (β.app Y.right.right)⟩
  map {Y Z} f := homMk ⟨by exact f.left.right, by exact f.right.right,
    by exact congrArg CommaMorphism.right f.w⟩

set_option backward.defeqAttrib.useBackward true in
/-- The unit establishing the equivalence `StructuredArrow.commaMapEquivalence`. -/
@[simps!]
/-
**CategoryTheory.StructuredArrow.commaMapEquivalenceUnitIso** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.StructuredArrow`。
形式化陈述：commaMapEquivalenceUnitIso [IsIso β] (X : Comma L' R') : 𝟭 (StructuredArro
w X (Comma.map α β)) ≅ commaMapEquivalenceFunctor α β X ⋙ commaMapEquivalenceInv
erse α β X
参数：X : Comma L' R'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit establishing the equivalence `StructuredArrow.commaMapEquivalence`.
-/
def commaMapEquivalenceUnitIso [IsIso β] (X : Comma L' R') :
    𝟭 (StructuredArrow X (Comma.map α β)) ≅
      commaMapEquivalenceFunctor α β X ⋙ commaMapEquivalenceInverse α β X :=
  NatIso.ofComponents (fun _ => isoMk (Iso.refl _))

set_option backward.defeqAttrib.useBackward true in
/-- The counit functor establishing the equivalence `StructuredArrow.commaMapEquivalence`. -/
@[simps!]
/-
**CategoryTheory.StructuredArrow.commaMapEquivalenceCounitIso** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.StructuredArrow`。
形式化陈述：commaMapEquivalenceCounitIso [IsIso β] (X : Comma L' R') : commaMapEquival
enceInverse α β X ⋙ commaMapEquivalenceFunctor α β X ≅ 𝟭 (Comma (map₂ (𝟙 (L'.obj
 X.left)) α) (map₂ X.hom (inv β)))
参数：X : Comma L' R'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit functor establishing the equivalence `StructuredArrow.commaMapEquival
ence`.
-/
def commaMapEquivalenceCounitIso [IsIso β] (X : Comma L' R') :
    commaMapEquivalenceInverse α β X ⋙ commaMapEquivalenceFunctor α β X ≅
      𝟭 (Comma (map₂ (𝟙 (L'.obj X.left)) α) (map₂ X.hom (inv β))) :=
  NatIso.ofComponents (fun _ => Comma.isoMk (Iso.refl _) (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The structured arrow category on the functor `Comma.map α β`, with `β` a natural isomorphism,
is equivalent to a comma category on two instances of `StructuredArrow.map₂`. -/
/-
**CategoryTheory.StructuredArrow.commaMapEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.StructuredArrow`。
形式化陈述：commaMapEquivalence [IsIso β] (X : Comma L' R') : StructuredArrow X (Comma
.map α β) ≌ Comma (map₂ (𝟙 _) α) (map₂ X.hom (inv β)) where functor
参数：X : Comma L' R'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structured arrow category on the functor `Comma.map α β`, with `β` a natural
 isomorphism,
is equivalent to a comma category on two instances of `StructuredArrow.map₂`.
-/
def commaMapEquivalence [IsIso β] (X : Comma L' R') :
    StructuredArrow X (Comma.map α β) ≌ Comma (map₂ (𝟙 _) α) (map₂ X.hom (inv β)) where
  functor := commaMapEquivalenceFunctor α β X
  inverse := commaMapEquivalenceInverse α β X
  unitIso := commaMapEquivalenceUnitIso α β X
  counitIso := commaMapEquivalenceCounitIso α β X

end

end StructuredArrow

end CategoryTheory

