/-
Copyright (c) 2025 Moisés Herradón Cueto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moisés Herradón Cueto
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.WithTerminal.Basic

/-!
# Relations between `Cone`, `WithTerminal` and `Over`

Given categories `C` and `J`, an object `X : C` and a functor `K : J ⥤ Over X`,
it has an obvious lift `liftFromOver K : WithTerminal J ⥤ C`, namely, send the terminal
object to `X`. These two functors have equivalent categories of cones (`coneEquiv`).
As a corollary, the limit of `K` is the limit of `liftFromOver K`, and vice-versa.
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

open CategoryTheory Limits

universe w w' v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J]

namespace CategoryTheory.WithTerminal
variable {X : C} {K : J ⥤ Over X} {F : C ⥤ D} {t : Cone K}

set_option backward.defeqAttrib.useBackward true in
/-- The category of functors `J ⥤ Over X` can be seen as part of a comma category,
namely the comma category constructed from the identity of the category of functors
`J ⥤ C` and the functor that maps `X : C` to the constant functor `J ⥤ C`.

Given a functor `K : J ⥤ Over X`, it is mapped to a natural transformation from the
obvious functor `J ⥤ C` to the constant functor `X`. -/
@[simps]
/-
**CategoryTheory.WithTerminal.commaFromOver** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.WithTerminal`。
形式化陈述：commaFromOver : (J ⥤ Over X) ⥤ Comma (𝟭 (J ⥤ C)) (Functor.const J) where o
bj K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of functors `J ⥤ Over X` can be seen as part of a comma category,
namely the comma category constructed from the identity of the category of funct
ors
`J ⥤ C` and the functor that maps `X : C` to the constant functor `J ⥤ C`.

Given a functor `K : J ⥤ Over X`, it is mapped to a natural transformation from 
the
obvious functor `J ⥤ C` to the constant functor `X`.
-/
def commaFromOver : (J ⥤ Over X) ⥤ Comma (𝟭 (J ⥤ C)) (Functor.const J) where
  obj K := {
    left := K ⋙ Over.forget X
    right := X
    hom.app a := (K.obj a).hom
  }
  map f := {
    left := Functor.whiskerRight f (Over.forget X)
    right := 𝟙 X
  }

/-- For any functor `K : J ⥤ Over X`, there is a canonical extension
`WithTerminal J ⥤ C`, that sends `star` to `X`. -/
@[simps!]
/-
**CategoryTheory.WithTerminal.liftFromOver** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.WithTerminal`。
形式化陈述：liftFromOver : (J ⥤ Over X) ⥤ WithTerminal J ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any functor `K : J ⥤ Over X`, there is a canonical extension
`WithTerminal J ⥤ C`, that sends `star` to `X`.
-/
def liftFromOver : (J ⥤ Over X) ⥤ WithTerminal J ⥤ C := commaFromOver ⋙ equivComma.inverse

set_option backward.isDefEq.respectTransparency.types false in
/-- The extension of a functor to over categories behaves well with compositions. -/
@[simps]
/-
**CategoryTheory.WithTerminal.liftFromOverComp** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.WithTerminal`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {J : Typ
e w} →           [inst_2 : CategoryTheory.Category.{w', w} J] →             {X :
 C} →               {K : CategoryTheory.Functor J (CategoryTheory.Over X)} →    
             {F : CategoryTheory.Functor C D} →                   CategoryTheory
.WithTerminal.liftFromOver.obj (K.comp (CategoryTheory.Over.post F)) ≅          
           (CategoryTheory.WithTerminal.liftFromOver.obj K).comp F
参数：CategoryTheory.Over X；K.comp (CategoryTheory.Over.post F)；CategoryTheory.With
Terminal.liftFromOver.obj K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extension of a functor to over categories behaves well with compositions.
-/
def liftFromOverComp : liftFromOver.obj (K ⋙ Over.post F) ≅ liftFromOver.obj K ⋙ F where
  hom.app | star | of a => 𝟙 _
  inv.app | star | of a => 𝟙 _

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
/-- A cone of a functor `K : J ⥤ Over X` consists of an object of `Over X`, together
with morphisms. This same object is a cone of the extended functor
`liftFromOver.obj K : WithTerminal J ⥤ C`. -/
@[simps]
/-
**CategoryTheory.WithTerminal.coneLift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.WithTerminal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cone of a functor `K : J ⥤ Over X` consists of an object of `Over X`, together
with morphisms. This same object is a cone of the extended functor
`liftFromOver.obj K : WithTerminal J ⥤ C`.
-/
private def coneLift : Cone K ⥤ Cone (liftFromOver.obj K) where
  obj t := {
    pt := t.pt.left
    π.app
    | of a => (t.π.app a).left
    | star => t.pt.hom
    π.naturality
    | star, star, _
    | of a, star, _ => by aesop
    | of a, of b, f => by simp [← Comma.comp_left]
  }
  map {t₁ t₂} f := {
    hom := f.hom.left
    w
    | star => by cat_disch
    | of a => by simp [← Comma.comp_left]
  }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.privateInPublic true in
/-- This is the inverse of the previous construction: a cone of an extended functor
`liftFromOver.obj K : WithTerminal J ⥤ C` consists of an object of `C`, together
with morphisms. This same object is a cone of the original functor `K : J ⥤ Over X`. -/
@[simps]
/-
**CategoryTheory.WithTerminal.coneBack** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.WithTerminal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the inverse of the previous construction: a cone of an extended functor
`liftFromOver.obj K : WithTerminal J ⥤ C` consists of an object of `C`, together
with morphisms. This same object is a cone of the original functor `K : J ⥤ Over
 X`.
-/
private def coneBack : Cone (liftFromOver.obj K) ⥤ Cone K where
  obj t := {
    pt := .mk (t.π.app star)
    π.app a := Over.homMk (t.π.app (of a)) (t.w (homFrom a))
    π.naturality _ _ f := by ext; simpa using! (t.w (incl.map f)).symm }
  map {t₁ t₂ f} :=
    { hom := Over.homMk f.hom (by simp [dsimp% f.w star] )
      w j := by ext; simp [dsimp% f.w (of j)] }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Given a functor `K : J ⥤ Over X` and its extension `liftFromOver K : WithTerminal J ⥤ C`,
there is an obvious equivalence between cones of these two functors.
A cone of `K` is an object of `Over X`, so it has the form `t ⟶ X`.
Equivalently, a cone of `WithTerminal K` is an object `t : C`,
and we can recover the structure morphism as `π.app X : t ⟶ X`. -/
@[simps! functor_obj_pt functor_map_hom inverse_obj_pt_left inverse_obj_pt_right_as
  inverse_obj_pt_hom inverse_obj_π_app_left inverse_map_hom_left unitIso_hom_app_hom_left
  unitIso_inv_app_hom_left counitIso_hom_app_hom counitIso_inv_app_hom]
/-
**CategoryTheory.WithTerminal.coneEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.WithTerminal`。
形式化陈述：coneEquiv : Cone K ≌ Cone (liftFromOver.obj K) where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coneEquiv : Cone K ≌ Cone (liftFromOver.obj K) where
  functor := coneLift
  inverse := coneBack
  unitIso := .refl _
  counitIso := NatIso.ofComponents fun t ↦ Cone.ext <| .refl _

@[simp]
/-
**CategoryTheory.WithTerminal.coneEquiv_functor_obj_** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.WithTerminal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coneEquiv_functor_obj_π_app_star : (coneEquiv.functor.obj t).π.app star = t.pt.hom := rfl

@[simp]
/-
**CategoryTheory.WithTerminal.coneEquiv_functor_obj_** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.WithTerminal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coneEquiv_functor_obj_π_app_of (Y : J) :
    (coneEquiv.functor.obj t).π.app (of Y) = (t.π.app Y).left := rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- A cone `t` of `K : J ⥤ Over X` is a limit if and only if the corresponding cone
`coneLift t` of `liftFromOver.obj K : WithTerminal K ⥤ C` is a limit. -/
@[simps!]
/-
**CategoryTheory.WithTerminal.isLimitEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.WithTerminal`。
形式化陈述：isLimitEquiv : IsLimit (coneEquiv.functor.obj t) ≃ IsLimit t
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cone `t` of `K : J ⥤ Over X` is a limit if and only if the corresponding cone
`coneLift t` of `liftFromOver.obj K : WithTerminal K ⥤ C` is a limit.
-/
def isLimitEquiv : IsLimit (coneEquiv.functor.obj t) ≃ IsLimit t := IsLimit.ofConeEquiv coneEquiv

end WithTerminal

open WithTerminal in
/-
**CategoryTheory.Over.hasLimit_of_hasLimit_liftFromOver** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Over`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : Type w} [
inst_1 : CategoryTheory.Category.{w', w} J]   {X : C} (F : CategoryTheory.Functo
r J (CategoryTheory.Over X))   [CategoryTheory.Limits.HasLimit (CategoryTheory.W
ithTerminal.liftFromOver.obj F)], CategoryTheory.Limits.HasLimit F
参数：F : CategoryTheory.Functor J (CategoryTheory.Over X)；CategoryTheory.WithTermi
nal.liftFromOver.obj F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Over.hasLimit_of_hasLimit_liftFromOver {X : C} (F : J ⥤ Over X)
    [HasLimit (liftFromOver.obj F)] : HasLimit F :=
  ⟨_, isLimitEquiv <| .ofIsoLimit
    (limit.isLimit (liftFromOver.obj F)) (coneEquiv.counitIso.app _).symm⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) [HasLimitsOfShape (WithTerminal J) C] :
    HasLimitsOfShape J (Over X) where
  has_limit _ := Over.hasLimit_of_hasLimit_liftFromOver ..
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) [HasLimitsOfSize.{w, w'} C] : HasLimitsOfSize.{w, w'} (Over X) where

namespace WithInitial
variable {X : C} {K : J ⥤ Under X} {F : C ⥤ D} {t : Cocone K}

/-- The category of functors `J ⥤ Under X` can be seen as part of a comma category,
namely the comma category constructed from the identity of the category of functors
`J ⥤ C` and the functor that maps `X : C` to the constant functor `J ⥤ C`.

Given a functor `K : J ⥤ Under X`, it is mapped to a natural transformation to the
obvious functor `J ⥤ C` from the constant functor `X`. -/
@[simps]
/-
**CategoryTheory.WithInitial.commaFromUnder** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.WithInitial`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : T
ype w} →       [inst_1 : CategoryTheory.Category.{w', w} J] →         {X : C} → 
          CategoryTheory.Functor (CategoryTheory.Functor J (CategoryTheory.Under
 X))             (CategoryTheory.Comma (CategoryTheory.Functor.const J)         
      (CategoryTheory.Functor.id (CategoryTheory.Functor J C)))
参数：CategoryTheory.Functor J (CategoryTheory.Under X)；CategoryTheory.Comma (Categ
oryTheory.Functor.const J)               (CategoryTheory.Functor.id (CategoryThe
ory.Functor J C))。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of functors `J ⥤ Under X` can be seen as part of a comma category,
namely the comma category constructed from the identity of the category of funct
ors
`J ⥤ C` and the functor that maps `X : C` to the constant functor `J ⥤ C`.

Given a functor `K : J ⥤ Under X`, it is mapped to a natural transformation to t
he
obvious functor `J ⥤ C` from the constant functor `X`.
-/
def commaFromUnder : (J ⥤ Under X) ⥤ Comma (Functor.const J) (𝟭 (J ⥤ C)) where
  obj K := {
    left := X
    right := K ⋙ Under.forget X
    hom.app a := (K.obj a).hom
  }
  map f := {
    left := 𝟙 X
    right := Functor.whiskerRight f (Under.forget X)
  }

/-- For any functor `K : J ⥤ Under X`, there is a canonical extension
`WithInitial J ⥤ C`, that sends `star` to `X`. -/
@[simps!]
/-
**CategoryTheory.WithInitial.liftFromUnder** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.WithInitial`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : T
ype w} →       [inst_1 : CategoryTheory.Category.{w', w} J] →         {X : C} → 
          CategoryTheory.Functor (CategoryTheory.Functor J (CategoryTheory.Under
 X))             (CategoryTheory.Functor (CategoryTheory.WithInitial J) C)
参数：CategoryTheory.Functor J (CategoryTheory.Under X)；CategoryTheory.Functor (Cat
egoryTheory.WithInitial J) C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any functor `K : J ⥤ Under X`, there is a canonical extension
`WithInitial J ⥤ C`, that sends `star` to `X`.
-/
def liftFromUnder : (J ⥤ Under X) ⥤ WithInitial J ⥤ C := commaFromUnder ⋙ equivComma.inverse

set_option backward.isDefEq.respectTransparency.types false in
/-- The extension of a functor to under categories behaves well with compositions. -/
@[simps]
/-
**CategoryTheory.WithInitial.liftFromUnderComp** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.WithInitial`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {J : Typ
e w} →           [inst_2 : CategoryTheory.Category.{w', w} J] →             {X :
 C} →               {K : CategoryTheory.Functor J (CategoryTheory.Under X)} →   
              {F : CategoryTheory.Functor C D} →                   CategoryTheor
y.WithInitial.liftFromUnder.obj (K.comp (CategoryTheory.Under.post F)) ≅        
             (CategoryTheory.WithInitial.liftFromUnder.obj K).comp F
参数：CategoryTheory.Under X；K.comp (CategoryTheory.Under.post F)；CategoryTheory.Wi
thInitial.liftFromUnder.obj K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extension of a functor to under categories behaves well with compositions.
-/
def liftFromUnderComp : liftFromUnder.obj (K ⋙ Under.post F) ≅ liftFromUnder.obj K ⋙ F where
  hom.app | star | of a => 𝟙 _
  inv.app | star | of a => 𝟙 _

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
/-- A cocone of a functor `K : J ⥤ Under X` consists of an object of `Under X`, together
with morphisms. This same object is a cocone of the extended functor
`liftFromUnder.obj K : WithInitial J ⥤ C`. -/
@[simps]
/-
**CategoryTheory.WithInitial.coconeLift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.WithInitial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cocone of a functor `K : J ⥤ Under X` consists of an object of `Under X`, toge
ther
with morphisms. This same object is a cocone of the extended functor
`liftFromUnder.obj K : WithInitial J ⥤ C`.
-/
private def coconeLift : Cocone K ⥤ Cocone (liftFromUnder.obj K) where
  obj t := {
    pt := t.pt.right
    ι.app
    | of a => (t.ι.app a).right
    | star => t.pt.hom
    ι.naturality
    | star, star, _
    | star, of b, _ => by aesop
    | of a, of b, f => by simp [← Comma.comp_right]
  }
  map {t₁ t₂} f := {
    hom := f.hom.right
    w
    | star => by cat_disch
    | of a => by simp [← Comma.comp_right]
  }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.privateInPublic true in
/-- This is the inverse of the previous construction: a cocone of an extended functor
`liftFromUnder.obj K : WithInitial J ⥤ C` consists of an object of `C`, together
with morphisms. This same object is a cocone of the original functor `K : J ⥤ Under X`. -/
@[simps]
/-
**CategoryTheory.WithInitial.coconeBack** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.WithInitial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the inverse of the previous construction: a cocone of an extended functo
r
`liftFromUnder.obj K : WithInitial J ⥤ C` consists of an object of `C`, together
with morphisms. This same object is a cocone of the original functor `K : J ⥤ Un
der X`.
-/
private def coconeBack : Cocone (liftFromUnder.obj K) ⥤ Cocone K where
  obj t := {
    pt := .mk (t.ι.app star)
    ι.app a := Under.homMk (t.ι.app (of a)) (t.w (homTo a))
    ι.naturality _ _ f := by ext; simpa using! t.ι.naturality (incl.map f) }
  map {t₁ t₂ f} :=
    { hom := Under.homMk f.hom (f.w .star)
      w j := by ext; simp [dsimp% f.w (of j)] }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Given a functor `K : J ⥤ Under X` and its extension `liftFromUnder K : WithInitial J ⥤ C`,
there is an obvious equivalence between cocones of these two functors.
A cocone of `K` is an object of `Under X`, so it has the form `X ⟶ t`.
Equivalently, a cocone of `WithInitial K` is an object `t : C`,
and we can recover the structure morphism as `ι.app X : X ⟶ t`. -/
@[simps! functor_obj_pt functor_map_hom inverse_obj_pt_right inverse_obj_pt_left_as
  inverse_obj_pt_hom inverse_obj_ι_app_right inverse_map_hom_right unitIso_hom_app_hom_right
  unitIso_inv_app_hom_right counitIso_hom_app_hom counitIso_inv_app_hom]
/-
**CategoryTheory.WithInitial.coconeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.WithInitial`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : T
ype w} →       [inst_1 : CategoryTheory.Category.{w', w} J] →         {X : C} → 
          {K : CategoryTheory.Functor J (CategoryTheory.Under X)} →             
CategoryTheory.Limits.Cocone K ≌               CategoryTheory.Limits.Cocone (Cat
egoryTheory.WithInitial.liftFromUnder.obj K)
参数：CategoryTheory.Under X；CategoryTheory.WithInitial.liftFromUnder.obj K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coconeEquiv : Cocone K ≌ Cocone (liftFromUnder.obj K) where
  functor := coconeLift
  inverse := coconeBack
  unitIso := .refl _
  counitIso := NatIso.ofComponents fun t ↦ Cocone.ext <| .refl _

@[simp]
/-
**CategoryTheory.WithInitial.coconeEquiv_functor_obj_** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.WithInitial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coconeEquiv_functor_obj_ι_app_star : (coconeEquiv.functor.obj t).ι.app star = t.pt.hom := rfl

@[simp]
/-
**CategoryTheory.WithInitial.coconeEquiv_functor_obj_** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.WithInitial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coconeEquiv_functor_obj_ι_app_of (Y : J) :
    (coconeEquiv.functor.obj t).ι.app (of Y) = (t.ι.app Y).right := rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- A cocone `t` of `K : J ⥤ Under X` is a colimit if and only if the corresponding cocone
`coconeLift t` of `liftFromUnder.obj K : WithInitial K ⥤ C` is a colimit. -/
@[simps!]
/-
**CategoryTheory.WithInitial.isColimitEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.WithInitial`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : T
ype w} →       [inst_1 : CategoryTheory.Category.{w', w} J] →         {X : C} → 
          {K : CategoryTheory.Functor J (CategoryTheory.Under X)} →             
{t : CategoryTheory.Limits.Cocone K} →               CategoryTheory.Limits.IsCol
imit (CategoryTheory.WithInitial.coconeEquiv.functor.obj t) ≃                 Ca
tegoryTheory.Limits.IsColimit t
参数：CategoryTheory.Under X；CategoryTheory.WithInitial.coconeEquiv.functor.obj t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cocone `t` of `K : J ⥤ Under X` is a colimit if and only if the corresponding 
cocone
`coconeLift t` of `liftFromUnder.obj K : WithInitial K ⥤ C` is a colimit.
-/
def isColimitEquiv : IsColimit (coconeEquiv.functor.obj t) ≃ IsColimit t :=
  IsColimit.ofCoconeEquiv coconeEquiv

end CategoryTheory.WithInitial

open WithInitial in
/-
**Under.hasColimit_of_hasColimit_liftFromUnder** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.WithTerminal.WithInitial`。
形式化陈述：Under.hasColimit_of_hasColimit_liftFromUnder {X : C} (F : J ⥤ Under X) [Ha
sColimit (liftFromUnder.obj F)] : HasColimit F
参数：F : J ⥤ Under X；liftFromUnder.obj F。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Under.hasColimit_of_hasColimit_liftFromUnder {X : C} (F : J ⥤ Under X)
    [HasColimit (liftFromUnder.obj F)] : HasColimit F :=
  ⟨_, isColimitEquiv <| .ofIsoColimit
    (colimit.isColimit (liftFromUnder.obj F)) (coconeEquiv.counitIso.app _).symm⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) [HasColimitsOfShape (WithInitial J) C] :
    HasColimitsOfShape J (Under X) where
  has_colimit _ := Under.hasColimit_of_hasColimit_liftFromUnder ..
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) [HasColimitsOfSize.{w, w'} C] : HasColimitsOfSize.{w, w'} (Under X) where
