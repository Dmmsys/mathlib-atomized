/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Cones and limits

In this file, we give the natural isomorphism between cones on `F` with cone point `X` and the type
`lim Hom(X, F·)`, and similarly the natural isomorphism between cocones on `F` with cocone point `X`
and the type `lim Hom(F·, X)`.

-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits

open CategoryTheory.Functor Opposite

section

variable {J C : Type*} [Category* J] [Category* C]

set_option backward.defeqAttrib.useBackward true in
/-- Sections of `F ⋙ coyoneda.obj (op X)` identify to natural
transformations `(const J).obj X ⟶ F`. -/
@[simps]
/-
**CategoryTheory.Limits.compCoyonedaSectionsEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：compCoyonedaSectionsEquiv (F : J ⥤ C) (X : C) : (F ⋙ coyoneda.obj (op X)).
sections ≃ ((const J).obj X ⟶ F) where toFun s
参数：F : J ⥤ C；X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sections of `F ⋙ coyoneda.obj (op X)` identify to natural
transformations `(const J).obj X ⟶ F`.
-/
def compCoyonedaSectionsEquiv (F : J ⥤ C) (X : C) :
    (F ⋙ coyoneda.obj (op X)).sections ≃ ((const J).obj X ⟶ F) where
  toFun s :=
    { app := fun j => s.val j
      naturality := fun j j' f => by
        dsimp
        rw [Category.id_comp]
        exact (s.property f).symm }
  invFun τ := ⟨τ.app, fun {j j'} f => by simpa using! (τ.naturality f).symm⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Sections of `F.op ⋙ yoneda.obj X` identify to natural
transformations `F ⟶ (const J).obj X`. -/
@[simps]
/-
**CategoryTheory.Limits.opCompYonedaSectionsEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：opCompYonedaSectionsEquiv (F : J ⥤ C) (X : C) : (F.op ⋙ yoneda.obj X).sect
ions ≃ (F ⟶ (const J).obj X) where toFun s
参数：F : J ⥤ C；X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sections of `F.op ⋙ yoneda.obj X` identify to natural
transformations `F ⟶ (const J).obj X`.
-/
def opCompYonedaSectionsEquiv (F : J ⥤ C) (X : C) :
    (F.op ⋙ yoneda.obj X).sections ≃ (F ⟶ (const J).obj X) where
  toFun s :=
    { app := fun j => s.val (op j)
      naturality := fun j j' f => by
        dsimp
        rw [Category.comp_id]
        exact (s.property f.op) }
  invFun τ := ⟨fun j => τ.app j.unop, fun {j j'} f => by simp [τ.naturality f.unop]⟩

set_option backward.defeqAttrib.useBackward true in
/-- Sections of `F ⋙ yoneda.obj X` identify to natural
transformations `(const J).obj X ⟶ F`. -/
@[simps]
/-
**CategoryTheory.Limits.compYonedaSectionsEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：compYonedaSectionsEquiv (F : J ⥤ Cᵒᵖ) (X : C) : (F ⋙ yoneda.obj X).section
s ≃ ((const J).obj (op X) ⟶ F) where toFun s
参数：F : J ⥤ Cᵒᵖ；X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sections of `F ⋙ yoneda.obj X` identify to natural
transformations `(const J).obj X ⟶ F`.
-/
def compYonedaSectionsEquiv (F : J ⥤ Cᵒᵖ) (X : C) :
    (F ⋙ yoneda.obj X).sections ≃ ((const J).obj (op X) ⟶ F) where
  toFun s :=
    { app := fun j => (s.val j).op
      naturality := fun j j' f => by
        dsimp
        rw [Category.id_comp]
        exact Quiver.Hom.unop_inj (s.property f).symm }
  invFun τ := ⟨fun j => (τ.app j).unop,
    fun {j j'} f => Quiver.Hom.op_inj (by simpa using! (τ.naturality f).symm)⟩

end

variable {J : Type v} [SmallCategory J] {C : Type u} [Category.{v} C]

set_option backward.defeqAttrib.useBackward true in
attribute [local simp←] comp_apply in
set_option backward.isDefEq.respectTransparency false in
/-- A cone on `F` with cone point `X` is the same as an element of `lim Hom(X, F·)`. -/
@[simps]
/-
**CategoryTheory.Limits.limitCompCoyonedaIsoCone** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：limitCompCoyonedaIsoCone (F : J ⥤ C) (X : C) : limit (F ⋙ coyoneda.obj (op
 X)) ≅ ((const J).obj X ⟶ F) where hom
参数：F : J ⥤ C；X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cone on `F` with cone point `X` is the same as an element of `lim Hom(X, F·)`.
-/
noncomputable def limitCompCoyonedaIsoCone (F : J ⥤ C) (X : C) :
    limit (F ⋙ coyoneda.obj (op X)) ≅ ((const J).obj X ⟶ F) where
  hom := ↾fun a ↦ {
    app j := limit.π (F ⋙ coyoneda.obj (op X)) j a
    naturality _ _ _ := by simpa using! (limit.w_apply _ _ _).symm }
  inv := ↾fun t ↦ limit.lift _ (Types.coneOfSection (s := t.app) <| by
    simp [Functor.sections, ← t.naturality]) ⟨⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local simp←] comp_apply in
variable (J) (C) in
/-- A cone on `F` with cone point `X` is the same as an element of `lim Hom(X, F·)`,
    naturally in `F` and `X`. -/
@[simps!]
/-
**CategoryTheory.Limits.whiskeringLimYonedaIsoCones** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：whiskeringLimYonedaIsoCones : whiskeringLeft _ _ _ ⋙ (whiskeringRight _ _ 
_).obj lim ⋙ (whiskeringLeft _ _ _).obj coyoneda ≅ cones J C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cone on `F` with cone point `X` is the same as an element of `lim Hom(X, F·)`,
    naturally in `F` and `X`.
-/
noncomputable def whiskeringLimYonedaIsoCones : whiskeringLeft _ _ _ ⋙
    (whiskeringRight _ _ _).obj lim ⋙ (whiskeringLeft _ _ _).obj coyoneda ≅ cones J C :=
  NatIso.ofComponents fun F ↦ NatIso.ofComponents
    (fun X => limitCompCoyonedaIsoCone F X.unop)

set_option backward.defeqAttrib.useBackward true in
attribute [local simp←] comp_apply in
set_option backward.isDefEq.respectTransparency false in
/-- A cocone on `F` with cocone point `X` is the same as an element of `lim Hom(F·, X)`. -/
@[simps]
/-
**CategoryTheory.Limits.limitCompYonedaIsoCocone** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：limitCompYonedaIsoCocone (F : J ⥤ C) (X : C) : limit (F.op ⋙ yoneda.obj X)
 ≅ (F ⟶ (const J).obj X) where hom
参数：F : J ⥤ C；X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cocone on `F` with cocone point `X` is the same as an element of `lim Hom(F·, 
X)`.
-/
noncomputable def limitCompYonedaIsoCocone (F : J ⥤ C) (X : C) :
    limit (F.op ⋙ yoneda.obj X) ≅ (F ⟶ (const J).obj X) where
  hom := ↾fun a ↦ {
    app j := limit.π (F.op ⋙ yoneda.obj X) ⟨j⟩ a
    naturality _ _ f := by simpa using (limit.w_apply (F.op ⋙ yoneda.obj X) f.op a) }
  inv := ↾fun t ↦ limit.lift _ (Types.coneOfSection (s := fun j ↦ t.app j.unop) <| by
    simp [Functor.sections]) ⟨⟩

set_option backward.defeqAttrib.useBackward true in
attribute [local simp←] comp_apply in
set_option backward.isDefEq.respectTransparency false in
variable (J) (C) in
/-- A cocone on `F` with cocone point `X` is the same as an element of `lim Hom(F·, X)`,
    naturally in `F` and `X`. -/
@[simps!]
/-
**CategoryTheory.Limits.opHomCompWhiskeringLimYonedaIsoCocones** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：opHomCompWhiskeringLimYonedaIsoCocones : opHom _ _ ⋙ whiskeringLeft _ _ _ 
⋙ (whiskeringRight _ _ _).obj lim ⋙ (whiskeringLeft _ _ _).obj yoneda ≅ cocones 
J C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cocone on `F` with cocone point `X` is the same as an element of `lim Hom(F·, 
X)`,
    naturally in `F` and `X`.
-/
noncomputable def opHomCompWhiskeringLimYonedaIsoCocones : opHom _ _ ⋙ whiskeringLeft _ _ _ ⋙
      (whiskeringRight _ _ _).obj lim ⋙ (whiskeringLeft _ _ _).obj yoneda ≅ cocones J C :=
  NatIso.ofComponents fun F => NatIso.ofComponents (limitCompYonedaIsoCocone F.unop)

/-- A cocone on `F` with cocone point `X` is the same as an element of `lim Hom(F·, X)`,
naturally in `X`. -/
@[deprecated "Use `(opHomCompWhiskeringLimYonedaIsoCocones _ _).app _` instead"
  (since := "2026-04-08")]
/-
**CategoryTheory.Limits.yonedaCompLimIsoCocones** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：yonedaCompLimIsoCocones (F : J ⥤ C) : yoneda ⋙ (whiskeringLeft _ _ _).obj 
F.op ⋙ lim ≅ F.cocones
参数：F : J ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def yonedaCompLimIsoCocones (F : J ⥤ C) :
    yoneda ⋙ (whiskeringLeft _ _ _).obj F.op ⋙ lim ≅ F.cocones :=
  (opHomCompWhiskeringLimYonedaIsoCocones _ _).app (op F)

end CategoryTheory.Limits

