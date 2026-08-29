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
/--
Definition of `compCoyonedaSectionsEquiv` / `compCoyonedaSectionsEquiv` 的定义

English:
definition compCoyonedaSectionsEquiv
  signature: (F : J ⥤ C) (X : C)
  body: { app := fun j => s.val j
      naturality := fun j j' f => by
        dsimp
        rw [Category.id_comp]
        exact (s.property f).symm }
  invFun τ := ⟨τ.app, fun {j j'} f => by simpa using! (τ.naturality f).symm⟩

中文:
定义 compCoyonedaSectionsEquiv
  签名: (F : J ⥤ C) (X : C)
  定义体: { app := fun j => s.val j
      naturality := fun j j' f => by
        dsimp
        rw [Category.id_comp]
        exact (s.property f).symm }
  invFun τ := ⟨τ.app, fun {j j'} f => by simpa using! (τ.naturality f).symm⟩

Depends on / 依赖: Category, Category.id_comp, id_comp, invFun, naturality, property, s.property, s.val
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
/--
Definition of `opCompYonedaSectionsEquiv` / `opCompYonedaSectionsEquiv` 的定义

English:
definition opCompYonedaSectionsEquiv
  signature: (F : J ⥤ C) (X : C)
  body: { app := fun j => s.val (op j)
      naturality := fun j j' f => by
        dsimp
        rw [Category.comp_id]
        exact (s.property f.op) }
  invFun τ := ⟨fun j => τ.app j.unop, fun {j j'} f => by simp [τ.naturality f.unop]⟩

中文:
定义 opCompYonedaSectionsEquiv
  签名: (F : J ⥤ C) (X : C)
  定义体: { app := fun j => s.val (op j)
      naturality := fun j j' f => by
        dsimp
        rw [Category.comp_id]
        exact (s.property f.op) }
  invFun τ := ⟨fun j => τ.app j.unop, fun {j j'} f => by simp [τ.naturality f.unop]⟩

Depends on / 依赖: Category, Category.comp_id, comp_id, f.op, f.unop, invFun, j.unop, naturality, property, s.property, s.val
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
/--
Definition of `compYonedaSectionsEquiv` / `compYonedaSectionsEquiv` 的定义

English:
definition compYonedaSectionsEquiv
  signature: (F : J ⥤ Cᵒᵖ) (X : C)
  body: { app := fun j => (s.val j).op
      naturality := fun j j' f => by
        dsimp
        rw [Category.id_comp]
        exact Quiver.Hom.unop_inj (s.property f).symm }
  invFun τ := ⟨fun j => (τ.app j).unop,
    fun {j j'} f => Quiver.Hom.op_inj (by simpa using! (τ.naturality f).symm)⟩

中文:
定义 compYonedaSectionsEquiv
  签名: (F : J ⥤ Cᵒᵖ) (X : C)
  定义体: { app := fun j => (s.val j).op
      naturality := fun j j' f => by
        dsimp
        rw [Category.id_comp]
        exact Quiver.Hom.unop_inj (s.property f).symm }
  invFun τ := ⟨fun j => (τ.app j).unop,
    fun {j j'} f => Quiver.Hom.op_inj (by simpa using! (τ.naturality f).symm)⟩

Depends on / 依赖: Category, Category.id_comp, Quiver, Quiver.Hom.op_inj, Quiver.Hom.unop_inj, id_comp, invFun, naturality, op_inj, property, s.property, s.val, unop_inj
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
/--
Definition of `limitCompCoyonedaIsoCone` / `limitCompCoyonedaIsoCone` 的定义

English:
definition limitCompCoyonedaIsoCone
  signature: (F : J ⥤ C) (X : C)
  body: ↾fun a => {
    app j := limit.π (F ⋙ coyoneda.obj (op X)) j a
    naturality _ _ _ := by simpa using! (limit.w_apply _ _ _).symm }
  inv := ↾fun t => limit.lift _ (Types.coneOfSection (s := t.app) <| by
    simp [Functor.sections, ← t.naturality]) ⟨⟩

中文:
定义 limitCompCoyonedaIsoCone
  签名: (F : J ⥤ C) (X : C)
  定义体: ↾fun a => {
    app j := limit.π (F ⋙ coyoneda.obj (op X)) j a
    naturality _ _ _ := by simpa using! (limit.w_apply _ _ _).symm }
  inv := ↾fun t => limit.lift _ (Types.coneOfSection (s := t.app) <| by
    simp [Functor.sections, ← t.naturality]) ⟨⟩
-/
noncomputable def limitCompCoyonedaIsoCone (F : J ⥤ C) (X : C) :
    limit (F ⋙ coyoneda.obj (op X)) ≅ ((const J).obj X ⟶ F) where
  hom := ↾fun a => {
    app j := limit.π (F ⋙ coyoneda.obj (op X)) j a
    naturality _ _ _ := by simpa using! (limit.w_apply _ _ _).symm }
  inv := ↾fun t => limit.lift _ (Types.coneOfSection (s := t.app) <| by
    simp [Functor.sections, ← t.naturality]) ⟨⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local simp←] comp_apply in
variable (J) (C) in
/-- A cone on `F` with cone point `X` is the same as an element of `lim Hom(X, F·)`,
    naturally in `F` and `X`. -/
@[simps!]
/--
Definition of `whiskeringLimYonedaIsoCones` / `whiskeringLimYonedaIsoCones` 的定义

English:
definition whiskeringLimYonedaIsoCones
  signature: : whiskeringLeft _ _ _ ⋙
  body: NatIso.ofComponents fun F => NatIso.ofComponents
    (fun X => limitCompCoyonedaIsoCone F X.unop)

中文:
定义 whiskeringLimYonedaIsoCones
  签名: : whiskeringLeft _ _ _ ⋙
  定义体: NatIso.ofComponents fun F => NatIso.ofComponents
    (fun X => limitCompCoyonedaIsoCone F X.unop)

Depends on / 依赖: NatIso, NatIso.ofComponents, X.unop, limitCompCoyonedaIsoCone, ofComponents
-/
noncomputable def whiskeringLimYonedaIsoCones : whiskeringLeft _ _ _ ⋙
    (whiskeringRight _ _ _).obj lim ⋙ (whiskeringLeft _ _ _).obj coyoneda ≅ cones J C :=
  NatIso.ofComponents fun F => NatIso.ofComponents
    (fun X => limitCompCoyonedaIsoCone F X.unop)

set_option backward.defeqAttrib.useBackward true in
attribute [local simp←] comp_apply in
set_option backward.isDefEq.respectTransparency false in
/-- A cocone on `F` with cocone point `X` is the same as an element of `lim Hom(F·, X)`. -/
@[simps]
/--
Definition of `limitCompYonedaIsoCocone` / `limitCompYonedaIsoCocone` 的定义

English:
definition limitCompYonedaIsoCocone
  signature: (F : J ⥤ C) (X : C)
  body: ↾fun a => {
    app j := limit.π (F.op ⋙ yoneda.obj X) ⟨j⟩ a
    naturality _ _ f := by simpa using (limit.w_apply (F.op ⋙ yoneda.obj X) f.op a) }
  inv := ↾fun t => limit.lift _ (Types.coneOfSection (s := fun j => t.app j.unop) <| by
    simp [Functor.sections]) ⟨⟩

中文:
定义 limitCompYonedaIsoCocone
  签名: (F : J ⥤ C) (X : C)
  定义体: ↾fun a => {
    app j := limit.π (F.op ⋙ yoneda.obj X) ⟨j⟩ a
    naturality _ _ f := by simpa using (limit.w_apply (F.op ⋙ yoneda.obj X) f.op a) }
  inv := ↾fun t => limit.lift _ (Types.coneOfSection (s := fun j => t.app j.unop) <| by
    simp [Functor.sections]) ⟨⟩

Depends on / 依赖: Functor, Functor.preservesInjectiveObjects_of_isEquivalence, preservesInjectiveObjects_of_isEquivalence
-/
noncomputable def limitCompYonedaIsoCocone (F : J ⥤ C) (X : C) :
    limit (F.op ⋙ yoneda.obj X) ≅ (F ⟶ (const J).obj X) where
  hom := ↾fun a => {
    app j := limit.π (F.op ⋙ yoneda.obj X) ⟨j⟩ a
    naturality _ _ f := by simpa using (limit.w_apply (F.op ⋙ yoneda.obj X) f.op a) }
  inv := ↾fun t => limit.lift _ (Types.coneOfSection (s := fun j => t.app j.unop) <| by
    simp [Functor.sections]) ⟨⟩

set_option backward.defeqAttrib.useBackward true in
attribute [local simp←] comp_apply in
set_option backward.isDefEq.respectTransparency false in
variable (J) (C) in
/-- A cocone on `F` with cocone point `X` is the same as an element of `lim Hom(F·, X)`,
    naturally in `F` and `X`. -/
@[simps!]
/--
Definition of `opHomCompWhiskeringLimYonedaIsoCocones` / `opHomCompWhiskeringLimYonedaIsoCocones` 的定义

English:
definition opHomCompWhiskeringLimYonedaIsoCocones
  signature: : opHom _ _ ⋙ whiskeringLeft _ _ _ ⋙
  body: NatIso.ofComponents fun F => NatIso.ofComponents (limitCompYonedaIsoCocone F.unop)

中文:
定义 opHomCompWhiskeringLimYonedaIsoCocones
  签名: : opHom _ _ ⋙ whiskeringLeft _ _ _ ⋙
  定义体: NatIso.ofComponents fun F => NatIso.ofComponents (limitCompYonedaIsoCocone F.unop)

Depends on / 依赖: F.unop, NatIso, NatIso.ofComponents, limitCompYonedaIsoCocone, ofComponents
-/
noncomputable def opHomCompWhiskeringLimYonedaIsoCocones : opHom _ _ ⋙ whiskeringLeft _ _ _ ⋙
      (whiskeringRight _ _ _).obj lim ⋙ (whiskeringLeft _ _ _).obj yoneda ≅ cocones J C :=
  NatIso.ofComponents fun F => NatIso.ofComponents (limitCompYonedaIsoCocone F.unop)

/-- A cocone on `F` with cocone point `X` is the same as an element of `lim Hom(F·, X)`,
naturally in `X`. -/
@[deprecated "Use `(opHomCompWhiskeringLimYonedaIsoCocones _ _).app _` instead"
  (since := "2026-04-08")]
/--
Definition of `yonedaCompLimIsoCocones` / `yonedaCompLimIsoCocones` 的定义

English:
definition yonedaCompLimIsoCocones
  signature: (F : J ⥤ C)
  body: (opHomCompWhiskeringLimYonedaIsoCocones _ _).app (op F)

中文:
定义 yonedaCompLimIsoCocones
  签名: (F : J ⥤ C)
  定义体: (opHomCompWhiskeringLimYonedaIsoCocones _ _).app (op F)

Depends on / 依赖: opHomCompWhiskeringLimYonedaIsoCocones
-/
noncomputable def yonedaCompLimIsoCocones (F : J ⥤ C) :
    yoneda ⋙ (whiskeringLeft _ _ _).obj F.op ⋙ lim ≅ F.cocones :=
  (opHomCompWhiskeringLimYonedaIsoCocones _ _).app (op F)

end CategoryTheory.Limits
