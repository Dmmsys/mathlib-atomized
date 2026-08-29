/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.EffectiveEpi.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Tactic.ApplyFun
/-!

# Effective epimorphic families and coproducts

This file proves that an effective epimorphic family induces an effective epi from the coproduct if
the coproduct exists, and the converse under some more conditions on the coproduct (that it
interacts well with pullbacks).
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]

set_option backward.isDefEq.respectTransparency false in
/--
Given an `EffectiveEpiFamily X π` and a corresponding coproduct cocone, the family descends to an
`EffectiveEpi` from the coproduct.
-/
noncomputable
/--
Definition of `effectiveEpiStructIsColimitDescOfEffectiveEpiFamily` / `effectiveEpiStructIsColimitDescOfEffectiveEpiFamily` 的定义

English:
definition effectiveEpiStructIsColimitDescOfEffectiveEpiFamily
  signature: {B : C} {α : Type*} (X : α -> C)
  body: EffectiveEpiFamily.desc X π (fun a => c.ι.app ⟨a⟩ ≫ e) (fun a₁ a₂ g₁ g₂ hg => by
    simp only [← Category.assoc]
    exact h (g₁ ≫ c.ι.app ⟨a₁⟩) (g₂ ≫ c.ι.app ⟨a₂⟩) (by simpa))
  fac e h := hc.hom_ext (fun ⟨j⟩ => (by simp))
  uniq e _ m hm := EffectiveEpiFamily.uniq X π (fun a => c.ι.app ⟨a⟩ ≫ e)
      (fun _ _ _ _ hg => (by simp [← hm, reassoc_of% hg])) m (fun _ => (by simp [← hm]))

中文:
定义 effectiveEpiStructIsColimitDescOfEffectiveEpiFamily
  签名: {B : C} {α : 类型} (X : α -> C)
  定义体: EffectiveEpiFamily.desc X π (fun a => c.ι.app ⟨a⟩ ≫ e) (fun a₁ a₂ g₁ g₂ hg => by
    simp only [← Category.assoc]
    exact h (g₁ ≫ c.ι.app ⟨a₁⟩) (g₂ ≫ c.ι.app ⟨a₂⟩) (by simpa))
  fac e h := hc.hom_ext (fun ⟨j⟩ => (by simp))
  uniq e _ m hm := EffectiveEpiFamily.uniq X π (fun a => c.ι.app ⟨a⟩ ≫ e)
      (fun _ _ _ _ hg => (by simp [← hm, reassoc_of% hg])) m (fun _ => (by simp [← hm]))

Depends on / 依赖: Category, Category.assoc, EffectiveEpiFamily, EffectiveEpiFamily.desc, EffectiveEpiFamily.uniq, hc.hom_ext, hom_ext, reassoc_of
-/
def effectiveEpiStructIsColimitDescOfEffectiveEpiFamily {B : C} {α : Type*} (X : α -> C)
    (c : Cofan X) (hc : IsColimit c) (π : (a : α) -> (X a ⟶ B)) [EffectiveEpiFamily X π] :
    EffectiveEpiStruct (hc.desc (Cofan.mk B π)) where
  desc e h := EffectiveEpiFamily.desc X π (fun a => c.ι.app ⟨a⟩ ≫ e) (fun a₁ a₂ g₁ g₂ hg => by
    simp only [← Category.assoc]
    exact h (g₁ ≫ c.ι.app ⟨a₁⟩) (g₂ ≫ c.ι.app ⟨a₂⟩) (by simpa))
  fac e h := hc.hom_ext (fun ⟨j⟩ => (by simp))
  uniq e _ m hm := EffectiveEpiFamily.uniq X π (fun a => c.ι.app ⟨a⟩ ≫ e)
      (fun _ _ _ _ hg => (by simp [← hm, reassoc_of% hg])) m (fun _ => (by simp [← hm]))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
instance {B : C} {α : Type*} (X : α -> C) (π : (a : α) -> (X a ⟶ B)) [HasCoproduct X]
    [EffectiveEpiFamily X π] : EffectiveEpi (Sigma.desc π) := by
  let e := effectiveEpiStructIsColimitDescOfEffectiveEpiFamily X _ (coproductIsCoproduct _) π
  simp only [Cofan.mk_pt, coproductIsCoproduct, colimit.cocone_x, IsColimit.ofIsoColimit_desc,
    Cocone.ext_inv_hom, Iso.refl_inv, colimit.isColimit_desc, Category.id_comp] at e
  exact ⟨⟨e⟩⟩

example {B : C} {α : Type*} (X : α -> C) (π : (a : α) -> (X a ⟶ B)) [EffectiveEpiFamily X π]
    [HasCoproduct X] : Epi (Sigma.desc π) := inferInstance

set_option backward.isDefEq.respectTransparency false in
/--
theorem `effectiveEpiFamilyStructOfEffectiveEpiDesc_aux` / 定理 `effectiveEpiFamilyStructOfEffectiveEpiDesc_aux`

English:
theorem effectiveEpiFamilyStructOfEffectiveEpiDesc_aux
  statement: {B : C} {α : Type*} {X : α -> C}
  proof: by
  apply_fun ((Sigma.desc fun a => pullback.fst g₁ (Sigma.ι X a)) ≫ ·) using
    (fun a b => (cancel_epi _).mp)
  ext a
  simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_ι_app]
  rw [← Category.assoc]; rw [pullback.condition]
  simp only [Category.assoc, colimit.ι_desc, Cofan.mk_ι_app]
  apply_fun ((Sigma.desc fun a => pullback.fst (pullback.fst _ _ ≫ g₂) (Sigma.ι X a)) ≫ ·)
    using (fun a b => (cancel_epi _).mp)
  ext b
  simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_ι_app]
  simp only [← Category.assoc]
  rw [(Category.assoc _ _ g₂)]; rw [pullback.condition]
  simp only [Category.assoc, colimit.ι_desc, Cofan.mk_ι_app]
  rw [← Category.assoc]
  apply h
  apply_fun (pullback.fst g₁ (Sigma.ι X a) ≫ ·) at hg
  rw [← Category.assoc]; rw [pullback.condition] at hg
  simp only [Category.assoc, colimit.ι_desc, Cofan.mk_ι_app] at hg
  apply_fun ((Sigma.ι (fun a => pullback _ _) b) ≫ (Sigma.desc fun a =>
    pullback.fst (pullback.fst _ _ ≫ g₂) (Sigma.ι X a)) ≫ ·) at hg
  simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_ι_app] at hg
  simp only [← Category.assoc] at hg
  rw [(Category.assoc _ _ g₂)]; rw [pullback.condition] at hg
  simpa using hg

中文:
定理 effectiveEpiFamilyStructOfEffectiveEpiDesc_aux
  结论: {B : C} {α : 类型} {X : α -> C}
  证明: by
  apply_fun ((Sigma.desc fun a => pullback.fst g₁ (Sigma.ι X a)) ≫ ·) using
    (fun a b => (cancel_epi _).mp)
  ext a
  simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_ι_app]
  rw [← Category.assoc]; rw [pullback.condition]
  simp only [Category.assoc, colimit.ι_desc, Cofan.mk_ι_app]
  apply_fun ((Sigma.desc fun a => pullback.fst (pullback.fst _ _ ≫ g₂) (Sigma.ι X a)) ≫ ·)
    using (fun a b => (cancel_epi _).mp)
  ext b
  simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_ι_app]
  simp only [← Category.assoc]
  rw [(Category.assoc _ _ g₂)]; rw [pullback.condition]
  simp only [Category.assoc, colimit.ι_desc, Cofan.mk_ι_app]
  rw [← Category.assoc]
  apply h
  apply_fun (pullback.fst g₁ (Sigma.ι X a) ≫ ·) at hg
  rw [← Category.assoc]; rw [pullback.condition] at hg
  simp only [Category.assoc, colimit.ι_desc, Cofan.mk_ι_app] at hg
  apply_fun ((Sigma.ι (fun a => pullback _ _) b) ≫ (Sigma.desc fun a =>
    pullback.fst (pullback.fst _ _ ≫ g₂) (Sigma.ι X a)) ≫ ·) at hg
  simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_ι_app] at hg
  simp only [← Category.assoc] at hg
  rw [(Category.assoc _ _ g₂)]; rw [pullback.condition] at hg
  simpa using hg

Depends on / 依赖: Category, Category.assoc, Cofan.mk_, Discrete, Discrete.functor_obj, Sigma.desc, apply_fun, cancel_epi, colimit, condition, functor_obj, pullback, pullback.condition, pullback.fst
-/
theorem effectiveEpiFamilyStructOfEffectiveEpiDesc_aux {B : C} {α : Type*} {X : α -> C}
    {π : (a : α) -> X a ⟶ B} [HasCoproduct X]
    [forall {Z : C} (g : Z ⟶ ∐ X) (a : α), HasPullback g (Sigma.ι X a)]
    [forall {Z : C} (g : Z ⟶ ∐ X), HasCoproduct fun a => pullback g (Sigma.ι X a)]
    [forall {Z : C} (g : Z ⟶ ∐ X), Epi (Sigma.desc fun a => pullback.fst g (Sigma.ι X a))]
    {W : C} {e : (a : α) -> X a ⟶ W} (h : forall {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π a₁ = g₂ ≫ π a₂ -> g₁ ≫ e a₁ = g₂ ≫ e a₂) {Z : C}
    {g₁ g₂ : Z ⟶ ∐ fun b => X b} (hg : g₁ ≫ Sigma.desc π = g₂ ≫ Sigma.desc π) :
    g₁ ≫ Sigma.desc e = g₂ ≫ Sigma.desc e := by
  apply_fun ((Sigma.desc fun a => pullback.fst g₁ (Sigma.ι X a)) ≫ ·) using
    (fun a b => (cancel_epi _).mp)
  ext a
  simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_ι_app]
  rw [← Category.assoc]; rw [pullback.condition]
  simp only [Category.assoc, colimit.ι_desc, Cofan.mk_ι_app]
  apply_fun ((Sigma.desc fun a => pullback.fst (pullback.fst _ _ ≫ g₂) (Sigma.ι X a)) ≫ ·)
    using (fun a b => (cancel_epi _).mp)
  ext b
  simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_ι_app]
  simp only [← Category.assoc]
  rw [(Category.assoc _ _ g₂)]; rw [pullback.condition]
  simp only [Category.assoc, colimit.ι_desc, Cofan.mk_ι_app]
  rw [← Category.assoc]
  apply h
  apply_fun (pullback.fst g₁ (Sigma.ι X a) ≫ ·) at hg
  rw [← Category.assoc]; rw [pullback.condition] at hg
  simp only [Category.assoc, colimit.ι_desc, Cofan.mk_ι_app] at hg
  apply_fun ((Sigma.ι (fun a => pullback _ _) b) ≫ (Sigma.desc fun a =>
    pullback.fst (pullback.fst _ _ ≫ g₂) (Sigma.ι X a)) ≫ ·) at hg
  simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_ι_app] at hg
  simp only [← Category.assoc] at hg
  rw [(Category.assoc _ _ g₂)]; rw [pullback.condition] at hg
  simpa using hg

set_option backward.isDefEq.respectTransparency false in
/--
If a coproduct interacts well enough with pullbacks, then a family whose domains are the terms of
the coproduct is effective epimorphic whenever `Sigma.desc` induces an effective epimorphism from
the coproduct itself.
-/
noncomputable
/--
Definition of `effectiveEpiFamilyStructOfEffectiveEpiDesc` / `effectiveEpiFamilyStructOfEffectiveEpiDesc` 的定义

English:
definition effectiveEpiFamilyStructOfEffectiveEpiDesc
  signature: {B : C} {α : Type*} (X : α -> C)
  body: EffectiveEpi.desc (Sigma.desc π) (Sigma.desc e) fun _ _ hg =>
    effectiveEpiFamilyStructOfEffectiveEpiDesc_aux h hg
  fac e h a := by
    rw [(by simp : π a = Sigma.ι X a ≫ Sigma.desc π)]; rw [(by simp : e a = Sigma.ι X a ≫ Sigma.desc e)]; rw [Category.assoc]; rw [EffectiveEpi.fac (Sigma.desc π) (Sigma.desc e) (fun g₁ g₂ hg =>
      effectiveEpiFamilyStructOfEffectiveEpiDesc_aux h hg)]
  uniq _ _ _ hm := by
    apply EffectiveEpi.uniq (Sigma.desc π)
    ext
    simpa using hm _

中文:
定义 effectiveEpiFamilyStructOfEffectiveEpiDesc
  签名: {B : C} {α : 类型} (X : α -> C)
  定义体: EffectiveEpi.desc (Sigma.desc π) (Sigma.desc e) fun _ _ hg =>
    effectiveEpiFamilyStructOfEffectiveEpiDesc_aux h hg
  fac e h a := by
    rw [(by simp : π a = Sigma.ι X a ≫ Sigma.desc π)]; rw [(by simp : e a = Sigma.ι X a ≫ Sigma.desc e)]; rw [Category.assoc]; rw [EffectiveEpi.fac (Sigma.desc π) (Sigma.desc e) (fun g₁ g₂ hg =>
      effectiveEpiFamilyStructOfEffectiveEpiDesc_aux h hg)]
  uniq _ _ _ hm := by
    apply EffectiveEpi.uniq (Sigma.desc π)
    ext
    simpa using hm _

Depends on / 依赖: EffectiveEpi, EffectiveEpi.desc, Sigma.desc
-/
def effectiveEpiFamilyStructOfEffectiveEpiDesc {B : C} {α : Type*} (X : α -> C)
    (π : (a : α) -> (X a ⟶ B)) [HasCoproduct X] [EffectiveEpi (Sigma.desc π)]
    [forall {Z : C} (g : Z ⟶ ∐ X) (a : α), HasPullback g (Sigma.ι X a)]
    [forall {Z : C} (g : Z ⟶ ∐ X), HasCoproduct (fun a => pullback g (Sigma.ι X a))]
    [forall {Z : C} (g : Z ⟶ ∐ X),
      Epi (Sigma.desc (fun a => pullback.fst g (Sigma.ι X a)))] :
    EffectiveEpiFamilyStruct X π where
  desc e h := EffectiveEpi.desc (Sigma.desc π) (Sigma.desc e) fun _ _ hg =>
    effectiveEpiFamilyStructOfEffectiveEpiDesc_aux h hg
  fac e h a := by
    rw [(by simp : π a = Sigma.ι X a ≫ Sigma.desc π)]; rw [(by simp : e a = Sigma.ι X a ≫ Sigma.desc e)]; rw [Category.assoc]; rw [EffectiveEpi.fac (Sigma.desc π) (Sigma.desc e) (fun g₁ g₂ hg =>
      effectiveEpiFamilyStructOfEffectiveEpiDesc_aux h hg)]
  uniq _ _ _ hm := by
    apply EffectiveEpi.uniq (Sigma.desc π)
    ext
    simpa using hm _

end CategoryTheory
