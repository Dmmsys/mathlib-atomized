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
/-
**CategoryTheory.effectiveEpiStructIsColimitDescOfEffectiveEpiFamily** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：effectiveEpiStructIsColimitDescOfEffectiveEpiFamily {B : C} {α : Type*} (X
 : α -> C) (c : Cofan X) (hc : IsColimit c) (π : (a : α) -> (X a ⟶ B)) [Effectiv
eEpiFamily X π] : EffectiveEpiStruct (hc.desc (Cofan.mk B π)) where desc e h
参数：X : α -> C；c : Cofan X；hc : IsColimit c；π : (a : α) -> (X a ⟶ B)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def effectiveEpiStructIsColimitDescOfEffectiveEpiFamily {B : C} {α : Type*} (X : α → C)
    (c : Cofan X) (hc : IsColimit c) (π : (a : α) → (X a ⟶ B)) [EffectiveEpiFamily X π] :
    EffectiveEpiStruct (hc.desc (Cofan.mk B π)) where
  desc e h := EffectiveEpiFamily.desc X π (fun a ↦ c.ι.app ⟨a⟩ ≫ e) (fun a₁ a₂ g₁ g₂ hg ↦ by
    simp only [← Category.assoc]
    exact h (g₁ ≫ c.ι.app ⟨a₁⟩) (g₂ ≫ c.ι.app ⟨a₂⟩) (by simpa))
  fac e h := hc.hom_ext (fun ⟨j⟩ ↦ (by simp))
  uniq e _ m hm := EffectiveEpiFamily.uniq X π (fun a ↦ c.ι.app ⟨a⟩ ≫ e)
      (fun _ _ _ _ hg ↦ (by simp [← hm, reassoc_of% hg])) m (fun _ ↦ (by simp [← hm]))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {B : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B)) [HasCoproduct X]
    [EffectiveEpiFamily X π] : EffectiveEpi (Sigma.desc π) := by
  let e := effectiveEpiStructIsColimitDescOfEffectiveEpiFamily X _ (coproductIsCoproduct _) π
  simp only [Cofan.mk_pt, coproductIsCoproduct, colimit.cocone_x, IsColimit.ofIsoColimit_desc,
    Cocone.ext_inv_hom, Iso.refl_inv, colimit.isColimit_desc, Category.id_comp] at e
  exact ⟨⟨e⟩⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {B : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B)) [EffectiveEpiFamily X π]
    [HasCoproduct X] : Epi (Sigma.desc π) := inferInstance

set_option backward.isDefEq.respectTransparency false in
/--
This is an auxiliary lemma used twice in the definition of  `EffectiveEpiFamilyOfEffectiveEpiDesc`.
It is the `h` hypothesis of `EffectiveEpi.desc` and `EffectiveEpi.fac`.
-/
/-
**CategoryTheory.effectiveEpiFamilyStructOfEffectiveEpiDesc_aux** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory`。
形式化陈述：effectiveEpiFamilyStructOfEffectiveEpiDesc_aux {B : C} {α : Type*} {X : α 
-> C} {π : (a : α) -> X a ⟶ B} [HasCoproduct X] [forall {Z : C} (g : Z ⟶ ∐ X) (a
 : α), HasPullback g (Sigma.ι X a)] [forall {Z : C} (g : Z ⟶ ∐ X), HasCoproduct 
fun a => pullback g (Sigma.ι X a)] [forall {Z : C} (g : Z ⟶ ∐ X), Epi (Sigma.des
c fun a => pullback.fst g (Sigma.ι X a))] {W : C} {e : (a : α) -> X a ⟶ W} (h : 
forall {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂), g₁ ≫ π a₁ = g₂ ≫ π a
₂ -> g₁ ≫ e a₁ = g₂ ≫ e a₂
参数：a : α；g : Z ⟶ ∐ X；a : α；Sigma.ι X a；g : Z ⟶ ∐ X；Sigma.ι X a；g : Z ⟶ ∐ X；Sigma
.desc fun a => pullback.fst g (Sigma.ι X a)；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
This is an auxiliary lemma used twice in the definition of  `EffectiveEpiFamilyO
fEffectiveEpiDesc`.
It is the `h` hypothesis of `EffectiveEpi.desc` and `EffectiveEpi.fac`.
-/
theorem effectiveEpiFamilyStructOfEffectiveEpiDesc_aux {B : C} {α : Type*} {X : α → C}
    {π : (a : α) → X a ⟶ B} [HasCoproduct X]
    [∀ {Z : C} (g : Z ⟶ ∐ X) (a : α), HasPullback g (Sigma.ι X a)]
    [∀ {Z : C} (g : Z ⟶ ∐ X), HasCoproduct fun a ↦ pullback g (Sigma.ι X a)]
    [∀ {Z : C} (g : Z ⟶ ∐ X), Epi (Sigma.desc fun a ↦ pullback.fst g (Sigma.ι X a))]
    {W : C} {e : (a : α) → X a ⟶ W} (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π a₁ = g₂ ≫ π a₂ → g₁ ≫ e a₁ = g₂ ≫ e a₂) {Z : C}
    {g₁ g₂ : Z ⟶ ∐ fun b ↦ X b} (hg : g₁ ≫ Sigma.desc π = g₂ ≫ Sigma.desc π) :
    g₁ ≫ Sigma.desc e = g₂ ≫ Sigma.desc e := by
  apply_fun ((Sigma.desc fun a ↦ pullback.fst g₁ (Sigma.ι X a)) ≫ ·) using
    (fun a b ↦ (cancel_epi _).mp)
  ext a
  simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_ι_app]
  rw [← Category.assoc, pullback.condition]
  simp only [Category.assoc, colimit.ι_desc, Cofan.mk_ι_app]
  apply_fun ((Sigma.desc fun a ↦ pullback.fst (pullback.fst _ _ ≫ g₂) (Sigma.ι X a)) ≫ ·)
    using (fun a b ↦ (cancel_epi _).mp)
  ext b
  simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_ι_app]
  simp only [← Category.assoc]
  rw [(Category.assoc _ _ g₂), pullback.condition]
  simp only [Category.assoc, colimit.ι_desc, Cofan.mk_ι_app]
  rw [← Category.assoc]
  apply h
  apply_fun (pullback.fst g₁ (Sigma.ι X a) ≫ ·) at hg
  rw [← Category.assoc, pullback.condition] at hg
  simp only [Category.assoc, colimit.ι_desc, Cofan.mk_ι_app] at hg
  apply_fun ((Sigma.ι (fun a ↦ pullback _ _) b) ≫ (Sigma.desc fun a ↦
    pullback.fst (pullback.fst _ _ ≫ g₂) (Sigma.ι X a)) ≫ ·) at hg
  simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_ι_app] at hg
  simp only [← Category.assoc] at hg
  rw [(Category.assoc _ _ g₂), pullback.condition] at hg
  simpa using hg

set_option backward.isDefEq.respectTransparency false in
/--
If a coproduct interacts well enough with pullbacks, then a family whose domains are the terms of
the coproduct is effective epimorphic whenever `Sigma.desc` induces an effective epimorphism from
the coproduct itself.
-/
noncomputable
/-
**CategoryTheory.effectiveEpiFamilyStructOfEffectiveEpiDesc** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory`。
形式化陈述：effectiveEpiFamilyStructOfEffectiveEpiDesc {B : C} {α : Type*} (X : α -> C
) (π : (a : α) -> (X a ⟶ B)) [HasCoproduct X] [EffectiveEpi (Sigma.desc π)] [for
all {Z : C} (g : Z ⟶ ∐ X) (a : α), HasPullback g (Sigma.ι X a)] [forall {Z : C} 
(g : Z ⟶ ∐ X), HasCoproduct (fun a => pullback g (Sigma.ι X a))] [forall {Z : C}
 (g : Z ⟶ ∐ X), Epi (Sigma.desc (fun a => pullback.fst g (Sigma.ι X a)))] : Effe
ctiveEpiFamilyStruct X π where desc e h
参数：X : α -> C；π : (a : α) -> (X a ⟶ B)；Sigma.desc π；g : Z ⟶ ∐ X；a : α；Sigma.ι X 
a；g : Z ⟶ ∐ X；fun a => pullback g (Sigma.ι X a)；g : Z ⟶ ∐ X；Sigma.desc (fun a =>
 pullback.fst g (Sigma.ι X a))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def effectiveEpiFamilyStructOfEffectiveEpiDesc {B : C} {α : Type*} (X : α → C)
    (π : (a : α) → (X a ⟶ B)) [HasCoproduct X] [EffectiveEpi (Sigma.desc π)]
    [∀ {Z : C} (g : Z ⟶ ∐ X) (a : α), HasPullback g (Sigma.ι X a)]
    [∀ {Z : C} (g : Z ⟶ ∐ X), HasCoproduct (fun a ↦ pullback g (Sigma.ι X a))]
    [∀ {Z : C} (g : Z ⟶ ∐ X),
      Epi (Sigma.desc (fun a ↦ pullback.fst g (Sigma.ι X a)))] :
    EffectiveEpiFamilyStruct X π where
  desc e h := EffectiveEpi.desc (Sigma.desc π) (Sigma.desc e) fun _ _ hg ↦
    effectiveEpiFamilyStructOfEffectiveEpiDesc_aux h hg
  fac e h a := by
    rw [(by simp : π a = Sigma.ι X a ≫ Sigma.desc π), (by simp : e a = Sigma.ι X a ≫ Sigma.desc e),
      Category.assoc, EffectiveEpi.fac (Sigma.desc π) (Sigma.desc e) (fun g₁ g₂ hg ↦
      effectiveEpiFamilyStructOfEffectiveEpiDesc_aux h hg)]
  uniq _ _ _ hm := by
    apply EffectiveEpi.uniq (Sigma.desc π)
    ext
    simpa using hm _

end CategoryTheory

