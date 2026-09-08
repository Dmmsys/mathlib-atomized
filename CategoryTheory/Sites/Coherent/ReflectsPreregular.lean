/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.EffectiveEpi.Enough
public import Mathlib.CategoryTheory.EffectiveEpi.Preserves
public import Mathlib.CategoryTheory.Sites.Coherent.RegularTopology
/-!

# Reflecting the property of being preregular

We prove that given a fully faithful functor `F : C ⥤ D`, with `Preregular D`, such that for every
object `X` of `D` there exists an object `W` of `C` with an effective epi `π : F.obj W ⟶ X`, the
category `C` is `Preregular`.
-/

public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
  [F.PreservesEffectiveEpis] [F.ReflectsEffectiveEpis]
  [F.EffectivelyEnough]
  [Preregular D] [F.Full] [F.Faithful]

set_option backward.isDefEq.respectTransparency false in
include F in
/-
**CategoryTheory.Functor.reflects_preregular** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Functor`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (F : CategoryTheory.Functo
r C D) [F.PreservesEffectiveEpis]   [F.ReflectsEffectiveEpis] [F.EffectivelyEnou
gh] [CategoryTheory.Preregular D] [F.Full] [F.Faithful],   CategoryTheory.Prereg
ular C
参数：F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Preregular.exists_fac`：∀ {C : Type u_1} {inst : CategoryT
heory.Category.{v_1, u_1} C} [self : CategoryTheory.Preregular C] {X Y Z : C}   
(f : X ⟶ Y) (g : Z ⟶ Y) [C…
· 使用定理 `CategoryTheory.Functor.EffectivelyEnough.presentation`：∀ {C : Type u_1} 
{D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : Categor
yTheory.Category.{v_2, u_2} D} {F : Categor…
· 使用引理 `CategoryTheory.Functor.effectiveEpi_of_map`：effectiveEpi_of_map (F : C ⥤
 D) [F.ReflectsEffectiveEpis] {X Y : C} (f : X ⟶ Y) (h : EffectiveEpi (F.map f))
 : EffectiveEpi f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `CategoryTheory.regularTopology.instEffectiveEpiComp`：∀ {C : Type u_1} [i
nst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Preregular C] {X Y Y
' : C} (π : Y ⟶ X)   [CategoryTheory.Effe…
· 使用定理 `CategoryTheory.Functor.instEffectiveEpiEffectiveEpiOver`：∀ {C : Type u_1
} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Functor.reflects_preregular : Preregular C where
  exists_fac f g _ := by
    obtain ⟨W, f', _, i, w⟩ := Preregular.exists_fac (F.map f) (F.map g)
    refine ⟨_, F.preimage (F.effectiveEpiOver W ≫ f'),
      ⟨F.effectiveEpi_of_map _ ?_, F.preimage (F.effectiveEpiOver W ≫ i), ?_⟩⟩
    · simp only [Functor.map_preimage]
      infer_instance
    · apply F.map_injective
      simp [w]

end CategoryTheory

