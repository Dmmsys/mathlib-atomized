/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.QuasiIso
public import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Quasi-isomorphisms of short complexes are stable under retracts

-/

public section

namespace CategoryTheory

open Limits

namespace ShortComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  {S₁ T₁ S₂ T₂ : ShortComplex C}
  [S₁.HasHomology] [T₁.HasHomology] [S₂.HasHomology] [T₂.HasHomology]
  {f₁ : S₁ ⟶ T₁} {f₂ : S₂ ⟶ T₂}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.quasiIso_of_retract** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ShortComplex`。
形式化陈述：quasiIso_of_retract (h : RetractArrow f₁ f₂) [hf₂ : QuasiIso f₂] : QuasiIs
o f₁
参数：h : RetractArrow f₁ f₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_iff`：quasiIso_iff (φ : S₁ ⟶ S₂) : Q
uasiIso φ ↔ IsIso (homologyMap φ)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Arrow.w_mk_right`：w_mk_right {f : Arrow T} {X Y : T} {g :
 X ⟶ Y} (sq : f ⟶ mk g) : dsimp% sq.left ≫ g = f.hom ≫ sq.right
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Arrow.hom_ext`：hom_ext {X Y : Arrow T} (f g : X ⟶ Y) (h₁ 
: f.left = g.left) (h₂ : f.right = g.right) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.RetractArrow.retract_left`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W}   (h : Category
Theory.RetractArrow f g),   Ca…
· 使用引理 `CategoryTheory.ShortComplex.homologyMap_id`：homologyMap_id [HasHomology 
S] : homologyMap (𝟙 S) = 𝟙 _
· 使用定理 `CategoryTheory.RetractArrow.retract_right`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X Y Z W : C} {f : Y ⟶ X} {g : W ⟶ Z}   (h : Categor
yTheory.RetractArrow f g),   Ca…
· 使用引理 `CategoryTheory.MorphismProperty.of_retract`：of_retract {P : MorphismProp
erty C} [P.IsStableUnderRetracts] {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W} (h : Ret
ractArrow f g) (hg : P g) : P f
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderRetracts.isomorphisms`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C],   (CategoryTheory.Morphism
Property.isomorphisms C).IsStableUnderRetracts
-/
lemma quasiIso_of_retract (h : RetractArrow f₁ f₂) [hf₂ : QuasiIso f₂] :
    QuasiIso f₁ := by
  rw [quasiIso_iff] at hf₂ ⊢
  have h : RetractArrow (homologyMap f₁) (homologyMap f₂) :=
    { i := Arrow.homMk (u := homologyMap (show S₁ ⟶ S₂ from h.i.left))
        (v := homologyMap (show T₁ ⟶ T₂ from h.i.right)) (by simp [← homologyMap_comp])
      r := Arrow.homMk (u := homologyMap (show S₂ ⟶ S₁ from h.r.left))
        (v := homologyMap (show T₂ ⟶ T₁ from h.r.right)) (by simp [← homologyMap_comp])
      retract := by ext <;> simp [← homologyMap_comp] }
  exact (MorphismProperty.isomorphisms C).of_retract h hf₂

end ShortComplex

end CategoryTheory

