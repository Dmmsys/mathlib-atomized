/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-! # Essential surjectivity of the functor induced on composable arrows

Assuming that `L : C ⥤ D` is a localization functor for a class of morphisms `W`
that has a calculus of left *or* right fractions, we show in this file
that the functor `L.mapComposableArrows n : ComposableArrows C n ⥤ ComposableArrows D n`
is essentially surjective for any `n : ℕ`.

-/

public section

namespace CategoryTheory

namespace Localization

variable {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) (W : MorphismProperty C)
  [L.IsLocalization W]

open ComposableArrows

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Localization.essSurj_mapComposableArrows_of_hasRightCalculusOfF
ractions** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Localization`。
形式化陈述：essSurj_mapComposableArrows_of_hasRightCalculusOfFractions [W.HasRightCalc
ulusOfFractions] (n : Nat) : (L.mapComposableArrows n).EssSurj where mem_essImag
e Y
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.essSurj`：essSurj (W) [L.IsLocalization W] : 
L.EssSurj
· 使用引理 `CategoryTheory.ComposableArrows.mk₀_surjective`：mk₀_surjective (F : Comp
osableArrows C 0) : exists (X : C), F = mk₀ X
· 使用定理 `CategoryTheory.Functor.EssSurj.mem_essImage`：∀ {C : Type u₁} {D : Type u
₂} {inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   (F : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ComposableArrows.precomp_surjective`：precomp_surjective (
F : ComposableArrows C (n + 1)) : exists (F₀ : ComposableArrows C n) (X₀ : C) (f
₀ : X₀ ⟶ F₀.left), F = F₀.precomp f₀
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.Localization.exists_rightFraction`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.MorphismProperty.RightFraction.hs`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}
 {X Y : C}   (self : W.RightFraction X…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsSplitMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f], 
  CategoryTheory.Mono…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.MorphismProperty.RightFraction.map_s_comp_map`：map_s_comp
_map (φ : W.RightFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) : L.map φ.s ≫
 φ.map L hL = L.map φ.f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma essSurj_mapComposableArrows_of_hasRightCalculusOfFractions
    [W.HasRightCalculusOfFractions] (n : ℕ) :
    (L.mapComposableArrows n).EssSurj where
  mem_essImage Y := by
    have := essSurj L W
    induction n with
    | zero =>
      obtain ⟨Y, rfl⟩ := mk₀_surjective Y
      exact ⟨mk₀ _, ⟨isoMk₀ (L.objObjPreimageIso Y)⟩⟩
    | succ n hn =>
      obtain ⟨Y, Z, f, rfl⟩ := ComposableArrows.precomp_surjective Y
      obtain ⟨Y', ⟨e⟩⟩ := hn Y
      obtain ⟨f', hf'⟩ := exists_rightFraction L W
        ((L.objObjPreimageIso Z).hom ≫ f ≫ (e.app 0).inv)
      refine ⟨Y'.precomp f'.f,
        ⟨isoMkSucc (isoOfHom L W _ f'.hs ≪≫ L.objObjPreimageIso Z) e ?_⟩⟩
      dsimp at hf' ⊢
      simp [← cancel_mono (e.inv.app 0), hf']
/-
**CategoryTheory.Localization.essSurj_mapComposableArrows** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Localization`。
形式化陈述：essSurj_mapComposableArrows [W.HasLeftCalculusOfFractions] (n : Nat) : (L.
mapComposableArrows n).EssSurj
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Localization.essSurj_mapComposableArrows_of_hasRightCalcu
lusOfFractions`：essSurj_mapComposableArrows_of_hasRightCalculusOfFractions [W.Ha
sRightCalculusOfFractions] (n : Nat) : (L.mapComposableArrows n).EssSurj whe…
· 使用定理 `CategoryTheory.Functor.IsLocalization.op`：∀ {C : Type u_1} {D : Type u_2
} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.MorphismProperty.instHasRightCalculusOfFractionsOppositeO
pOfHasLeftCalculusOfFractions`：∀ {C : Type u_1} [inst : CategoryTheory.Category.
{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}   [h : W.HasLeftCalculusOf
Fractions],…
· 使用引理 `CategoryTheory.Functor.essSurj_of_iso`：essSurj_of_iso {F G : C ⥤ D} [Ess
Surj F] (α : F ≅ G) : EssSurj G where mem_essImage Y
· 使用定理 `CategoryTheory.Functor.instEssSurjOppositeRightOp`：∀ (C : Type u₁) [inst
 : CategoryTheory.Category.{v₁, u₁} C] (D : Type u₂) [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instEssSurjOppositeOp`：∀ (C : Type u₁) [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] (D : Type u₂) [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {F : CategoryTheor…
· 使用引理 `CategoryTheory.Functor.essSurj_of_comp_fully_faithful`：essSurj_of_comp_f
ully_faithful (F : C ⥤ D) (G : D ⥤ E) [(F ⋙ G).EssSurj] [G.Faithful] [G.Full] : 
F.EssSurj where mem_essImage X
-/
lemma essSurj_mapComposableArrows [W.HasLeftCalculusOfFractions] (n : ℕ) :
    (L.mapComposableArrows n).EssSurj := by
  have := essSurj_mapComposableArrows_of_hasRightCalculusOfFractions L.op W.op n
  have := Functor.essSurj_of_iso (L.mapComposableArrowsOpIso n).symm
  exact Functor.essSurj_of_comp_fully_faithful _ (opEquivalence D n).functor.rightOp

end Localization

end CategoryTheory

