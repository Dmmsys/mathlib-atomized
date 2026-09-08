/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.LocalizerMorphism
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Composition of localization functors

Given two composable functors `L₁ : C₁ ⥤ C₂` and `L₂ : C₂ ⥤ C₃`, it is shown
in this file that under some suitable conditions on `W₁ : MorphismProperty C₁`
`W₂ : MorphismProperty C₂` and `W₃ : MorphismProperty C₁`, then
if `L₁ : C₁ ⥤ C₂` is a localization functor for `W₁`,
then the composition `L₁ ⋙ L₂ : C₁ ⥤ C₃` is a localization functor for `W₃`
if and only if `L₂ : C₂ ⥤ C₃` is a localization functor for `W₂`.
The two implications are the lemmas `Functor.IsLocalization.comp` and
`Functor.IsLocalization.of_comp`.

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {E : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} E]
  {L₁ : C₁ ⥤ C₂} {L₂ : C₂ ⥤ C₃} {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace Localization

/-- Under some conditions on the `MorphismProperty`, functors satisfying the strict
universal property of the localization are stable under composition -/
/-
**CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.comp** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.Localization.StrictUniversalPropertyFixedTarget`
。
形式化陈述：{C₁ : Type u₁} →   {C₂ : Type u₂} →     {C₃ : Type u₃} →       {E : Type u
₄} →         [inst : CategoryTheory.Category.{v₁, u₁} C₁] →           [inst_1 : 
CategoryTheory.Category.{v₂, u₂} C₂] →             [inst_2 : CategoryTheory.Cate
gory.{v₃, u₃} C₃] →               [inst_3 : CategoryTheory.Category.{v₄, u₄} E] 
→                 {L₁ : CategoryTheory.Functor C₁ C₂} →                   {L₂ : 
CategoryTheory.Functor C₂ C₃} →                     {W₁ : CategoryTheory.Morphis
mProperty C₁} →                       {W₂ : CategoryTheory.MorphismProperty C₂} 
→                         CategoryTheory.Localization.StrictUniversalPropertyFix
edTarget L₁ W₁ E →                           CategoryTheory.Localization.StrictU
niversalPropertyFixedTarget L₂ W₂ E →                             (W₃ : Category
Theory.MorphismProperty C₁) →                               W₃.IsInvertedBy (L₁.
comp L₂) →                                 W₁ ≤ W₃ →                            
       W₂ ≤ W₃.map L₁ →                                     CategoryTheory.Local
ization.StrictUniversalPropertyFixedTarget (L₁.comp L₂) W₃ E
参数：W₃ : CategoryTheory.MorphismProperty C₁；L₁.comp L₂；L₁.comp L₂。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.IsInvertedBy.of_le`：of_le (P Q : Morphis
mProperty C) (F : C ⥤ D) (hQ : Q.IsInvertedBy F) (h : P <= Q) : P.IsInvertedBy F

--- 原说明 ---
Under some conditions on the `MorphismProperty`, functors satisfying the strict
universal property of the localization are stable under composition
-/
def StrictUniversalPropertyFixedTarget.comp
    (h₁ : StrictUniversalPropertyFixedTarget L₁ W₁ E)
    (h₂ : StrictUniversalPropertyFixedTarget L₂ W₂ E)
    (W₃ : MorphismProperty C₁) (hW₃ : W₃.IsInvertedBy (L₁ ⋙ L₂))
    (hW₁₃ : W₁ ≤ W₃) (hW₂₃ : W₂ ≤ W₃.map L₁) :
    StrictUniversalPropertyFixedTarget (L₁ ⋙ L₂) W₃ E where
  inverts := hW₃
  lift F hF := h₂.lift (h₁.lift F (MorphismProperty.IsInvertedBy.of_le _ _ F hF hW₁₃)) (by
    refine MorphismProperty.IsInvertedBy.of_le _ _ _ ?_ hW₂₃
    simpa only [MorphismProperty.IsInvertedBy.map_iff, h₁.fac F] using hF)
  fac F hF := by rw [Functor.assoc, h₂.fac, h₁.fac]
  uniq _ _ h := h₂.uniq _ _ (h₁.uniq _ _ (by simpa only [Functor.assoc] using h))

end Localization

open Localization

namespace Functor

namespace IsLocalization

variable (L₁ W₁ L₂ W₂)

/-
**CategoryTheory.Functor.IsLocalization.comp** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Functor.IsLocalization`。
形式化陈述：comp [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] (W₃ : MorphismProperty 
C₁) (hW₃ : W₃.IsInvertedBy (L₁ ⋙ L₂)) (hW₁₃ : W₁ <= W₃) (hW₂₃ : W₂ <= W₃.map L₁)
 : (L₁ ⋙ L₂).IsLocalization W₃
参数：W₃ : MorphismProperty C₁；hW₃ : W₃.IsInvertedBy (L₁ ⋙ L₂)；hW₁₃ : W₁ <= W₃；hW₂₃
 : W₂ <= W₃.map L₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.inverseImage_map_eq_of_isEquivalence`：in
verseImage_map_eq_of_isEquivalence (P : MorphismProperty C) [P.RespectsIso] (F :
 C ⥤ D) [F.IsEquivalence] : (P.map F).inverseImage F = P
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.map_isoClosure`：map_isoClosure (P : Morp
hismProperty C) (F : C ⥤ D) : P.isoClosure.map F = P.map F
· 使用引理 `CategoryTheory.MorphismProperty.le_isoClosure`：le_isoClosure (P : Morphi
smProperty C) : P <= P.isoClosure
· 使用定理 `CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence.of_equivalence`：
∀ {C₁ : Type u₁} {C₂ : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [
inst_1 : CategoryTheory.Category.{v₂, u₂} C₂] {W₁ : Category…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.IsInvertedBy.iff_comp`：∀ {C₁ : Type u_1}
 {C₂ : Type u_2} {C₃ : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C₁] 
  [inst_1 : CategoryTheory.Category.{v_2, u…
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.MorphismProperty.IsInvertedBy.iff_of_iso`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory
.Category.{v', u'} D]   (W : CategoryTheory.M…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.MorphismProperty.monotone_map`：monotone_map (F : C ⥤ D) :
 Monotone (map · F)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.MorphismProperty.map_map`：map_map (P : MorphismProperty C
) (F : C ⥤ D) {E : Type*} [Category* E] (G : D ⥤ E) : (P.map F).map G = P.map (F
 ⋙ G)
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `CategoryTheory.MorphismProperty.map_eq_of_iso`：map_eq_of_iso (P : Morphi
smProperty C) {F G : C ⥤ D} (e : F ≅ G) : P.map F = P.map G
· 使用定理 `CategoryTheory.Functor.IsLocalization.mk'`：∀ {C : Type u_1} {D : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cate
gory.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.Functor.IsLocalization.of_equivalence_target`：of_equivale
nce_target {E : Type*} [Category* E] (L' : C ⥤ E) (eq : D ≌ E) [L.IsLocalization
 W] (e : L ⋙ eq.functor ≅ L') : L'.IsLocalization…
-/
lemma comp [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
    (W₃ : MorphismProperty C₁) (hW₃ : W₃.IsInvertedBy (L₁ ⋙ L₂))
    (hW₁₃ : W₁ ≤ W₃) (hW₂₃ : W₂ ≤ W₃.map L₁) :
    (L₁ ⋙ L₂).IsLocalization W₃ := by
  -- The proof proceeds by reducing to the case of the constructed
  -- localized categories, which satisfy the strict universal property
  -- of the localization. In order to do this, we introduce
  -- an equivalence of categories `E₂ : C₂ ≅ W₁.Localization`. Via
  -- this equivalence, we introduce `W₂' : MorphismProperty W₁.Localization`
  -- which corresponds to `W₂` via the equivalence `E₂`.
  -- Then, we have a localizer morphism `Φ : LocalizerMorphism W₂ W₂'` which
  -- is a localized equivalence (because `E₂` is an equivalence).
  let E₂ := Localization.uniq L₁ W₁.Q W₁
  let W₂' := W₂.map E₂.functor
  let Φ : LocalizerMorphism W₂ W₂' :=
    { functor := E₂.functor
      map := by
        have eq := W₂.isoClosure.inverseImage_map_eq_of_isEquivalence E₂.functor
        rw [MorphismProperty.map_isoClosure] at eq
        rw [eq]
        apply W₂.le_isoClosure }
  have := LocalizerMorphism.IsLocalizedEquivalence.of_equivalence Φ (by rfl)
  -- The fact that `Φ` is a localized equivalence allows to consider
  -- the induced equivalence of categories `E₃ : C₃ ≅ W₂'.Localization`, and
  -- the isomorphism `iso : (W₁.Q ⋙ W₂'.Q) ⋙ E₃.inverse ≅ L₁ ⋙ L₂`
  let E₃ := (Φ.localizedFunctor L₂ W₂'.Q).asEquivalence
  let iso : (W₁.Q ⋙ W₂'.Q) ⋙ E₃.inverse ≅ L₁ ⋙ L₂ := by
    calc
      _ ≅ L₁ ⋙ E₂.functor ⋙ W₂'.Q ⋙ E₃.inverse :=
          Functor.associator _ _ _ ≪≫ isoWhiskerRight (compUniqFunctor L₁ W₁.Q W₁).symm _ ≪≫
            Functor.associator _ _ _
      _ ≅ L₁ ⋙ L₂ ⋙ E₃.functor ⋙ E₃.inverse :=
          isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
            isoWhiskerRight (Φ.catCommSq L₂ W₂'.Q).iso E₃.inverse ≪≫ Functor.associator _ _ _)
      _ ≅ L₁ ⋙ L₂ := isoWhiskerLeft _ (isoWhiskerLeft _ E₃.unitIso.symm ≪≫ L₂.rightUnitor)
  -- In order to show `(W₁.Q ⋙ W₂'.Q).IsLocalization W₃`, we need
  -- to check the assumptions of `StrictUniversalPropertyFixedTarget.comp`
  have hW₃' : W₃.IsInvertedBy (W₁.Q ⋙ W₂'.Q) := by
    simpa only [← MorphismProperty.IsInvertedBy.iff_comp _ _ E₃.inverse,
      MorphismProperty.IsInvertedBy.iff_of_iso W₃ iso] using hW₃
  have hW₂₃' : W₂' ≤ W₃.map W₁.Q := (MorphismProperty.monotone_map E₂.functor hW₂₃).trans
    (by simpa only [W₃.map_map]
      using le_of_eq (W₃.map_eq_of_iso (compUniqFunctor L₁ W₁.Q W₁)))
  have : (W₁.Q ⋙ W₂'.Q).IsLocalization W₃ := by
    refine IsLocalization.mk' _ _ ?_ ?_
    all_goals
      exact (StrictUniversalPropertyFixedTarget.comp
        (strictUniversalPropertyFixedTargetQ W₁ _)
        (strictUniversalPropertyFixedTargetQ W₂' _) W₃ hW₃' hW₁₃ hW₂₃')
  -- Finally, the previous result can be transported via the equivalence `E₃`
  exact IsLocalization.of_equivalence_target _ W₃ _ E₃.symm iso
/-
**CategoryTheory.Functor.IsLocalization.of_comp** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Functor.IsLocalization`。
形式化陈述：of_comp (W₃ : MorphismProperty C₁) [L₁.IsLocalization W₁] [(L₁ ⋙ L₂).IsLoc
alization W₃] (hW₁₃ : W₁ <= W₃) (hW₂₃ : W₂ = W₃.map L₁) : L₂.IsLocalization W₂
参数：W₃ : MorphismProperty C₁；L₁ ⋙ L₂；hW₁₃ : W₁ <= W₃；hW₂₃ : W₂ = W₃.map L₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.IsLocalization.comp`：comp [L₁.IsLocalization W₁] 
[L₂.IsLocalization W₂] (W₃ : MorphismProperty C₁) (hW₃ : W₃.IsInvertedBy (L₁ ⋙ L
₂)) (hW₁₃ : W₁ <= W₃) (hW₂₃ : W₂…
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.MorphismProperty.map_mem_map`：map_mem_map (P : MorphismPr
operty C) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (hf : P f) : (P.map F) (F.map f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `CategoryTheory.Functor.IsLocalization.of_equivalence_target`：of_equivale
nce_target {E : Type*} [Category* E] (L' : C ⥤ E) (eq : D ≌ E) [L.IsLocalization
 W] (e : L ⋙ eq.functor ≅ L') : L'.IsLocalization…
-/
lemma of_comp (W₃ : MorphismProperty C₁)
    [L₁.IsLocalization W₁] [(L₁ ⋙ L₂).IsLocalization W₃]
    (hW₁₃ : W₁ ≤ W₃) (hW₂₃ : W₂ = W₃.map L₁) :
    L₂.IsLocalization W₂ := by
    have : (L₁ ⋙ W₂.Q).IsLocalization W₃ :=
      comp L₁ W₂.Q W₁ W₂ W₃ (fun X Y f hf => Localization.inverts W₂.Q W₂ _
        (by simpa only [hW₂₃] using W₃.map_mem_map _ _ hf)) hW₁₃
        (by rw [hW₂₃])
    exact IsLocalization.of_equivalence_target W₂.Q W₂ L₂
      (Localization.uniq (L₁ ⋙ W₂.Q) (L₁ ⋙ L₂) W₃)
      (liftNatIso L₁ W₁ _ _ _ _
        ((Functor.associator _ _ _).symm ≪≫
          Localization.compUniqFunctor (L₁ ⋙ W₂.Q) (L₁ ⋙ L₂) W₃))

end IsLocalization

end Functor

end CategoryTheory

