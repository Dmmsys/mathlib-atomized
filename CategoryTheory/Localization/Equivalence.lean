/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.CatCommSq

/-!
# Localization functors are preserved through equivalences

In `Mathlib/CategoryTheory/Localization/Predicate.lean`, the lemma
`Localization.of_equivalence_target` already showed that the predicate of localized categories is
unchanged when we replace the target category (i.e. the candidate localized category) by an
equivalent category.
In this file, we show the same for the source category (`Localization.of_equivalence_source`).
More generally, `Localization.of_equivalences` shows that we may replace both the
source and target categories by equivalent categories. This is obtained using
`Localization.isEquivalence` which provide a sufficient condition in order to show
that a functor between localized categories is an equivalence.

-/

@[expose] public section

namespace CategoryTheory

open Category Localization

variable {C₁ C₂ D D₁ D₂ : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Category* D₁] [Category* D₂]

namespace Localization

variable
  (L₁ : C₁ ⥤ D₁) (W₁ : MorphismProperty C₁) [L₁.IsLocalization W₁]
  (L₂ : C₂ ⥤ D₂) (W₂ : MorphismProperty C₂) [L₂.IsLocalization W₂]
  (G : C₁ ⥤ D₂) (G' : D₁ ⥤ D₂) [Lifting L₁ W₁ G G']
  (F : C₂ ⥤ D₁) (F' : D₂ ⥤ D₁) [Lifting L₂ W₂ F F']
  (α : G ⋙ F' ≅ L₁) (β : F ⋙ G' ≅ L₂)

/-- Basic constructor of an equivalence between localized categories -/
/-
**CategoryTheory.Localization.equivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Localization`。
形式化陈述：equivalence : D₁ ≌ D₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Basic constructor of an equivalence between localized categories
-/
noncomputable def equivalence : D₁ ≌ D₂ :=
  Equivalence.mk G' F' (liftNatIso L₁ W₁ L₁ (G ⋙ F') (𝟭 D₁) (G' ⋙ F') α.symm)
    (liftNatIso L₂ W₂ (F ⋙ G') L₂ (F' ⋙ G') (𝟭 D₂) β)

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Localization.equivalence_counitIso_app** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Localization`。
形式化陈述：equivalence_counitIso_app (X : C₂) : (equivalence L₁ W₁ L₂ W₂ G G' F F' α 
β).counitIso.app (L₂.obj X) = (Lifting.iso L₂ W₂ (F ⋙ G') (F' ⋙ G')).app X ≪≫ β.
app X
参数：X : C₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Localization.liftNatTrans_app`：liftNatTrans_app (F₁ F₂ : 
C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂'] (τ : F₁ ⟶ F₂)
 (X : C) : (liftNatTrans L W F₁ F₂…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma equivalence_counitIso_app (X : C₂) :
    (equivalence L₁ W₁ L₂ W₂ G G' F F' α β).counitIso.app (L₂.obj X) =
      (Lifting.iso L₂ W₂ (F ⋙ G') (F' ⋙ G')).app X ≪≫ β.app X := by
  ext
  dsimp [equivalence, Equivalence.mk]
  rw [liftNatTrans_app]
  dsimp [Lifting.iso]
  rw [comp_id]

include L₁ W₁ L₂ W₂ G F F' α β in
/-- Basic constructor of an equivalence between localized categories -/
/-
**CategoryTheory.Localization.isEquivalence** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Localization`。
形式化陈述：isEquivalence : G'.IsEquivalence
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…

--- 原说明 ---
Basic constructor of an equivalence between localized categories
-/
lemma isEquivalence : G'.IsEquivalence :=
  (equivalence L₁ W₁ L₂ W₂ G G' F F' α β).isEquivalence_functor

end Localization

namespace Functor

namespace IsLocalization

/-- If `L₁ : C₁ ⥤ D` is a localization functor for `W₁ : MorphismProperty C₁`, then it is also
the case of a functor `L₂ : C₂ ⥤ D` for a suitable `W₂ : MorphismProperty C₂` when
we have an equivalence of category `E : C₁ ≌ C₂` and an isomorphism `E.functor ⋙ L₂ ≅ L₁`. -/
/-
**CategoryTheory.Functor.IsLocalization.of_equivalence_source** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Functor.IsLocalization`。
形式化陈述：of_equivalence_source (L₁ : C₁ ⥤ D) (W₁ : MorphismProperty C₁) (L₂ : C₂ ⥤ 
D) (W₂ : MorphismProperty C₂) (E : C₁ ≌ C₂) (hW₁ : W₁ <= W₂.isoClosure.inverseIm
age E.functor) (hW₂ : W₂.IsInvertedBy L₂) [L₁.IsLocalization W₁] (iso : E.functo
r ⋙ L₂ ≅ L₁) : L₂.IsLocalization W₂
参数：L₁ : C₁ ⥤ D；W₁ : MorphismProperty C₁；L₂ : C₂ ⥤ D；W₂ : MorphismProperty C₂；E :
 C₁ ≌ C₂；hW₁ : W₁ <= W₂.isoClosure.inverseImage E.functor；hW₂ : W₂.IsInvertedBy 
L₂；iso : E.functor ⋙ L₂ ≅ L₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.isomorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.iso
morphisms C).RespectsIso
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用引理 `CategoryTheory.Localization.isEquivalence`：isEquivalence : G'.IsEquivale
nce

--- 原说明 ---
If `L₁ : C₁ ⥤ D` is a localization functor for `W₁ : MorphismProperty C₁`, then 
it is also
the case of a functor `L₂ : C₂ ⥤ D` for a suitable `W₂ : MorphismProperty C₂` wh
en
we have an equivalence of category `E : C₁ ≌ C₂` and an isomorphism `E.functor ⋙
 L₂ ≅ L₁`.
-/
lemma of_equivalence_source (L₁ : C₁ ⥤ D) (W₁ : MorphismProperty C₁)
    (L₂ : C₂ ⥤ D) (W₂ : MorphismProperty C₂)
    (E : C₁ ≌ C₂) (hW₁ : W₁ ≤ W₂.isoClosure.inverseImage E.functor) (hW₂ : W₂.IsInvertedBy L₂)
    [L₁.IsLocalization W₁] (iso : E.functor ⋙ L₂ ≅ L₁) : L₂.IsLocalization W₂ := by
  have h : W₁.IsInvertedBy (E.functor ⋙ W₂.Q) := fun _ _ f hf => by
    obtain ⟨_, _, f', hf', ⟨e⟩⟩ := hW₁ f hf
    exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (W₂.Q.mapArrow.mapIso e)).1 (Localization.inverts W₂.Q W₂ _ hf')
  exact
    { inverts := hW₂
      isEquivalence :=
        Localization.isEquivalence W₂.Q W₂ L₁ W₁ L₂ (Construction.lift L₂ hW₂)
          (E.functor ⋙ W₂.Q) (Localization.lift (E.functor ⋙ W₂.Q) h L₁) (by
            calc
              L₂ ⋙ lift (E.functor ⋙ W₂.Q) h L₁ ≅ _ := (leftUnitor _).symm
              _ ≅ _ := isoWhiskerRight E.counitIso.symm _
              _ ≅ E.inverse ⋙ E.functor ⋙ L₂ ⋙ lift (E.functor ⋙ W₂.Q) h L₁ :=
                    Functor.associator _ _ _
              _ ≅ E.inverse ⋙ L₁ ⋙ lift (E.functor ⋙ W₂.Q) h L₁ :=
                    isoWhiskerLeft E.inverse ((Functor.associator _ _ _).symm ≪≫
                      isoWhiskerRight iso _)
              _ ≅ E.inverse ⋙ E.functor ⋙ W₂.Q :=
                    isoWhiskerLeft _ (Localization.fac (E.functor ⋙ W₂.Q) h L₁)
              _ ≅ (E.inverse ⋙ E.functor) ⋙ W₂.Q := (Functor.associator _ _ _).symm
              _ ≅ 𝟭 C₂ ⋙ W₂.Q := isoWhiskerRight E.counitIso _
              _ ≅ W₂.Q := leftUnitor _)
          (Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Lifting.iso W₂.Q W₂ _ _) ≪≫ iso) }

/-- If `L₁ : C₁ ⥤ D₁` is a localization functor for `W₁ : MorphismProperty C₁`, then if we
transport this functor `L₁` via equivalences `C₁ ≌ C₂` and `D₁ ≌ D₂` to get a functor
`L₂ : C₂ ⥤ D₂`, then `L₂` is also a localization functor for
a suitable `W₂ : MorphismProperty C₂`. -/
/-
**CategoryTheory.Functor.IsLocalization.of_equivalences** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Functor.IsLocalization`。
形式化陈述：of_equivalences (L₁ : C₁ ⥤ D₁) (W₁ : MorphismProperty C₁) [L₁.IsLocalizati
on W₁] (L₂ : C₂ ⥤ D₂) (W₂ : MorphismProperty C₂) (E : C₁ ≌ C₂) (E' : D₁ ≌ D₂) [C
atCommSq E.functor L₁ L₂ E'.functor] (hW₁ : W₁ <= W₂.isoClosure.inverseImage E.f
unctor) (hW₂ : W₂.IsInvertedBy L₂) : L₂.IsLocalization W₂
参数：L₁ : C₁ ⥤ D₁；W₁ : MorphismProperty C₁；L₂ : C₂ ⥤ D₂；W₂ : MorphismProperty C₂；E
 : C₁ ≌ C₂；E' : D₁ ≌ D₂；hW₁ : W₁ <= W₂.isoClosure.inverseImage E.functor；hW₂ : W
₂.IsInvertedBy L₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsLocalization.of_equivalence_target`：of_equivale
nce_target {E : Type*} [Category* E] (L' : C ⥤ E) (eq : D ≌ E) [L.IsLocalization
 W] (e : L ⋙ eq.functor ≅ L') : L'.IsLocalization…
· 使用引理 `CategoryTheory.Functor.IsLocalization.of_equivalence_source`：of_equivale
nce_source (L₁ : C₁ ⥤ D) (W₁ : MorphismProperty C₁) (L₂ : C₂ ⥤ D) (W₂ : Morphism
Property C₂) (E : C₁ ≌ C₂) (hW₁ : W₁ <= W₂.isoClo…

--- 原说明 ---
If `L₁ : C₁ ⥤ D₁` is a localization functor for `W₁ : MorphismProperty C₁`, then
 if we
transport this functor `L₁` via equivalences `C₁ ≌ C₂` and `D₁ ≌ D₂` to get a fu
nctor
`L₂ : C₂ ⥤ D₂`, then `L₂` is also a localization functor for
a suitable `W₂ : MorphismProperty C₂`.
-/
lemma of_equivalences (L₁ : C₁ ⥤ D₁) (W₁ : MorphismProperty C₁) [L₁.IsLocalization W₁]
    (L₂ : C₂ ⥤ D₂) (W₂ : MorphismProperty C₂)
    (E : C₁ ≌ C₂) (E' : D₁ ≌ D₂) [CatCommSq E.functor L₁ L₂ E'.functor]
    (hW₁ : W₁ ≤ W₂.isoClosure.inverseImage E.functor) (hW₂ : W₂.IsInvertedBy L₂) :
    L₂.IsLocalization W₂ := by
  have : (E.functor ⋙ L₂).IsLocalization W₁ :=
    of_equivalence_target L₁ W₁ _ E' ((CatCommSq.iso _ _ _ _).symm)
  exact of_equivalence_source (E.functor ⋙ L₂) W₁ L₂ W₂ E hW₁ hW₂ (Iso.refl _)

end IsLocalization

end Functor

end CategoryTheory

