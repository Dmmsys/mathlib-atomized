/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# Lifting of bifunctors

In this file, in the context of the localization of categories, we extend the notion
of lifting of functors to the case of bifunctors. As the localization of categories
behaves well with respect to finite products of categories (when the classes of
morphisms contain identities), all the definitions for bifunctors `C₁ ⥤ C₂ ⥤ E`
are obtained by reducing to the case of functors `(C₁ × C₂) ⥤ E` by using
currying and uncurrying.

Given morphism properties `W₁ : MorphismProperty C₁` and `W₂ : MorphismProperty C₂`,
and a functor `F : C₁ ⥤ C₂ ⥤ E`, we define `MorphismProperty.IsInvertedBy₂ W₁ W₂ F`
as the condition that the functor `uncurry.obj F : C₁ × C₂ ⥤ E` inverts `W₁.prod W₂`.

If `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` are localization functors for `W₁` and `W₂`
respectively, and `F : C₁ ⥤ C₂ ⥤ E` satisfies `MorphismProperty.IsInvertedBy₂ W₁ W₂ F`,
we introduce `Localization.lift₂ F hF L₁ L₂ : D₁ ⥤ D₂ ⥤ E` which is a bifunctor
which lifts `F`.

-/

@[expose] public section

namespace CategoryTheory

open Category CategoryTheory.Functor

variable {C₁ C₂ D₁ D₂ E E' : Type*} [Category* C₁] [Category* C₂]
  [Category* D₁] [Category* D₂] [Category* E] [Category* E']

namespace MorphismProperty

/--
Definition of `IsInvertedBy₂` / `IsInvertedBy₂` 的定义

English:
definition IsInvertedBy₂
  signature: (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  body: (W₁.prod W₂).IsInvertedBy (uncurry.obj F)

中文:
定义 IsInvertedBy₂
  签名: (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  定义体: (W₁.prod W₂).IsInvertedBy (uncurry.obj F)

Depends on / 依赖: IsInvertedBy, uncurry, uncurry.obj
-/
def IsInvertedBy₂ (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    (F : C₁ ⥤ C₂ ⥤ E) : Prop :=
  (W₁.prod W₂).IsInvertedBy (uncurry.obj F)

end MorphismProperty

namespace Localization

section

variable (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)

/--
Definition of `Lifting₂` / `Lifting₂` 的定义

English:
class Lifting₂
  parameters: (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  axioms and operations (1):
    - iso((L₁ L₂ W₁ W₂ F F')) : (((whiskeringLeft₂ E).obj L₁).obj L₂).obj F' ≅ F

中文:
类 Lifting₂
  参数: (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  公理与运算 (1 个):
    - iso((L₁ L₂ W₁ W₂ F F')) : (((whiskeringLeft₂ E).obj L₁).obj L₂).obj F' ≅ F
-/
class Lifting₂ (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    (F : C₁ ⥤ C₂ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ E) where
  /-- the isomorphism `(((whiskeringLeft₂ E).obj L₁).obj L₂).obj F' ≅ F` expressing
  that `F` is induced by `F'` up to an isomorphism -/
  iso (L₁ L₂ W₁ W₂ F F') : (((whiskeringLeft₂ E).obj L₁).obj L₂).obj F' ≅ F

variable (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  (F : C₁ ⥤ C₂ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ E) [Lifting₂ L₁ L₂ W₁ W₂ F F']

/-- If `Lifting₂ L₁ L₂ W₁ W₂ F F'` holds, then `Lifting L₂ W₂ (F.obj X₁) (F'.obj (L₁.obj X₁))`
holds for any `X₁ : C₁`. -/
@[instance_reducible]
/--
Definition of `Lifting₂.fst` / `Lifting₂.fst` 的定义

English:
definition Lifting₂.fst
  signature: (X₁ : C₁)
  body: ((evaluation _ _).obj X₁).mapIso (Lifting₂.iso L₁ L₂ W₁ W₂ F F')

中文:
定义 Lifting₂.fst
  签名: (X₁ : C₁)
  定义体: ((evaluation _ _).obj X₁).mapIso (Lifting₂.iso L₁ L₂ W₁ W₂ F F')

Depends on / 依赖: evaluation, mapIso
-/
noncomputable def Lifting₂.fst (X₁ : C₁) :
    Lifting L₂ W₂ (F.obj X₁) (F'.obj (L₁.obj X₁)) where
  iso := ((evaluation _ _).obj X₁).mapIso (Lifting₂.iso L₁ L₂ W₁ W₂ F F')

/--
Instance `Lifting₂.flip` / 实例 `Lifting₂.flip`

English:
instance Lifting₂.flip
  signature: : Lifting₂ L₂ L₁ W₂ W₁ F.flip F'.flip where
  body: (flipFunctor _ _ _).mapIso (Lifting₂.iso L₁ L₂ W₁ W₂ F F')

中文:
实例 Lifting₂.flip
  签名: : Lifting₂ L₂ L₁ W₂ W₁ F.flip F'.flip where
  定义体: (flipFunctor _ _ _).mapIso (Lifting₂.iso L₁ L₂ W₁ W₂ F F')

Depends on / 依赖: flipFunctor, infer_instance, isFinitelyPresentable_iff_preservesFilteredColimitsOfSize, mapIso
-/
noncomputable instance Lifting₂.flip : Lifting₂ L₂ L₁ W₂ W₁ F.flip F'.flip where
  iso := (flipFunctor _ _ _).mapIso (Lifting₂.iso L₁ L₂ W₁ W₂ F F')

/-- If `Lifting₂ L₁ L₂ W₁ W₂ F F'` holds, then
`Lifting L₁ W₁ (F.flip.obj X₂) (F'.flip.obj (L₂.obj X₂))` holds for any `X₂ : C₂`. -/
@[instance_reducible]
/--
Definition of `Lifting₂.snd` / `Lifting₂.snd` 的定义

English:
definition Lifting₂.snd
  signature: (X₂ : C₂)
  body: Lifting₂.fst L₂ L₁ W₂ W₁ F.flip F'.flip X₂

中文:
定义 Lifting₂.snd
  签名: (X₂ : C₂)
  定义体: Lifting₂.fst L₂ L₁ W₂ W₁ F.flip F'.flip X₂

Depends on / 依赖: F.flip, X.property, property
-/
noncomputable def Lifting₂.snd (X₂ : C₂) :
    Lifting L₁ W₁ (F.flip.obj X₂) (F'.flip.obj (L₂.obj X₂)) :=
  Lifting₂.fst L₂ L₁ W₂ W₁ F.flip F'.flip X₂

/--
Instance `Lifting₂.uncurry` / 实例 `Lifting₂.uncurry`

English:
instance Lifting₂.uncurry
  signature: :
  body: Functor.uncurry.mapIso (Lifting₂.iso L₁ L₂ W₁ W₂ F F')

中文:
实例 Lifting₂.uncurry
  签名: :
  定义体: Functor.uncurry.mapIso (Lifting₂.iso L₁ L₂ W₁ W₂ F F')

Depends on / 依赖: Functor, Functor.uncurry.mapIso, mapIso, uncurry
-/
noncomputable instance Lifting₂.uncurry :
    Lifting (L₁.prod L₂) (W₁.prod W₂) (uncurry.obj F) (uncurry.obj F') where
  iso := Functor.uncurry.mapIso (Lifting₂.iso L₁ L₂ W₁ W₂ F F')

end

section

variable (F : C₁ ⥤ C₂ ⥤ E) {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  (hF : MorphismProperty.IsInvertedBy₂ W₁ W₂ F)
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities]

/--
Definition of `lift₂` / `lift₂` 的定义

English:
definition lift₂
  signature: : D₁ ⥤ D₂ ⥤ E
  body: curry.obj (lift (uncurry.obj F) hF (L₁.prod L₂))

中文:
定义 lift₂
  签名: : D₁ ⥤ D₂ ⥤ E
  定义体: curry.obj (lift (uncurry.obj F) hF (L₁.prod L₂))

Depends on / 依赖: curry.obj, uncurry, uncurry.obj
-/
noncomputable def lift₂ : D₁ ⥤ D₂ ⥤ E :=
  curry.obj (lift (uncurry.obj F) hF (L₁.prod L₂))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Lifting₂ L₁ L₂ W₁ W₂ F (lift₂ F hF L₁ L₂)
  body: (curryObjProdComp _ _ _).symm ≪≫
    curry.mapIso (fac (uncurry.obj F) hF (L₁.prod L₂)) ≪≫
    currying.unitIso.symm.app F

中文:
实例 :
  签名: Lifting₂ L₁ L₂ W₁ W₂ F (lift₂ F hF L₁ L₂)
  定义体: (curryObjProdComp _ _ _).symm ≪≫
    curry.mapIso (fac (uncurry.obj F) hF (L₁.prod L₂)) ≪≫
    currying.unitIso.symm.app F

Depends on / 依赖: curryObjProdComp
-/
noncomputable instance : Lifting₂ L₁ L₂ W₁ W₂ F (lift₂ F hF L₁ L₂) where
  iso := (curryObjProdComp _ _ _).symm ≪≫
    curry.mapIso (fac (uncurry.obj F) hF (L₁.prod L₂)) ≪≫
    currying.unitIso.symm.app F

/--
Instance `Lifting₂.liftingLift₂` / 实例 `Lifting₂.liftingLift₂`

English:
instance Lifting₂.liftingLift₂
  signature: (X₁ : C₁)
  body: Lifting₂.fst _ _ W₁ _ _ _ _

中文:
实例 Lifting₂.liftingLift₂
  签名: (X₁ : C₁)
  定义体: Lifting₂.fst _ _ W₁ _ _ _ _
-/
noncomputable instance Lifting₂.liftingLift₂ (X₁ : C₁) :
    Lifting L₂ W₂ (F.obj X₁) ((lift₂ F hF L₁ L₂).obj (L₁.obj X₁)) :=
  Lifting₂.fst _ _ W₁ _ _ _ _

/--
Instance `Lifting₂.liftingLift₂Flip` / 实例 `Lifting₂.liftingLift₂Flip`

English:
instance Lifting₂.liftingLift₂Flip
  signature: (X₂ : C₂)
  body: Lifting₂.snd _ _ _ W₂ _ _ _

中文:
实例 Lifting₂.liftingLift₂Flip
  签名: (X₂ : C₂)
  定义体: Lifting₂.snd _ _ _ W₂ _ _ _
-/
noncomputable instance Lifting₂.liftingLift₂Flip (X₂ : C₂) :
    Lifting L₁ W₁ (F.flip.obj X₂) ((lift₂ F hF L₁ L₂).flip.obj (L₂.obj X₂)) :=
  Lifting₂.snd _ _ _ W₂ _ _ _

/--
lemma `lift₂_iso_hom_app_app₁` / 引理 `lift₂_iso_hom_app_app₁`

English:
lemma lift₂_iso_hom_app_app₁
  given: (X₁ : C₁) (X₂ : C₂)
  proof: rfl

中文:
引理 lift₂_iso_hom_app_app₁
  条件: (X₁ : C₁) (X₂ : C₂)
  证明: rfl
-/
lemma lift₂_iso_hom_app_app₁ (X₁ : C₁) (X₂ : C₂) :
    ((Lifting₂.iso L₁ L₂ W₁ W₂ F (lift₂ F hF L₁ L₂)).hom.app X₁).app X₂ =
      (Lifting.iso L₂ W₂ (F.obj X₁) ((lift₂ F hF L₁ L₂).obj (L₁.obj X₁))).hom.app X₂ :=
  rfl

/--
lemma `lift₂_iso_hom_app_app₂` / 引理 `lift₂_iso_hom_app_app₂`

English:
lemma lift₂_iso_hom_app_app₂
  given: (X₁ : C₁) (X₂ : C₂)
  proof: rfl

中文:
引理 lift₂_iso_hom_app_app₂
  条件: (X₁ : C₁) (X₂ : C₂)
  证明: rfl
-/
lemma lift₂_iso_hom_app_app₂ (X₁ : C₁) (X₂ : C₂) :
    ((Lifting₂.iso L₁ L₂ W₁ W₂ F (lift₂ F hF L₁ L₂)).hom.app X₁).app X₂ =
      (Lifting.iso L₁ W₁ (F.flip.obj X₂) ((lift₂ F hF L₁ L₂).flip.obj (L₂.obj X₂))).hom.app X₁ :=
  rfl

end

section

variable (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)
  (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities]
  (F : C₁ ⥤ C₂ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ E)
  [Lifting₂ L₁ L₂ W₁ W₂ F F']

/--
Instance `Lifting₂.compRight` / 实例 `Lifting₂.compRight`

English:
instance Lifting₂.compRight
  signature: {E' : Type*} [Category* E'] (G : E ⥤ E')
  body: ⟨isoWhiskerRight (iso L₁ L₂ W₁ W₂ F F') ((whiskeringRight _ _ _).obj G)⟩

中文:
实例 Lifting₂.compRight
  签名: {E' : 类型} [范畴* E'] (G : E ⥤ E')
  定义体: ⟨isoWhiskerRight (iso L₁ L₂ W₁ W₂ F F') ((whiskeringRight _ _ _).obj G)⟩

Depends on / 依赖: isoWhiskerRight, whiskeringRight
-/
noncomputable instance Lifting₂.compRight {E' : Type*} [Category* E'] (G : E ⥤ E') :
    Lifting₂ L₁ L₂ W₁ W₂
      (F ⋙ (whiskeringRight _ _ _).obj G)
      (F' ⋙ (whiskeringRight _ _ _).obj G) :=
  ⟨isoWhiskerRight (iso L₁ L₂ W₁ W₂ F F') ((whiskeringRight _ _ _).obj G)⟩

end

section

variable (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)
  (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities]
  (F₁ F₂ : C₁ ⥤ C₂ ⥤ E) (F₁' F₂' : D₁ ⥤ D₂ ⥤ E)
  [Lifting₂ L₁ L₂ W₁ W₂ F₁ F₁'] [Lifting₂ L₁ L₂ W₁ W₂ F₂ F₂']

/--
Definition of `lift₂NatTrans` / `lift₂NatTrans` 的定义

English:
definition lift₂NatTrans
  signature: (τ : F₁ ⟶ F₂)
  body: fullyFaithfulUncurry.preimage
    (liftNatTrans (L₁.prod L₂) (W₁.prod W₂) (uncurry.obj F₁)
      (uncurry.obj F₂) (uncurry.obj F₁') (uncurry.obj F₂') (uncurry.map τ))

中文:
定义 lift₂自然数Trans
  签名: (τ : F₁ ⟶ F₂)
  定义体: fullyFaithfulUncurry.preimage
    (liftNatTrans (L₁.prod L₂) (W₁.prod W₂) (uncurry.obj F₁)
      (uncurry.obj F₂) (uncurry.obj F₁') (uncurry.obj F₂') (uncurry.map τ))

Depends on / 依赖: fullyFaithfulUncurry, fullyFaithfulUncurry.preimage, liftNatTrans, preimage, uncurry, uncurry.map, uncurry.obj
-/
noncomputable def lift₂NatTrans (τ : F₁ ⟶ F₂) : F₁' ⟶ F₂' :=
  fullyFaithfulUncurry.preimage
    (liftNatTrans (L₁.prod L₂) (W₁.prod W₂) (uncurry.obj F₁)
      (uncurry.obj F₂) (uncurry.obj F₁') (uncurry.obj F₂') (uncurry.map τ))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `lift₂NatTrans_app_app` / 定理 `lift₂NatTrans_app_app`

English:
theorem lift₂NatTrans_app_app
  given: (τ : F₁ ⟶ F₂) (X₁ : C₁) (X₂ : C₂)
  proof: by
  dsimp [lift₂NatTrans, fullyFaithfulUncurry, Equivalence.fullyFaithfulFunctor]
  simp only [comp_id, id_comp]
  exact liftNatTrans_app _ _ _ _ (uncurry.obj F₁') (uncurry.obj F₂') (uncurry.map τ) ⟨X₁, X₂⟩

中文:
定理 lift₂自然数Trans_app_app
  条件: (τ : F₁ ⟶ F₂) (X₁ : C₁) (X₂ : C₂)
  证明: by
  dsimp [lift₂NatTrans, fullyFaithfulUncurry, Equivalence.fullyFaithfulFunctor]
  simp only [comp_id, id_comp]
  exact liftNatTrans_app _ _ _ _ (uncurry.obj F₁') (uncurry.obj F₂') (uncurry.map τ) ⟨X₁, X₂⟩

Depends on / 依赖: Equivalence, Equivalence.fullyFaithfulFunctor, comp_id, fullyFaithfulFunctor, fullyFaithfulUncurry, id_comp, liftNatTrans_app, uncurry, uncurry.map, uncurry.obj
-/
theorem lift₂NatTrans_app_app (τ : F₁ ⟶ F₂) (X₁ : C₁) (X₂ : C₂) :
    ((lift₂NatTrans L₁ L₂ W₁ W₂ F₁ F₂ F₁' F₂' τ).app (L₁.obj X₁)).app (L₂.obj X₂) =
      ((Lifting₂.iso L₁ L₂ W₁ W₂ F₁ F₁').hom.app X₁).app X₂ ≫ (τ.app X₁).app X₂ ≫
        ((Lifting₂.iso L₁ L₂ W₁ W₂ F₂ F₂').inv.app X₁).app X₂ := by
  dsimp [lift₂NatTrans, fullyFaithfulUncurry, Equivalence.fullyFaithfulFunctor]
  simp only [comp_id, id_comp]
  exact liftNatTrans_app _ _ _ _ (uncurry.obj F₁') (uncurry.obj F₂') (uncurry.map τ) ⟨X₁, X₂⟩

variable {F₁' F₂'} in
include W₁ W₂ in
/--
theorem `natTrans₂_ext` / 定理 `natTrans₂_ext`

English:
theorem natTrans₂_ext
  statement: {τ τ' : F₁' ⟶ F₂'}
  proof: uncurry.map_injective (natTrans_ext (L₁.prod L₂) (W₁.prod W₂) (fun _ => h _ _))

中文:
定理 natTrans₂_ext
  结论: {τ τ' : F₁' ⟶ F₂'}
  证明: uncurry.map_injective (natTrans_ext (L₁.prod L₂) (W₁.prod W₂) (fun _ => h _ _))

Depends on / 依赖: map_injective, natTrans_ext, uncurry, uncurry.map_injective
-/
theorem natTrans₂_ext {τ τ' : F₁' ⟶ F₂'}
    (h : forall (X₁ : C₁) (X₂ : C₂), (τ.app (L₁.obj X₁)).app (L₂.obj X₂) =
      (τ'.app (L₁.obj X₁)).app (L₂.obj X₂)) : τ = τ' :=
  uncurry.map_injective (natTrans_ext (L₁.prod L₂) (W₁.prod W₂) (fun _ => h _ _))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism `F₁' ≅ F₂'` of bifunctors induced by a
natural isomorphism `e : F₁ ≅ F₂` when `Lifting₂ L₁ L₂ W₁ W₂ F₁ F₁'`
and `Lifting₂ L₁ L₂ W₁ W₂ F₂ F₂'` hold. -/
@[simps]
/--
Definition of `lift₂NatIso` / `lift₂NatIso` 的定义

English:
definition lift₂NatIso
  signature: (e : F₁ ≅ F₂)
  body: lift₂NatTrans L₁ L₂ W₁ W₂ F₁ F₂ F₁' F₂' e.hom
  inv := lift₂NatTrans L₁ L₂ W₁ W₂ F₂ F₁ F₂' F₁' e.inv
  hom_inv_id := natTrans₂_ext L₁ L₂ W₁ W₂ (by simp)
  inv_hom_id := natTrans₂_ext L₁ L₂ W₁ W₂ (by simp)

中文:
定义 lift₂自然数Iso
  签名: (e : F₁ ≅ F₂)
  定义体: lift₂NatTrans L₁ L₂ W₁ W₂ F₁ F₂ F₁' F₂' e.hom
  inv := lift₂NatTrans L₁ L₂ W₁ W₂ F₂ F₁ F₂' F₁' e.inv
  hom_inv_id := natTrans₂_ext L₁ L₂ W₁ W₂ (by simp)
  inv_hom_id := natTrans₂_ext L₁ L₂ W₁ W₂ (by simp)

Depends on / 依赖: e.hom
-/
noncomputable def lift₂NatIso (e : F₁ ≅ F₂) : F₁' ≅ F₂' where
  hom := lift₂NatTrans L₁ L₂ W₁ W₂ F₁ F₂ F₁' F₂' e.hom
  inv := lift₂NatTrans L₁ L₂ W₁ W₂ F₂ F₁ F₂' F₁' e.inv
  hom_inv_id := natTrans₂_ext L₁ L₂ W₁ W₂ (by simp)
  inv_hom_id := natTrans₂_ext L₁ L₂ W₁ W₂ (by simp)

end

end Localization

end CategoryTheory
