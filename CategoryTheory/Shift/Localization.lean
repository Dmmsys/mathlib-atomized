/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.Induced
public import Mathlib.CategoryTheory.Localization.HasLocalization
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# The shift induced on a localized category

Let `C` be a category equipped with a shift by a monoid `A`. A morphism property `W`
on `C` satisfies `W.IsCompatibleWithShift A` when for all `a : A`,
a morphism `f` is in `W` iff `f⟦a⟧'` is. When this compatibility is satisfied,
then the corresponding localized category can be equipped with
a shift by `A`, and the localization functor is compatible with the shift.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃ w

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
  (A : Type w) [AddMonoid A] [HasShift C A]

namespace MorphismProperty

/--
Definition of `IsCompatibleWithShift` / `IsCompatibleWithShift` 的定义

English:
class IsCompatibleWithShift
  parameters: : Prop where
  axioms and operations (1):
    - condition : forall (a : A), W.inverseImage (shiftFunctor C a) = W

中文:
类 IsCompatibleWithShift
  参数: : 命题 where
  公理与运算 (1 个):
    - condition : 对任意 (a : A), W.inverseImage (shiftFunctor C a) = W
-/
class IsCompatibleWithShift : Prop where
  /-- the condition that for all `a : A`, the morphism property `W` is not changed when
  we take its inverse image by the shift functor by `a` -/
  condition : forall (a : A), W.inverseImage (shiftFunctor C a) = W

variable [W.IsCompatibleWithShift A]

namespace IsCompatibleWithShift

variable {A}

/--
lemma `iff` / 引理 `iff`

English:
lemma iff
  given: {X Y : C} (f : X ⟶ Y) (a : A)
  statement: W (f⟦a⟧') ↔ W f
  proof: by
  conv_rhs => rw [← @IsCompatibleWithShift.condition _ _ W A _ _ _ a]
  rfl

中文:
引理 iff
  条件: {X Y : C} (f : X ⟶ Y) (a : A)
  结论: W (f⟦a⟧') ↔ W f
  证明: by
  conv_rhs => rw [← @IsCompatibleWithShift.condition _ _ W A _ _ _ a]
  rfl

Depends on / 依赖: IsCompatibleWithShift, IsCompatibleWithShift.condition, condition, conv_rhs
-/
lemma iff {X Y : C} (f : X ⟶ Y) (a : A) : W (f⟦a⟧') ↔ W f := by
  conv_rhs => rw [← @IsCompatibleWithShift.condition _ _ W A _ _ _ a]
  rfl

/--
lemma `shiftFunctor_comp_inverts` / 引理 `shiftFunctor_comp_inverts`

English:
lemma shiftFunctor_comp_inverts
  given: (a : A)
  proof: fun _ _ f hf =>
  Localization.inverts L W _ (by simpa only [iff] using hf)

中文:
引理 shiftFunctor_comp_inverts
  条件: (a : A)
  证明: fun _ _ f hf =>
  Localization.inverts L W _ (by simpa only [iff] using hf)
-/
lemma shiftFunctor_comp_inverts (a : A) :
    W.IsInvertedBy (shiftFunctor C a ⋙ L) := fun _ _ f hf =>
  Localization.inverts L W _ (by simpa only [iff] using hf)

end IsCompatibleWithShift

variable {A} in
/--
lemma `shift` / 引理 `shift`

English:
lemma shift
  given: {X Y : C} {f : X ⟶ Y} (hf : W f) (a : A)
  statement: W (f⟦a⟧')
  proof: by
  simpa only [IsCompatibleWithShift.iff W f a] using hf

中文:
引理 shift
  条件: {X Y : C} {f : X ⟶ Y} (hf : W f) (a : A)
  结论: W (f⟦a⟧')
  证明: by
  simpa only [IsCompatibleWithShift.iff W f a] using hf

Depends on / 依赖: IsCompatibleWithShift, IsCompatibleWithShift.iff
-/
lemma shift {X Y : C} {f : X ⟶ Y} (hf : W f) (a : A) : W (f⟦a⟧') := by
  simpa only [IsCompatibleWithShift.iff W f a] using hf

variable {A} in
/--
Definition of `shiftLocalizerMorphism` / `shiftLocalizerMorphism` 的定义

English:
abbreviation shiftLocalizerMorphism
  signature: (a : A)
  body: shiftFunctor C a
  map := by rw [MorphismProperty.IsCompatibleWithShift.condition]

中文:
缩写 shiftLocalizerMorphism
  签名: (a : A)
  定义体: shiftFunctor C a
  map := by rw [MorphismProperty.IsCompatibleWithShift.condition]

Depends on / 依赖: shiftFunctor
-/
abbrev shiftLocalizerMorphism (a : A) : LocalizerMorphism W W where
  functor := shiftFunctor C a
  map := by rw [MorphismProperty.IsCompatibleWithShift.condition]

end MorphismProperty

section
variable [W.IsCompatibleWithShift A]

/-- When `L : C ⥤ D` is a localization functor with respect to a morphism property `W`
that is compatible with the shift by a monoid `A` on `C`, this is the induced
shift on the category `D`. -/
@[instance_reducible]
/--
Definition of `HasShift.localized` / `HasShift.localized` 的定义

English:
definition HasShift.localized
  signature: : HasShift D A
  body: have := Localization.full_whiskeringLeft L W D
  have := Localization.faithful_whiskeringLeft L W D
  HasShift.induced L A
    (fun a => Localization.lift (shiftFunctor C a ⋙ L)
      (MorphismProperty.IsCompatibleWithShift.shiftFunctor_comp_inverts L W a) L)
    (fun _ => Localization.fac _ _ _)

中文:
定义 HasShift.localized
  签名: : HasShift D A
  定义体: have := Localization.full_whiskeringLeft L W D
  have := Localization.faithful_whiskeringLeft L W D
  HasShift.induced L A
    (fun a => Localization.lift (shiftFunctor C a ⋙ L)
      (MorphismProperty.IsCompatibleWithShift.shiftFunctor_comp_inverts L W a) L)
    (fun _ => Localization.fac _ _ _)

Depends on / 依赖: HasShift, HasShift.induced, IsCompatibleWithShift, Localization, Localization.fac, Localization.faithful_whiskeringLeft, Localization.full_whiskeringLeft, Localization.lift, MorphismProperty, MorphismProperty.IsCompatibleWithShift.shiftFunctor_comp_inverts, faithful_whiskeringLeft, full_whiskeringLeft, induced, shiftFunctor, shiftFunctor_comp_inverts
-/
noncomputable def HasShift.localized : HasShift D A :=
  have := Localization.full_whiskeringLeft L W D
  have := Localization.faithful_whiskeringLeft L W D
  HasShift.induced L A
    (fun a => Localization.lift (shiftFunctor C a ⋙ L)
      (MorphismProperty.IsCompatibleWithShift.shiftFunctor_comp_inverts L W a) L)
    (fun _ => Localization.fac _ _ _)

/-- The localization functor `L : C ⥤ D` is compatible with the shift. -/
@[nolint unusedHavesSuffices, instance_reducible]
/--
Definition of `Functor.CommShift.localized` / `Functor.CommShift.localized` 的定义

English:
definition Functor.CommShift.localized
  signature: :
  body: have := Localization.full_whiskeringLeft L W D
  have := Localization.faithful_whiskeringLeft L W D
  Functor.CommShift.ofInduced _ _ _ _

中文:
定义 Functor.CommShift.localized
  签名: :
  定义体: have := Localization.full_whiskeringLeft L W D
  have := Localization.faithful_whiskeringLeft L W D
  Functor.CommShift.ofInduced _ _ _ _

Depends on / 依赖: CommShift, Functor, Functor.CommShift.ofInduced, Localization, Localization.faithful_whiskeringLeft, Localization.full_whiskeringLeft, faithful_whiskeringLeft, full_whiskeringLeft, ofInduced
-/
noncomputable def Functor.CommShift.localized :
    @Functor.CommShift _ _ _ _ L A _ _ (HasShift.localized L W A) :=
  have := Localization.full_whiskeringLeft L W D
  have := Localization.faithful_whiskeringLeft L W D
  Functor.CommShift.ofInduced _ _ _ _

attribute [irreducible] HasShift.localized Functor.CommShift.localized

/--
Instance `HasShift.localization` / 实例 `HasShift.localization`

English:
instance HasShift.localization
  signature: :
  body: HasShift.localized W.Q W A

中文:
实例 HasShift.localization
  签名: :
  定义体: HasShift.localized W.Q W A

Depends on / 依赖: HasShift, HasShift.localized, localized
-/
noncomputable instance HasShift.localization :
    HasShift W.Localization A :=
  HasShift.localized W.Q W A

/--
Instance `MorphismProperty.commShift_Q` / 实例 `MorphismProperty.commShift_Q`

English:
instance MorphismProperty.commShift_Q
  signature: :
  body: Functor.CommShift.localized W.Q W A

中文:
实例 MorphismProperty.commShift_Q
  签名: :
  定义体: Functor.CommShift.localized W.Q W A

Depends on / 依赖: CommShift, Functor, Functor.CommShift.localized, localized
-/
noncomputable instance MorphismProperty.commShift_Q :
    W.Q.CommShift A :=
  Functor.CommShift.localized W.Q W A

attribute [irreducible] HasShift.localization MorphismProperty.commShift_Q

variable [W.HasLocalization]

/--
Instance `HasShift.localization'` / 实例 `HasShift.localization'`

English:
instance HasShift.localization'
  signature: :
  body: HasShift.localized W.Q' W A

中文:
实例 HasShift.localization'
  签名: :
  定义体: HasShift.localized W.Q' W A

Depends on / 依赖: HasShift, HasShift.localized, localized
-/
noncomputable instance HasShift.localization' :
    HasShift W.Localization' A :=
  HasShift.localized W.Q' W A

/--
Instance `MorphismProperty.commShift_Q'` / 实例 `MorphismProperty.commShift_Q'`

English:
instance MorphismProperty.commShift_Q'
  signature: :
  body: Functor.CommShift.localized W.Q' W A

中文:
实例 MorphismProperty.commShift_Q'
  签名: :
  定义体: Functor.CommShift.localized W.Q' W A

Depends on / 依赖: CommShift, Functor, Functor.CommShift.localized, localized
-/
noncomputable instance MorphismProperty.commShift_Q' :
    W.Q'.CommShift A :=
  Functor.CommShift.localized W.Q' W A

attribute [irreducible] HasShift.localization' MorphismProperty.commShift_Q'

end

section

open Localization

variable (F : C ⥤ E) (F' : D ⥤ E) [Lifting L W F F']
  [HasShift D A] [HasShift E A] [L.CommShift A] [F.CommShift A]

namespace Functor

namespace commShiftOfLocalization

variable {A}

/--
Definition of `iso` / `iso` 的定义

English:
definition iso
  signature: (a : A)
  body: Localization.liftNatIso L W (L ⋙ shiftFunctor D a ⋙ F')
    (L ⋙ F' ⋙ shiftFunctor E a) _ _
      ((Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (L.commShiftIso a).symm F' ≪≫
        Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (Lifting.iso L W F F') ≪≫
        F.commShiftIso a 

中文:
定义 iso
  签名: (a : A)
  定义体: Localization.liftNatIso L W (L ⋙ shiftFunctor D a ⋙ F')
    (L ⋙ F' ⋙ shiftFunctor E a) _ _
      ((Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (L.commShiftIso a).symm F' ≪≫
        Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (Lifting.iso L W F F') ≪≫
        F.commShiftIso a 

Depends on / 依赖: F.commShiftIso, Functor, Functor.associator, L.commShiftIso, Lifting, Lifting.iso, Localization, Localization.liftNatIso, associator, commShiftIso, isoWhiskerLeft, isoWhiskerRight, liftNatIso, shiftFunctor
-/
noncomputable def iso (a : A) :
    shiftFunctor D a ⋙ F' ≅ F' ⋙ shiftFunctor E a :=
  Localization.liftNatIso L W (L ⋙ shiftFunctor D a ⋙ F')
    (L ⋙ F' ⋙ shiftFunctor E a) _ _
      ((Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (L.commShiftIso a).symm F' ≪≫
        Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (Lifting.iso L W F F') ≪≫
        F.commShiftIso a ≪≫
        isoWhiskerRight (Lifting.iso L W F F').symm _ ≪≫ Functor.associator _ _ _)

set_option backward.defeqAttrib.useBackward true in
@[simp, reassoc]
/--
lemma `iso_hom_app` / 引理 `iso_hom_app`

English:
lemma iso_hom_app
  given: (a : A) (X : C)
  proof: by
  simp [commShiftOfLocalization.iso]

中文:
引理 iso_hom_app
  条件: (a : A) (X : C)
  证明: by
  simp [commShiftOfLocalization.iso]

Depends on / 依赖: commShiftOfLocalization, commShiftOfLocalization.iso
-/
lemma iso_hom_app (a : A) (X : C) :
    (commShiftOfLocalization.iso L W F F' a).hom.app (L.obj X) =
      F'.map ((L.commShiftIso a).inv.app X) ≫
      (Lifting.iso L W F F').hom.app (X⟦a⟧) ≫
        (F.commShiftIso a).hom.app X ≫
          (shiftFunctor E a).map ((Lifting.iso L W F F').inv.app X) := by
  simp [commShiftOfLocalization.iso]

set_option backward.defeqAttrib.useBackward true in
@[simp, reassoc]
/--
lemma `iso_inv_app` / 引理 `iso_inv_app`

English:
lemma iso_inv_app
  given: (a : A) (X : C)
  proof: by
  simp [commShiftOfLocalization.iso]

中文:
引理 iso_inv_app
  条件: (a : A) (X : C)
  证明: by
  simp [commShiftOfLocalization.iso]

Depends on / 依赖: commShiftOfLocalization, commShiftOfLocalization.iso
-/
lemma iso_inv_app (a : A) (X : C) :
    (commShiftOfLocalization.iso L W F F' a).inv.app (L.obj X) =
      (shiftFunctor E a).map ((Lifting.iso L W F F').hom.app X) ≫
      (F.commShiftIso a).inv.app X ≫
      (Lifting.iso L W F F').inv.app (X⟦a⟧) ≫
      F'.map ((L.commShiftIso a).hom.app X) := by
  simp [commShiftOfLocalization.iso]

end commShiftOfLocalization

set_option backward.defeqAttrib.useBackward true in
/-- In the context of localization of categories, if a functor
is induced by a functor which commutes with the shift, then
this functor commutes with the shift. -/
@[instance_reducible]
/--
Definition of `commShiftOfLocalization` / `commShiftOfLocalization` 的定义

English:
definition commShiftOfLocalization
  signature: : F'.CommShift A where
  body: commShiftOfLocalization.iso L W F F'
  commShiftIso_zero := by
    ext1
    apply natTrans_ext L W
    intro X
    dsimp
    simp only [commShiftOfLocalization.iso_hom_app, comp_obj, commShiftIso_zero,
      CommShift.isoZero_inv_app, map_comp, CommShift.isoZero_hom_app, Category.assoc,
      ← NatT

中文:
定义 commShiftOfLocalization
  签名: : F'.CommShift A where
  定义体: commShiftOfLocalization.iso L W F F'
  commShiftIso_zero := by
    ext1
    apply natTrans_ext L W
    intro X
    dsimp
    simp only [commShiftOfLocalization.iso_hom_app, comp_obj, commShiftIso_zero,
      CommShift.isoZero_inv_app, map_comp, CommShift.isoZero_hom_app, Category.assoc,
      ← NatT

Depends on / 依赖: commShiftOfLocalization, commShiftOfLocalization.iso
-/
noncomputable def commShiftOfLocalization : F'.CommShift A where
  commShiftIso := commShiftOfLocalization.iso L W F F'
  commShiftIso_zero := by
    ext1
    apply natTrans_ext L W
    intro X
    dsimp
    simp only [commShiftOfLocalization.iso_hom_app, comp_obj, commShiftIso_zero,
      CommShift.isoZero_inv_app, map_comp, CommShift.isoZero_hom_app, Category.assoc,
      ← NatTrans.naturality_assoc, ← NatTrans.naturality]
    dsimp
    simp only [← Functor.map_comp_assoc, ← Functor.map_comp,
      Iso.inv_hom_id_app, id_obj, map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
  commShiftIso_add a b := by
    ext1
    apply natTrans_ext L W
    intro X
    dsimp
    simp only [commShiftOfLocalization.iso_hom_app, comp_obj, commShiftIso_add,
      CommShift.isoAdd_inv_app, map_comp, CommShift.isoAdd_hom_app, Category.assoc]
    congr 1
    rw [← cancel_epi (F'.map ((shiftFunctor D b).map ((L.commShiftIso a).hom.app X)))]; rw [← F'.map_comp_assoc]; rw [← map_comp]; rw [Iso.hom_inv_id_app]; rw [map_id]; rw [map_id]; rw [Category.id_comp]
    conv_lhs =>
      erw [← NatTrans.naturality_assoc]
      dsimp
      rw [← Functor.map_comp_assoc]; rw [← map_comp_assoc]; rw [Category.assoc]; rw [← map_comp]; rw [Iso.inv_hom_id_app]
      dsimp
      rw [map_id]; rw [Category.comp_id]; rw [← NatTrans.naturality]
      dsimp
    conv_rhs =>
      erw [← NatTrans.naturality_assoc]
      dsimp
      rw [← Functor.map_comp_assoc]; rw [← map_comp]; rw [Iso.hom_inv_id_app]
      dsimp
      rw [map_id]; rw [map_id]; rw [Category.id_comp]; rw [commShiftOfLocalization.iso_hom_app]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [← map_comp_assoc]; rw [Iso.inv_hom_id_app]; rw [map_id]; rw [Category.id_comp]

variable {A}

/--
lemma `commShiftOfLocalization_iso_hom_app` / 引理 `commShiftOfLocalization_iso_hom_app`

English:
lemma commShiftOfLocalization_iso_hom_app
  given: (a : A) (X : C)
  proof: Functor.commShiftOfLocalization L W A F F'
    (F'.commShiftIso a).hom.app (L.obj X) =
      F'.map ((L.commShiftIso a).inv.app X) ≫ (Lifting.iso L W F F').hom.app (X⟦a⟧) ≫
        (F.commShiftIso a).hom.app X ≫
          (shiftFunctor E a).map ((Lifting.iso L W F F').inv.app X) := by
  apply commSh

中文:
引理 commShiftOfLocalization_iso_hom_app
  条件: (a : A) (X : C)
  证明: Functor.commShiftOfLocalization L W A F F'
    (F'.commShiftIso a).hom.app (L.obj X) =
      F'.map ((L.commShiftIso a).inv.app X) ≫ (Lifting.iso L W F F').hom.app (X⟦a⟧) ≫
        (F.commShiftIso a).hom.app X ≫
          (shiftFunctor E a).map ((Lifting.iso L W F F').inv.app X) := by
  apply commSh

Depends on / 依赖: Functor, Functor.commShiftOfLocalization, commShiftOfLocalization
-/
lemma commShiftOfLocalization_iso_hom_app (a : A) (X : C) :
    letI := Functor.commShiftOfLocalization L W A F F'
    (F'.commShiftIso a).hom.app (L.obj X) =
      F'.map ((L.commShiftIso a).inv.app X) ≫ (Lifting.iso L W F F').hom.app (X⟦a⟧) ≫
        (F.commShiftIso a).hom.app X ≫
          (shiftFunctor E a).map ((Lifting.iso L W F F').inv.app X) := by
  apply commShiftOfLocalization.iso_hom_app

/--
lemma `commShiftOfLocalization_iso_inv_app` / 引理 `commShiftOfLocalization_iso_inv_app`

English:
lemma commShiftOfLocalization_iso_inv_app
  given: (a : A) (X : C)
  proof: Functor.commShiftOfLocalization L W A F F'
    (F'.commShiftIso a).inv.app (L.obj X) =
      (shiftFunctor E a).map ((Lifting.iso L W F F').hom.app X) ≫
      (F.commShiftIso a).inv.app X ≫ (Lifting.iso L W F F').inv.app (X⟦a⟧) ≫
      F'.map ((L.commShiftIso a).hom.app X) := by
  apply commShiftOfL

中文:
引理 commShiftOfLocalization_iso_inv_app
  条件: (a : A) (X : C)
  证明: Functor.commShiftOfLocalization L W A F F'
    (F'.commShiftIso a).inv.app (L.obj X) =
      (shiftFunctor E a).map ((Lifting.iso L W F F').hom.app X) ≫
      (F.commShiftIso a).inv.app X ≫ (Lifting.iso L W F F').inv.app (X⟦a⟧) ≫
      F'.map ((L.commShiftIso a).hom.app X) := by
  apply commShiftOfL

Depends on / 依赖: Functor, Functor.commShiftOfLocalization, commShiftOfLocalization
-/
lemma commShiftOfLocalization_iso_inv_app (a : A) (X : C) :
    letI := Functor.commShiftOfLocalization L W A F F'
    (F'.commShiftIso a).inv.app (L.obj X) =
      (shiftFunctor E a).map ((Lifting.iso L W F F').hom.app X) ≫
      (F.commShiftIso a).inv.app X ≫ (Lifting.iso L W F F').inv.app (X⟦a⟧) ≫
      F'.map ((L.commShiftIso a).hom.app X) := by
  apply commShiftOfLocalization.iso_inv_app

end Functor

set_option backward.defeqAttrib.useBackward true in
/--
Instance `NatTrans.commShift_iso_hom_of_localization` / 实例 `NatTrans.commShift_iso_hom_of_localization`

English:
instance NatTrans.commShift_iso_hom_of_localization
  signature: :
  body: Functor.commShiftOfLocalization L W A F F'
    NatTrans.CommShift (Lifting.iso L W F F').hom A := by
  let := Functor.commShiftOfLocalization L W A F F'
  constructor
  intro a
  ext X
  simp only [comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app,
  

中文:
实例 NatTrans.commShift_iso_hom_of_localization
  签名: :
  定义体: Functor.commShiftOfLocalization L W A F F'
    NatTrans.CommShift (Lifting.iso L W F F').hom A := by
  let := Functor.commShiftOfLocalization L W A F F'
  constructor
  intro a
  ext X
  simp only [comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app,
  

Depends on / 依赖: Functor, Functor.commShiftOfLocalization, commShiftOfLocalization
-/
instance NatTrans.commShift_iso_hom_of_localization :
    letI := Functor.commShiftOfLocalization L W A F F'
    NatTrans.CommShift (Lifting.iso L W F F').hom A := by
  let := Functor.commShiftOfLocalization L W A F F'
  constructor
  intro a
  ext X
  simp only [comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app,
    Functor.commShiftOfLocalization_iso_hom_app,
    Category.assoc, ← Functor.map_comp, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, Functor.map_id, Iso.inv_hom_id_app,
    Category.comp_id, Category.id_comp, Functor.comp_obj]

end

namespace LocalizerMorphism

open Localization

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂} (Φ : LocalizerMorphism W₁ W₂)
  {M : Type*} [AddMonoid M] [HasShift C₁ M] [HasShift C₂ M]
  [Φ.functor.CommShift M]
  {D₁ D₂ : Type*} [Category* D₁] [Category* D₂]
  (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁] (L₂ : C₂ ⥤ D₂)
  [HasShift D₁ M] [HasShift D₂ M] [L₁.CommShift M] [L₂.CommShift M]

section

variable (G : D₁ ⥤ D₂) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G)

variable (M) in
/-- This is the commutation of a functor `G` to shifts by an additive monoid `M` when
`e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G` is an isomorphism, `Φ` is a localizer morphism and
`L₁` is a localization functor. We assume that all categories involved
are equipped with shifts and that `L₁`, `L₂` and `Φ.functor` commute to them. -/
@[instance_reducible]
/--
Definition of `commShift` / `commShift` 的定义

English:
definition commShift
  signature: : G.CommShift M
  body: by
  letI : Localization.Lifting L₁ W₁ (Φ.functor ⋙ L₂) G := ⟨e.symm⟩
  exact Functor.commShiftOfLocalization L₁ W₁ M (Φ.functor ⋙ L₂) G

中文:
定义 commShift
  签名: : G.CommShift M
  定义体: by
  letI : Localization.Lifting L₁ W₁ (Φ.functor ⋙ L₂) G := ⟨e.symm⟩
  exact Functor.commShiftOfLocalization L₁ W₁ M (Φ.functor ⋙ L₂) G

Depends on / 依赖: Functor, Functor.commShiftOfLocalization, Lifting, Localization, Localization.Lifting, commShiftOfLocalization, e.symm, functor
-/
noncomputable def commShift : G.CommShift M := by
  letI : Localization.Lifting L₁ W₁ (Φ.functor ⋙ L₂) G := ⟨e.symm⟩
  exact Functor.commShiftOfLocalization L₁ W₁ M (Φ.functor ⋙ L₂) G

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `commShift_iso_hom_app` / 引理 `commShift_iso_hom_app`

English:
lemma commShift_iso_hom_app
  given: (m : M) (X : C₁)
  proof: Φ.commShift M L₁ L₂ G e
    (G.commShiftIso m).hom.app (L₁.obj X) =
      G.map ((L₁.commShiftIso m).inv.app X) ≫ e.inv.app _ ≫
        L₂.map ((Φ.functor.commShiftIso m).hom.app X) ≫
        (L₂.commShiftIso m).hom.app _ ≫ (e.hom.app X)⟦m⟧' := by
  simp [Functor.commShiftOfLocalization_iso_hom_app,

中文:
引理 commShift_iso_hom_app
  条件: (m : M) (X : C₁)
  证明: Φ.commShift M L₁ L₂ G e
    (G.commShiftIso m).hom.app (L₁.obj X) =
      G.map ((L₁.commShiftIso m).inv.app X) ≫ e.inv.app _ ≫
        L₂.map ((Φ.functor.commShiftIso m).hom.app X) ≫
        (L₂.commShiftIso m).hom.app _ ≫ (e.hom.app X)⟦m⟧' := by
  simp [Functor.commShiftOfLocalization_iso_hom_app,

Depends on / 依赖: commShift
-/
lemma commShift_iso_hom_app (m : M) (X : C₁) :
    letI := Φ.commShift M L₁ L₂ G e
    (G.commShiftIso m).hom.app (L₁.obj X) =
      G.map ((L₁.commShiftIso m).inv.app X) ≫ e.inv.app _ ≫
        L₂.map ((Φ.functor.commShiftIso m).hom.app X) ≫
        (L₂.commShiftIso m).hom.app _ ≫ (e.hom.app X)⟦m⟧' := by
  simp [Functor.commShiftOfLocalization_iso_hom_app,
    Functor.commShiftIso_comp_hom_app]

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `commShift_iso_inv_app` / 引理 `commShift_iso_inv_app`

English:
lemma commShift_iso_inv_app
  given: (m : M) (X : C₁)
  proof: Φ.commShift M L₁ L₂ G e
    (G.commShiftIso m).inv.app (L₁.obj X) =
      (e.inv.app X)⟦m⟧' ≫ (L₂.commShiftIso m).inv.app _ ≫
        L₂.map ((Φ.functor.commShiftIso m).inv.app X) ≫ e.hom.app _ ≫
          G.map ((L₁.commShiftIso m).hom.app X) := by
  simp [Functor.commShiftOfLocalization_iso_inv_ap

中文:
引理 commShift_iso_inv_app
  条件: (m : M) (X : C₁)
  证明: Φ.commShift M L₁ L₂ G e
    (G.commShiftIso m).inv.app (L₁.obj X) =
      (e.inv.app X)⟦m⟧' ≫ (L₂.commShiftIso m).inv.app _ ≫
        L₂.map ((Φ.functor.commShiftIso m).inv.app X) ≫ e.hom.app _ ≫
          G.map ((L₁.commShiftIso m).hom.app X) := by
  simp [Functor.commShiftOfLocalization_iso_inv_ap

Depends on / 依赖: commShift
-/
lemma commShift_iso_inv_app (m : M) (X : C₁) :
    letI := Φ.commShift M L₁ L₂ G e
    (G.commShiftIso m).inv.app (L₁.obj X) =
      (e.inv.app X)⟦m⟧' ≫ (L₂.commShiftIso m).inv.app _ ≫
        L₂.map ((Φ.functor.commShiftIso m).inv.app X) ≫ e.hom.app _ ≫
          G.map ((L₁.commShiftIso m).hom.app X) := by
  simp [Functor.commShiftOfLocalization_iso_inv_app,
    Functor.commShiftIso_comp_inv_app]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `natTransCommShift_hom` / 引理 `natTransCommShift_hom`

English:
lemma natTransCommShift_hom
  proof: Φ.commShift M L₁ L₂ G e
    NatTrans.CommShift e.hom M := by
  let := Φ.commShift M L₁ L₂ G e
  refine ⟨fun m => ?_⟩
  ext X
  simp [Functor.commShiftIso_comp_hom_app, commShift_iso_hom_app, ← Functor.map_comp_assoc]

中文:
引理 natTransCommShift_hom
  证明: Φ.commShift M L₁ L₂ G e
    NatTrans.CommShift e.hom M := by
  let := Φ.commShift M L₁ L₂ G e
  refine ⟨fun m => ?_⟩
  ext X
  simp [Functor.commShiftIso_comp_hom_app, commShift_iso_hom_app, ← Functor.map_comp_assoc]

Depends on / 依赖: commShift
-/
lemma natTransCommShift_hom :
    letI := Φ.commShift M L₁ L₂ G e
    NatTrans.CommShift e.hom M := by
  let := Φ.commShift M L₁ L₂ G e
  refine ⟨fun m => ?_⟩
  ext X
  simp [Functor.commShiftIso_comp_hom_app, commShift_iso_hom_app, ← Functor.map_comp_assoc]

end

variable [W₁.IsCompatibleWithShift M] [W₂.IsCompatibleWithShift M]
  [L₂.IsLocalization W₂]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Φ.localizedFunctor L₁ L₂).CommShift M
  body: Φ.commShift M L₁ L₂ _ (CatCommSq.iso ..)

中文:
实例 :
  签名: (Φ.localizedFunctor L₁ L₂).CommShift M
  定义体: Φ.commShift M L₁ L₂ _ (CatCommSq.iso ..)

Depends on / 依赖: CatCommSq, CatCommSq.iso, commShift
-/
noncomputable instance : (Φ.localizedFunctor L₁ L₂).CommShift M :=
  Φ.commShift M L₁ L₂ _ (CatCommSq.iso ..)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: natTransCommShift_hom ..

中文:
实例 :
  定义体: natTransCommShift_hom ..

Depends on / 依赖: natTransCommShift_hom
-/
instance :
    NatTrans.CommShift (CatCommSq.iso Φ.functor W₁.Q W₂.Q
      (Φ.localizedFunctor W₁.Q W₂.Q)).hom M :=
  natTransCommShift_hom ..

end LocalizerMorphism

end CategoryTheory
