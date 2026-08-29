/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Localization.StructuredArrow

/-!
# Pointwise right derived functors

We define pointwise right derived functors using the notion
of pointwise left Kan extensions.

We show that if `F : C ⥤ H` inverts `W : MorphismProperty C`,
then it has a pointwise right derived functor.

Note: the file `Mathlib/CategoryTheory/Functor/Derived/PointwiseLeftDerived.lean` was obtained
by dualizing this file. These two files should be kept in sync.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C : Type u₁} {D : Type u₂} {H : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} H]
  (F' : D ⥤ H) (F : C ⥤ H) (L : C ⥤ D) (α : F ⟶ L ⋙ F') (W : MorphismProperty C)

/--
Definition of `HasPointwiseRightDerivedFunctorAt` / `HasPointwiseRightDerivedFunctorAt` 的定义

English:
class HasPointwiseRightDerivedFunctorAt
  parameters: (X : C)
  axioms and operations (1):
    - hasColimit' : HasPointwiseLeftKanExtensionAt W.Q F (W.Q.obj X)

中文:
类 有PointwiseRightDerivedFunctorAt
  参数: (X : C)
  公理与运算 (1 个):
    - hasColimit' : HasPointwiseLeftKanExtensionAt W.Q F (W.Q.obj X)

Depends on / 依赖: HasFiniteLimits, hasFiniteProducts_of_hasFiniteLimits
-/
class HasPointwiseRightDerivedFunctorAt (X : C) : Prop where
  /-- Use the more general `hasColimit` lemma instead, see also
  `hasPointwiseRightDerivedFunctorAt_iff` -/
  hasColimit' : HasPointwiseLeftKanExtensionAt W.Q F (W.Q.obj X)

/--
Definition of `HasPointwiseRightDerivedFunctor` / `HasPointwiseRightDerivedFunctor` 的定义

English:
abbreviation HasPointwiseRightDerivedFunctor
  body: forall (X : C), F.HasPointwiseRightDerivedFunctorAt W X

中文:
缩写 HasPointwiseRightDerivedFunctor
  定义体: forall (X : C), F.HasPointwiseRightDerivedFunctorAt W X

Depends on / 依赖: F.HasPointwiseRightDerivedFunctorAt, HasPointwiseRightDerivedFunctorAt
-/
abbrev HasPointwiseRightDerivedFunctor := forall (X : C), F.HasPointwiseRightDerivedFunctorAt W X

/--
lemma `hasPointwiseRightDerivedFunctorAt_iff` / 引理 `hasPointwiseRightDerivedFunctorAt_iff`

English:
lemma hasPointwiseRightDerivedFunctorAt_iff
  given: [L.IsLocalization W] (X : C)
  proof: by
  rw [← hasPointwiseLeftKanExtensionAt_iff_of_equivalence W.Q L F
    (Localization.uniq W.Q L W) (Localization.compUniqFunctor W.Q L W) (W.Q.obj X) (L.obj X)
    ((Localization.compUniqFunctor W.Q L W).app X)]
  exact ⟨fun h => h.hasColimit', fun h => ⟨h⟩⟩

中文:
引理 hasPointwiseRightDerivedFunctorAt_iff
  条件: [L.是Localization W] (X : C)
  证明: by
  rw [← hasPointwiseLeftKanExtensionAt_iff_of_equivalence W.Q L F
    (Localization.uniq W.Q L W) (Localization.compUniqFunctor W.Q L W) (W.Q.obj X) (L.obj X)
    ((Localization.compUniqFunctor W.Q L W).app X)]
  exact ⟨fun h => h.hasColimit', fun h => ⟨h⟩⟩

Depends on / 依赖: L.obj, Localization, Localization.compUniqFunctor, Localization.uniq, W.Q.obj, compUniqFunctor, h.hasColimit, hasColimit, hasPointwiseLeftKanExtensionAt_iff_of_equivalence
-/
lemma hasPointwiseRightDerivedFunctorAt_iff [L.IsLocalization W] (X : C) :
    F.HasPointwiseRightDerivedFunctorAt W X ↔
      HasPointwiseLeftKanExtensionAt L F (L.obj X) := by
  rw [← hasPointwiseLeftKanExtensionAt_iff_of_equivalence W.Q L F
    (Localization.uniq W.Q L W) (Localization.compUniqFunctor W.Q L W) (W.Q.obj X) (L.obj X)
    ((Localization.compUniqFunctor W.Q L W).app X)]
  exact ⟨fun h => h.hasColimit', fun h => ⟨h⟩⟩

/--
lemma `HasPointwiseRightDerivedFunctorAt.hasColimit` / 引理 `HasPointwiseRightDerivedFunctorAt.hasColimit`

English:
lemma HasPointwiseRightDerivedFunctorAt.hasColimit
  proof: by
  rwa [← hasPointwiseRightDerivedFunctorAt_iff F L W]

中文:
引理 有PointwiseRightDerivedFunctorAt.hasColimit
  证明: by
  rwa [← hasPointwiseRightDerivedFunctorAt_iff F L W]

Depends on / 依赖: hasPointwiseRightDerivedFunctorAt_iff
-/
lemma HasPointwiseRightDerivedFunctorAt.hasColimit
    [L.IsLocalization W] (X : C) [F.HasPointwiseRightDerivedFunctorAt W X] :
    HasPointwiseLeftKanExtensionAt L F (L.obj X) := by
  rwa [← hasPointwiseRightDerivedFunctorAt_iff F L W]

/--
lemma `hasPointwiseRightDerivedFunctorAt_iff_of_mem` / 引理 `hasPointwiseRightDerivedFunctorAt_iff_of_mem`

English:
lemma hasPointwiseRightDerivedFunctorAt_iff_of_mem
  given: {X Y : C} (w : X ⟶ Y) (hw : W w)
  proof: by
  simp only [F.hasPointwiseRightDerivedFunctorAt_iff W.Q W]
  exact hasPointwiseLeftKanExtensionAt_iff_of_iso W.Q F (Localization.isoOfHom W.Q W w hw)

中文:
引理 hasPointwiseRightDerivedFunctorAt_iff_of_mem
  条件: {X Y : C} (w : X ⟶ Y) (hw : W w)
  证明: by
  simp only [F.hasPointwiseRightDerivedFunctorAt_iff W.Q W]
  exact hasPointwiseLeftKanExtensionAt_iff_of_iso W.Q F (Localization.isoOfHom W.Q W w hw)

Depends on / 依赖: F.hasPointwiseRightDerivedFunctorAt_iff, HasFiniteColimits, Localization, Localization.isoOfHom, hasFiniteCoproducts_of_hasFiniteColimits, hasPointwiseLeftKanExtensionAt_iff_of_iso, hasPointwiseRightDerivedFunctorAt_iff, isoOfHom
-/
lemma hasPointwiseRightDerivedFunctorAt_iff_of_mem {X Y : C} (w : X ⟶ Y) (hw : W w) :
    F.HasPointwiseRightDerivedFunctorAt W X ↔
      F.HasPointwiseRightDerivedFunctorAt W Y := by
  simp only [F.hasPointwiseRightDerivedFunctorAt_iff W.Q W]
  exact hasPointwiseLeftKanExtensionAt_iff_of_iso W.Q F (Localization.isoOfHom W.Q W w hw)

section

variable [F.HasPointwiseRightDerivedFunctor W]

/--
lemma `hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor` / 引理 `hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor`

English:
lemma hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor
  given: [L.IsLocalization W]
  proof: fun Y => by
  have := Localization.essSurj L W
  rw [← hasPointwiseLeftKanExtensionAt_iff_of_iso _ F (L.objObjPreimageIso Y)]; rw [← F.hasPointwiseRightDerivedFunctorAt_iff L W]
  infer_instance

中文:
引理 hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor
  条件: [L.是Localization W]
  证明: fun Y => by
  have := Localization.essSurj L W
  rw [← hasPointwiseLeftKanExtensionAt_iff_of_iso _ F (L.objObjPreimageIso Y)]; rw [← F.hasPointwiseRightDerivedFunctorAt_iff L W]
  infer_instance

Depends on / 依赖: F.hasPointwiseRightDerivedFunctorAt_iff, L.objObjPreimageIso, Localization, Localization.essSurj, essSurj, hasPointwiseLeftKanExtensionAt_iff_of_iso, hasPointwiseRightDerivedFunctorAt_iff, infer_instance, objObjPreimageIso
-/
lemma hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor [L.IsLocalization W] :
    HasPointwiseLeftKanExtension L F := fun Y => by
  have := Localization.essSurj L W
  rw [← hasPointwiseLeftKanExtensionAt_iff_of_iso _ F (L.objObjPreimageIso Y)]; rw [← F.hasPointwiseRightDerivedFunctorAt_iff L W]
  infer_instance

/--
lemma `hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor` / 引理 `hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor`

English:
lemma hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor
  proof: by
    have := F.hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor W.Q W
    infer_instance

中文:
引理 hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor
  证明: by
    have := F.hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor W.Q W
    infer_instance

Depends on / 依赖: F.hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor, hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor, infer_instance
-/
lemma hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor :
    F.HasRightDerivedFunctor W where
  hasLeftKanExtension' := by
    have := F.hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor W.Q W
    infer_instance

attribute [instance] hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor

variable {F L}

/--
Definition of `isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor` / `isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor` 的定义

English:
definition isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor
  body: have := hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor F L
  have := IsRightDerivedFunctor.isLeftKanExtension F' α W
  isPointwiseLeftKanExtensionOfIsLeftKanExtension F' α

中文:
定义 isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor
  定义体: have := hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor F L
  have := IsRightDerivedFunctor.isLeftKanExtension F' α W
  isPointwiseLeftKanExtensionOfIsLeftKanExtension F' α

Depends on / 依赖: IsRightDerivedFunctor, IsRightDerivedFunctor.isLeftKanExtension, hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor, isLeftKanExtension, isPointwiseLeftKanExtensionOfIsLeftKanExtension
-/
noncomputable def isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor
     [L.IsLocalization W] [F'.IsRightDerivedFunctor α W] :
    (LeftExtension.mk _ α).IsPointwiseLeftKanExtension :=
  have := hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor F L
  have := IsRightDerivedFunctor.isLeftKanExtension F' α W
  isPointwiseLeftKanExtensionOfIsLeftKanExtension F' α

end

section

variable {F L}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isPointwiseLeftKanExtensionAtOfIsoOfIsLocalization` / `isPointwiseLeftKanExtensionAtOfIsoOfIsLocalization` 的定义

English:
definition isPointwiseLeftKanExtensionAtOfIsoOfIsLocalization
  body: e.inv.app Y ≫ s.ι.app (CostructuredArrow.mk (𝟙 (L.obj Y)))
  fac s j := by
    refine Localization.induction_costructuredArrow L W _ (by simp)
      (fun X₁ X₂ f φ hφ => ?_) (fun X₁ X₂ w hw φ hφ => ?_) j
    · have eq := s.ι.naturality
        (CostructuredArrow.homMk f : CostructuredArrow.mk (L.map f ≫ φ) ⟶ CostructuredArrow.mk φ)
      dsimp at eq hφ ⊢
      rw [comp_id] at eq
      rw [assoc] at hφ
      rw [assoc]; rw [map_comp_assoc]; rw [← eq]; rw [← hφ]; rw [NatTrans.naturality_assoc]; rw [comp_map]
    · have : IsIso (F.map w) := by
        have := Localization.inverts L W w hw
        rw [← NatIso.naturality_2 e w]
        dsimp
        infer_instance
      have eq := s.ι.naturality
        (CostructuredArrow.homMk w : CostructuredArrow.mk φ ⟶ CostructuredArrow.mk
          ((Localization.isoOfHom L W w hw).inv ≫ φ))
      dsimp at eq hφ ⊢
      rw [comp_id] at eq
      rw [assoc] at hφ
      rw [map_comp]; rw [assoc]; rw [assoc]; rw [← cancel_epi (F.map w)]; rw [eq]; rw [← hφ]; rw [NatTrans.naturality_assoc]; rw [comp_map]; rw [← G.map_comp_assoc]
      simp
  uniq s m hm := by
    have := hm (CostructuredArrow.mk (𝟙 (L.obj Y)))
    dsimp at this m hm ⊢
    simp only [← this, map_id, comp_id, Iso.inv_hom_id_app_assoc]

中文:
定义 isPointwiseLeftKanExtensionAtOfIsoOfIsLocalization
  定义体: e.inv.app Y ≫ s.ι.app (CostructuredArrow.mk (𝟙 (L.obj Y)))
  fac s j := by
    refine Localization.induction_costructuredArrow L W _ (by simp)
      (fun X₁ X₂ f φ hφ => ?_) (fun X₁ X₂ w hw φ hφ => ?_) j
    · have eq := s.ι.naturality
        (CostructuredArrow.homMk f : CostructuredArrow.mk (L.map f ≫ φ) ⟶ CostructuredArrow.mk φ)
      dsimp at eq hφ ⊢
      rw [comp_id] at eq
      rw [assoc] at hφ
      rw [assoc]; rw [map_comp_assoc]; rw [← eq]; rw [← hφ]; rw [NatTrans.naturality_assoc]; rw [comp_map]
    · have : IsIso (F.map w) := by
        have := Localization.inverts L W w hw
        rw [← NatIso.naturality_2 e w]
        dsimp
        infer_instance
      have eq := s.ι.naturality
        (CostructuredArrow.homMk w : CostructuredArrow.mk φ ⟶ CostructuredArrow.mk
          ((Localization.isoOfHom L W w hw).inv ≫ φ))
      dsimp at eq hφ ⊢
      rw [comp_id] at eq
      rw [assoc] at hφ
      rw [map_comp]; rw [assoc]; rw [assoc]; rw [← cancel_epi (F.map w)]; rw [eq]; rw [← hφ]; rw [NatTrans.naturality_assoc]; rw [comp_map]; rw [← G.map_comp_assoc]
      simp
  uniq s m hm := by
    have := hm (CostructuredArrow.mk (𝟙 (L.obj Y)))
    dsimp at this m hm ⊢
    simp only [← this, map_id, comp_id, Iso.inv_hom_id_app_assoc]

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk, L.obj, e.inv.app
-/
def isPointwiseLeftKanExtensionAtOfIsoOfIsLocalization
    {G : D ⥤ H} (e : F ≅ L ⋙ G) [L.IsLocalization W] (Y : C) :
    (LeftExtension.mk _ e.hom).IsPointwiseLeftKanExtensionAt (L.obj Y) where
  desc s := e.inv.app Y ≫ s.ι.app (CostructuredArrow.mk (𝟙 (L.obj Y)))
  fac s j := by
    refine Localization.induction_costructuredArrow L W _ (by simp)
      (fun X₁ X₂ f φ hφ => ?_) (fun X₁ X₂ w hw φ hφ => ?_) j
    · have eq := s.ι.naturality
        (CostructuredArrow.homMk f : CostructuredArrow.mk (L.map f ≫ φ) ⟶ CostructuredArrow.mk φ)
      dsimp at eq hφ ⊢
      rw [comp_id] at eq
      rw [assoc] at hφ
      rw [assoc]; rw [map_comp_assoc]; rw [← eq]; rw [← hφ]; rw [NatTrans.naturality_assoc]; rw [comp_map]
    · have : IsIso (F.map w) := by
        have := Localization.inverts L W w hw
        rw [← NatIso.naturality_2 e w]
        dsimp
        infer_instance
      have eq := s.ι.naturality
        (CostructuredArrow.homMk w : CostructuredArrow.mk φ ⟶ CostructuredArrow.mk
          ((Localization.isoOfHom L W w hw).inv ≫ φ))
      dsimp at eq hφ ⊢
      rw [comp_id] at eq
      rw [assoc] at hφ
      rw [map_comp]; rw [assoc]; rw [assoc]; rw [← cancel_epi (F.map w)]; rw [eq]; rw [← hφ]; rw [NatTrans.naturality_assoc]; rw [comp_map]; rw [← G.map_comp_assoc]
      simp
  uniq s m hm := by
    have := hm (CostructuredArrow.mk (𝟙 (L.obj Y)))
    dsimp at this m hm ⊢
    simp only [← this, map_id, comp_id, Iso.inv_hom_id_app_assoc]

/--
Definition of `isPointwiseLeftKanExtensionOfIsoOfIsLocalization` / `isPointwiseLeftKanExtensionOfIsoOfIsLocalization` 的定义

English:
definition isPointwiseLeftKanExtensionOfIsoOfIsLocalization
  body: fun Y =>
  have := Localization.essSurj L W
  (LeftExtension.mk _ e.hom).isPointwiseLeftKanExtensionAtEquivOfIso'
    (L.objObjPreimageIso Y) (isPointwiseLeftKanExtensionAtOfIsoOfIsLocalization W e _)

中文:
定义 isPointwiseLeftKanExtensionOfIsoOfIsLocalization
  定义体: fun Y =>
  have := Localization.essSurj L W
  (LeftExtension.mk _ e.hom).isPointwiseLeftKanExtensionAtEquivOfIso'
    (L.objObjPreimageIso Y) (isPointwiseLeftKanExtensionAtOfIsoOfIsLocalization W e _)
-/
noncomputable def isPointwiseLeftKanExtensionOfIsoOfIsLocalization
    {G : D ⥤ H} (e : F ≅ L ⋙ G) [L.IsLocalization W] :
    (LeftExtension.mk _ e.hom).IsPointwiseLeftKanExtension := fun Y =>
  have := Localization.essSurj L W
  (LeftExtension.mk _ e.hom).isPointwiseLeftKanExtensionAtEquivOfIso'
    (L.objObjPreimageIso Y) (isPointwiseLeftKanExtensionAtOfIsoOfIsLocalization W e _)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `LeftExtension.isPointwiseLeftKanExtensionOfIsIsoOfIsLocalization` / `LeftExtension.isPointwiseLeftKanExtensionOfIsIsoOfIsLocalization` 的定义

English:
definition LeftExtension.isPointwiseLeftKanExtensionOfIsIsoOfIsLocalization
  body: Functor.isPointwiseLeftKanExtensionOfIsoOfIsLocalization W (asIso E.hom)

中文:
定义 LeftExtension.isPointwiseLeftKanExtensionOfIsIsoOfIsLocalization
  定义体: Functor.isPointwiseLeftKanExtensionOfIsoOfIsLocalization W (asIso E.hom)

Depends on / 依赖: E.hom, Functor, Functor.isPointwiseLeftKanExtensionOfIsoOfIsLocalization, isPointwiseLeftKanExtensionOfIsoOfIsLocalization
-/
noncomputable def LeftExtension.isPointwiseLeftKanExtensionOfIsIsoOfIsLocalization
    (E : LeftExtension L F) [IsIso E.hom] [L.IsLocalization W] :
    E.IsPointwiseLeftKanExtension :=
  Functor.isPointwiseLeftKanExtensionOfIsoOfIsLocalization W (asIso E.hom)

/--
lemma `hasPointwiseRightDerivedFunctor_of_inverts` / 引理 `hasPointwiseRightDerivedFunctor_of_inverts`

English:
lemma hasPointwiseRightDerivedFunctor_of_inverts
  proof: by
  intro X
  rw [hasPointwiseRightDerivedFunctorAt_iff F W.Q W]
  exact (isPointwiseLeftKanExtensionOfIsoOfIsLocalization W
    (Localization.fac F hF W.Q).symm).hasPointwiseLeftKanExtension _

中文:
引理 hasPointwiseRightDerivedFunctor_of_inverts
  证明: by
  intro X
  rw [hasPointwiseRightDerivedFunctorAt_iff F W.Q W]
  exact (isPointwiseLeftKanExtensionOfIsoOfIsLocalization W
    (Localization.fac F hF W.Q).symm).hasPointwiseLeftKanExtension _

Depends on / 依赖: Localization, Localization.fac, hasPointwiseLeftKanExtension, hasPointwiseRightDerivedFunctorAt_iff, isPointwiseLeftKanExtensionOfIsoOfIsLocalization
-/
lemma hasPointwiseRightDerivedFunctor_of_inverts
    (F : C ⥤ H) {W : MorphismProperty C} (hF : W.IsInvertedBy F) :
    F.HasPointwiseRightDerivedFunctor W := by
  intro X
  rw [hasPointwiseRightDerivedFunctorAt_iff F W.Q W]
  exact (isPointwiseLeftKanExtensionOfIsoOfIsLocalization W
    (Localization.fac F hF W.Q).symm).hasPointwiseLeftKanExtension _

/--
lemma `isRightDerivedFunctor_of_inverts` / 引理 `isRightDerivedFunctor_of_inverts`

English:
lemma isRightDerivedFunctor_of_inverts
  proof: (isPointwiseLeftKanExtensionOfIsoOfIsLocalization W e.symm).isLeftKanExtension

中文:
引理 isRightDerivedFunctor_of_inverts
  证明: (isPointwiseLeftKanExtensionOfIsoOfIsLocalization W e.symm).isLeftKanExtension

Depends on / 依赖: e.symm, isLeftKanExtension, isPointwiseLeftKanExtensionOfIsoOfIsLocalization
-/
lemma isRightDerivedFunctor_of_inverts
    [L.IsLocalization W] (F' : D ⥤ H) (e : L ⋙ F' ≅ F) :
    F'.IsRightDerivedFunctor e.inv W where
  isLeftKanExtension :=
    (isPointwiseLeftKanExtensionOfIsoOfIsLocalization W e.symm).isLeftKanExtension

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [L.IsLocalization
  signature: W] (hF
  body: isRightDerivedFunctor_of_inverts W _ _

中文:
实例 [L.是Localization
  签名: W] (hF
  定义体: isRightDerivedFunctor_of_inverts W _ _

Depends on / 依赖: isRightDerivedFunctor_of_inverts
-/
instance [L.IsLocalization W] (hF : W.IsInvertedBy F) :
    (Localization.lift F hF L).IsRightDerivedFunctor (Localization.fac F hF L).inv W :=
  isRightDerivedFunctor_of_inverts W _ _

variable {W} in
/--
lemma `isIso_of_isRightDerivedFunctor_of_inverts` / 引理 `isIso_of_isRightDerivedFunctor_of_inverts`

English:
lemma isIso_of_isRightDerivedFunctor_of_inverts
  statement: [L.IsLocalization W]
  proof: by
  have : α = (Localization.fac F hF L).inv ≫
    whiskerLeft _ (rightDerivedUnique _ _ (Localization.fac F hF L).inv α W).hom := by simp
  rw [this]
  infer_instance

中文:
引理 isIso_of_isRightDerivedFunctor_of_inverts
  结论: [L.是Localization W]
  证明: by
  have : α = (Localization.fac F hF L).inv ≫
    whiskerLeft _ (rightDerivedUnique _ _ (Localization.fac F hF L).inv α W).hom := by simp
  rw [this]
  infer_instance

Depends on / 依赖: Localization, Localization.fac, infer_instance, rightDerivedUnique, whiskerLeft
-/
lemma isIso_of_isRightDerivedFunctor_of_inverts [L.IsLocalization W]
    {F : C ⥤ H} (RF : D ⥤ H) (α : F ⟶ L ⋙ RF)
    (hF : W.IsInvertedBy F) [RF.IsRightDerivedFunctor α W] :
    IsIso α := by
  have : α = (Localization.fac F hF L).inv ≫
    whiskerLeft _ (rightDerivedUnique _ _ (Localization.fac F hF L).inv α W).hom := by simp
  rw [this]
  infer_instance

variable {W} in
/--
lemma `isRightDerivedFunctor_iff_of_inverts` / 引理 `isRightDerivedFunctor_iff_of_inverts`

English:
lemma isRightDerivedFunctor_iff_of_inverts
  statement: [L.IsLocalization W]
  proof: ⟨fun _ => isIso_of_isRightDerivedFunctor_of_inverts RF α hF, fun _ =>
    isRightDerivedFunctor_of_inverts W RF (asIso α).symm⟩

中文:
引理 isRightDerivedFunctor_iff_of_inverts
  结论: [L.是Localization W]
  证明: ⟨fun _ => isIso_of_isRightDerivedFunctor_of_inverts RF α hF, fun _ =>
    isRightDerivedFunctor_of_inverts W RF (asIso α).symm⟩

Depends on / 依赖: isIso_of_isRightDerivedFunctor_of_inverts, isRightDerivedFunctor_of_inverts
-/
lemma isRightDerivedFunctor_iff_of_inverts [L.IsLocalization W]
    {F : C ⥤ H} (RF : D ⥤ H) (α : F ⟶ L ⋙ RF)
    (hF : W.IsInvertedBy F) :
    RF.IsRightDerivedFunctor α W ↔ IsIso α :=
  ⟨fun _ => isIso_of_isRightDerivedFunctor_of_inverts RF α hF, fun _ =>
    isRightDerivedFunctor_of_inverts W RF (asIso α).symm⟩

end

end Functor

end CategoryTheory
