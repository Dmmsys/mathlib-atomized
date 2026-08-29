/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Localization.StructuredArrow

/-!
# Pointwise left derived functors

We define pointwise left derived functors using the notion
of pointwise right Kan extensions.

We show that if `F : C ⥤ H` inverts `W : MorphismProperty C`,
then it has a pointwise left derived functor.

Note: this file was obtained by dualizing the definitions in the file
`Mathlib/CategoryTheory/Functor/Derived/PointwiseRightDerived.lean`. These two files should be
kept in sync.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C : Type u₁} {D : Type u₂} {H : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} H]
  (F' : D ⥤ H) (F : C ⥤ H) (L : C ⥤ D) (α : L ⋙ F' ⟶ F) (W : MorphismProperty C)

/--
Definition of `HasPointwiseLeftDerivedFunctorAt` / `HasPointwiseLeftDerivedFunctorAt` 的定义

English:
class HasPointwiseLeftDerivedFunctorAt
  parameters: (X : C)
  axioms and operations (1):
    - hasLimit' : HasPointwiseRightKanExtensionAt W.Q F (W.Q.obj X)

中文:
类 有PointwiseLeftDerivedFunctorAt
  参数: (X : C)
  公理与运算 (1 个):
    - hasLimit' : HasPointwiseRightKanExtensionAt W.Q F (W.Q.obj X)
-/
class HasPointwiseLeftDerivedFunctorAt (X : C) : Prop where
  /-- Use the more general `hasLimit` lemma instead, see also
  `hasPointwiseLeftDerivedFunctorAt_iff` -/
  hasLimit' : HasPointwiseRightKanExtensionAt W.Q F (W.Q.obj X)

/--
Definition of `HasPointwiseLeftDerivedFunctor` / `HasPointwiseLeftDerivedFunctor` 的定义

English:
abbreviation HasPointwiseLeftDerivedFunctor
  body: forall (X : C), F.HasPointwiseLeftDerivedFunctorAt W X

中文:
缩写 HasPointwiseLeftDerivedFunctor
  定义体: forall (X : C), F.HasPointwiseLeftDerivedFunctorAt W X

Depends on / 依赖: F.HasPointwiseLeftDerivedFunctorAt, HasPointwiseLeftDerivedFunctorAt
-/
abbrev HasPointwiseLeftDerivedFunctor := forall (X : C), F.HasPointwiseLeftDerivedFunctorAt W X

/--
lemma `hasPointwiseLeftDerivedFunctorAt_iff` / 引理 `hasPointwiseLeftDerivedFunctorAt_iff`

English:
lemma hasPointwiseLeftDerivedFunctorAt_iff
  given: [L.IsLocalization W] (X : C)
  proof: by
  rw [← hasPointwiseRightKanExtensionAt_iff_of_equivalence W.Q L F
    (Localization.uniq W.Q L W) (Localization.compUniqFunctor W.Q L W) (W.Q.obj X) (L.obj X)
    ((Localization.compUniqFunctor W.Q L W).app X)]
  exact ⟨fun h => h.hasLimit', fun h => ⟨h⟩⟩

中文:
引理 hasPointwiseLeftDerivedFunctorAt_iff
  条件: [L.是Localization W] (X : C)
  证明: by
  rw [← hasPointwiseRightKanExtensionAt_iff_of_equivalence W.Q L F
    (Localization.uniq W.Q L W) (Localization.compUniqFunctor W.Q L W) (W.Q.obj X) (L.obj X)
    ((Localization.compUniqFunctor W.Q L W).app X)]
  exact ⟨fun h => h.hasLimit', fun h => ⟨h⟩⟩

Depends on / 依赖: L.obj, Localization, Localization.compUniqFunctor, Localization.uniq, W.Q.obj, compUniqFunctor, h.hasLimit, hasLimit, hasPointwiseRightKanExtensionAt_iff_of_equivalence
-/
lemma hasPointwiseLeftDerivedFunctorAt_iff [L.IsLocalization W] (X : C) :
    F.HasPointwiseLeftDerivedFunctorAt W X ↔
      HasPointwiseRightKanExtensionAt L F (L.obj X) := by
  rw [← hasPointwiseRightKanExtensionAt_iff_of_equivalence W.Q L F
    (Localization.uniq W.Q L W) (Localization.compUniqFunctor W.Q L W) (W.Q.obj X) (L.obj X)
    ((Localization.compUniqFunctor W.Q L W).app X)]
  exact ⟨fun h => h.hasLimit', fun h => ⟨h⟩⟩

/--
lemma `HasPointwiseLeftDerivedFunctorAt.hasLimit` / 引理 `HasPointwiseLeftDerivedFunctorAt.hasLimit`

English:
lemma HasPointwiseLeftDerivedFunctorAt.hasLimit
  proof: by
  rwa [← hasPointwiseLeftDerivedFunctorAt_iff F L W]

中文:
引理 有PointwiseLeftDerivedFunctorAt.hasLimit
  证明: by
  rwa [← hasPointwiseLeftDerivedFunctorAt_iff F L W]

Depends on / 依赖: hasPointwiseLeftDerivedFunctorAt_iff
-/
lemma HasPointwiseLeftDerivedFunctorAt.hasLimit
    [L.IsLocalization W] (X : C) [F.HasPointwiseLeftDerivedFunctorAt W X] :
    HasPointwiseRightKanExtensionAt L F (L.obj X) := by
  rwa [← hasPointwiseLeftDerivedFunctorAt_iff F L W]

/--
lemma `hasPointwiseLeftDerivedFunctorAt_iff_of_mem` / 引理 `hasPointwiseLeftDerivedFunctorAt_iff_of_mem`

English:
lemma hasPointwiseLeftDerivedFunctorAt_iff_of_mem
  given: {X Y : C} (w : X ⟶ Y) (hw : W w)
  proof: by
  simp only [F.hasPointwiseLeftDerivedFunctorAt_iff W.Q W]
  exact hasPointwiseRightKanExtensionAt_iff_of_iso W.Q F (Localization.isoOfHom W.Q W w hw)

中文:
引理 hasPointwiseLeftDerivedFunctorAt_iff_of_mem
  条件: {X Y : C} (w : X ⟶ Y) (hw : W w)
  证明: by
  simp only [F.hasPointwiseLeftDerivedFunctorAt_iff W.Q W]
  exact hasPointwiseRightKanExtensionAt_iff_of_iso W.Q F (Localization.isoOfHom W.Q W w hw)

Depends on / 依赖: F.hasPointwiseLeftDerivedFunctorAt_iff, Localization, Localization.isoOfHom, hasPointwiseLeftDerivedFunctorAt_iff, hasPointwiseRightKanExtensionAt_iff_of_iso, isoOfHom
-/
lemma hasPointwiseLeftDerivedFunctorAt_iff_of_mem {X Y : C} (w : X ⟶ Y) (hw : W w) :
    F.HasPointwiseLeftDerivedFunctorAt W X ↔
      F.HasPointwiseLeftDerivedFunctorAt W Y := by
  simp only [F.hasPointwiseLeftDerivedFunctorAt_iff W.Q W]
  exact hasPointwiseRightKanExtensionAt_iff_of_iso W.Q F (Localization.isoOfHom W.Q W w hw)

section

variable [F.HasPointwiseLeftDerivedFunctor W]

/--
lemma `hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor` / 引理 `hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor`

English:
lemma hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor
  given: [L.IsLocalization W]
  proof: fun Y => by
  have := Localization.essSurj L W
  rw [← hasPointwiseRightKanExtensionAt_iff_of_iso _ F (L.objObjPreimageIso Y)]; rw [← F.hasPointwiseLeftDerivedFunctorAt_iff L W]
  infer_instance

中文:
引理 hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor
  条件: [L.是Localization W]
  证明: fun Y => by
  have := Localization.essSurj L W
  rw [← hasPointwiseRightKanExtensionAt_iff_of_iso _ F (L.objObjPreimageIso Y)]; rw [← F.hasPointwiseLeftDerivedFunctorAt_iff L W]
  infer_instance

Depends on / 依赖: F.hasPointwiseLeftDerivedFunctorAt_iff, L.objObjPreimageIso, Localization, Localization.essSurj, essSurj, hasPointwiseLeftDerivedFunctorAt_iff, hasPointwiseRightKanExtensionAt_iff_of_iso, infer_instance, objObjPreimageIso
-/
lemma hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor [L.IsLocalization W] :
    HasPointwiseRightKanExtension L F := fun Y => by
  have := Localization.essSurj L W
  rw [← hasPointwiseRightKanExtensionAt_iff_of_iso _ F (L.objObjPreimageIso Y)]; rw [← F.hasPointwiseLeftDerivedFunctorAt_iff L W]
  infer_instance

/--
lemma `hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor` / 引理 `hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor`

English:
lemma hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor
  proof: by
    have := F.hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor W.Q W
    infer_instance

中文:
引理 hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor
  证明: by
    have := F.hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor W.Q W
    infer_instance

Depends on / 依赖: F.hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor, hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor, infer_instance
-/
lemma hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor :
    F.HasLeftDerivedFunctor W where
  hasRightKanExtension' := by
    have := F.hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor W.Q W
    infer_instance

attribute [instance] hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor

variable {F L}

/--
Definition of `isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor` / `isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor` 的定义

English:
definition isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor
  body: have := hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor F L
  have := IsLeftDerivedFunctor.isRightKanExtension F' α W
  isPointwiseRightKanExtensionOfIsRightKanExtension F' α

中文:
定义 isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor
  定义体: have := hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor F L
  have := IsLeftDerivedFunctor.isRightKanExtension F' α W
  isPointwiseRightKanExtensionOfIsRightKanExtension F' α

Depends on / 依赖: IsLeftDerivedFunctor, IsLeftDerivedFunctor.isRightKanExtension, hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor, isPointwiseRightKanExtensionOfIsRightKanExtension, isRightKanExtension
-/
noncomputable def isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor
     [L.IsLocalization W] [F'.IsLeftDerivedFunctor α W] :
    (RightExtension.mk _ α).IsPointwiseRightKanExtension :=
  have := hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor F L
  have := IsLeftDerivedFunctor.isRightKanExtension F' α W
  isPointwiseRightKanExtensionOfIsRightKanExtension F' α

end

section

variable {F L}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isPointwiseRightKanExtensionAtOfIsoOfIsLocalization` / `isPointwiseRightKanExtensionAtOfIsoOfIsLocalization` 的定义

English:
definition isPointwiseRightKanExtensionAtOfIsoOfIsLocalization
  body: s.π.app (StructuredArrow.mk (𝟙 (L.obj Y))) ≫ e.hom.app Y
  fac s j := by
    refine Localization.induction_structuredArrow L W _ (by simp)
      (fun X₁ X₂ f φ hφ => ?_) (fun X₁ X₂ w hw φ hφ => ?_) j
    · have eq := s.π.naturality
        (StructuredArrow.homMk f : StructuredArrow.mk φ ⟶ Structured

中文:
定义 isPointwiseRightKanExtensionAtOfIsoOfIsLocalization
  定义体: s.π.app (StructuredArrow.mk (𝟙 (L.obj Y))) ≫ e.hom.app Y
  fac s j := by
    refine Localization.induction_structuredArrow L W _ (by simp)
      (fun X₁ X₂ f φ hφ => ?_) (fun X₁ X₂ w hw φ hφ => ?_) j
    · have eq := s.π.naturality
        (StructuredArrow.homMk f : StructuredArrow.mk φ ⟶ Structured

Depends on / 依赖: L.obj, StructuredArrow, StructuredArrow.mk, e.hom.app
-/
def isPointwiseRightKanExtensionAtOfIsoOfIsLocalization
    {G : D ⥤ H} (e : F ≅ L ⋙ G) [L.IsLocalization W] (Y : C) :
    (RightExtension.mk _ e.inv).IsPointwiseRightKanExtensionAt (L.obj Y) where
  lift s := s.π.app (StructuredArrow.mk (𝟙 (L.obj Y))) ≫ e.hom.app Y
  fac s j := by
    refine Localization.induction_structuredArrow L W _ (by simp)
      (fun X₁ X₂ f φ hφ => ?_) (fun X₁ X₂ w hw φ hφ => ?_) j
    · have eq := s.π.naturality
        (StructuredArrow.homMk f : StructuredArrow.mk φ ⟶ StructuredArrow.mk (φ ≫ L.map f))
      dsimp at eq hφ ⊢
      rw [id_comp] at eq
      rw [assoc] at hφ
      simp [eq, ← reassoc_of% hφ, ← e.inv.naturality f]
    · have : IsIso (F.map w) := by
        have := Localization.inverts L W w hw
        rw [← NatIso.naturality_2 e w]
        dsimp
        infer_instance
      have eq := s.π.naturality (StructuredArrow.homMk w :
          StructuredArrow.mk (φ ≫ (Localization.isoOfHom L W w hw).inv) ⟶
            StructuredArrow.mk φ)
      dsimp at eq hφ ⊢
      rw [id_comp] at eq
      rw [assoc] at hφ
      simp only [← cancel_mono (F.map w), ← eq, comp_obj, comp_map, assoc,
        ← hφ, ← NatTrans.naturality, ← G.map_comp_assoc,
        Localization.isoOfHom_inv_hom_id, comp_id]
  uniq s m hm := by
    have := hm (StructuredArrow.mk (𝟙 (L.obj Y)))
    dsimp at this m hm ⊢
    simp [← reassoc_of% this]

/--
Definition of `isPointwiseRightKanExtensionOfIsoOfIsLocalization` / `isPointwiseRightKanExtensionOfIsoOfIsLocalization` 的定义

English:
definition isPointwiseRightKanExtensionOfIsoOfIsLocalization
  body: fun Y =>
  have := Localization.essSurj L W
  (RightExtension.mk _ e.inv).isPointwiseRightKanExtensionAtEquivOfIso'
    (L.objObjPreimageIso Y) (isPointwiseRightKanExtensionAtOfIsoOfIsLocalization W e _)

中文:
定义 isPointwiseRightKanExtensionOfIsoOfIsLocalization
  定义体: fun Y =>
  have := Localization.essSurj L W
  (RightExtension.mk _ e.inv).isPointwiseRightKanExtensionAtEquivOfIso'
    (L.objObjPreimageIso Y) (isPointwiseRightKanExtensionAtOfIsoOfIsLocalization W e _)
-/
noncomputable def isPointwiseRightKanExtensionOfIsoOfIsLocalization
    {G : D ⥤ H} (e : F ≅ L ⋙ G) [L.IsLocalization W] :
    (RightExtension.mk _ e.inv).IsPointwiseRightKanExtension := fun Y =>
  have := Localization.essSurj L W
  (RightExtension.mk _ e.inv).isPointwiseRightKanExtensionAtEquivOfIso'
    (L.objObjPreimageIso Y) (isPointwiseRightKanExtensionAtOfIsoOfIsLocalization W e _)

/--
Definition of `RightExtension.isPointwiseRightKanExtensionOfIsIsoOfIsLocalization` / `RightExtension.isPointwiseRightKanExtensionOfIsIsoOfIsLocalization` 的定义

English:
definition RightExtension.isPointwiseRightKanExtensionOfIsIsoOfIsLocalization
  body: Functor.isPointwiseRightKanExtensionOfIsoOfIsLocalization W (asIso E.hom).symm

中文:
定义 RightExtension.isPointwiseRightKanExtensionOfIsIsoOfIsLocalization
  定义体: Functor.isPointwiseRightKanExtensionOfIsoOfIsLocalization W (asIso E.hom).symm

Depends on / 依赖: E.hom, Functor, Functor.isPointwiseRightKanExtensionOfIsoOfIsLocalization, isPointwiseRightKanExtensionOfIsoOfIsLocalization
-/
noncomputable def RightExtension.isPointwiseRightKanExtensionOfIsIsoOfIsLocalization
    (E : RightExtension L F) [IsIso E.hom] [L.IsLocalization W] :
    E.IsPointwiseRightKanExtension :=
  Functor.isPointwiseRightKanExtensionOfIsoOfIsLocalization W (asIso E.hom).symm

/--
lemma `hasPointwiseLeftDerivedFunctor_of_inverts` / 引理 `hasPointwiseLeftDerivedFunctor_of_inverts`

English:
lemma hasPointwiseLeftDerivedFunctor_of_inverts
  proof: by
  intro X
  rw [hasPointwiseLeftDerivedFunctorAt_iff F W.Q W]
  exact (isPointwiseRightKanExtensionOfIsoOfIsLocalization W
    (Localization.fac F hF W.Q).symm).hasPointwiseRightKanExtension _

中文:
引理 hasPointwiseLeftDerivedFunctor_of_inverts
  证明: by
  intro X
  rw [hasPointwiseLeftDerivedFunctorAt_iff F W.Q W]
  exact (isPointwiseRightKanExtensionOfIsoOfIsLocalization W
    (Localization.fac F hF W.Q).symm).hasPointwiseRightKanExtension _

Depends on / 依赖: HasFiniteLimits, Localization, Localization.fac, hasFiniteWidePullbacks_of_hasFiniteLimits, hasPointwiseLeftDerivedFunctorAt_iff, hasPointwiseRightKanExtension, isPointwiseRightKanExtensionOfIsoOfIsLocalization
-/
lemma hasPointwiseLeftDerivedFunctor_of_inverts
    (F : C ⥤ H) {W : MorphismProperty C} (hF : W.IsInvertedBy F) :
    F.HasPointwiseLeftDerivedFunctor W := by
  intro X
  rw [hasPointwiseLeftDerivedFunctorAt_iff F W.Q W]
  exact (isPointwiseRightKanExtensionOfIsoOfIsLocalization W
    (Localization.fac F hF W.Q).symm).hasPointwiseRightKanExtension _

/--
lemma `isLeftDerivedFunctor_of_inverts` / 引理 `isLeftDerivedFunctor_of_inverts`

English:
lemma isLeftDerivedFunctor_of_inverts
  proof: (isPointwiseRightKanExtensionOfIsoOfIsLocalization W e.symm).isRightKanExtension

中文:
引理 isLeftDerivedFunctor_of_inverts
  证明: (isPointwiseRightKanExtensionOfIsoOfIsLocalization W e.symm).isRightKanExtension

Depends on / 依赖: HasFiniteColimits, e.symm, hasFiniteWidePushouts_of_has_finite_limits, isPointwiseRightKanExtensionOfIsoOfIsLocalization, isRightKanExtension
-/
lemma isLeftDerivedFunctor_of_inverts
    [L.IsLocalization W] (F' : D ⥤ H) (e : L ⋙ F' ≅ F) :
    F'.IsLeftDerivedFunctor e.hom W where
  isRightKanExtension :=
    (isPointwiseRightKanExtensionOfIsoOfIsLocalization W e.symm).isRightKanExtension

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [L.IsLocalization
  signature: W] (hF
  body: isLeftDerivedFunctor_of_inverts W _ _

中文:
实例 [L.是Localization
  签名: W] (hF
  定义体: isLeftDerivedFunctor_of_inverts W _ _

Depends on / 依赖: isLeftDerivedFunctor_of_inverts
-/
instance [L.IsLocalization W] (hF : W.IsInvertedBy F) :
    (Localization.lift F hF L).IsLeftDerivedFunctor (Localization.fac F hF L).hom W :=
  isLeftDerivedFunctor_of_inverts W _ _

variable {W} in
/--
lemma `isIso_of_isLeftDerivedFunctor_of_inverts` / 引理 `isIso_of_isLeftDerivedFunctor_of_inverts`

English:
lemma isIso_of_isLeftDerivedFunctor_of_inverts
  statement: [L.IsLocalization W]
  proof: by
  have : α = whiskerLeft _ (leftDerivedUnique _ _ (Localization.fac F hF L).hom α W).inv ≫
      (Localization.fac F hF L).hom := by simp
  rw [this]
  infer_instance

中文:
引理 isIso_of_isLeftDerivedFunctor_of_inverts
  结论: [L.是Localization W]
  证明: by
  have : α = whiskerLeft _ (leftDerivedUnique _ _ (Localization.fac F hF L).hom α W).inv ≫
      (Localization.fac F hF L).hom := by simp
  rw [this]
  infer_instance

Depends on / 依赖: Localization, Localization.fac, infer_instance, leftDerivedUnique, whiskerLeft
-/
lemma isIso_of_isLeftDerivedFunctor_of_inverts [L.IsLocalization W]
    {F : C ⥤ H} (LF : D ⥤ H) (α : L ⋙ LF ⟶ F)
    (hF : W.IsInvertedBy F) [LF.IsLeftDerivedFunctor α W] :
    IsIso α := by
  have : α = whiskerLeft _ (leftDerivedUnique _ _ (Localization.fac F hF L).hom α W).inv ≫
      (Localization.fac F hF L).hom := by simp
  rw [this]
  infer_instance

variable {W} in
/--
lemma `isLeftDerivedFunctor_iff_of_inverts` / 引理 `isLeftDerivedFunctor_iff_of_inverts`

English:
lemma isLeftDerivedFunctor_iff_of_inverts
  statement: [L.IsLocalization W]
  proof: ⟨fun _ => isIso_of_isLeftDerivedFunctor_of_inverts LF α hF, fun _ =>
    isLeftDerivedFunctor_of_inverts W LF (asIso α)⟩

中文:
引理 isLeftDerivedFunctor_iff_of_inverts
  结论: [L.是Localization W]
  证明: ⟨fun _ => isIso_of_isLeftDerivedFunctor_of_inverts LF α hF, fun _ =>
    isLeftDerivedFunctor_of_inverts W LF (asIso α)⟩

Depends on / 依赖: isIso_of_isLeftDerivedFunctor_of_inverts, isLeftDerivedFunctor_of_inverts
-/
lemma isLeftDerivedFunctor_iff_of_inverts [L.IsLocalization W]
    {F : C ⥤ H} (LF : D ⥤ H) (α : L ⋙ LF ⟶ F)
    (hF : W.IsInvertedBy F) :
    LF.IsLeftDerivedFunctor α W ↔ IsIso α :=
  ⟨fun _ => isIso_of_isLeftDerivedFunctor_of_inverts LF α hF, fun _ =>
    isLeftDerivedFunctor_of_inverts W LF (asIso α)⟩

end

end Functor

end CategoryTheory
