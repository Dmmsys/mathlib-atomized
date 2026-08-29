/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.CatCommSq
public import Mathlib.CategoryTheory.Localization.Opposite
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Opposites

/-!
# Localization of adjunctions

In this file, we show that if we have an adjunction `adj : G ⊣ F` such that both
functors `G : C₁ ⥤ C₂` and `F : C₂ ⥤ C₁` induce functors
`G' : D₁ ⥤ D₂` and `F' : D₂ ⥤ D₁` on localized categories, i.e. that we
have localization functors `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` with respect
to morphism properties `W₁` and `W₂` respectively, and 2-commutative diagrams
`[CatCommSq G L₁ L₂ G']` and `[CatCommSq F L₂ L₁ F']`, then we have an
induced adjunction `Adjunction.localization L₁ W₁ L₂ W₂ G' F' : G' ⊣ F'`.

-/

@[expose] public section

namespace CategoryTheory

open Localization Category CategoryTheory.Functor

namespace Adjunction

variable {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  {G : C₁ ⥤ C₂} {F : C₂ ⥤ C₁} (adj : G ⊣ F)

section

variable (L₁ : C₁ ⥤ D₁) (W₁ : MorphismProperty C₁) [L₁.IsLocalization W₁]
  (L₂ : C₂ ⥤ D₂) (W₂ : MorphismProperty C₂) [L₂.IsLocalization W₂]
  (G' : D₁ ⥤ D₂) (F' : D₂ ⥤ D₁)
  [CatCommSq G L₁ L₂ G'] [CatCommSq F L₂ L₁ F']


namespace Localization

/--
Definition of `ε` / `ε` 的定义

English:
definition ε
  signature: : 𝟭 D₁ ⟶ G' ⋙ F'
  body: by
  letI : Lifting L₁ W₁ ((G ⋙ F) ⋙ L₁) (G' ⋙ F') :=
    Lifting.mk (CatCommSq.hComp G F L₁ L₂ L₁ G' F').iso.symm
  exact Localization.liftNatTrans L₁ W₁ L₁ ((G ⋙ F) ⋙ L₁) (𝟭 D₁) (G' ⋙ F')
    (whiskerRight adj.unit L₁)

中文:
定义 ε
  签名: : 𝟭 D₁ ⟶ G' ⋙ F'
  定义体: by
  letI : Lifting L₁ W₁ ((G ⋙ F) ⋙ L₁) (G' ⋙ F') :=
    Lifting.mk (CatCommSq.hComp G F L₁ L₂ L₁ G' F').iso.symm
  exact Localization.liftNatTrans L₁ W₁ L₁ ((G ⋙ F) ⋙ L₁) (𝟭 D₁) (G' ⋙ F')
    (whiskerRight adj.unit L₁)

Depends on / 依赖: CatCommSq, CatCommSq.hComp, Lifting, Lifting.mk, Localization, Localization.liftNatTrans, adj.unit, iso.symm, liftNatTrans, whiskerRight
-/
noncomputable def ε : 𝟭 D₁ ⟶ G' ⋙ F' := by
  letI : Lifting L₁ W₁ ((G ⋙ F) ⋙ L₁) (G' ⋙ F') :=
    Lifting.mk (CatCommSq.hComp G F L₁ L₂ L₁ G' F').iso.symm
  exact Localization.liftNatTrans L₁ W₁ L₁ ((G ⋙ F) ⋙ L₁) (𝟭 D₁) (G' ⋙ F')
    (whiskerRight adj.unit L₁)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `ε_app` / 引理 `ε_app`

English:
lemma ε_app
  given: (X₁ : C₁)
  proof: by
  let : Lifting L₁ W₁ ((G ⋙ F) ⋙ L₁) (G' ⋙ F') :=
    Lifting.mk (CatCommSq.hComp G F L₁ L₂ L₁ G' F').iso.symm
  simp only [ε, liftNatTrans_app, Lifting.iso, Iso.symm,
    Functor.id_obj, Functor.comp_obj, Functor.rightUnitor_hom_app,
      whiskerRight_app, CatCommSq.hComp_iso_hom_app, id_comp]

中文:
引理 ε_app
  条件: (X₁ : C₁)
  证明: by
  let : Lifting L₁ W₁ ((G ⋙ F) ⋙ L₁) (G' ⋙ F') :=
    Lifting.mk (CatCommSq.hComp G F L₁ L₂ L₁ G' F').iso.symm
  simp only [ε, liftNatTrans_app, Lifting.iso, Iso.symm,
    Functor.id_obj, Functor.comp_obj, Functor.rightUnitor_hom_app,
      whiskerRight_app, CatCommSq.hComp_iso_hom_app, id_comp]

Depends on / 依赖: CatCommSq, CatCommSq.hComp, CatCommSq.hComp_iso_hom_app, Functor, Functor.comp_obj, Functor.id_obj, Functor.rightUnitor_hom_app, Iso.symm, Lifting, Lifting.iso, Lifting.mk, comp_obj, hComp_iso_hom_app, id_comp, id_obj, iso.symm, liftNatTrans_app, rightUnitor_hom_app, whiskerRight_app
-/
lemma ε_app (X₁ : C₁) :
    (ε adj L₁ W₁ L₂ G' F').app (L₁.obj X₁) =
      L₁.map (adj.unit.app X₁) ≫ (CatCommSq.iso F L₂ L₁ F').hom.app (G.obj X₁) ≫
        F'.map ((CatCommSq.iso G L₁ L₂ G').hom.app X₁) := by
  let : Lifting L₁ W₁ ((G ⋙ F) ⋙ L₁) (G' ⋙ F') :=
    Lifting.mk (CatCommSq.hComp G F L₁ L₂ L₁ G' F').iso.symm
  simp only [ε, liftNatTrans_app, Lifting.iso, Iso.symm,
    Functor.id_obj, Functor.comp_obj, Functor.rightUnitor_hom_app,
      whiskerRight_app, CatCommSq.hComp_iso_hom_app, id_comp]

/--
Definition of `η` / `η` 的定义

English:
definition η
  signature: : F' ⋙ G' ⟶ 𝟭 D₂
  body: by
  letI : Lifting L₂ W₂ ((F ⋙ G) ⋙ L₂) (F' ⋙ G') :=
    Lifting.mk (CatCommSq.hComp F G L₂ L₁ L₂ F' G').iso.symm
  exact liftNatTrans L₂ W₂ ((F ⋙ G) ⋙ L₂) L₂ (F' ⋙ G') (𝟭 D₂) (whiskerRight adj.counit L₂)

中文:
定义 η
  签名: : F' ⋙ G' ⟶ 𝟭 D₂
  定义体: by
  letI : Lifting L₂ W₂ ((F ⋙ G) ⋙ L₂) (F' ⋙ G') :=
    Lifting.mk (CatCommSq.hComp F G L₂ L₁ L₂ F' G').iso.symm
  exact liftNatTrans L₂ W₂ ((F ⋙ G) ⋙ L₂) L₂ (F' ⋙ G') (𝟭 D₂) (whiskerRight adj.counit L₂)

Depends on / 依赖: CatCommSq, CatCommSq.hComp, Lifting, Lifting.mk, adj.counit, counit, iso.symm, liftNatTrans, whiskerRight
-/
noncomputable def η : F' ⋙ G' ⟶ 𝟭 D₂ := by
  letI : Lifting L₂ W₂ ((F ⋙ G) ⋙ L₂) (F' ⋙ G') :=
    Lifting.mk (CatCommSq.hComp F G L₂ L₁ L₂ F' G').iso.symm
  exact liftNatTrans L₂ W₂ ((F ⋙ G) ⋙ L₂) L₂ (F' ⋙ G') (𝟭 D₂) (whiskerRight adj.counit L₂)

/--
lemma `η_app` / 引理 `η_app`

English:
lemma η_app
  given: (X₂ : C₂)
  proof: by
  let : Lifting L₂ W₂ ((F ⋙ G) ⋙ L₂) (F' ⋙ G') :=
    Lifting.mk (CatCommSq.hComp F G L₂ L₁ L₂ F' G').iso.symm
  simp only [η, liftNatTrans_app, Lifting.iso, Iso.symm, CatCommSq.hComp_iso_inv_app,
    whiskerRight_app, Functor.rightUnitor_inv_app, comp_id, assoc]

中文:
引理 η_app
  条件: (X₂ : C₂)
  证明: by
  let : Lifting L₂ W₂ ((F ⋙ G) ⋙ L₂) (F' ⋙ G') :=
    Lifting.mk (CatCommSq.hComp F G L₂ L₁ L₂ F' G').iso.symm
  simp only [η, liftNatTrans_app, Lifting.iso, Iso.symm, CatCommSq.hComp_iso_inv_app,
    whiskerRight_app, Functor.rightUnitor_inv_app, comp_id, assoc]

Depends on / 依赖: CatCommSq, CatCommSq.hComp, CatCommSq.hComp_iso_inv_app, Functor, Functor.rightUnitor_inv_app, Iso.symm, Lifting, Lifting.iso, Lifting.mk, comp_id, hComp_iso_inv_app, iso.symm, liftNatTrans_app, rightUnitor_inv_app, whiskerRight_app
-/
lemma η_app (X₂ : C₂) :
    (η adj L₁ L₂ W₂ G' F').app (L₂.obj X₂) =
      G'.map ((CatCommSq.iso F L₂ L₁ F').inv.app X₂) ≫
        (CatCommSq.iso G L₁ L₂ G').inv.app (F.obj X₂) ≫
        L₂.map (adj.counit.app X₂) := by
  let : Lifting L₂ W₂ ((F ⋙ G) ⋙ L₂) (F' ⋙ G') :=
    Lifting.mk (CatCommSq.hComp F G L₂ L₁ L₂ F' G').iso.symm
  simp only [η, liftNatTrans_app, Lifting.iso, Iso.symm, CatCommSq.hComp_iso_inv_app,
    whiskerRight_app, Functor.rightUnitor_inv_app, comp_id, assoc]

end Localization

/--
Definition of `localization` / `localization` 的定义

English:
definition localization
  signature: : G' ⊣ F'
  body: Adjunction.mkOfUnitCounit
    { unit := Localization.ε adj L₁ W₁ L₂ G' F'
      counit := Localization.η adj L₁ L₂ W₂ G' F'
      left_triangle := by
        apply natTrans_ext L₁ W₁
        intro X₁
        have eq := adj.left_triangle_components X₁
        rw [NatTrans.comp_app]; rw [NatTrans.comp

中文:
定义 localization
  签名: : G' ⊣ F'
  定义体: Adjunction.mkOfUnitCounit
    { unit := Localization.ε adj L₁ W₁ L₂ G' F'
      counit := Localization.η adj L₁ L₂ W₂ G' F'
      left_triangle := by
        apply natTrans_ext L₁ W₁
        intro X₁
        have eq := adj.left_triangle_components X₁
        rw [NatTrans.comp_app]; rw [NatTrans.comp

Depends on / 依赖: Adjunction, Adjunction.mkOfUnitCounit, Functor, Functor.associator_hom_app, Localization, NatTrans, NatTrans.comp_app, adj.left_triangle_components, associator_hom_app, comp_app, counit, id_comp, left_triangle, left_triangle_components, map_comp, mkOfUnitCounit, natTrans_ext, naturality, whiskerLeft_app, whiskerRight_app
-/
noncomputable def localization : G' ⊣ F' :=
  Adjunction.mkOfUnitCounit
    { unit := Localization.ε adj L₁ W₁ L₂ G' F'
      counit := Localization.η adj L₁ L₂ W₂ G' F'
      left_triangle := by
        apply natTrans_ext L₁ W₁
        intro X₁
        have eq := adj.left_triangle_components X₁
        rw [NatTrans.comp_app]; rw [NatTrans.comp_app]; rw [whiskerRight_app]; rw [Localization.ε_app]; rw [Functor.associator_hom_app]; rw [id_comp]; rw [whiskerLeft_app]; rw [G'.map_comp]; rw [G'.map_comp]; rw [assoc]; rw [assoc]
        erw [(Localization.η adj L₁ L₂ W₂ G' F').naturality, Localization.η_app,
          assoc, assoc, ← G'.map_comp_assoc, ← G'.map_comp_assoc, assoc, Iso.hom_inv_id_app,
          comp_id, (CatCommSq.iso G L₁ L₂ G').inv.naturality_assoc, ← L₂.map_comp_assoc, eq,
          L₂.map_id, id_comp, Iso.inv_hom_id_app]
        rfl
      right_triangle := by
        apply natTrans_ext L₂ W₂
        intro X₂
        have eq := adj.right_triangle_components X₂
        rw [NatTrans.comp_app]; rw [NatTrans.comp_app]; rw [whiskerLeft_app]; rw [whiskerRight_app]; rw [Localization.η_app]; rw [Functor.associator_inv_app]; rw [id_comp]; rw [F'.map_comp]; rw [F'.map_comp]
        erw [← (Localization.ε _ _ _ _ _ _).naturality_assoc, Localization.ε_app,
          assoc, assoc, ← F'.map_comp_assoc, Iso.hom_inv_id_app, F'.map_id, id_comp,
          ← NatTrans.naturality, ← L₁.map_comp_assoc, eq, L₁.map_id, id_comp,
          Iso.inv_hom_id_app]
        rfl }

@[simp]
/--
lemma `localization_unit_app` / 引理 `localization_unit_app`

English:
lemma localization_unit_app
  given: (X₁ : C₁)
  proof: by
  apply Localization.ε_app

@[simp]

中文:
引理 localization_unit_app
  条件: (X₁ : C₁)
  证明: by
  apply Localization.ε_app

@[simp]

Depends on / 依赖: Localization
-/
lemma localization_unit_app (X₁ : C₁) :
    (adj.localization L₁ W₁ L₂ W₂ G' F').unit.app (L₁.obj X₁) =
    L₁.map (adj.unit.app X₁) ≫ (CatCommSq.iso F L₂ L₁ F').hom.app (G.obj X₁) ≫
      F'.map ((CatCommSq.iso G L₁ L₂ G').hom.app X₁) := by
  apply Localization.ε_app

@[simp]
/--
lemma `localization_counit_app` / 引理 `localization_counit_app`

English:
lemma localization_counit_app
  given: (X₂ : C₂)
  proof: by
  apply Localization.η_app

中文:
引理 localization_counit_app
  条件: (X₂ : C₂)
  证明: by
  apply Localization.η_app

Depends on / 依赖: Localization
-/
lemma localization_counit_app (X₂ : C₂) :
    (adj.localization L₁ W₁ L₂ W₂ G' F').counit.app (L₂.obj X₂) =
    G'.map ((CatCommSq.iso F L₂ L₁ F').inv.app X₂) ≫
      (CatCommSq.iso G L₁ L₂ G').inv.app (F.obj X₂) ≫
      L₂.map (adj.counit.app X₂) := by
  apply Localization.η_app

end

include adj in
/--
lemma `isLocalization` / 引理 `isLocalization`

English:
lemma isLocalization
  given: [F.Full] [F.Faithful]
  proof: by
  let W := ((MorphismProperty.isomorphisms C₂).inverseImage G)
  have hG : W.IsInvertedBy G := fun _ _ _ hf => hf
  have : forall (X : C₁), IsIso ((whiskerRight adj.unit W.Q).app X) := fun X =>
    Localization.inverts W.Q W _ (by
      change IsIso _
      infer_instance)
  have : IsIso (whisker

中文:
引理 isLocalization
  条件: [F.满] [F.忠实]
  证明: by
  let W := ((MorphismProperty.isomorphisms C₂).inverseImage G)
  have hG : W.IsInvertedBy G := fun _ _ _ hf => hf
  have : forall (X : C₁), IsIso ((whiskerRight adj.unit W.Q).app X) := fun X =>
    Localization.inverts W.Q W _ (by
      change IsIso _
      infer_instance)
  have : IsIso (whisker

Depends on / 依赖: Equivalence, Equivalence.mk, IsInvertedBy, Localization, Localization.inverts, Localization.lift, MorphismProperty, MorphismProperty.isomorphisms, NatIso, NatIso.isIso_of_isIso_app, W.IsInvertedBy, W.Localization, W.Q.leftUnitor.symm, adj.unit, infer_instance, inverseImage, inverts, isIso_of_isIso_app, isomorphisms, leftUnitor
-/
lemma isLocalization [F.Full] [F.Faithful] :
    G.IsLocalization ((MorphismProperty.isomorphisms C₂).inverseImage G) := by
  let W := ((MorphismProperty.isomorphisms C₂).inverseImage G)
  have hG : W.IsInvertedBy G := fun _ _ _ hf => hf
  have : forall (X : C₁), IsIso ((whiskerRight adj.unit W.Q).app X) := fun X =>
    Localization.inverts W.Q W _ (by
      change IsIso _
      infer_instance)
  have : IsIso (whiskerRight adj.unit W.Q) := NatIso.isIso_of_isIso_app _
  let e : W.Localization ≌ C₂ := Equivalence.mk (Localization.lift G hG W.Q) (F ⋙ W.Q)
    (liftNatIso W.Q W W.Q (G ⋙ F ⋙ W.Q) _ _
    (W.Q.leftUnitor.symm ≪≫ asIso (whiskerRight adj.unit W.Q)))
    (Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Localization.fac G hG W.Q) ≪≫
      asIso adj.counit)
  apply Functor.IsLocalization.of_equivalence_target W.Q W G e
    (Localization.fac G hG W.Q)

include adj in
/--
lemma `isLocalization'` / 引理 `isLocalization'`

English:
lemma isLocalization'
  given: [G.Full] [G.Faithful]
  proof: by
  rw [← Functor.IsLocalization.op_iff]; rw [MorphismProperty.op_inverseImage]; rw [MorphismProperty.op_isomorphisms]
  exact adj.op.isLocalization

中文:
引理 isLocalization'
  条件: [G.满] [G.忠实]
  证明: by
  rw [← Functor.IsLocalization.op_iff]; rw [MorphismProperty.op_inverseImage]; rw [MorphismProperty.op_isomorphisms]
  exact adj.op.isLocalization

Depends on / 依赖: Functor, Functor.IsLocalization.op_iff, IsLocalization, MorphismProperty, MorphismProperty.op_inverseImage, MorphismProperty.op_isomorphisms, adj.op.isLocalization, isLocalization, op_iff, op_inverseImage, op_isomorphisms
-/
lemma isLocalization' [G.Full] [G.Faithful] :
    F.IsLocalization ((MorphismProperty.isomorphisms C₁).inverseImage F) := by
  rw [← Functor.IsLocalization.op_iff]; rw [MorphismProperty.op_inverseImage]; rw [MorphismProperty.op_isomorphisms]
  exact adj.op.isLocalization

end Adjunction

end CategoryTheory
