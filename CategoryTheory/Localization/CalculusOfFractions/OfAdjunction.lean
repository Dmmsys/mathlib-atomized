/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-!
# The calculus of fractions deduced from an adjunction

If `G ⊣ F` is an adjunction, `F` is fully faithful,
and `W` is a class of morphisms that is inverted by `G`
and such that the morphism `adj.unit.app X` belongs to `W`
for any object `X`, then `G` is a localization functor
with respect to `W`. Moreover, if `W` is multiplicative,
then `W` has a calculus of left fractions. This
holds in particular if `W` is the inverse image of
the class of isomorphisms by `G`.

(The dual statement is also obtained.)

-/

public section

namespace CategoryTheory

open MorphismProperty

namespace Adjunction

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
  {G : C₁ ⥤ C₂} {F : C₂ ⥤ C₁}

/--
lemma `hasLeftCalculusOfFractions` / 引理 `hasLeftCalculusOfFractions`

English:
lemma hasLeftCalculusOfFractions
  statement: (adj : G ⊣ F) (W : MorphismProperty C₁)
  proof: by
    obtain ⟨T, s, _, f, rfl⟩ := φ.cases
    dsimp
    have := hW s (by assumption)
    exact ⟨{
      f := adj.unit.app X ≫ F.map (inv (G.map s)) ≫ F.map (G.map f)
      s := adj.unit.app Y
      hs := hW' Y}, by
      have := adj.unit.naturality s
      dsimp at this ⊢
      rw [reassoc_of% this

中文:
引理 hasLeftCalculusOfFractions
  结论: (adj : G ⊣ F) (W : MorphismProperty C₁)
  证明: by
    obtain ⟨T, s, _, f, rfl⟩ := φ.cases
    dsimp
    have := hW s (by assumption)
    exact ⟨{
      f := adj.unit.app X ≫ F.map (inv (G.map s)) ≫ F.map (G.map f)
      s := adj.unit.app Y
      hs := hW' Y}, by
      have := adj.unit.naturality s
      dsimp at this ⊢
      rw [reassoc_of% this

Depends on / 依赖: F.map, Functor, Functor.map_inv, G.map, IsIso.hom_inv_id_assoc, adj.unit.app, adj.unit.naturality, adj.unit_naturality, hom_inv_id_assoc, map_inv, naturality, reassoc_of, unit_naturality
-/
lemma hasLeftCalculusOfFractions (adj : G ⊣ F) (W : MorphismProperty C₁)
    [W.IsMultiplicative] (hW : W.IsInvertedBy G) (hW' : (W.functorCategory C₁) adj.unit) :
    W.HasLeftCalculusOfFractions where
  exists_leftFraction X Y φ := by
    obtain ⟨T, s, _, f, rfl⟩ := φ.cases
    dsimp
    have := hW s (by assumption)
    exact ⟨{
      f := adj.unit.app X ≫ F.map (inv (G.map s)) ≫ F.map (G.map f)
      s := adj.unit.app Y
      hs := hW' Y}, by
      have := adj.unit.naturality s
      dsimp at this ⊢
      rw [reassoc_of% this]; rw [Functor.map_inv]; rw [IsIso.hom_inv_id_assoc]; rw [adj.unit_naturality]⟩
  ext X' X Y f₁ f₂ s _ h := by
    have := hW s (by assumption)
    refine ⟨_, adj.unit.app Y, hW' _, ?_⟩
    rw [← adj.unit_naturality f₁]; rw [← adj.unit_naturality f₂]
    congr 2
    rw [← cancel_epi (G.map s)]; rw [← G.map_comp]; rw [← G.map_comp]; rw [h]

/--
lemma `hasRightCalculusOfFractions` / 引理 `hasRightCalculusOfFractions`

English:
lemma hasRightCalculusOfFractions
  statement: (adj : F ⊣ G) (W : MorphismProperty C₁)
  proof: have := hasLeftCalculusOfFractions adj.op W.op hW.op (fun _ => hW' _)
  inferInstanceAs W.op.unop.HasRightCalculusOfFractions

中文:
引理 hasRightCalculusOfFractions
  结论: (adj : F ⊣ G) (W : MorphismProperty C₁)
  证明: have := hasLeftCalculusOfFractions adj.op W.op hW.op (fun _ => hW' _)
  inferInstanceAs W.op.unop.HasRightCalculusOfFractions

Depends on / 依赖: HasRightCalculusOfFractions, W.op, W.op.unop.HasRightCalculusOfFractions, adj.op, hW.op, hasLeftCalculusOfFractions
-/
lemma hasRightCalculusOfFractions (adj : F ⊣ G) (W : MorphismProperty C₁)
    [W.IsMultiplicative] (hW : W.IsInvertedBy G) (hW' : (W.functorCategory _) adj.counit) :
    W.HasRightCalculusOfFractions :=
  have := hasLeftCalculusOfFractions adj.op W.op hW.op (fun _ => hW' _)
  inferInstanceAs W.op.unop.HasRightCalculusOfFractions

section

variable [F.Full] [F.Faithful]

/--
lemma `isLocalization_leftAdjoint` / 引理 `isLocalization_leftAdjoint`

English:
lemma isLocalization_leftAdjoint
  proof: by
  let Φ : W.Localization ⥤ C₂ := Localization.lift _ hW W.Q
  let e : W.Q ⋙ Φ ≅ G := by apply Localization.fac
  have : IsIso (Functor.whiskerRight adj.unit W.Q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    exact Localization.inverts W.Q W _ (hW' X)
  exact Functor.IsLocalization.o

中文:
引理 isLocalization_leftAdjoint
  证明: by
  let Φ : W.Localization ⥤ C₂ := Localization.lift _ hW W.Q
  let e : W.Q ⋙ Φ ≅ G := by apply Localization.fac
  have : IsIso (Functor.whiskerRight adj.unit W.Q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    exact Localization.inverts W.Q W _ (hW' X)
  exact Functor.IsLocalization.o

Depends on / 依赖: Equivalence, Equivalence.mk, Functor, Functor.IsLocalization.of_equivalence_target, Functor.assoc, Functor.associator, Functor.whiskerRight, IsLocalization, Localization, Localization.fac, Localization.inverts, Localization.lift, Localization.liftNatIso, NatTrans, NatTrans.isIso_iff_isIso_app, W.Localization, W.Q.leftUnitor.symm, adj.unit, associator, inverts
-/
lemma isLocalization_leftAdjoint
    (adj : G ⊣ F) (W : MorphismProperty C₁)
    (hW : W.IsInvertedBy G) (hW' : (W.functorCategory C₁) adj.unit) :
    G.IsLocalization W := by
  let Φ : W.Localization ⥤ C₂ := Localization.lift _ hW W.Q
  let e : W.Q ⋙ Φ ≅ G := by apply Localization.fac
  have : IsIso (Functor.whiskerRight adj.unit W.Q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    exact Localization.inverts W.Q W _ (hW' X)
  exact Functor.IsLocalization.of_equivalence_target W.Q W _
    (Equivalence.mk Φ (F ⋙ W.Q)
      (Localization.liftNatIso W.Q W W.Q (G ⋙ F ⋙ W.Q) _ _
        (W.Q.leftUnitor.symm ≪≫ asIso (Functor.whiskerRight adj.unit W.Q) ≪≫
        Functor.associator _ _ _))
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e ≪≫ asIso adj.counit)) e

/--
lemma `isLocalization_rightAdjoint` / 引理 `isLocalization_rightAdjoint`

English:
lemma isLocalization_rightAdjoint
  proof: by
  simpa using isLocalization_leftAdjoint adj.op W.op hW.op (fun X => hW' X.unop)

中文:
引理 isLocalization_rightAdjoint
  证明: by
  simpa using isLocalization_leftAdjoint adj.op W.op hW.op (fun X => hW' X.unop)

Depends on / 依赖: W.op, X.unop, adj.op, hW.op, isLocalization_leftAdjoint
-/
lemma isLocalization_rightAdjoint
    (adj : F ⊣ G) (W : MorphismProperty C₁)
    (hW : W.IsInvertedBy G) (hW' : (W.functorCategory C₁) adj.counit) :
    G.IsLocalization W := by
  simpa using isLocalization_leftAdjoint adj.op W.op hW.op (fun X => hW' X.unop)

/--
lemma `functorCategory_inverseImage_isomorphisms_unit` / 引理 `functorCategory_inverseImage_isomorphisms_unit`

English:
lemma functorCategory_inverseImage_isomorphisms_unit
  given: (adj : G ⊣ F)
  proof: by
  intro
  simp only [Functor.id_obj, inverseImage_iff, isomorphisms.iff]
  infer_instance

中文:
引理 functorCategory_inverseImage_isomorphisms_unit
  条件: (adj : G ⊣ F)
  证明: by
  intro
  simp only [Functor.id_obj, inverseImage_iff, isomorphisms.iff]
  infer_instance

Depends on / 依赖: Functor, Functor.id_obj, id_obj, infer_instance, inverseImage_iff, isomorphisms, isomorphisms.iff
-/
lemma functorCategory_inverseImage_isomorphisms_unit (adj : G ⊣ F) :
    ((isomorphisms C₂).inverseImage G).functorCategory C₁ adj.unit := by
  intro
  simp only [Functor.id_obj, inverseImage_iff, isomorphisms.iff]
  infer_instance

/--
lemma `functorCategory_inverseImage_isomorphisms_counit` / 引理 `functorCategory_inverseImage_isomorphisms_counit`

English:
lemma functorCategory_inverseImage_isomorphisms_counit
  given: (adj : F ⊣ G)
  proof: by
  intro
  simp only [Functor.id_obj, inverseImage_iff, isomorphisms.iff]
  infer_instance

中文:
引理 functorCategory_inverseImage_isomorphisms_counit
  条件: (adj : F ⊣ G)
  证明: by
  intro
  simp only [Functor.id_obj, inverseImage_iff, isomorphisms.iff]
  infer_instance

Depends on / 依赖: Functor, Functor.id_obj, id_obj, infer_instance, inverseImage_iff, isomorphisms, isomorphisms.iff
-/
lemma functorCategory_inverseImage_isomorphisms_counit (adj : F ⊣ G) :
    ((isomorphisms C₂).inverseImage G).functorCategory C₁ adj.counit := by
  intro
  simp only [Functor.id_obj, inverseImage_iff, isomorphisms.iff]
  infer_instance

/--
lemma `isLocalization_leftAdjoint'` / 引理 `isLocalization_leftAdjoint'`

English:
lemma isLocalization_leftAdjoint'
  given: (adj : G ⊣ F)
  proof: adj.isLocalization_leftAdjoint _ (fun _ _ _ h => h)
    adj.functorCategory_inverseImage_isomorphisms_unit

中文:
引理 isLocalization_leftAdjoint'
  条件: (adj : G ⊣ F)
  证明: adj.isLocalization_leftAdjoint _ (fun _ _ _ h => h)
    adj.functorCategory_inverseImage_isomorphisms_unit

Depends on / 依赖: adj.functorCategory_inverseImage_isomorphisms_unit, adj.isLocalization_leftAdjoint, functorCategory_inverseImage_isomorphisms_unit, isLocalization_leftAdjoint
-/
lemma isLocalization_leftAdjoint' (adj : G ⊣ F) :
    G.IsLocalization ((isomorphisms C₂).inverseImage G) :=
  adj.isLocalization_leftAdjoint _ (fun _ _ _ h => h)
    adj.functorCategory_inverseImage_isomorphisms_unit

/--
lemma `isLocalization_rightAdjoint'` / 引理 `isLocalization_rightAdjoint'`

English:
lemma isLocalization_rightAdjoint'
  given: (adj : F ⊣ G)
  proof: adj.isLocalization_rightAdjoint _ (fun _ _ _ h => h)
    adj.functorCategory_inverseImage_isomorphisms_counit

中文:
引理 isLocalization_rightAdjoint'
  条件: (adj : F ⊣ G)
  证明: adj.isLocalization_rightAdjoint _ (fun _ _ _ h => h)
    adj.functorCategory_inverseImage_isomorphisms_counit

Depends on / 依赖: adj.functorCategory_inverseImage_isomorphisms_counit, adj.isLocalization_rightAdjoint, functorCategory_inverseImage_isomorphisms_counit, isLocalization_rightAdjoint
-/
lemma isLocalization_rightAdjoint' (adj : F ⊣ G) :
    G.IsLocalization ((isomorphisms C₂).inverseImage G) :=
  adj.isLocalization_rightAdjoint _ (fun _ _ _ h => h)
    adj.functorCategory_inverseImage_isomorphisms_counit

/--
lemma `hasLeftCalculusOfFractions'` / 引理 `hasLeftCalculusOfFractions'`

English:
lemma hasLeftCalculusOfFractions'
  given: (adj : G ⊣ F)
  proof: hasLeftCalculusOfFractions adj _ (fun _ _ _ h => h)
    adj.functorCategory_inverseImage_isomorphisms_unit

中文:
引理 hasLeftCalculusOfFractions'
  条件: (adj : G ⊣ F)
  证明: hasLeftCalculusOfFractions adj _ (fun _ _ _ h => h)
    adj.functorCategory_inverseImage_isomorphisms_unit

Depends on / 依赖: adj.functorCategory_inverseImage_isomorphisms_unit, functorCategory_inverseImage_isomorphisms_unit, hasLeftCalculusOfFractions
-/
lemma hasLeftCalculusOfFractions' (adj : G ⊣ F) :
    ((isomorphisms C₂).inverseImage G).HasLeftCalculusOfFractions :=
  hasLeftCalculusOfFractions adj _ (fun _ _ _ h => h)
    adj.functorCategory_inverseImage_isomorphisms_unit

/--
lemma `hasRightCalculusOfFractions'` / 引理 `hasRightCalculusOfFractions'`

English:
lemma hasRightCalculusOfFractions'
  given: (adj : F ⊣ G)
  proof: hasRightCalculusOfFractions adj _ (fun _ _ _ h => h)
    adj.functorCategory_inverseImage_isomorphisms_counit

中文:
引理 hasRightCalculusOfFractions'
  条件: (adj : F ⊣ G)
  证明: hasRightCalculusOfFractions adj _ (fun _ _ _ h => h)
    adj.functorCategory_inverseImage_isomorphisms_counit

Depends on / 依赖: adj.functorCategory_inverseImage_isomorphisms_counit, functorCategory_inverseImage_isomorphisms_counit, hasRightCalculusOfFractions
-/
lemma hasRightCalculusOfFractions' (adj : F ⊣ G) :
    ((isomorphisms C₂).inverseImage G).HasRightCalculusOfFractions :=
  hasRightCalculusOfFractions adj _ (fun _ _ _ h => h)
    adj.functorCategory_inverseImage_isomorphisms_counit

end

end Adjunction

end CategoryTheory
