/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Monad.Equalizer

/-!
# Adjoint lifting

This file gives two constructions for building right adjoints: the adjoint triangle theorem and the
adjoint lifting theorem.

The adjoint triangle theorem concerns a functor `F : B ⥤ A` with a right adjoint `U` such
that `η_X : X ⟶ UFX` is a regular mono. Then for any category `C` with equalizers of coreflexive
pairs, a functor `L : C ⥤ B` has a right adjoint if (and only if) the composite `L ⋙ F` does.
Note that the condition on `F` regarding `η_X` is automatically satisfied in the case when `F` is
a comonadic functor, giving the corollary: `isLeftAdjoint_triangle_lift_comonadic`, i.e. if `F` is
comonadic, `C` has coreflexive equalizers then `L : C ⥤ B` has a right adjoint provided `L ⋙ F`
does.

The adjoint lifting theorem says that given a commutative square of functors (up to isomorphism):

```
      Q
    A → B
  U ↓ ↓ V
    C → D
      L
```

where `V` is comonadic, `U` has a right adjoint, and `A` has coreflexive equalizers, then if `L` has
a right adjoint then `Q` has a right adjoint.

## Implementation

It is more convenient to prove this theorem by assuming we are given the explicit adjunction rather
than just a functor known to be a right adjoint. In docstrings, we write `(η, ε)` for the unit
and counit of the adjunction `adj₁ : F ⊣ U` and `(ι, δ)` for the unit and counit of the adjunction
`adj₂ : L ⋙ F ⊣ U'`.

This file has been adapted from `Mathlib/CategoryTheory/Adjunction/Lifting/Left.lean`.
Please try to keep them in sync.

## TODO

- Dualise to lift left adjoints through comonads (by reversing 2-cells).
- Investigate whether it is possible to give a more explicit description of the lifted adjoint,
  especially in the case when the isomorphism `comm` is `Iso.refl _`

## References
* https://ncatlab.org/nlab/show/adjoint+triangle+theorem
* https://ncatlab.org/nlab/show/adjoint+lifting+theorem
* Adjoint Lifting Theorems for Categories of Algebras (PT Johnstone, 1975)
* A unified approach to the lifting of adjoints (AJ Power, 1988)
-/

@[expose] public section


namespace CategoryTheory

open Category Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]

-- Hide implementation details in this namespace
namespace LiftRightAdjoint

variable {U : A ⥤ B} {F : B ⥤ A} (L : C ⥤ B) (U' : A ⥤ C)
variable (adj₁ : F ⊣ U) (adj₂ : L ⋙ F ⊣ U')

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `unitEqualises` / `unitEqualises` 的定义

English:
definition unitEqualises
  signature: (h : forall X : B, RegularMono (adj₁.unit.app X)) (X : B)
  body: Fork.IsLimit.mk' _ fun s => by
.mono have := fun Y => h Y
    refine ⟨((h X).lift' s.ι ?_).1, ?_, ?_⟩
    · rw [← cancel_mono (adj₁.unit.app ((h X).Z)), assoc, ← adj₁.unit_naturality (h _).left]
      dsimp only [Functor.comp_obj]
      have := s.condition
      dsimp only [Functor.comp_obj] at this
      rw [← assoc]; rw [← this]; rw [assoc]; rw [← U.map_comp]; rw [← F.map_comp]; rw [RegularMono.w]; rw [F.map_comp]; rw [U.map_comp]; rw [s.condition_assoc]; rw [assoc]; rw [← adj₁.unit_naturality (h _).right]
    · apply ((h X).lift' s.ι _).2
    · intro m hm
      rw [← cancel_mono (adj₁.unit.app X)]
      apply hm.trans ((h X).lift' s.ι _).2.symm

中文:
定义 unitEqualises
  签名: (h : 对任意 X : B, 正则单态射 (adj₁.unit.app X)) (X : B)
  定义体: Fork.IsLimit.mk' _ fun s => by
.mono have := fun Y => h Y
    refine ⟨((h X).lift' s.ι ?_).1, ?_, ?_⟩
    · rw [← cancel_mono (adj₁.unit.app ((h X).Z)), assoc, ← adj₁.unit_naturality (h _).left]
      dsimp only [Functor.comp_obj]
      have := s.condition
      dsimp only [Functor.comp_obj] at this
      rw [← assoc]; rw [← this]; rw [assoc]; rw [← U.map_comp]; rw [← F.map_comp]; rw [RegularMono.w]; rw [F.map_comp]; rw [U.map_comp]; rw [s.condition_assoc]; rw [assoc]; rw [← adj₁.unit_naturality (h _).right]
    · apply ((h X).lift' s.ι _).2
    · intro m hm
      rw [← cancel_mono (adj₁.unit.app X)]
      apply hm.trans ((h X).lift' s.ι _).2.symm

Depends on / 依赖: F.map_comp, Fork.IsLimit.mk, Functor, Functor.comp_obj, IsLimit, RegularMono, RegularMono.w, U.map_comp, cancel_mono, comp_obj, condition, condition_assoc, map_comp, s.condition, s.condition_assoc, unit.app, unit_naturality
-/
def unitEqualises (h : forall X : B, RegularMono (adj₁.unit.app X)) (X : B) :
    IsLimit (Fork.ofι (adj₁.unit.app X) (adj₁.unit_naturality _)) :=
  Fork.IsLimit.mk' _ fun s => by
.mono have := fun Y => h Y
    refine ⟨((h X).lift' s.ι ?_).1, ?_, ?_⟩
    · rw [← cancel_mono (adj₁.unit.app ((h X).Z)), assoc, ← adj₁.unit_naturality (h _).left]
      dsimp only [Functor.comp_obj]
      have := s.condition
      dsimp only [Functor.comp_obj] at this
      rw [← assoc]; rw [← this]; rw [assoc]; rw [← U.map_comp]; rw [← F.map_comp]; rw [RegularMono.w]; rw [F.map_comp]; rw [U.map_comp]; rw [s.condition_assoc]; rw [assoc]; rw [← adj₁.unit_naturality (h _).right]
    · apply ((h X).lift' s.ι _).2
    · intro m hm
      rw [← cancel_mono (adj₁.unit.app X)]
      apply hm.trans ((h X).lift' s.ι _).2.symm

/--
Definition of `otherMap` / `otherMap` 的定义

English:
definition otherMap
  signature: (X : B)
  body: adj₂.unit.app _ ≫ U'.map (F.map (adj₁.unit.app _ ≫ (U.map (adj₂.counit.app _))))

中文:
定义 otherMap
  签名: (X : B)
  定义体: adj₂.unit.app _ ≫ U'.map (F.map (adj₁.unit.app _ ≫ (U.map (adj₂.counit.app _))))

Depends on / 依赖: F.map, U.map, counit, counit.app, unit.app
-/
def otherMap (X : B) : U'.obj (F.obj X) ⟶ U'.obj (F.obj (U.obj (F.obj X))) :=
  adj₂.unit.app _ ≫ U'.map (F.map (adj₁.unit.app _ ≫ (U.map (adj₂.counit.app _))))

/-- `(U'Fη_X, otherMap X)` is a coreflexive pair: in particular if `C` has coreflexive equalizers
then this pair has an equalizer.
-/
instance (X : B) :
    IsCoreflexivePair (U'.map (F.map (adj₁.unit.app X))) (otherMap _ _ adj₁ adj₂ X) :=
  IsCoreflexivePair.mk' (U'.map (adj₁.counit.app (F.obj X)))
    (by simp [← Functor.map_comp])
    (by simp only [otherMap, assoc, ← Functor.map_comp]; simp)

variable [HasCoreflexiveEqualizers C]

/--
Definition of `constructRightAdjointObj` / `constructRightAdjointObj` 的定义

English:
definition constructRightAdjointObj
  signature: (Y : B)
  body: equalizer (U'.map (F.map (adj₁.unit.app Y))) (otherMap _ _ adj₁ adj₂ Y)

中文:
定义 constructRightAdjointObj
  签名: (Y : B)
  定义体: equalizer (U'.map (F.map (adj₁.unit.app Y))) (otherMap _ _ adj₁ adj₂ Y)

Depends on / 依赖: F.map, equalizer, otherMap, unit.app
-/
noncomputable def constructRightAdjointObj (Y : B) : C :=
  equalizer (U'.map (F.map (adj₁.unit.app Y))) (otherMap _ _ adj₁ adj₂ Y)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The homset equivalence which helps show that `L` is a left adjoint. -/
@[simps!]
/--
Definition of `constructRightAdjointEquiv` / `constructRightAdjointEquiv` 的定义

English:
definition constructRightAdjointEquiv
  signature: (h : forall X : B, RegularMono (adj₁.unit.app X)) (Y : C)
  body: calc
    (Y ⟶ constructRightAdjointObj _ _ adj₁ adj₂ X) ≃
        { f : Y ⟶ U'.obj (F.obj X) //
          f ≫ U'.map (F.map (adj₁.unit.app X)) = f ≫ (otherMap _ _ adj₁ adj₂ X) } :=
      Fork.IsLimit.homIso (limit.isLimit _) _
    _ ≃ { g : F.obj (L.obj Y) ⟶ F.obj X // F.map (adj₁.unit.app _≫ U.map g) =
        g ≫ F.map (adj₁.unit.app _) } := by
      apply (adj₂.homEquiv _ _).symm.subtypeEquiv _
      intro f
      rw [← (adj₂.homEquiv _ _).injective.eq_iff]; rw [eq_comm]; rw [otherMap]; rw [← adj₂.homEquiv_naturality_right_symm]; rw [adj₂.homEquiv_unit]; rw [← adj₂.unit_naturality_assoc]; rw [adj₂.homEquiv_counit]
      simp
    _ ≃ { z : L.obj Y ⟶ U.obj (F.obj X) //
        z ≫ U.map (F.map (adj₁.unit.app X)) = z ≫ adj₁.unit.app (U.obj (F.obj X)) } := by
      apply (adj₁.homEquiv _ _).subtypeEquiv
      intro g
      rw [← (adj₁.homEquiv _ _).injective.eq_iff]; rw [adj₁.homEquiv_unit]; rw [adj₁.homEquiv_unit]; rw [adj₁.homEquiv_unit]; rw [eq_comm]
      simp
    _ ≃ (L.obj Y ⟶ X) := (Fork.IsLimit.homIso (unitEqualises adj₁ h X) _).symm

中文:
定义 constructRightAdjointEquiv
  签名: (h : 对任意 X : B, 正则单态射 (adj₁.unit.app X)) (Y : C)
  定义体: calc
    (Y ⟶ constructRightAdjointObj _ _ adj₁ adj₂ X) ≃
        { f : Y ⟶ U'.obj (F.obj X) //
          f ≫ U'.map (F.map (adj₁.unit.app X)) = f ≫ (otherMap _ _ adj₁ adj₂ X) } :=
      Fork.IsLimit.homIso (limit.isLimit _) _
    _ ≃ { g : F.obj (L.obj Y) ⟶ F.obj X // F.map (adj₁.unit.app _≫ U.map g) =
        g ≫ F.map (adj₁.unit.app _) } := by
      apply (adj₂.homEquiv _ _).symm.subtypeEquiv _
      intro f
      rw [← (adj₂.homEquiv _ _).injective.eq_iff]; rw [eq_comm]; rw [otherMap]; rw [← adj₂.homEquiv_naturality_right_symm]; rw [adj₂.homEquiv_unit]; rw [← adj₂.unit_naturality_assoc]; rw [adj₂.homEquiv_counit]
      simp
    _ ≃ { z : L.obj Y ⟶ U.obj (F.obj X) //
        z ≫ U.map (F.map (adj₁.unit.app X)) = z ≫ adj₁.unit.app (U.obj (F.obj X)) } := by
      apply (adj₁.homEquiv _ _).subtypeEquiv
      intro g
      rw [← (adj₁.homEquiv _ _).injective.eq_iff]; rw [adj₁.homEquiv_unit]; rw [adj₁.homEquiv_unit]; rw [adj₁.homEquiv_unit]; rw [eq_comm]
      simp
    _ ≃ (L.obj Y ⟶ X) := (Fork.IsLimit.homIso (unitEqualises adj₁ h X) _).symm

Depends on / 依赖: F.map, F.obj, Fork.IsLimit.homIso, IsLimit, L.obj, U.map, constructRightAdjointObj, eq_comm, eq_iff, homEquiv, homEquiv_naturality_right_symm, homEquiv_u, homIso, injective, injective.eq_iff, isLimit, limit.isLimit, otherMap, subtypeEquiv, symm.subtypeEquiv
-/
noncomputable def constructRightAdjointEquiv (h : forall X : B, RegularMono (adj₁.unit.app X)) (Y : C)
    (X : B) : (Y ⟶ constructRightAdjointObj _ _ adj₁ adj₂ X) ≃ (L.obj Y ⟶ X) :=
  calc
    (Y ⟶ constructRightAdjointObj _ _ adj₁ adj₂ X) ≃
        { f : Y ⟶ U'.obj (F.obj X) //
          f ≫ U'.map (F.map (adj₁.unit.app X)) = f ≫ (otherMap _ _ adj₁ adj₂ X) } :=
      Fork.IsLimit.homIso (limit.isLimit _) _
    _ ≃ { g : F.obj (L.obj Y) ⟶ F.obj X // F.map (adj₁.unit.app _≫ U.map g) =
        g ≫ F.map (adj₁.unit.app _) } := by
      apply (adj₂.homEquiv _ _).symm.subtypeEquiv _
      intro f
      rw [← (adj₂.homEquiv _ _).injective.eq_iff]; rw [eq_comm]; rw [otherMap]; rw [← adj₂.homEquiv_naturality_right_symm]; rw [adj₂.homEquiv_unit]; rw [← adj₂.unit_naturality_assoc]; rw [adj₂.homEquiv_counit]
      simp
    _ ≃ { z : L.obj Y ⟶ U.obj (F.obj X) //
        z ≫ U.map (F.map (adj₁.unit.app X)) = z ≫ adj₁.unit.app (U.obj (F.obj X)) } := by
      apply (adj₁.homEquiv _ _).subtypeEquiv
      intro g
      rw [← (adj₁.homEquiv _ _).injective.eq_iff]; rw [adj₁.homEquiv_unit]; rw [adj₁.homEquiv_unit]; rw [adj₁.homEquiv_unit]; rw [eq_comm]
      simp
    _ ≃ (L.obj Y ⟶ X) := (Fork.IsLimit.homIso (unitEqualises adj₁ h X) _).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `constructRightAdjoint` / `constructRightAdjoint` 的定义

English:
definition constructRightAdjoint
  signature: (h : forall X : B, RegularMono (adj₁.unit.app X))
  body: by
  refine Adjunction.rightAdjointOfEquiv
    (fun X Y => (constructRightAdjointEquiv L _ adj₁ adj₂ h X Y).symm) ?_
  intro X Y Y' g h
  rw [constructRightAdjointEquiv_symm_apply]; rw [constructRightAdjointEquiv_symm_apply]; rw [Equiv.symm_apply_eq]; rw [Subtype.ext_iff]
  dsimp
  simp only [Adjunction.homEquiv_counit]
  erw [Fork.IsLimit.homIso_natural, Fork.IsLimit.homIso_natural]
  simp only [Fork.ofι_pt, Functor.map_comp, assoc, limit.cone_x]
  erw [adj₂.homEquiv_naturality_left, Equiv.rightInverse_symm]
  simp

中文:
定义 constructRightAdjoint
  签名: (h : 对任意 X : B, 正则单态射 (adj₁.unit.app X))
  定义体: by
  refine Adjunction.rightAdjointOfEquiv
    (fun X Y => (constructRightAdjointEquiv L _ adj₁ adj₂ h X Y).symm) ?_
  intro X Y Y' g h
  rw [constructRightAdjointEquiv_symm_apply]; rw [constructRightAdjointEquiv_symm_apply]; rw [Equiv.symm_apply_eq]; rw [Subtype.ext_iff]
  dsimp
  simp only [Adjunction.homEquiv_counit]
  erw [Fork.IsLimit.homIso_natural, Fork.IsLimit.homIso_natural]
  simp only [Fork.ofι_pt, Functor.map_comp, assoc, limit.cone_x]
  erw [adj₂.homEquiv_naturality_left, Equiv.rightInverse_symm]
  simp

Depends on / 依赖: Adjunction, Adjunction.homEquiv_counit, Adjunction.rightAdjointOfEquiv, Equiv.rightInverse_symm, Equiv.symm_apply_eq, Fork.IsLimit.homIso_natural, Fork.of, Functor, Functor.map_comp, IsLimit, Subtype, Subtype.ext_iff, cone_x, constructRightAdjointEquiv, constructRightAdjointEquiv_symm_apply, ext_iff, homEquiv_counit, homEquiv_naturality_left, homIso_natural, limit.cone_x
-/
noncomputable def constructRightAdjoint (h : forall X : B, RegularMono (adj₁.unit.app X)) : B ⥤ C := by
  refine Adjunction.rightAdjointOfEquiv
    (fun X Y => (constructRightAdjointEquiv L _ adj₁ adj₂ h X Y).symm) ?_
  intro X Y Y' g h
  rw [constructRightAdjointEquiv_symm_apply]; rw [constructRightAdjointEquiv_symm_apply]; rw [Equiv.symm_apply_eq]; rw [Subtype.ext_iff]
  dsimp
  simp only [Adjunction.homEquiv_counit]
  erw [Fork.IsLimit.homIso_natural, Fork.IsLimit.homIso_natural]
  simp only [Fork.ofι_pt, Functor.map_comp, assoc, limit.cone_x]
  erw [adj₂.homEquiv_naturality_left, Equiv.rightInverse_symm]
  simp

end LiftRightAdjoint

/--
lemma `isLeftAdjoint_triangle_lift` / 引理 `isLeftAdjoint_triangle_lift`

English:
lemma isLeftAdjoint_triangle_lift
  statement: {U : A ⥤ B} {F : B ⥤ A} (L : C ⥤ B) (adj₁ : F ⊣ U)
  proof: ⟨LiftRightAdjoint.constructRightAdjoint L _ adj₁ (Adjunction.ofIsLeftAdjoint _) h,
      ⟨Adjunction.adjunctionOfEquivRight _ _⟩⟩

中文:
引理 isLeftAdjoint_triangle_lift
  结论: {U : A ⥤ B} {F : B ⥤ A} (L : C ⥤ B) (adj₁ : F ⊣ U)
  证明: ⟨LiftRightAdjoint.constructRightAdjoint L _ adj₁ (Adjunction.ofIsLeftAdjoint _) h,
      ⟨Adjunction.adjunctionOfEquivRight _ _⟩⟩

Depends on / 依赖: Adjunction, Adjunction.adjunctionOfEquivRight, Adjunction.ofIsLeftAdjoint, Finite, Finite.of_injective, LiftRightAdjoint, LiftRightAdjoint.constructRightAdjoint, adjunctionOfEquivRight, constructRightAdjoint, ofIsLeftAdjoint, of_injective
-/
lemma isLeftAdjoint_triangle_lift {U : A ⥤ B} {F : B ⥤ A} (L : C ⥤ B) (adj₁ : F ⊣ U)
    (h : forall X, RegularMono (adj₁.unit.app X)) [HasCoreflexiveEqualizers C]
    [(L ⋙ F).IsLeftAdjoint] : L.IsLeftAdjoint where
  exists_rightAdjoint :=
    ⟨LiftRightAdjoint.constructRightAdjoint L _ adj₁ (Adjunction.ofIsLeftAdjoint _) h,
      ⟨Adjunction.adjunctionOfEquivRight _ _⟩⟩

/--
lemma `isLeftAdjoint_triangle_lift_comonadic` / 引理 `isLeftAdjoint_triangle_lift_comonadic`

English:
lemma isLeftAdjoint_triangle_lift_comonadic
  statement: (F : B ⥤ A) [ComonadicLeftAdjoint F] {L : C ⥤ B}
  proof: by
  let L' : _ ⥤ _ := L ⋙ Comonad.comparison (comonadicAdjunction F)
  rsuffices : L'.IsLeftAdjoint
  · let : (L' ⋙ (Comonad.comparison (comonadicAdjunction F)).inv).IsLeftAdjoint := by
      infer_instance
    refine ((Adjunction.ofIsLeftAdjoint
      (L' ⋙ (Comonad.comparison (comonadicAdjunction F)).inv)).ofNatIsoLeft ?_).isLeftAdjoint
    exact Functor.isoWhiskerLeft L (Comonad.comparison _).asEquivalence.unitIso.symm ≪≫ L.leftUnitor
  let : (L' ⋙ Comonad.forget (comonadicAdjunction F).toComonad).IsLeftAdjoint := by
    refine ((Adjunction.ofIsLeftAdjoint (L ⋙ F)).ofNatIsoLeft ?_).isLeftAdjoint
    exact Functor.isoWhiskerLeft L (Comonad.comparisonForget (comonadicAdjunction F)).symm
  let : forall X, RegularMono ((Comonad.adj (comonadicAdjunction F).toComonad).unit.app X) := by
    intro X
    simp only [Comonad.adj_unit]
    exact ⟨_, _, _, _, Comonad.beckCoalgebraEqualizer X⟩
  exact isLeftAdjoint_triangle_lift L' (Comonad.adj _) this

中文:
引理 isLeftAdjoint_triangle_lift_comonadic
  结论: (F : B ⥤ A) [余monadicLeftAdjoint F] {L : C ⥤ B}
  证明: by
  let L' : _ ⥤ _ := L ⋙ Comonad.comparison (comonadicAdjunction F)
  rsuffices : L'.IsLeftAdjoint
  · let : (L' ⋙ (Comonad.comparison (comonadicAdjunction F)).inv).IsLeftAdjoint := by
      infer_instance
    refine ((Adjunction.ofIsLeftAdjoint
      (L' ⋙ (Comonad.comparison (comonadicAdjunction F)).inv)).ofNatIsoLeft ?_).isLeftAdjoint
    exact Functor.isoWhiskerLeft L (Comonad.comparison _).asEquivalence.unitIso.symm ≪≫ L.leftUnitor
  let : (L' ⋙ Comonad.forget (comonadicAdjunction F).toComonad).IsLeftAdjoint := by
    refine ((Adjunction.ofIsLeftAdjoint (L ⋙ F)).ofNatIsoLeft ?_).isLeftAdjoint
    exact Functor.isoWhiskerLeft L (Comonad.comparisonForget (comonadicAdjunction F)).symm
  let : forall X, RegularMono ((Comonad.adj (comonadicAdjunction F).toComonad).unit.app X) := by
    intro X
    simp only [Comonad.adj_unit]
    exact ⟨_, _, _, _, Comonad.beckCoalgebraEqualizer X⟩
  exact isLeftAdjoint_triangle_lift L' (Comonad.adj _) this

Depends on / 依赖: Adjunction, Adjunction.ofIsLeftAdjoint, Comonad, Comonad.comparison, Comonad.forget, Finite, Finite.of_injective, Functor, Functor.isoWhiskerLeft, IsLeftAdjoint, L.leftUnitor, Subtype, Subtype.ext, asEquivalence, asEquivalence.unitIso.symm, comonadicAdjunction, comparison, forget, infer_instance, isLeftAdjoint
-/
lemma isLeftAdjoint_triangle_lift_comonadic (F : B ⥤ A) [ComonadicLeftAdjoint F] {L : C ⥤ B}
    [HasCoreflexiveEqualizers C] [(L ⋙ F).IsLeftAdjoint] : L.IsLeftAdjoint := by
  let L' : _ ⥤ _ := L ⋙ Comonad.comparison (comonadicAdjunction F)
  rsuffices : L'.IsLeftAdjoint
  · let : (L' ⋙ (Comonad.comparison (comonadicAdjunction F)).inv).IsLeftAdjoint := by
      infer_instance
    refine ((Adjunction.ofIsLeftAdjoint
      (L' ⋙ (Comonad.comparison (comonadicAdjunction F)).inv)).ofNatIsoLeft ?_).isLeftAdjoint
    exact Functor.isoWhiskerLeft L (Comonad.comparison _).asEquivalence.unitIso.symm ≪≫ L.leftUnitor
  let : (L' ⋙ Comonad.forget (comonadicAdjunction F).toComonad).IsLeftAdjoint := by
    refine ((Adjunction.ofIsLeftAdjoint (L ⋙ F)).ofNatIsoLeft ?_).isLeftAdjoint
    exact Functor.isoWhiskerLeft L (Comonad.comparisonForget (comonadicAdjunction F)).symm
  let : forall X, RegularMono ((Comonad.adj (comonadicAdjunction F).toComonad).unit.app X) := by
    intro X
    simp only [Comonad.adj_unit]
    exact ⟨_, _, _, _, Comonad.beckCoalgebraEqualizer X⟩
  exact isLeftAdjoint_triangle_lift L' (Comonad.adj _) this

variable {D : Type u₄}
variable [Category.{v₄} D]

/--
lemma `isLeftAdjoint_square_lift` / 引理 `isLeftAdjoint_square_lift`

English:
lemma isLeftAdjoint_square_lift
  statement: (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (L : C ⥤ D)
  proof: have := ((Adjunction.ofIsLeftAdjoint (U ⋙ L)).ofNatIsoLeft comm).isLeftAdjoint
  isLeftAdjoint_triangle_lift Q (Adjunction.ofIsLeftAdjoint V) h

中文:
引理 isLeftAdjoint_square_lift
  结论: (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (L : C ⥤ D)
  证明: have := ((Adjunction.ofIsLeftAdjoint (U ⋙ L)).ofNatIsoLeft comm).isLeftAdjoint
  isLeftAdjoint_triangle_lift Q (Adjunction.ofIsLeftAdjoint V) h

Depends on / 依赖: Adjunction, Adjunction.ofIsLeftAdjoint, isLeftAdjoint, isLeftAdjoint_triangle_lift, ofIsLeftAdjoint, ofNatIsoLeft
-/
lemma isLeftAdjoint_square_lift (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (L : C ⥤ D)
    (comm : U ⋙ L ≅ Q ⋙ V) [U.IsLeftAdjoint] [V.IsLeftAdjoint] [L.IsLeftAdjoint]
    (h : forall X, RegularMono ((Adjunction.ofIsLeftAdjoint V).unit.app X))
    [HasCoreflexiveEqualizers A] : Q.IsLeftAdjoint :=
  have := ((Adjunction.ofIsLeftAdjoint (U ⋙ L)).ofNatIsoLeft comm).isLeftAdjoint
  isLeftAdjoint_triangle_lift Q (Adjunction.ofIsLeftAdjoint V) h

/--
lemma `isLeftAdjoint_square_lift_comonadic` / 引理 `isLeftAdjoint_square_lift_comonadic`

English:
lemma isLeftAdjoint_square_lift_comonadic
  statement: (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (L : C ⥤ D)
  proof: have := ((Adjunction.ofIsLeftAdjoint (U ⋙ L)).ofNatIsoLeft comm).isLeftAdjoint
  isLeftAdjoint_triangle_lift_comonadic V

中文:
引理 isLeftAdjoint_square_lift_comonadic
  结论: (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (L : C ⥤ D)
  证明: have := ((Adjunction.ofIsLeftAdjoint (U ⋙ L)).ofNatIsoLeft comm).isLeftAdjoint
  isLeftAdjoint_triangle_lift_comonadic V

Depends on / 依赖: Adjunction, Adjunction.ofIsLeftAdjoint, isLeftAdjoint, isLeftAdjoint_triangle_lift_comonadic, ofIsLeftAdjoint, ofNatIsoLeft
-/
lemma isLeftAdjoint_square_lift_comonadic (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (L : C ⥤ D)
    (comm : U ⋙ L ≅ Q ⋙ V) [U.IsLeftAdjoint] [ComonadicLeftAdjoint V] [L.IsLeftAdjoint]
    [HasCoreflexiveEqualizers A] : Q.IsLeftAdjoint :=
  have := ((Adjunction.ofIsLeftAdjoint (U ⋙ L)).ofNatIsoLeft comm).isLeftAdjoint
  isLeftAdjoint_triangle_lift_comonadic V

end CategoryTheory
