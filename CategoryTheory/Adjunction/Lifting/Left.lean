/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Monad.Coequalizer

/-!
# Adjoint lifting

This file gives two constructions for building left adjoints: the adjoint triangle theorem and the
adjoint lifting theorem.

The adjoint triangle theorem concerns a functor `U : B ⥤ C` with a left adjoint `F` such
that `ε_X : FUX ⟶ X` is a regular epi. Then for any category `A` with coequalizers of reflexive
pairs, a functor `R : A ⥤ B` has a left adjoint if (and only if) the composite `R ⋙ U` does.
Note that the condition on `U` regarding `ε_X` is automatically satisfied in the case when `U` is
a monadic functor, giving the corollary: `isRightAdjoint_triangle_lift_monadic`, i.e. if `U` is
monadic, `A` has reflexive coequalizers then `R : A ⥤ B` has a left adjoint provided `R ⋙ U` does.

The adjoint lifting theorem says that given a commutative square of functors (up to isomorphism):

```
      Q
    A → B
  U ↓ ↓ V
    C → D
      R
```

where `V` is monadic, `U` has a left adjoint, and `A` has reflexive coequalizers, then if `R` has a
left adjoint then `Q` has a left adjoint.

## Implementation

It is more convenient to prove this theorem by assuming we are given the explicit adjunction rather
than just a functor known to be a right adjoint. In docstrings, we write `(η, ε)` for the unit
and counit of the adjunction `adj₁ : F ⊣ U` and `(ι, δ)` for the unit and counit of the adjunction
`adj₂ : F' ⊣ R ⋙ U`.

This file has been adapted to `Mathlib/CategoryTheory/Adjunction/Lifting/Right.lean`.
Please try to keep them in sync.

## TODO

- Dualise to lift right adjoints through monads (by reversing 2-cells).
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
namespace LiftLeftAdjoint

variable {U : B ⥤ C} {F : C ⥤ B} (R : A ⥤ B) (F' : C ⥤ A)
variable (adj₁ : F ⊣ U) (adj₂ : F' ⊣ R ⋙ U)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `counitCoequalises` / `counitCoequalises` 的定义

English:
definition counitCoequalises
  signature: (h : forall X : B, RegularEpi (adj₁.counit.app X)) (X : B)
  body: Cofork.IsColimit.mk' _ fun s => by
.epi have := fun Y => h Y
    refine ⟨((h X).desc' s.π ?_).1, ?_, ?_⟩
    · rw [← cancel_epi (adj₁.counit.app (h X).W)]
      rw [← adj₁.counit_naturality_assoc (h X).left]
      dsimp
      rw [← dsimp% s.condition]; rw [← F.map_comp_assoc]; rw [← U.map_comp]; rw 

中文:
定义 counitCoequalises
  签名: (h : 对任意 X : B, 正则满态射 (adj₁.counit.app X)) (X : B)
  定义体: Cofork.IsColimit.mk' _ fun s => by
.epi have := fun Y => h Y
    refine ⟨((h X).desc' s.π ?_).1, ?_, ?_⟩
    · rw [← cancel_epi (adj₁.counit.app (h X).W)]
      rw [← adj₁.counit_naturality_assoc (h X).left]
      dsimp
      rw [← dsimp% s.condition]; rw [← F.map_comp_assoc]; rw [← U.map_comp]; rw 

Depends on / 依赖: Cofork, Cofork.IsColimit.mk, F.map_comp_assoc, IsColimit, RegularEpi, RegularEpi.w, U.map_comp, cancel_epi, condition, counit, counit.app, counit_naturality_assoc, hm.trans, map_comp, map_comp_assoc, s.condition
-/
def counitCoequalises (h : forall X : B, RegularEpi (adj₁.counit.app X)) (X : B) :
    IsColimit (Cofork.ofπ (adj₁.counit.app X) (adj₁.counit_naturality _)) :=
  Cofork.IsColimit.mk' _ fun s => by
.epi have := fun Y => h Y
    refine ⟨((h X).desc' s.π ?_).1, ?_, ?_⟩
    · rw [← cancel_epi (adj₁.counit.app (h X).W)]
      rw [← adj₁.counit_naturality_assoc (h X).left]
      dsimp
      rw [← dsimp% s.condition]; rw [← F.map_comp_assoc]; rw [← U.map_comp]; rw [RegularEpi.w]; rw [U.map_comp]; rw [F.map_comp_assoc]; rw [s.condition]; rw [← adj₁.counit_naturality_assoc (h X).right]
    · apply ((h X).desc' s.π _).2
    · intro m hm
      rw [← cancel_epi (adj₁.counit.app X)]
      apply hm.trans ((h _).desc' s.π _).2.symm

/--
Definition of `otherMap` / `otherMap` 的定义

English:
definition otherMap
  signature: (X)
  body: F'.map (U.map (F.map (adj₂.unit.app _) ≫ adj₁.counit.app _)) ≫ adj₂.counit.app _

中文:
定义 otherMap
  签名: (X)
  定义体: F'.map (U.map (F.map (adj₂.unit.app _) ≫ adj₁.counit.app _)) ≫ adj₂.counit.app _

Depends on / 依赖: F.map, U.map, counit, counit.app, unit.app
-/
def otherMap (X) : F'.obj (U.obj (F.obj (U.obj X))) ⟶ F'.obj (U.obj X) :=
  F'.map (U.map (F.map (adj₂.unit.app _) ≫ adj₁.counit.app _)) ≫ adj₂.counit.app _

set_option backward.defeqAttrib.useBackward true in
/-- `(F'Uε_X, otherMap X)` is a reflexive pair: in particular if `A` has reflexive coequalizers then
this pair has a coequalizer.
-/
instance (X : B) :
    IsReflexivePair (F'.map (U.map (adj₁.counit.app X))) (otherMap _ _ adj₁ adj₂ X) :=
  IsReflexivePair.mk' (F'.map (adj₁.unit.app (U.obj X)))
    (by
      rw [← F'.map_comp]; rw [adj₁.right_triangle_components]
      apply F'.map_id)
    (by
      dsimp [otherMap]
      rw [← F'.map_comp_assoc]; rw [U.map_comp]; rw [adj₁.unit_naturality_assoc]; rw [adj₁.right_triangle_components]; rw [comp_id]; rw [adj₂.left_triangle_components])

variable [HasReflexiveCoequalizers A]

/--
Definition of `constructLeftAdjointObj` / `constructLeftAdjointObj` 的定义

English:
definition constructLeftAdjointObj
  signature: (Y : B)
  body: coequalizer (F'.map (U.map (adj₁.counit.app Y))) (otherMap _ _ adj₁ adj₂ Y)

#adaptation_note

中文:
定义 constructLeftAdjointObj
  签名: (Y : B)
  定义体: coequalizer (F'.map (U.map (adj₁.counit.app Y))) (otherMap _ _ adj₁ adj₂ Y)

#adaptation_note

Depends on / 依赖: U.map, coequalizer, counit, counit.app, otherMap
-/
noncomputable def constructLeftAdjointObj (Y : B) : A :=
  coequalizer (F'.map (U.map (adj₁.counit.app Y))) (otherMap _ _ adj₁ adj₂ Y)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The homset equivalence which helps show that `R` is a right adjoint. -/
@[simps!]
/--
Definition of `constructLeftAdjointEquiv` / `constructLeftAdjointEquiv` 的定义

English:
definition constructLeftAdjointEquiv
  signature: (h : forall X : B, RegularEpi (adj₁.counit.app X)) (Y : A)
  body: calc
    (constructLeftAdjointObj _ _ adj₁ adj₂ X ⟶ Y) ≃
        { f : F'.obj (U.obj X) ⟶ Y //
          F'.map (U.map (adj₁.counit.app X)) ≫ f = otherMap _ _ adj₁ adj₂ _ ≫ f } :=
      Cofork.IsColimit.homIso (colimit.isColimit _) _
    _ ≃ { g : U.obj X ⟶ U.obj (R.obj Y) //
          U.map (F.map 

中文:
定义 constructLeftAdjointEquiv
  签名: (h : 对任意 X : B, 正则满态射 (adj₁.counit.app X)) (Y : A)
  定义体: calc
    (constructLeftAdjointObj _ _ adj₁ adj₂ X ⟶ Y) ≃
        { f : F'.obj (U.obj X) ⟶ Y //
          F'.map (U.map (adj₁.counit.app X)) ≫ f = otherMap _ _ adj₁ adj₂ _ ≫ f } :=
      Cofork.IsColimit.homIso (colimit.isColimit _) _
    _ ≃ { g : U.obj X ⟶ U.obj (R.obj Y) //
          U.map (F.map 

Depends on / 依赖: Cofork, Cofork.IsColimit.homIso, F.map, IsColimit, R.obj, U.map, U.obj, colimit, colimit.isColimit, constructLeftAdjointObj, counit, counit.app, eq_comm, eq_iff, homEquiv, homEquiv_naturality_left, homIso, injective, injective.eq_iff, isColimit
-/
noncomputable def constructLeftAdjointEquiv (h : forall X : B, RegularEpi (adj₁.counit.app X)) (Y : A)
    (X : B) : (constructLeftAdjointObj _ _ adj₁ adj₂ X ⟶ Y) ≃ (X ⟶ R.obj Y) :=
  calc
    (constructLeftAdjointObj _ _ adj₁ adj₂ X ⟶ Y) ≃
        { f : F'.obj (U.obj X) ⟶ Y //
          F'.map (U.map (adj₁.counit.app X)) ≫ f = otherMap _ _ adj₁ adj₂ _ ≫ f } :=
      Cofork.IsColimit.homIso (colimit.isColimit _) _
    _ ≃ { g : U.obj X ⟶ U.obj (R.obj Y) //
          U.map (F.map g ≫ adj₁.counit.app _) = U.map (adj₁.counit.app _) ≫ g } := by
      apply (adj₂.homEquiv _ _).subtypeEquiv _
      intro f
      rw [← (adj₂.homEquiv _ _).injective.eq_iff]; rw [eq_comm]; rw [adj₂.homEquiv_naturality_left]; rw [otherMap]; rw [assoc]; rw [adj₂.homEquiv_naturality_left]; rw [← adj₂.counit_naturality]; rw [adj₂.homEquiv_naturality_left]; rw [adj₂.homEquiv_unit]; rw [adj₂.right_triangle_components]; rw [comp_id]; rw [Functor.comp_map]; rw [← U.map_comp]; rw [assoc]
      dsimp
      rw [← adj₁.counit_naturality]
      simp [dsimp% adj₂.homEquiv_unit _ _ f ]
    _ ≃ { z : F.obj (U.obj X) ⟶ R.obj Y // _ } := by
      apply (adj₁.homEquiv _ _).symm.subtypeEquiv
      intro g
      rw [← (adj₁.homEquiv _ _).symm.injective.eq_iff]; rw [adj₁.homEquiv_counit]; rw [adj₁.homEquiv_counit]; rw [adj₁.homEquiv_counit]; rw [F.map_comp]; rw [assoc]; rw [U.map_comp]; rw [F.map_comp]; rw [assoc]; rw [adj₁.counit_naturality]; rw [adj₁.counit_naturality_assoc]
      apply eq_comm
    _ ≃ (X ⟶ R.obj Y) := (Cofork.IsColimit.homIso (counitCoequalises adj₁ h X) _).symm

attribute [local simp] Adjunction.homEquiv_counit

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `constructLeftAdjoint` / `constructLeftAdjoint` 的定义

English:
definition constructLeftAdjoint
  signature: (h : forall X : B, RegularEpi (adj₁.counit.app X))
  body: by
  refine Adjunction.leftAdjointOfEquiv (fun X Y => constructLeftAdjointEquiv R _ adj₁ adj₂ h Y X) ?_
  intro X Y Y' g h
  rw [constructLeftAdjointEquiv_apply]; rw [constructLeftAdjointEquiv_apply]; rw [Equiv.symm_apply_eq]; rw [Subtype.ext_iff]
  dsimp
  -- This used to be `rw`, but we need `erw`

中文:
定义 constructLeftAdjoint
  签名: (h : 对任意 X : B, 正则满态射 (adj₁.counit.app X))
  定义体: by
  refine Adjunction.leftAdjointOfEquiv (fun X Y => constructLeftAdjointEquiv R _ adj₁ adj₂ h Y X) ?_
  intro X Y Y' g h
  rw [constructLeftAdjointEquiv_apply]; rw [constructLeftAdjointEquiv_apply]; rw [Equiv.symm_apply_eq]; rw [Subtype.ext_iff]
  dsimp
  -- This used to be `rw`, but we need `erw`

Depends on / 依赖: Adjunction, Adjunction.leftAdjointOfEquiv, Equiv.symm_apply_eq, Subtype, Subtype.ext_iff, constructLeftAdjointEquiv, constructLeftAdjointEquiv_apply, ext_iff, leftAdjointOfEquiv, symm_apply_eq
-/
noncomputable def constructLeftAdjoint (h : forall X : B, RegularEpi (adj₁.counit.app X)) : B ⥤ A := by
  refine Adjunction.leftAdjointOfEquiv (fun X Y => constructLeftAdjointEquiv R _ adj₁ adj₂ h Y X) ?_
  intro X Y Y' g h
  rw [constructLeftAdjointEquiv_apply]; rw [constructLeftAdjointEquiv_apply]; rw [Equiv.symm_apply_eq]; rw [Subtype.ext_iff]
  dsimp
  -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
  erw [Cofork.IsColimit.homIso_natural, Cofork.IsColimit.homIso_natural]
  erw [adj₂.homEquiv_naturality_right]
  simp_rw [Functor.comp_map]
  -- This used to be `simp`, but we need `cat_disch` after https://github.com/leanprover/lean4/pull/2644
  cat_disch

end LiftLeftAdjoint

/--
lemma `isRightAdjoint_triangle_lift` / 引理 `isRightAdjoint_triangle_lift`

English:
lemma isRightAdjoint_triangle_lift
  statement: {U : B ⥤ C} {F : C ⥤ B} (R : A ⥤ B) (adj₁ : F ⊣ U)
  proof: ⟨LiftLeftAdjoint.constructLeftAdjoint R _ adj₁ (Adjunction.ofIsRightAdjoint _) h,
      ⟨Adjunction.adjunctionOfEquivLeft _ _⟩⟩

中文:
引理 isRightAdjoint_triangle_lift
  结论: {U : B ⥤ C} {F : C ⥤ B} (R : A ⥤ B) (adj₁ : F ⊣ U)
  证明: ⟨LiftLeftAdjoint.constructLeftAdjoint R _ adj₁ (Adjunction.ofIsRightAdjoint _) h,
      ⟨Adjunction.adjunctionOfEquivLeft _ _⟩⟩

Depends on / 依赖: Adjunction, Adjunction.adjunctionOfEquivLeft, Adjunction.ofIsRightAdjoint, LiftLeftAdjoint, LiftLeftAdjoint.constructLeftAdjoint, adjunctionOfEquivLeft, constructLeftAdjoint, ofIsRightAdjoint
-/
lemma isRightAdjoint_triangle_lift {U : B ⥤ C} {F : C ⥤ B} (R : A ⥤ B) (adj₁ : F ⊣ U)
    (h : forall X : B, RegularEpi (adj₁.counit.app X)) [HasReflexiveCoequalizers A]
    [(R ⋙ U).IsRightAdjoint] : R.IsRightAdjoint where
  exists_leftAdjoint :=
    ⟨LiftLeftAdjoint.constructLeftAdjoint R _ adj₁ (Adjunction.ofIsRightAdjoint _) h,
      ⟨Adjunction.adjunctionOfEquivLeft _ _⟩⟩

/--
lemma `isRightAdjoint_triangle_lift_monadic` / 引理 `isRightAdjoint_triangle_lift_monadic`

English:
lemma isRightAdjoint_triangle_lift_monadic
  statement: (U : B ⥤ C) [MonadicRightAdjoint U] {R : A ⥤ B}
  proof: by
  let R' : A ⥤ _ := R ⋙ Monad.comparison (monadicAdjunction U)
  rsuffices : R'.IsRightAdjoint
  · let : (R' ⋙ (Monad.comparison (monadicAdjunction U)).inv).IsRightAdjoint := by
      infer_instance
    refine ((Adjunction.ofIsRightAdjoint
      (R' ⋙ (Monad.comparison (monadicAdjunction U)).inv)

中文:
引理 isRightAdjoint_triangle_lift_monadic
  结论: (U : B ⥤ C) [MonadicRightAdjoint U] {R : A ⥤ B}
  证明: by
  let R' : A ⥤ _ := R ⋙ Monad.comparison (monadicAdjunction U)
  rsuffices : R'.IsRightAdjoint
  · let : (R' ⋙ (Monad.comparison (monadicAdjunction U)).inv).IsRightAdjoint := by
      infer_instance
    refine ((Adjunction.ofIsRightAdjoint
      (R' ⋙ (Monad.comparison (monadicAdjunction U)).inv)

Depends on / 依赖: Adjunction, Adjunction.ofIsRightAdjoint, Functor, Functor.isoWhiskerLeft, IsRightAdjoint, Monad.comparison, Monad.forget, R.rightUnitor, asEquivalence, asEquivalence.unitIso.symm, comparison, forget, infer_instance, isRightAdjoint, isoWhiskerLeft, monadicAdjunction, ofIsRightAdjoint, ofNatIsoRight, rightUnitor, rsuffices
-/
lemma isRightAdjoint_triangle_lift_monadic (U : B ⥤ C) [MonadicRightAdjoint U] {R : A ⥤ B}
    [HasReflexiveCoequalizers A] [(R ⋙ U).IsRightAdjoint] : R.IsRightAdjoint := by
  let R' : A ⥤ _ := R ⋙ Monad.comparison (monadicAdjunction U)
  rsuffices : R'.IsRightAdjoint
  · let : (R' ⋙ (Monad.comparison (monadicAdjunction U)).inv).IsRightAdjoint := by
      infer_instance
    refine ((Adjunction.ofIsRightAdjoint
      (R' ⋙ (Monad.comparison (monadicAdjunction U)).inv)).ofNatIsoRight ?_).isRightAdjoint
    exact Functor.isoWhiskerLeft R (Monad.comparison _).asEquivalence.unitIso.symm ≪≫ R.rightUnitor
  let : (R' ⋙ Monad.forget (monadicAdjunction U).toMonad).IsRightAdjoint := by
    refine ((Adjunction.ofIsRightAdjoint (R ⋙ U)).ofNatIsoRight ?_).isRightAdjoint
    exact Functor.isoWhiskerLeft R (Monad.comparisonForget (monadicAdjunction U)).symm
  let : forall X, RegularEpi ((Monad.adj (monadicAdjunction U).toMonad).counit.app X) := by
    intro X
    simp only [Monad.adj_counit]
    exact ⟨_, _, _, _, Monad.beckAlgebraCoequalizer X⟩
  exact isRightAdjoint_triangle_lift R' (Monad.adj _) this

variable {D : Type u₄}
variable [Category.{v₄} D]

/--
lemma `isRightAdjoint_square_lift` / 引理 `isRightAdjoint_square_lift`

English:
lemma isRightAdjoint_square_lift
  statement: (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (R : C ⥤ D)
  proof: have := ((Adjunction.ofIsRightAdjoint (U ⋙ R)).ofNatIsoRight comm).isRightAdjoint
  isRightAdjoint_triangle_lift Q (Adjunction.ofIsRightAdjoint V) h

中文:
引理 isRightAdjoint_square_lift
  结论: (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (R : C ⥤ D)
  证明: have := ((Adjunction.ofIsRightAdjoint (U ⋙ R)).ofNatIsoRight comm).isRightAdjoint
  isRightAdjoint_triangle_lift Q (Adjunction.ofIsRightAdjoint V) h

Depends on / 依赖: Adjunction, Adjunction.ofIsRightAdjoint, isRightAdjoint, isRightAdjoint_triangle_lift, ofIsRightAdjoint, ofNatIsoRight
-/
lemma isRightAdjoint_square_lift (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (R : C ⥤ D)
    (comm : U ⋙ R ≅ Q ⋙ V) [U.IsRightAdjoint] [V.IsRightAdjoint] [R.IsRightAdjoint]
    (h : forall X, RegularEpi ((Adjunction.ofIsRightAdjoint V).counit.app X))
    [HasReflexiveCoequalizers A] :
    Q.IsRightAdjoint :=
  have := ((Adjunction.ofIsRightAdjoint (U ⋙ R)).ofNatIsoRight comm).isRightAdjoint
  isRightAdjoint_triangle_lift Q (Adjunction.ofIsRightAdjoint V) h

/--
lemma `isRightAdjoint_square_lift_monadic` / 引理 `isRightAdjoint_square_lift_monadic`

English:
lemma isRightAdjoint_square_lift_monadic
  statement: (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (R : C ⥤ D)
  proof: have := ((Adjunction.ofIsRightAdjoint (U ⋙ R)).ofNatIsoRight comm).isRightAdjoint
  isRightAdjoint_triangle_lift_monadic V

中文:
引理 isRightAdjoint_square_lift_monadic
  结论: (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (R : C ⥤ D)
  证明: have := ((Adjunction.ofIsRightAdjoint (U ⋙ R)).ofNatIsoRight comm).isRightAdjoint
  isRightAdjoint_triangle_lift_monadic V

Depends on / 依赖: Adjunction, Adjunction.ofIsRightAdjoint, isRightAdjoint, isRightAdjoint_triangle_lift_monadic, ofIsRightAdjoint, ofNatIsoRight
-/
lemma isRightAdjoint_square_lift_monadic (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (R : C ⥤ D)
    (comm : U ⋙ R ≅ Q ⋙ V) [U.IsRightAdjoint] [MonadicRightAdjoint V] [R.IsRightAdjoint]
    [HasReflexiveCoequalizers A] : Q.IsRightAdjoint :=
  have := ((Adjunction.ofIsRightAdjoint (U ⋙ R)).ofNatIsoRight comm).isRightAdjoint
  isRightAdjoint_triangle_lift_monadic V

end CategoryTheory
