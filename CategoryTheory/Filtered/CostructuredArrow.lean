/-
Copyright (c) 2024 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Filtered.OfColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Preserves.Grothendieck
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Inferring Filteredness from Filteredness of Costructured Arrow Categories

## References

* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Proposition 3.1.8

-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits CategoryTheory.Functor

section Small

variable {A : Type u₁} [SmallCategory A] {B : Type u₁} [SmallCategory B]
variable {T : Type u₁} [SmallCategory T]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `isFiltered_of_isFiltered_costructuredArrow_small` / 引理 `isFiltered_of_isFiltered_costructuredArrow_small`

English:
lemma isFiltered_of_isFiltered_costructuredArrow_small
  statement: (L : A ⥤ T) (R : B ⥤ T)
  proof: by
  refine isFiltered_of_nonempty_limit_colimit_to_colimit_limit fun J {_ _} F => ⟨?_⟩
  let R' := Grothendieck.pre (CostructuredArrow.functor L) R
  haveI : forall b, PreservesLimitsOfShape J
      (colim (J := (R ⋙ CostructuredArrow.functor L).obj b) (C := Type u₁)) := fun b => by
    simp only [

中文:
引理 isFiltered_of_isFiltered_costructuredArrow_small
  结论: (L : A ⥤ T) (R : B ⥤ T)
  证明: by
  refine isFiltered_of_nonempty_limit_colimit_to_colimit_limit fun J {_ _} F => ⟨?_⟩
  let R' := Grothendieck.pre (CostructuredArrow.functor L) R
  haveI : forall b, PreservesLimitsOfShape J
      (colim (J := (R ⋙ CostructuredArrow.functor L).obj b) (C := Type u₁)) := fun b => by
    simp only [
-/
private lemma isFiltered_of_isFiltered_costructuredArrow_small (L : A ⥤ T) (R : B ⥤ T)
    [IsFiltered B] [Final R] [forall b, IsFiltered (CostructuredArrow L (R.obj b))] : IsFiltered A := by
  refine isFiltered_of_nonempty_limit_colimit_to_colimit_limit fun J {_ _} F => ⟨?_⟩
  let R' := Grothendieck.pre (CostructuredArrow.functor L) R
  haveI : forall b, PreservesLimitsOfShape J
      (colim (J := (R ⋙ CostructuredArrow.functor L).obj b) (C := Type u₁)) := fun b => by
    simp only [comp_obj, CostructuredArrow.functor_obj, Cat.of_α]
    exact filtered_colim_preservesFiniteLimits
  refine lim.map ((colimitIsoColimitGrothendieck L F.flip).hom ≫
    (inv (colimit.pre (CostructuredArrow.grothendieckProj L ⋙ F.flip) R'))) ≫
    (colimitLimitIso (R' ⋙ CostructuredArrow.grothendieckProj L ⋙ F.flip).flip).inv ≫
    colim.map ?_ ≫
    colimit.pre _ R' ≫
    (colimitIsoColimitGrothendieck L (limit F)).inv
  exact (limitCompWhiskeringLeftIsoCompLimit F (R' ⋙ CostructuredArrow.grothendieckProj L)).hom

end Small

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
variable {T : Type u₃} [Category.{v₃} T]

/--
theorem `isFiltered_of_isFiltered_costructuredArrow` / 定理 `isFiltered_of_isFiltered_costructuredArrow`

English:
theorem isFiltered_of_isFiltered_costructuredArrow
  statement: (L : A ⥤ T) (R : B ⥤ T)
  proof: by
  let sA : A ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} A := AsSmall.equiv
  let sB : B ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} B := AsSmall.equiv
  let sT : T ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} T := AsSmall.equiv
  let sC : forall b, CostructuredArrow (sA.inverse ⋙ L ⋙ sT.functor)
      ((sB.inverse ⋙ R ⋙ sT.fu

中文:
定理 isFiltered_of_isFiltered_costructuredArrow
  结论: (L : A ⥤ T) (R : B ⥤ T)
  证明: by
  let sA : A ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} A := AsSmall.equiv
  let sB : B ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} B := AsSmall.equiv
  let sT : T ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} T := AsSmall.equiv
  let sC : forall b, CostructuredArrow (sA.inverse ⋙ L ⋙ sT.functor)
      ((sB.inverse ⋙ R ⋙ sT.fu

Depends on / 依赖: AsSmall, AsSmall.equiv, CostructuredArrow, CostructuredArrow.post, CostructuredArrow.pre, R.obj, asEquivalence, asEquivalence.symm, asEquivalence.trans, functor, inverse, sA.inverse, sB.inverse, sT.functor
-/
theorem isFiltered_of_isFiltered_costructuredArrow (L : A ⥤ T) (R : B ⥤ T)
    [IsFiltered B] [Final R] [forall b, IsFiltered (CostructuredArrow L (R.obj b))] : IsFiltered A := by
  let sA : A ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} A := AsSmall.equiv
  let sB : B ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} B := AsSmall.equiv
  let sT : T ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} T := AsSmall.equiv
  let sC : forall b, CostructuredArrow (sA.inverse ⋙ L ⋙ sT.functor)
      ((sB.inverse ⋙ R ⋙ sT.functor).obj ⟨b⟩) ≌ CostructuredArrow L (R.obj b) := fun b =>
    (CostructuredArrow.pre sA.inverse (L ⋙ sT.functor) _).asEquivalence.trans
      (CostructuredArrow.post L sT.functor _).asEquivalence.symm
  have : forall b, IsFiltered (CostructuredArrow _ ((sB.inverse ⋙ R ⋙ sT.functor).obj b)) :=
    fun b => IsFiltered.of_equivalence (sC b.1).symm
  have := isFiltered_of_isFiltered_costructuredArrow_small
    (sA.inverse ⋙ L ⋙ sT.functor) (sB.inverse ⋙ R ⋙ sT.functor)
  exact IsFiltered.of_equivalence sA.symm

end CategoryTheory
