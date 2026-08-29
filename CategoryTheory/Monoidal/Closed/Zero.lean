/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
public import Mathlib.CategoryTheory.PUnit
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# A Cartesian closed category with zero object is trivial

A Cartesian closed category with zero object is trivial: it is equivalent to the category with one
object and one morphism.

## References

* https://mathoverflow.net/a/136480

-/

@[expose] public section


universe w v u

noncomputable section

namespace CategoryTheory

open Category Limits MonoidalCategory

variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]

open scoped CartesianClosed

/-- If a Cartesian closed category has an initial object which is isomorphic to the terminal object,
then each homset has exactly one element.
-/
@[instance_reducible]
/--
Definition of `uniqueHomsetOfInitialIsoUnit` / `uniqueHomsetOfInitialIsoUnit` 的定义

English:
definition uniqueHomsetOfInitialIsoUnit
  signature: [HasInitial C] (i : ⊥_ C ≅ 𝟙_ C) (X Y : C)
  body: Equiv.unique
    calc
      (X ⟶ Y) ≃ (X otimes 𝟙_ C ⟶ Y) := Iso.homCongr (rightUnitor _).symm (Iso.refl _)
      _ ≃ (X otimes ⊥_ C ⟶ Y) := (Iso.homCongr ((Iso.refl _) otimesᵢ i.symm) (Iso.refl _))
      _ ≃ (⊥_ C ⟶ Y ^^ X) := (ihom.adjunction _).homEquiv _ _

中文:
定义 uniqueHomsetOfInitialIsoUnit
  签名: [HasInitial C] (i : ⊥_ C ≅ 𝟙_ C) (X Y : C)
  定义体: Equiv.unique
    calc
      (X ⟶ Y) ≃ (X otimes 𝟙_ C ⟶ Y) := Iso.homCongr (rightUnitor _).symm (Iso.refl _)
      _ ≃ (X otimes ⊥_ C ⟶ Y) := (Iso.homCongr ((Iso.refl _) otimesᵢ i.symm) (Iso.refl _))
      _ ≃ (⊥_ C ⟶ Y ^^ X) := (ihom.adjunction _).homEquiv _ _

Depends on / 依赖: Equiv.unique, Iso.homCongr, Iso.refl, adjunction, homCongr, homEquiv, i.symm, ihom.adjunction, otimes, rightUnitor, unique
-/
def uniqueHomsetOfInitialIsoUnit [HasInitial C] (i : ⊥_ C ≅ 𝟙_ C) (X Y : C) : Unique (X ⟶ Y) :=
Equiv.unique
    calc
      (X ⟶ Y) ≃ (X otimes 𝟙_ C ⟶ Y) := Iso.homCongr (rightUnitor _).symm (Iso.refl _)
      _ ≃ (X otimes ⊥_ C ⟶ Y) := (Iso.homCongr ((Iso.refl _) otimesᵢ i.symm) (Iso.refl _))
      _ ≃ (⊥_ C ⟶ Y ^^ X) := (ihom.adjunction _).homEquiv _ _

open scoped ZeroObject

/-- If a Cartesian closed category has a zero object, each homset has exactly one element. -/
@[instance_reducible]
/--
Definition of `uniqueHomsetOfZero` / `uniqueHomsetOfZero` 的定义

English:
definition uniqueHomsetOfZero
  signature: [HasZeroObject C] (X Y : C)
  body: by
  haveI : HasInitial C := HasZeroObject.hasInitial
  apply uniqueHomsetOfInitialIsoUnit _ X Y
  refine ⟨default, (default : 𝟙_ C ⟶ 0) ≫ default, ?_, ?_⟩ <;> simp [eq_iff_true_of_subsingleton]

中文:
定义 uniqueHomsetOfZero
  签名: [有ZeroObject C] (X Y : C)
  定义体: by
  haveI : HasInitial C := HasZeroObject.hasInitial
  apply uniqueHomsetOfInitialIsoUnit _ X Y
  refine ⟨default, (default : 𝟙_ C ⟶ 0) ≫ default, ?_, ?_⟩ <;> simp [eq_iff_true_of_subsingleton]

Depends on / 依赖: HasInitial, HasZeroObject, HasZeroObject.hasInitial, eq_iff_true_of_subsingleton, hasInitial, uniqueHomsetOfInitialIsoUnit
-/
def uniqueHomsetOfZero [HasZeroObject C] (X Y : C) : Unique (X ⟶ Y) := by
  haveI : HasInitial C := HasZeroObject.hasInitial
  apply uniqueHomsetOfInitialIsoUnit _ X Y
  refine ⟨default, (default : 𝟙_ C ⟶ 0) ≫ default, ?_, ?_⟩ <;> simp [eq_iff_true_of_subsingleton]

attribute [local instance] uniqueHomsetOfZero

/--
Definition of `equivPUnit` / `equivPUnit` 的定义

English:
definition equivPUnit
  signature: [HasZeroObject C]
  body: Functor.star C
  inverse := Functor.fromPUnit 0
  unitIso := NatIso.ofComponents
      (fun X =>
        { hom := default
          inv := default })
      fun _ => Subsingleton.elim _ _
  counitIso := Functor.punitExt _ _

中文:
定义 equivPUnit
  签名: [有ZeroObject C]
  定义体: Functor.star C
  inverse := Functor.fromPUnit 0
  unitIso := NatIso.ofComponents
      (fun X =>
        { hom := default
          inv := default })
      fun _ => Subsingleton.elim _ _
  counitIso := Functor.punitExt _ _

Depends on / 依赖: Functor, Functor.star
-/
def equivPUnit [HasZeroObject C] : C ≌ Discrete PUnit.{w + 1} where
  functor := Functor.star C
  inverse := Functor.fromPUnit 0
  unitIso := NatIso.ofComponents
      (fun X =>
        { hom := default
          inv := default })
      fun _ => Subsingleton.elim _ _
  counitIso := Functor.punitExt _ _

end CategoryTheory
