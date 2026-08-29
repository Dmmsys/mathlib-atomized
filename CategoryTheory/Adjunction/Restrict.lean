/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.HomCongr
/-!

# Restricting adjunctions

`Adjunction.restrictFullyFaithful` shows that an adjunction can be restricted along fully faithful
inclusions.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

universe v₁ v₂ u₁ u₂ v₃ v₄ u₃ u₄

open Category Opposite

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {C' : Type u₃} [Category.{v₃} C']
variable {D' : Type u₄} [Category.{v₄} D']
variable {iC : C ⥤ C'} {iD : D ⥤ D'}
  {L' : C' ⥤ D'} {R' : D' ⥤ C'} (adj : L' ⊣ R') (hiC : iC.FullyFaithful) (hiD : iD.FullyFaithful)
  {L : C ⥤ D} {R : D ⥤ C} (comm1 : iC ⋙ L' ≅ L ⋙ iD) (comm2 : iD ⋙ R' ≅ R ⋙ iC)

attribute [local simp] homEquiv_unit homEquiv_counit

/--
Definition of `restrictFullyFaithful` / `restrictFullyFaithful` 的定义

English:
definition restrictFullyFaithful
  signature: : L ⊣ R
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        calc
          (L.obj X ⟶ Y) ≃ (iD.obj (L.obj X) ⟶ iD.obj Y) := hiD.homEquiv
          _ ≃ (L'.obj (iC.obj X) ⟶ iD.obj Y) := Iso.homCongr (comm1.symm.app X) (Iso.refl _)
          _ ≃ (iC.obj X ⟶ R'.obj (iD.obj Y)) := adj.homEquiv _ _
          _ ≃ (iC.obj X ⟶ iC.obj (R.obj Y)) := Iso.homCongr (Iso.refl _) (comm2.app Y)
          _ ≃ (X ⟶ R.obj Y) := hiC.homEquiv.symm

      homEquiv_naturality_left_symm := fun {X' X Y} f g => by
        apply hiD.map_injective
        simpa [Trans.trans] using (comm1.inv.naturality_assoc f _).symm
      homEquiv_naturality_right := fun {X Y' Y} f g => by
        apply hiC.map_injective
        suffices R'.map (iD.map g) ≫ comm2.hom.app Y = comm2.hom.app Y' ≫ iC.map (R.map g) by
          simp [Trans.trans, this]
        apply comm2.hom.naturality g }

中文:
定义 restrictFullyFaithful
  签名: : L ⊣ R
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        calc
          (L.obj X ⟶ Y) ≃ (iD.obj (L.obj X) ⟶ iD.obj Y) := hiD.homEquiv
          _ ≃ (L'.obj (iC.obj X) ⟶ iD.obj Y) := Iso.homCongr (comm1.symm.app X) (Iso.refl _)
          _ ≃ (iC.obj X ⟶ R'.obj (iD.obj Y)) := adj.homEquiv _ _
          _ ≃ (iC.obj X ⟶ iC.obj (R.obj Y)) := Iso.homCongr (Iso.refl _) (comm2.app Y)
          _ ≃ (X ⟶ R.obj Y) := hiC.homEquiv.symm

      homEquiv_naturality_left_symm := fun {X' X Y} f g => by
        apply hiD.map_injective
        simpa [Trans.trans] using (comm1.inv.naturality_assoc f _).symm
      homEquiv_naturality_right := fun {X Y' Y} f g => by
        apply hiC.map_injective
        suffices R'.map (iD.map g) ≫ comm2.hom.app Y = comm2.hom.app Y' ≫ iC.map (R.map g) by
          simp [Trans.trans, this]
        apply comm2.hom.naturality g }

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, Iso.homCongr, Iso.refl, L.obj, R.obj, adj.homEquiv, comm1.symm.app, comm2.app, hiC.homEquiv.symm, hiD.homEquiv, homCongr, homEquiv, iC.obj, iD.obj, mkOfHomEquiv
-/
noncomputable def restrictFullyFaithful : L ⊣ R :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        calc
          (L.obj X ⟶ Y) ≃ (iD.obj (L.obj X) ⟶ iD.obj Y) := hiD.homEquiv
          _ ≃ (L'.obj (iC.obj X) ⟶ iD.obj Y) := Iso.homCongr (comm1.symm.app X) (Iso.refl _)
          _ ≃ (iC.obj X ⟶ R'.obj (iD.obj Y)) := adj.homEquiv _ _
          _ ≃ (iC.obj X ⟶ iC.obj (R.obj Y)) := Iso.homCongr (Iso.refl _) (comm2.app Y)
          _ ≃ (X ⟶ R.obj Y) := hiC.homEquiv.symm

      homEquiv_naturality_left_symm := fun {X' X Y} f g => by
        apply hiD.map_injective
        simpa [Trans.trans] using (comm1.inv.naturality_assoc f _).symm
      homEquiv_naturality_right := fun {X Y' Y} f g => by
        apply hiC.map_injective
        suffices R'.map (iD.map g) ≫ comm2.hom.app Y = comm2.hom.app Y' ≫ iC.map (R.map g) by
          simp [Trans.trans, this]
        apply comm2.hom.naturality g }

set_option backward.defeqAttrib.useBackward true in
@[simp, reassoc]
/--
lemma `map_restrictFullyFaithful_unit_app` / 引理 `map_restrictFullyFaithful_unit_app`

English:
lemma map_restrictFullyFaithful_unit_app
  given: (X : C)
  proof: by
  simp [restrictFullyFaithful]

中文:
引理 map_restrictFullyFaithful_unit_app
  条件: (X : C)
  证明: by
  simp [restrictFullyFaithful]

Depends on / 依赖: restrictFullyFaithful
-/
lemma map_restrictFullyFaithful_unit_app (X : C) :
    iC.map ((adj.restrictFullyFaithful hiC hiD comm1 comm2).unit.app X) =
    adj.unit.app (iC.obj X) ≫ R'.map (comm1.hom.app X) ≫ comm2.hom.app (L.obj X) := by
  simp [restrictFullyFaithful]

set_option backward.defeqAttrib.useBackward true in
@[simp, reassoc]
/--
lemma `map_restrictFullyFaithful_counit_app` / 引理 `map_restrictFullyFaithful_counit_app`

English:
lemma map_restrictFullyFaithful_counit_app
  given: (X : D)
  proof: by
  dsimp [restrictFullyFaithful]
  simp

中文:
引理 map_restrictFullyFaithful_counit_app
  条件: (X : D)
  证明: by
  dsimp [restrictFullyFaithful]
  simp

Depends on / 依赖: restrictFullyFaithful
-/
lemma map_restrictFullyFaithful_counit_app (X : D) :
    iD.map ((adj.restrictFullyFaithful hiC hiD comm1 comm2).counit.app X) =
    comm1.inv.app (R.obj X) ≫ L'.map (comm2.inv.app X) ≫ adj.counit.app (iD.obj X) := by
  dsimp [restrictFullyFaithful]
  simp

/--
lemma `restrictFullyFaithful_homEquiv_apply` / 引理 `restrictFullyFaithful_homEquiv_apply`

English:
lemma restrictFullyFaithful_homEquiv_apply
  given: {X : C} {Y : D} (f : L.obj X ⟶ Y)
  proof: by
  -- This proof was just `simp [restrictFullyFaithful]` before https://github.com/leanprover-community/mathlib4/pull/16317
  apply hiC.map_injective
  simp only [homEquiv_apply, Functor.map_comp, map_restrictFullyFaithful_unit_app,
    Functor.id_obj, assoc, Functor.FullyFaithful.map_preimage]
  congr 2
  exact (comm2.hom.naturality _).symm

中文:
引理 restrictFullyFaithful_homEquiv_apply
  条件: {X : C} {Y : D} (f : L.obj X ⟶ Y)
  证明: by
  -- This proof was just `simp [restrictFullyFaithful]` before https://github.com/leanprover-community/mathlib4/pull/16317
  apply hiC.map_injective
  simp only [homEquiv_apply, Functor.map_comp, map_restrictFullyFaithful_unit_app,
    Functor.id_obj, assoc, Functor.FullyFaithful.map_preimage]
  congr 2
  exact (comm2.hom.naturality _).symm
-/
lemma restrictFullyFaithful_homEquiv_apply {X : C} {Y : D} (f : L.obj X ⟶ Y) :
    (adj.restrictFullyFaithful hiC hiD comm1 comm2).homEquiv X Y f =
      hiC.preimage (adj.unit.app (iC.obj X) ≫ R'.map (comm1.hom.app X) ≫
        R'.map (iD.map f) ≫ comm2.hom.app Y) := by
  -- This proof was just `simp [restrictFullyFaithful]` before https://github.com/leanprover-community/mathlib4/pull/16317
  apply hiC.map_injective
  simp only [homEquiv_apply, Functor.map_comp, map_restrictFullyFaithful_unit_app,
    Functor.id_obj, assoc, Functor.FullyFaithful.map_preimage]
  congr 2
  exact (comm2.hom.naturality _).symm

end CategoryTheory.Adjunction
