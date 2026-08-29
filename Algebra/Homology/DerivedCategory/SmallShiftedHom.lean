/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.CategoryTheory.Localization.SmallShiftedHom

/-!
# Cohomology of `HomComplex` and morphisms in the derived category

Let `K` and `L` be two cochain complexes in an abelian category `C`.
Given a class `x : HomComplex.CohomologyClass K L n`, we construct an
element in the type
`SmallShiftedHom (HomologicalComplex.quasiIso C (.up ℤ)) K L n`, and
compute its image as a morphism `Q.obj K ⟶ (Q.obj L)⟦n⟧` in the
derived category when `x` is given as the class of a cocycle.

-/

@[expose] public section

universe w v u

open CategoryTheory Localization

namespace CochainComplex.HomComplex.CohomologyClass

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L : CochainComplex C Int} {n : Int}
  [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up Int)) Int K L]

/--
Definition of `toSmallShiftedHom` / `toSmallShiftedHom` 的定义

English:
definition toSmallShiftedHom
  signature: (x : CohomologyClass K L n)
  body: Quotient.lift (fun y => SmallShiftedHom.mk _ (Cocycle.equivHomShift.symm y)) (by
    let := HasDerivedCategory.standard C
    intro y₁ y₂ h
    refine (SmallShiftedHom.equiv _ DerivedCategory.Q).injective ?_
    simp only [SmallShiftedHom.equiv_mk, ShiftedHom.map]
    rw [cancel_mono]; rw [DerivedCa

中文:
定义 toSmallShiftedHom
  签名: (x : CohomologyClass K L n)
  定义体: Quotient.lift (fun y => SmallShiftedHom.mk _ (Cocycle.equivHomShift.symm y)) (by
    let := HasDerivedCategory.standard C
    intro y₁ y₂ h
    refine (SmallShiftedHom.equiv _ DerivedCategory.Q).injective ?_
    simp only [SmallShiftedHom.equiv_mk, ShiftedHom.map]
    rw [cancel_mono]; rw [DerivedCa

Depends on / 依赖: Cocycle, Cocycle.equivHomShift.symm, DerivedCategory, DerivedCategory.Q, DerivedCategory.Q_map_eq_of_homotopy, HasDerivedCategory, HasDerivedCategory.standard, HomotopyCategory, HomotopyCategory.homotopyOfEq, Q_map_eq_of_homotopy, Quotient, Quotient.lift, Quotient.sound, ShiftedHom, ShiftedHom.map, SmallShiftedHom, SmallShiftedHom.equiv, SmallShiftedHom.equiv_mk, SmallShiftedHom.mk, cancel_mono
-/
noncomputable def toSmallShiftedHom (x : CohomologyClass K L n) :
    SmallShiftedHom.{w} (HomologicalComplex.quasiIso C (.up Int)) K L n :=
  Quotient.lift (fun y => SmallShiftedHom.mk _ (Cocycle.equivHomShift.symm y)) (by
    let := HasDerivedCategory.standard C
    intro y₁ y₂ h
    refine (SmallShiftedHom.equiv _ DerivedCategory.Q).injective ?_
    simp only [SmallShiftedHom.equiv_mk, ShiftedHom.map]
    rw [cancel_mono]; rw [DerivedCategory.Q_map_eq_of_homotopy]
    apply HomotopyCategory.homotopyOfEq
    rw [← toHom_mk]; rw [← toHom_mk]
    congr 1
    exact Quotient.sound h) x

/--
lemma `toSmallShiftedHom_mk` / 引理 `toSmallShiftedHom_mk`

English:
lemma toSmallShiftedHom_mk
  given: (x : Cocycle K L n)
  proof: rfl

@[simp]

中文:
引理 toSmallShiftedHom_mk
  条件: (x : Cocycle K L n)
  证明: rfl

@[simp]
-/
lemma toSmallShiftedHom_mk (x : Cocycle K L n) :
    (mk x).toSmallShiftedHom =
      SmallShiftedHom.mk _ (Cocycle.equivHomShift.symm x) := rfl

@[simp]
/--
lemma `equiv_toSmallShiftedHom_mk` / 引理 `equiv_toSmallShiftedHom_mk`

English:
lemma equiv_toSmallShiftedHom_mk
  given: [HasDerivedCategory C] (x : Cocycle K L n)
  proof: by
  simp [toSmallShiftedHom_mk]

中文:
引理 equiv_toSmallShiftedHom_mk
  条件: [HasDerivedCategory C] (x : Cocycle K L n)
  证明: by
  simp [toSmallShiftedHom_mk]

Depends on / 依赖: toSmallShiftedHom_mk
-/
lemma equiv_toSmallShiftedHom_mk [HasDerivedCategory C] (x : Cocycle K L n) :
    SmallShiftedHom.equiv _ DerivedCategory.Q (mk x).toSmallShiftedHom =
      ShiftedHom.map (Cocycle.equivHomShift.symm x) DerivedCategory.Q := by
  simp [toSmallShiftedHom_mk]

end CochainComplex.HomComplex.CohomologyClass
