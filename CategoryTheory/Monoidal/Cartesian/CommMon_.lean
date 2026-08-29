/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

/-!
# Yoneda embedding of `CommMon C`
-/

public section

assert_not_exists MonoidWithZero

open CategoryTheory MonoidalCategory Limits Opposite CartesianMonoidalCategory MonObj

namespace CategoryTheory
universe w v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C] {X : C}

variable (X) in
/--
lemma `IsCommMonObj.ofRepresentableBy` / 引理 `IsCommMonObj.ofRepresentableBy`

English:
lemma IsCommMonObj.ofRepresentableBy
  given: (F : Cᵒᵖ ⥤ CommMonCat) (α : (F ⋙ forget _).RepresentableBy X)
  proof: .ofRepresentableBy X (F ⋙ forget₂ CommMonCat MonCat) α
    IsCommMonObj X := by
  let : MonObj X := .ofRepresentableBy X (F ⋙ forget₂ CommMonCat MonCat) α
  have : μ = α.homEquiv'.symm (α.homEquiv' (fst X X) * α.homEquiv' (snd X X)) := rfl
  constructor
  simp_rw [this, ← α.homEquiv'.apply_eq_iff_eq

中文:
引理 IsCommMonObj.ofRepresentableBy
  条件: (F : Cᵒᵖ ⥤ CommMonCat) (α : (F ⋙ forget _).RepresentableBy X)
  证明: .ofRepresentableBy X (F ⋙ forget₂ CommMonCat MonCat) α
    IsCommMonObj X := by
  let : MonObj X := .ofRepresentableBy X (F ⋙ forget₂ CommMonCat MonCat) α
  have : μ = α.homEquiv'.symm (α.homEquiv' (fst X X) * α.homEquiv' (snd X X)) := rfl
  constructor
  simp_rw [this, ← α.homEquiv'.apply_eq_iff_eq

Depends on / 依赖: CommMonCat, MonCat, ofRepresentableBy
-/
lemma IsCommMonObj.ofRepresentableBy (F : Cᵒᵖ ⥤ CommMonCat) (α : (F ⋙ forget _).RepresentableBy X) :
    letI : MonObj X := .ofRepresentableBy X (F ⋙ forget₂ CommMonCat MonCat) α
    IsCommMonObj X := by
  let : MonObj X := .ofRepresentableBy X (F ⋙ forget₂ CommMonCat MonCat) α
  have : μ = α.homEquiv'.symm (α.homEquiv' (fst X X) * α.homEquiv' (snd X X)) := rfl
  constructor
  simp_rw [this, ← α.homEquiv'.apply_eq_iff_eq, α.homEquiv'_comp,
    Equiv.apply_symm_apply, map_mul, ← α.homEquiv'_comp, op_tensorObj,
    braiding_hom_fst, braiding_hom_snd, _root_.mul_comm]

end CategoryTheory
