/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.NCompGamma

/-! # The Dold-Kan equivalence for additive categories.

This file defines `Preadditive.DoldKan.equivalence` which is the equivalence
of categories `Karoubi (SimplicialObject C) ≌ Karoubi (ChainComplex C ℕ)`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

@[expose] public section


noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Idempotents AlgebraicTopology.DoldKan

variable {C : Type*} [Category* C] [Preadditive C]

namespace CategoryTheory

namespace Preadditive

namespace DoldKan

/-- The functor `Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C ℕ)` of
the Dold-Kan equivalence for additive categories. -/
@[simp]
/--
Definition of `N` / `N` 的定义

English:
definition N
  signature: : Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C Nat)
  body: N₂

中文:
定义 N
  签名: : Karoubi (SimplicialObject C) ⥤ Karoubi (链复形 C 自然数)
  定义体: N₂
-/
def N : Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C Nat) :=
  N₂

variable [HasFiniteCoproducts C]

/-- The inverse functor `Karoubi (ChainComplex C ℕ) ⥤ Karoubi (SimplicialObject C)` of
the Dold-Kan equivalence for additive categories. -/
@[simp]
/--
Definition of `Γ` / `Γ` 的定义

English:
definition Γ
  signature: : Karoubi (ChainComplex C Nat) ⥤ Karoubi (SimplicialObject C)
  body: Γ₂

中文:
定义 Γ
  签名: : Karoubi (链复形 C 自然数) ⥤ Karoubi (SimplicialObject C)
  定义体: Γ₂
-/
def Γ : Karoubi (ChainComplex C Nat) ⥤ Karoubi (SimplicialObject C) :=
  Γ₂

set_option backward.isDefEq.respectTransparency false in
/-- The Dold-Kan equivalence `Karoubi (SimplicialObject C) ≌ Karoubi (ChainComplex C ℕ)`
for additive categories. -/
@[simps]
/--
Definition of `equivalence` / `equivalence` 的定义

English:
definition equivalence
  signature: : Karoubi (SimplicialObject C) ≌ Karoubi (ChainComplex C Nat) where
  body: N
  inverse := Γ
  unitIso := Γ₂N₂
  counitIso := N₂Γ₂
  functor_unitIso_comp P := by
    let α := N.mapIso (Γ₂N₂.app P)
    let β := N₂Γ₂.app (N.obj P)
    symm
    change 𝟙 _ = α.hom ≫ β.hom
    rw [← Iso.inv_comp_eq]; rw [comp_id]; rw [← comp_id β.hom]; rw [← Iso.inv_comp_eq]
    exact AlgebraicTopology.DoldKan.identity_N₂_objectwise P

中文:
定义 equivalence
  签名: : Karoubi (SimplicialObject C) ≌ Karoubi (链复形 C 自然数) where
  定义体: N
  inverse := Γ
  unitIso := Γ₂N₂
  counitIso := N₂Γ₂
  functor_unitIso_comp P := by
    let α := N.mapIso (Γ₂N₂.app P)
    let β := N₂Γ₂.app (N.obj P)
    symm
    change 𝟙 _ = α.hom ≫ β.hom
    rw [← Iso.inv_comp_eq]; rw [comp_id]; rw [← comp_id β.hom]; rw [← Iso.inv_comp_eq]
    exact AlgebraicTopology.DoldKan.identity_N₂_objectwise P
-/
def equivalence : Karoubi (SimplicialObject C) ≌ Karoubi (ChainComplex C Nat) where
  functor := N
  inverse := Γ
  unitIso := Γ₂N₂
  counitIso := N₂Γ₂
  functor_unitIso_comp P := by
    let α := N.mapIso (Γ₂N₂.app P)
    let β := N₂Γ₂.app (N.obj P)
    symm
    change 𝟙 _ = α.hom ≫ β.hom
    rw [← Iso.inv_comp_eq]; rw [comp_id]; rw [← comp_id β.hom]; rw [← Iso.inv_comp_eq]
    exact AlgebraicTopology.DoldKan.identity_N₂_objectwise P

end DoldKan

end Preadditive

end CategoryTheory
