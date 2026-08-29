/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# Comonoid objects in a Cartesian monoidal category.

The category of comonoid objects in a Cartesian monoidal category is equivalent
to the category itself, via the forgetful functor.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits ComonObj

universe v u

noncomputable section

namespace CategoryTheory
variable (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C]

attribute [local simp] leftUnitor_hom rightUnitor_hom

/--
Definition of `cartesianComon` / `cartesianComon` 的定义

English:
definition cartesianComon
  signature: : C ⥤ Comon C where
  body: {
    X := X
    comon := {
      comul := lift (𝟙 _) (𝟙 _)
      counit := toUnit _
    }
  }
  map f := .mk' f (f_comul := by
    #adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12244
    this argument was provided by the auto_param. -/
    simp +instances)

中文:
定义 cartesianComon
  签名: : C ⥤ 余mon C where
  定义体: {
    X := X
    comon := {
      comul := lift (𝟙 _) (𝟙 _)
      counit := toUnit _
    }
  }
  map f := .mk' f (f_comul := by
    #adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12244
    this argument was provided by the auto_param. -/
    simp +instances)
-/
def cartesianComon : C ⥤ Comon C where
  obj X := {
    X := X
    comon := {
      comul := lift (𝟙 _) (𝟙 _)
      counit := toUnit _
    }
  }
  map f := .mk' f (f_comul := by
    #adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12244
    this argument was provided by the auto_param. -/
    simp +instances)

variable {C}

/--
theorem `counit_eq_toUnit` / 定理 `counit_eq_toUnit`

English:
theorem counit_eq_toUnit
  given: (A : C) [ComonObj A]
  statement: ε[A] = toUnit _
  proof: by ext

中文:
定理 counit_eq_toUnit
  条件: (A : C) [余monObj A]
  结论: ε[A] = toUnit _
  证明: by ext
-/
@[simp] theorem counit_eq_toUnit (A : C) [ComonObj A] : ε[A] = toUnit _ := by ext

/--
theorem `comul_eq_lift` / 定理 `comul_eq_lift`

English:
theorem comul_eq_lift
  given: (A : C) [ComonObj A]
  statement: Δ[A] = lift (𝟙 _) (𝟙 _)
  proof: by
  ext
  · simpa using comul_counit A =≫ fst _ _
  · simpa using counit_comul A =≫ snd _ _

中文:
定理 comul_eq_lift
  条件: (A : C) [余monObj A]
  结论: Δ[A] = lift (𝟙 _) (𝟙 _)
  证明: by
  ext
  · simpa using comul_counit A =≫ fst _ _
  · simpa using counit_comul A =≫ snd _ _
-/
@[simp] theorem comul_eq_lift (A : C) [ComonObj A] : Δ[A] = lift (𝟙 _) (𝟙 _) := by
  ext
  · simpa using comul_counit A =≫ fst _ _
  · simpa using counit_comul A =≫ snd _ _

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isoCartesianComon` / `isoCartesianComon` 的定义

English:
definition isoCartesianComon
  signature: (A : Comon C)
  body: { hom := .mk' (𝟙 _)
    inv := .mk' (𝟙 _) }

中文:
定义 isoCartesianComon
  签名: (A : 余mon C)
  定义体: { hom := .mk' (𝟙 _)
    inv := .mk' (𝟙 _) }
-/
@[simps] def isoCartesianComon (A : Comon C) : A ≅ (cartesianComon C).obj A.X :=
  { hom := .mk' (𝟙 _)
    inv := .mk' (𝟙 _) }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `comonEquiv` / `comonEquiv` 的定义

English:
definition comonEquiv
  signature: : Comon C ≌ C where
  body: Comon.forget C
  inverse := cartesianComon C
  unitIso := NatIso.ofComponents isoCartesianComon
  counitIso := NatIso.ofComponents (fun _ => .refl _)

中文:
定义 comonEquiv
  签名: : 余mon C ≌ C where
  定义体: Comon.forget C
  inverse := cartesianComon C
  unitIso := NatIso.ofComponents isoCartesianComon
  counitIso := NatIso.ofComponents (fun _ => .refl _)
-/
@[simps] def comonEquiv : Comon C ≌ C where
  functor := Comon.forget C
  inverse := cartesianComon C
  unitIso := NatIso.ofComponents isoCartesianComon
  counitIso := NatIso.ofComponents (fun _ => .refl _)

end CategoryTheory
