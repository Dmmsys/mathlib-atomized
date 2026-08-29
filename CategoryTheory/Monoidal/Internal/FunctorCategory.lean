/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Comon_
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# `Mon (C ⥤ D) ≌ C ⥤ Mon D`

When `D` is a monoidal category,
monoid objects in `C ⥤ D` are the same thing as functors from `C` into the monoid objects of `D`.

This is formalised as:
* `monFunctorCategoryEquivalence : Mon (C ⥤ D) ≌ C ⥤ Mon D`

The intended application is that as `Ring ≌ Mon Ab` (not yet constructed!),
we have `presheaf Ring X ≌ presheaf (Mon Ab) X ≌ Mon (presheaf Ab X)`,
and we can model a module over a presheaf of rings as a module object in `presheaf Ab X`.

## Future work
Presumably this statement is not specific to monoids,
and could be generalised to any internal algebraic objects,
if the appropriate framework was available.
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section


universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj ComonObj

namespace CategoryTheory.Monoidal

variable (C : Type u₁) [Category.{v₁} C]
variable (D : Type u₂) [Category.{v₂} D] [MonoidalCategory.{v₂} D]

namespace MonFunctorCategoryEquivalence

variable {C D}

/-- A monoid object in a functor category sends any object to a monoid object. -/
@[simps]
/--
Definition of `functorObjObj` / `functorObjObj` 的定义

English:
definition functorObjObj
  signature: (A : C ⥤ D) [MonObj A] (X : C)
  body: A.obj X
  mon :=
  { one := η[A].app X
    mul := μ[A].app X
    one_mul := congr_app (one_mul A) X
    mul_one := congr_app (mul_one A) X
    mul_assoc := congr_app (mul_assoc A) X }

中文:
定义 functorObjObj
  签名: (A : C ⥤ D) [MonObj A] (X : C)
  定义体: A.obj X
  mon :=
  { one := η[A].app X
    mul := μ[A].app X
    one_mul := congr_app (one_mul A) X
    mul_one := congr_app (mul_one A) X
    mul_assoc := congr_app (mul_assoc A) X }

Depends on / 依赖: A.obj
-/
def functorObjObj (A : C ⥤ D) [MonObj A] (X : C) : Mon D where
  X := A.obj X
  mon :=
  { one := η[A].app X
    mul := μ[A].app X
    one_mul := congr_app (one_mul A) X
    mul_one := congr_app (mul_one A) X
    mul_assoc := congr_app (mul_assoc A) X }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A monoid object in a functor category induces a functor to the category of monoid objects. -/
@[simps]
/--
Definition of `functorObj` / `functorObj` 的定义

English:
definition functorObj
  signature: (A : C ⥤ D) [MonObj A]
  body: functorObjObj A
  map f :=
    { hom := A.map f
      isMonHom_hom :=
        { one_hom := by dsimp; rw [← η[A].naturality, tensorUnit_map]; dsimp; rw [Category.id_comp]
          mul_hom := by dsimp; rw [← μ[A].naturality, tensorObj_map] } }
  map_id X := by ext; dsimp; rw [CategoryTheory.Functor.map_id]
  map_comp f g := by ext; dsimp; rw [Functor.map_comp]

中文:
定义 functorObj
  签名: (A : C ⥤ D) [MonObj A]
  定义体: functorObjObj A
  map f :=
    { hom := A.map f
      isMonHom_hom :=
        { one_hom := by dsimp; rw [← η[A].naturality, tensorUnit_map]; dsimp; rw [Category.id_comp]
          mul_hom := by dsimp; rw [← μ[A].naturality, tensorObj_map] } }
  map_id X := by ext; dsimp; rw [CategoryTheory.Functor.map_id]
  map_comp f g := by ext; dsimp; rw [Functor.map_comp]

Depends on / 依赖: functorObjObj
-/
def functorObj (A : C ⥤ D) [MonObj A] : C ⥤ Mon D where
  obj := functorObjObj A
  map f :=
    { hom := A.map f
      isMonHom_hom :=
        { one_hom := by dsimp; rw [← η[A].naturality, tensorUnit_map]; dsimp; rw [Category.id_comp]
          mul_hom := by dsimp; rw [← μ[A].naturality, tensorObj_map] } }
  map_id X := by ext; dsimp; rw [CategoryTheory.Functor.map_id]
  map_comp f g := by ext; dsimp; rw [Functor.map_comp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Functor translating a monoid object in a functor category
to a functor into the category of monoid objects.
-/
@[simps]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : Mon (C ⥤ D) ⥤ C ⥤ Mon D where
  body: functorObj A.X
  map f :=
  { app := fun X =>
    { hom := f.hom.app X
      isMonHom_hom :=
        { one_hom := congr_app (IsMonHom.one_hom f.hom) X
          mul_hom := congr_app (IsMonHom.mul_hom f.hom) X } } }

中文:
定义 functor
  签名: : 幺半群 (C ⥤ D) ⥤ C ⥤ 幺半群 D where
  定义体: functorObj A.X
  map f :=
  { app := fun X =>
    { hom := f.hom.app X
      isMonHom_hom :=
        { one_hom := congr_app (IsMonHom.one_hom f.hom) X
          mul_hom := congr_app (IsMonHom.mul_hom f.hom) X } } }

Depends on / 依赖: functorObj
-/
def functor : Mon (C ⥤ D) ⥤ C ⥤ Mon D where
  obj A := functorObj A.X
  map f :=
  { app := fun X =>
    { hom := f.hom.app X
      isMonHom_hom :=
        { one_hom := congr_app (IsMonHom.one_hom f.hom) X
          mul_hom := congr_app (IsMonHom.mul_hom f.hom) X } } }

set_option backward.defeqAttrib.useBackward true in
/-- A functor to the category of monoid objects can be translated as a monoid object
in the functor category. -/
@[simps]
/--
Definition of `inverseObj` / `inverseObj` 的定义

English:
definition inverseObj
  signature: (F : C ⥤ Mon D)
  body: F ⋙ Mon.forget D
  mon :=
  { one := { app X := η[(F.obj X).X] }
    mul := { app X := μ[(F.obj X).X] } }

中文:
定义 inverseObj
  签名: (F : C ⥤ 幺半群 D)
  定义体: F ⋙ Mon.forget D
  mon :=
  { one := { app X := η[(F.obj X).X] }
    mul := { app X := μ[(F.obj X).X] } }

Depends on / 依赖: Mon.forget, forget
-/
def inverseObj (F : C ⥤ Mon D) : Mon (C ⥤ D) where
  X := F ⋙ Mon.forget D
  mon :=
  { one := { app X := η[(F.obj X).X] }
    mul := { app X := μ[(F.obj X).X] } }

set_option backward.defeqAttrib.useBackward true in
/-- Functor translating a functor into the category of monoid objects
to a monoid object in the functor category
-/
@[simps]
/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: : (C ⥤ Mon D) ⥤ Mon (C ⥤ D) where
  body: inverseObj
  map α := .mk'
    { app := fun X => (α.app X).hom
      naturality := fun _ _ f => congr_arg Mon.Hom.hom (α.naturality f) }

中文:
定义 inverse
  签名: : (C ⥤ 幺半群 D) ⥤ 幺半群 (C ⥤ D) where
  定义体: inverseObj
  map α := .mk'
    { app := fun X => (α.app X).hom
      naturality := fun _ _ f => congr_arg Mon.Hom.hom (α.naturality f) }

Depends on / 依赖: inverseObj
-/
def inverse : (C ⥤ Mon D) ⥤ Mon (C ⥤ D) where
  obj := inverseObj
  map α := .mk'
    { app := fun X => (α.app X).hom
      naturality := fun _ _ f => congr_arg Mon.Hom.hom (α.naturality f) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The unit for the equivalence `Mon (C ⥤ D) ≌ C ⥤ Mon D`.
-/
@[simps!]
/--
Definition of `unitIso` / `unitIso` 的定义

English:
definition unitIso
  signature: : 𝟭 (Mon (C ⥤ D)) ≅ functor ⋙ inverse
  body: NatIso.ofComponents (fun A =>
  { hom := .mk' { app := fun _ => 𝟙 _ }
    inv := .mk' { app := fun _ => 𝟙 _ } })

中文:
定义 unitIso
  签名: : 𝟭 (幺半群 (C ⥤ D)) ≅ functor ⋙ inverse
  定义体: NatIso.ofComponents (fun A =>
  { hom := .mk' { app := fun _ => 𝟙 _ }
    inv := .mk' { app := fun _ => 𝟙 _ } })

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
def unitIso : 𝟭 (Mon (C ⥤ D)) ≅ functor ⋙ inverse :=
  NatIso.ofComponents (fun A =>
  { hom := .mk' { app := fun _ => 𝟙 _ }
    inv := .mk' { app := fun _ => 𝟙 _ } })

set_option backward.isDefEq.respectTransparency false in
/-- The counit for the equivalence `Mon (C ⥤ D) ≌ C ⥤ Mon D`.
-/
@[simps!]
/--
Definition of `counitIso` / `counitIso` 的定义

English:
definition counitIso
  signature: : inverse ⋙ functor ≅ 𝟭 (C ⥤ Mon D)
  body: NatIso.ofComponents (fun A =>
    NatIso.ofComponents (fun X => { hom := { hom := 𝟙 _ }, inv := { hom := 𝟙 _ } }))

中文:
定义 counitIso
  签名: : inverse ⋙ functor ≅ 𝟭 (C ⥤ 幺半群 D)
  定义体: NatIso.ofComponents (fun A =>
    NatIso.ofComponents (fun X => { hom := { hom := 𝟙 _ }, inv := { hom := 𝟙 _ } }))

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
def counitIso : inverse ⋙ functor ≅ 𝟭 (C ⥤ Mon D) :=
  NatIso.ofComponents (fun A =>
    NatIso.ofComponents (fun X => { hom := { hom := 𝟙 _ }, inv := { hom := 𝟙 _ } }))

end MonFunctorCategoryEquivalence

open MonFunctorCategoryEquivalence

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- When `D` is a monoidal category,
monoid objects in `C ⥤ D` are the same thing
as functors from `C` into the monoid objects of `D`.
-/
@[simps]
/--
Definition of `monFunctorCategoryEquivalence` / `monFunctorCategoryEquivalence` 的定义

English:
definition monFunctorCategoryEquivalence
  signature: : Mon (C ⥤ D) ≌ C ⥤ Mon D where
  body: functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

中文:
定义 monFunctorCategoryEquivalence
  签名: : 幺半群 (C ⥤ D) ≌ C ⥤ 幺半群 D where
  定义体: functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

Depends on / 依赖: functor
-/
def monFunctorCategoryEquivalence : Mon (C ⥤ D) ≌ C ⥤ Mon D where
  functor := functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

namespace ComonFunctorCategoryEquivalence

variable {C D}

/-- A comonoid object in a functor category sends any object to a comonoid object. -/
@[simps]
/--
Definition of `functorObjObj` / `functorObjObj` 的定义

English:
definition functorObjObj
  signature: (A : C ⥤ D) [ComonObj A] (X : C)
  body: A.obj X
  comon :=
  { counit := ε[A].app X
    comul := Δ[A].app X
    counit_comul := congr_app (counit_comul A) X
    comul_counit := congr_app (comul_counit A) X
    comul_assoc := congr_app (comul_assoc A) X }

中文:
定义 functorObjObj
  签名: (A : C ⥤ D) [余monObj A] (X : C)
  定义体: A.obj X
  comon :=
  { counit := ε[A].app X
    comul := Δ[A].app X
    counit_comul := congr_app (counit_comul A) X
    comul_counit := congr_app (comul_counit A) X
    comul_assoc := congr_app (comul_assoc A) X }

Depends on / 依赖: A.obj
-/
def functorObjObj (A : C ⥤ D) [ComonObj A] (X : C) : Comon D where
  X := A.obj X
  comon :=
  { counit := ε[A].app X
    comul := Δ[A].app X
    counit_comul := congr_app (counit_comul A) X
    comul_counit := congr_app (comul_counit A) X
    comul_assoc := congr_app (comul_assoc A) X }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
A comonoid object in a functor category induces a functor to the category of comonoid objects.
-/
@[simps]
/--
Definition of `functorObj` / `functorObj` 的定义

English:
definition functorObj
  signature: (A : (C ⥤ D)) [ComonObj A]
  body: functorObjObj A
  map f :=
    { hom := A.map f
      isComonHom_hom.hom_counit := by
        dsimp; rw [ε[A].naturality, tensorUnit_map]; dsimp; rw [Category.comp_id]
      isComonHom_hom.hom_comul := by dsimp; rw [Δ[A].naturality, tensorObj_map] }
  map_id X := by ext; dsimp; rw [CategoryTheory.Functor.map_id]
  map_comp f g := by ext; dsimp; rw [Functor.map_comp]

中文:
定义 functorObj
  签名: (A : (C ⥤ D)) [余monObj A]
  定义体: functorObjObj A
  map f :=
    { hom := A.map f
      isComonHom_hom.hom_counit := by
        dsimp; rw [ε[A].naturality, tensorUnit_map]; dsimp; rw [Category.comp_id]
      isComonHom_hom.hom_comul := by dsimp; rw [Δ[A].naturality, tensorObj_map] }
  map_id X := by ext; dsimp; rw [CategoryTheory.Functor.map_id]
  map_comp f g := by ext; dsimp; rw [Functor.map_comp]

Depends on / 依赖: functorObjObj
-/
def functorObj (A : (C ⥤ D)) [ComonObj A] : C ⥤ Comon D where
  obj := functorObjObj A
  map f :=
    { hom := A.map f
      isComonHom_hom.hom_counit := by
        dsimp; rw [ε[A].naturality, tensorUnit_map]; dsimp; rw [Category.comp_id]
      isComonHom_hom.hom_comul := by dsimp; rw [Δ[A].naturality, tensorObj_map] }
  map_id X := by ext; dsimp; rw [CategoryTheory.Functor.map_id]
  map_comp f g := by ext; dsimp; rw [Functor.map_comp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Functor translating a comonoid object in a functor category
to a functor into the category of comonoid objects.
-/
@[simps]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : Comon (C ⥤ D) ⥤ C ⥤ Comon D where
  body: functorObj A.X
  map f :=
  { app := fun X =>
    { hom := f.hom.app X
      isComonHom_hom.hom_counit := congr_app (IsComonHom.hom_counit f.hom) X
      isComonHom_hom.hom_comul := congr_app (IsComonHom.hom_comul f.hom) X } }

中文:
定义 functor
  签名: : 余mon (C ⥤ D) ⥤ C ⥤ 余mon D where
  定义体: functorObj A.X
  map f :=
  { app := fun X =>
    { hom := f.hom.app X
      isComonHom_hom.hom_counit := congr_app (IsComonHom.hom_counit f.hom) X
      isComonHom_hom.hom_comul := congr_app (IsComonHom.hom_comul f.hom) X } }

Depends on / 依赖: functorObj
-/
def functor : Comon (C ⥤ D) ⥤ C ⥤ Comon D where
  obj A := functorObj A.X
  map f :=
  { app := fun X =>
    { hom := f.hom.app X
      isComonHom_hom.hom_counit := congr_app (IsComonHom.hom_counit f.hom) X
      isComonHom_hom.hom_comul := congr_app (IsComonHom.hom_comul f.hom) X } }

set_option backward.defeqAttrib.useBackward true in
/-- A functor to the category of comonoid objects can be translated as a comonoid object
in the functor category. -/
@[simps]
/--
Definition of `inverseObj` / `inverseObj` 的定义

English:
definition inverseObj
  signature: (F : C ⥤ Comon D)
  body: F ⋙ Comon.forget D
  comon :=
  { counit := { app X := ε[(F.obj X).X] }
    comul := { app X := Δ[(F.obj X).X] } }

中文:
定义 inverseObj
  签名: (F : C ⥤ 余mon D)
  定义体: F ⋙ Comon.forget D
  comon :=
  { counit := { app X := ε[(F.obj X).X] }
    comul := { app X := Δ[(F.obj X).X] } }

Depends on / 依赖: Comon.forget, forget
-/
def inverseObj (F : C ⥤ Comon D) : Comon (C ⥤ D) where
  X := F ⋙ Comon.forget D
  comon :=
  { counit := { app X := ε[(F.obj X).X] }
    comul := { app X := Δ[(F.obj X).X] } }

set_option backward.defeqAttrib.useBackward true in
set_option backward.privateInPublic true in
/-- Functor translating a functor into the category of comonoid objects
to a comonoid object in the functor category
-/
@[simps]
/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: : (C ⥤ Comon D) ⥤ Comon (C ⥤ D) where
  body: inverseObj
  map α :=
    { hom :=
      { app := fun X => (α.app X).hom
        naturality := fun _ _ f => congr_arg Comon.Hom.hom (α.naturality f) }
      isComonHom_hom.hom_counit := by ext x; dsimp; rw [IsComonHom.hom_counit (α.app x).hom]
      isComonHom_hom.hom_comul := by ext x; dsimp; rw [IsComonHom.hom_comul (α.app x).hom] }

中文:
定义 inverse
  签名: : (C ⥤ 余mon D) ⥤ 余mon (C ⥤ D) where
  定义体: inverseObj
  map α :=
    { hom :=
      { app := fun X => (α.app X).hom
        naturality := fun _ _ f => congr_arg Comon.Hom.hom (α.naturality f) }
      isComonHom_hom.hom_counit := by ext x; dsimp; rw [IsComonHom.hom_counit (α.app x).hom]
      isComonHom_hom.hom_comul := by ext x; dsimp; rw [IsComonHom.hom_comul (α.app x).hom] }
-/
private def inverse : (C ⥤ Comon D) ⥤ Comon (C ⥤ D) where
  obj := inverseObj
  map α :=
    { hom :=
      { app := fun X => (α.app X).hom
        naturality := fun _ _ f => congr_arg Comon.Hom.hom (α.naturality f) }
      isComonHom_hom.hom_counit := by ext x; dsimp; rw [IsComonHom.hom_counit (α.app x).hom]
      isComonHom_hom.hom_comul := by ext x; dsimp; rw [IsComonHom.hom_comul (α.app x).hom] }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.privateInPublic true in
/-- The unit for the equivalence `Comon (C ⥤ D) ≌ C ⥤ Comon D`.
-/
@[simps!]
/--
Definition of `unitIso` / `unitIso` 的定义

English:
definition unitIso
  signature: : 𝟭 (Comon (C ⥤ D)) ≅ functor ⋙ inverse
  body: NatIso.ofComponents (fun A =>
    { hom := .mk' { app := fun _ => 𝟙 _ }
      inv := .mk' { app := fun _ => 𝟙 _ } })

中文:
定义 unitIso
  签名: : 𝟭 (余mon (C ⥤ D)) ≅ functor ⋙ inverse
  定义体: NatIso.ofComponents (fun A =>
    { hom := .mk' { app := fun _ => 𝟙 _ }
      inv := .mk' { app := fun _ => 𝟙 _ } })
-/
private def unitIso : 𝟭 (Comon (C ⥤ D)) ≅ functor ⋙ inverse :=
  NatIso.ofComponents (fun A =>
    { hom := .mk' { app := fun _ => 𝟙 _ }
      inv := .mk' { app := fun _ => 𝟙 _ } })

set_option backward.isDefEq.respectTransparency false in
-- probably this was originally also intended to be a private def
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The counit for the equivalence `Mon (C ⥤ D) ≌ C ⥤ Mon D`.
-/
@[simps!]
/--
Definition of `counitIso` / `counitIso` 的定义

English:
definition counitIso
  signature: : inverse ⋙ functor ≅ 𝟭 (C ⥤ Comon D)
  body: NatIso.ofComponents (fun A =>
    NatIso.ofComponents (fun X => { hom := { hom := 𝟙 _ }, inv := { hom := 𝟙 _ } }))

中文:
定义 counitIso
  签名: : inverse ⋙ functor ≅ 𝟭 (C ⥤ 余mon D)
  定义体: NatIso.ofComponents (fun A =>
    NatIso.ofComponents (fun X => { hom := { hom := 𝟙 _ }, inv := { hom := 𝟙 _ } }))

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
def counitIso : inverse ⋙ functor ≅ 𝟭 (C ⥤ Comon D) :=
  NatIso.ofComponents (fun A =>
    NatIso.ofComponents (fun X => { hom := { hom := 𝟙 _ }, inv := { hom := 𝟙 _ } }))

end ComonFunctorCategoryEquivalence

open ComonFunctorCategoryEquivalence

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- When `D` is a monoidal category,
comonoid objects in `C ⥤ D` are the same thing
as functors from `C` into the comonoid objects of `D`.
-/
@[simps]
/--
Definition of `comonFunctorCategoryEquivalence` / `comonFunctorCategoryEquivalence` 的定义

English:
definition comonFunctorCategoryEquivalence
  signature: : Comon (C ⥤ D) ≌ C ⥤ Comon D where
  body: functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

中文:
定义 comonFunctorCategoryEquivalence
  签名: : 余mon (C ⥤ D) ≌ C ⥤ 余mon D where
  定义体: functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

Depends on / 依赖: functor
-/
def comonFunctorCategoryEquivalence : Comon (C ⥤ D) ≌ C ⥤ Comon D where
  functor := functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

variable [BraidedCategory.{v₂} D]

namespace CommMonFunctorCategoryEquivalence

variable {C D}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Functor translating a commutative monoid object in a functor category
to a functor into the category of commutative monoid objects.
-/
@[simps!]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : CommMon (C ⥤ D) ⥤ C ⥤ CommMon D where
  body: { obj X :=
        { ((monFunctorCategoryEquivalence C D).functor.obj A.toMon).obj X with
          comm := { mul_comm := congr_app (IsCommMonObj.mul_comm A.X) X } }
      map f :=
        CommMon.homMk (((monFunctorCategoryEquivalence C D).functor.obj A.toMon).map f) }
  map f :=
    { app X :=
        CommMon.homMk (((monFunctorCategoryEquivalence C D).functor.map f.hom).app X) }

中文:
定义 functor
  签名: : 交换幺半群 (C ⥤ D) ⥤ C ⥤ 交换幺半群 D where
  定义体: { obj X :=
        { ((monFunctorCategoryEquivalence C D).functor.obj A.toMon).obj X with
          comm := { mul_comm := congr_app (IsCommMonObj.mul_comm A.X) X } }
      map f :=
        CommMon.homMk (((monFunctorCategoryEquivalence C D).functor.obj A.toMon).map f) }
  map f :=
    { app X :=
        CommMon.homMk (((monFunctorCategoryEquivalence C D).functor.map f.hom).app X) }

Depends on / 依赖: A.toMon, CommMon, CommMon.homMk, IsCommMonObj, IsCommMonObj.mul_comm, congr_app, f.hom, functor, functor.map, functor.obj, monFunctorCategoryEquivalence, mul_comm
-/
def functor : CommMon (C ⥤ D) ⥤ C ⥤ CommMon D where
  obj A :=
    { obj X :=
        { ((monFunctorCategoryEquivalence C D).functor.obj A.toMon).obj X with
          comm := { mul_comm := congr_app (IsCommMonObj.mul_comm A.X) X } }
      map f :=
        CommMon.homMk (((monFunctorCategoryEquivalence C D).functor.obj A.toMon).map f) }
  map f :=
    { app X :=
        CommMon.homMk (((monFunctorCategoryEquivalence C D).functor.map f.hom).app X) }

/-- Functor translating a functor into the category of commutative monoid objects
to a commutative monoid object in the functor category
-/
@[simps!]
/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: : (C ⥤ CommMon D) ⥤ CommMon (C ⥤ D) where
  body: { (monFunctorCategoryEquivalence C D).inverse.obj (F ⋙ CommMon.forget₂Mon D) with
      comm := { mul_comm := by ext X; exact IsCommMonObj.mul_comm (F.obj X).X } }
  map α :=
    CommMon.homMk ((monFunctorCategoryEquivalence C D).inverse.map (Functor.whiskerRight α _))

中文:
定义 inverse
  签名: : (C ⥤ 交换幺半群 D) ⥤ 交换幺半群 (C ⥤ D) where
  定义体: { (monFunctorCategoryEquivalence C D).inverse.obj (F ⋙ CommMon.forget₂Mon D) with
      comm := { mul_comm := by ext X; exact IsCommMonObj.mul_comm (F.obj X).X } }
  map α :=
    CommMon.homMk ((monFunctorCategoryEquivalence C D).inverse.map (Functor.whiskerRight α _))

Depends on / 依赖: CommMon, CommMon.forget, CommMon.homMk, F.obj, Functor, Functor.whiskerRight, IsCommMonObj, IsCommMonObj.mul_comm, inverse, inverse.map, inverse.obj, monFunctorCategoryEquivalence, mul_comm, whiskerRight
-/
def inverse : (C ⥤ CommMon D) ⥤ CommMon (C ⥤ D) where
  obj F :=
    { (monFunctorCategoryEquivalence C D).inverse.obj (F ⋙ CommMon.forget₂Mon D) with
      comm := { mul_comm := by ext X; exact IsCommMonObj.mul_comm (F.obj X).X } }
  map α :=
    CommMon.homMk ((monFunctorCategoryEquivalence C D).inverse.map (Functor.whiskerRight α _))

set_option backward.isDefEq.respectTransparency.types false in
/-- The unit for the equivalence `CommMon (C ⥤ D) ≌ C ⥤ CommMon D`.
-/
@[simps!]
/--
Definition of `unitIso` / `unitIso` 的定义

English:
definition unitIso
  signature: : 𝟭 (CommMon (C ⥤ D)) ≅ functor ⋙ inverse
  body: NatIso.ofComponents (fun A => CommMon.mkIso (Iso.refl _))

中文:
定义 unitIso
  签名: : 𝟭 (交换幺半群 (C ⥤ D)) ≅ functor ⋙ inverse
  定义体: NatIso.ofComponents (fun A => CommMon.mkIso (Iso.refl _))

Depends on / 依赖: CommMon, CommMon.mkIso, Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def unitIso : 𝟭 (CommMon (C ⥤ D)) ≅ functor ⋙ inverse :=
  NatIso.ofComponents (fun A => CommMon.mkIso (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
/-- The counit for the equivalence `CommMon (C ⥤ D) ≌ C ⥤ CommMon D`.
-/
@[simps!]
/--
Definition of `counitIso` / `counitIso` 的定义

English:
definition counitIso
  signature: : inverse ⋙ functor ≅ 𝟭 (C ⥤ CommMon D)
  body: NatIso.ofComponents (fun A => NatIso.ofComponents (fun X => Iso.refl _))

中文:
定义 counitIso
  签名: : inverse ⋙ functor ≅ 𝟭 (C ⥤ 交换幺半群 D)
  定义体: NatIso.ofComponents (fun A => NatIso.ofComponents (fun X => Iso.refl _))

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def counitIso : inverse ⋙ functor ≅ 𝟭 (C ⥤ CommMon D) :=
  NatIso.ofComponents (fun A => NatIso.ofComponents (fun X => Iso.refl _))

end CommMonFunctorCategoryEquivalence

open CommMonFunctorCategoryEquivalence

set_option backward.isDefEq.respectTransparency.types false in
/-- When `D` is a braided monoidal category,
commutative monoid objects in `C ⥤ D` are the same thing
as functors from `C` into the commutative monoid objects of `D`.
-/
@[simps]
/--
Definition of `commMonFunctorCategoryEquivalence` / `commMonFunctorCategoryEquivalence` 的定义

English:
definition commMonFunctorCategoryEquivalence
  signature: : CommMon (C ⥤ D) ≌ C ⥤ CommMon D where
  body: functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

中文:
定义 commMonFunctorCategoryEquivalence
  签名: : 交换幺半群 (C ⥤ D) ≌ C ⥤ 交换幺半群 D where
  定义体: functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

Depends on / 依赖: functor
-/
def commMonFunctorCategoryEquivalence : CommMon (C ⥤ D) ≌ C ⥤ CommMon D where
  functor := functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

end CategoryTheory.Monoidal
