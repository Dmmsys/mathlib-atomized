/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.Data.ULift

/-!
# Basic API for ULift

This file contains a very basic API for working with the categorical
instance on `ULift C` where `C` is a type with a category instance.

1. `CategoryTheory.ULift.upFunctor` is the functorial version of the usual `ULift.up`.
2. `CategoryTheory.ULift.downFunctor` is the functorial version of the usual `ULift.down`.
3. `CategoryTheory.ULift.equivalence` is the categorical equivalence between
  `C` and `ULift C`.

## ULiftHom

Given a type `C : Type u`, `ULiftHom.{w} C` is just an alias for `C`.
If we have `Category.{v} C`, then `ULiftHom.{w} C` is endowed with a category instance
whose morphisms are obtained by applying `ULift.{w}` to the morphisms from `C`.

This is a category equivalent to `C`. The forward direction of the equivalence is `ULiftHom.up`,
the backward direction is `ULiftHom.down` and the equivalence is `ULiftHom.equiv`.

## AsSmall

This file also contains a construction which takes a type `C : Type u` with a
category instance `Category.{v} C` and makes a small category
`AsSmall.{w} C : Type (max w v u)` equivalent to `C`.

The forward direction of the equivalence, `C ⥤ AsSmall C`, is denoted `AsSmall.up`
and the backward direction is `AsSmall.down`. The equivalence itself is `AsSmall.equiv`.
-/

@[expose] public section

universe w₁ v₁ v₂ u₁ u₂

namespace CategoryTheory

attribute [local instance] uliftCategory

variable {C : Type u₁} [Category.{v₁} C]

/-- The functorial version of `ULift.up`. -/
@[simps]
/--
Definition of `ULift.upFunctor` / `ULift.upFunctor` 的定义

English:
definition ULift.upFunctor
  signature: : C ⥤ ULift.{u₂} C where
  body: ULift.up
  map f := f

中文:
定义 ULift.upFunctor
  签名: : C ⥤ ULift.{u₂} C where
  定义体: ULift.up
  map f := f

Depends on / 依赖: ULift.up
-/
def ULift.upFunctor : C ⥤ ULift.{u₂} C where
  obj := ULift.up
  map f := f

/-- The functorial version of `ULift.down`. -/
@[simps]
/--
Definition of `ULift.downFunctor` / `ULift.downFunctor` 的定义

English:
definition ULift.downFunctor
  signature: : ULift.{u₂} C ⥤ C where
  body: ULift.down
  map f := f

中文:
定义 ULift.downFunctor
  签名: : ULift.{u₂} C ⥤ C where
  定义体: ULift.down
  map f := f

Depends on / 依赖: ULift.down
-/
def ULift.downFunctor : ULift.{u₂} C ⥤ C where
  obj := ULift.down
  map f := f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The categorical equivalence between `C` and `ULift C`. -/
@[simps]
/--
Definition of `ULift.equivalence` / `ULift.equivalence` 的定义

English:
definition ULift.equivalence
  signature: : C ≌ ULift.{u₂} C where
  body: ULift.upFunctor
  inverse := ULift.downFunctor
  unitIso :=
    { hom := 𝟙 _
      inv := 𝟙 _ }
  counitIso :=
    { hom := { app := fun _ => 𝟙 _ }
      inv := { app := fun _ => 𝟙 _ } }

中文:
定义 ULift.equivalence
  签名: : C ≌ ULift.{u₂} C where
  定义体: ULift.upFunctor
  inverse := ULift.downFunctor
  unitIso :=
    { hom := 𝟙 _
      inv := 𝟙 _ }
  counitIso :=
    { hom := { app := fun _ => 𝟙 _ }
      inv := { app := fun _ => 𝟙 _ } }

Depends on / 依赖: ULift.upFunctor, upFunctor
-/
def ULift.equivalence : C ≌ ULift.{u₂} C where
  functor := ULift.upFunctor
  inverse := ULift.downFunctor
  unitIso :=
    { hom := 𝟙 _
      inv := 𝟙 _ }
  counitIso :=
    { hom := { app := fun _ => 𝟙 _ }
      inv := { app := fun _ => 𝟙 _ } }

section ULiftHom

/--
Definition of `ULiftHom.` / `ULiftHom.` 的定义

English:
definition ULiftHom.{w,
  signature: u} (C
  body: let _ := ULift.{w} C
  C

中文:
定义 ULiftHom.{w,
  签名: u} (C
  定义体: let _ := ULift.{w} C
  C
-/
def ULiftHom.{w, u} (C : Type u) : Type u :=
  let _ := ULift.{w} C
  C

instance {C} [Inhabited C] : Inhabited (ULiftHom C) :=
  ⟨(default : C)⟩

/--
Definition of `ULiftHom.objDown` / `ULiftHom.objDown` 的定义

English:
definition ULiftHom.objDown
  signature: {C} (A : ULiftHom C)
  body: A

中文:
定义 ULiftHom.objDown
  签名: {C} (A : ULiftHom C)
  定义体: A
-/
def ULiftHom.objDown {C} (A : ULiftHom C) : C :=
  A

/--
Definition of `ULiftHom.objUp` / `ULiftHom.objUp` 的定义

English:
definition ULiftHom.objUp
  signature: {C} (A : C)
  body: A

中文:
定义 ULiftHom.objUp
  签名: {C} (A : C)
  定义体: A
-/
def ULiftHom.objUp {C} (A : C) : ULiftHom C :=
  A

/--
Definition of `ULiftHom.objEquiv` / `ULiftHom.objEquiv` 的定义

English:
definition ULiftHom.objEquiv
  signature: {C}
  body: ULiftHom.objUp
  invFun := ULiftHom.objDown

@[simp]

中文:
定义 ULiftHom.objEquiv
  签名: {C}
  定义体: ULiftHom.objUp
  invFun := ULiftHom.objDown

@[simp]

Depends on / 依赖: ULiftHom, ULiftHom.objUp
-/
def ULiftHom.objEquiv {C} : C ≃ ULiftHom C where
  toFun := ULiftHom.objUp
  invFun := ULiftHom.objDown

@[simp]
/--
theorem `objDown_objUp` / 定理 `objDown_objUp`

English:
theorem objDown_objUp
  given: {C} (A : C)
  statement: (ULiftHom.objUp A).objDown = A
  proof: rfl

@[simp]

中文:
定理 objDown_objUp
  条件: {C} (A : C)
  结论: (ULiftHom.objUp A).objDown = A
  证明: rfl

@[simp]
-/
theorem objDown_objUp {C} (A : C) : (ULiftHom.objUp A).objDown = A :=
  rfl

@[simp]
/--
theorem `objUp_objDown` / 定理 `objUp_objDown`

English:
theorem objUp_objDown
  given: {C} (A : ULiftHom C)
  statement: ULiftHom.objUp A.objDown = A
  proof: rfl

中文:
定理 objUp_objDown
  条件: {C} (A : ULiftHom C)
  结论: ULiftHom.objUp A.objDown = A
  证明: rfl
-/
theorem objUp_objDown {C} (A : ULiftHom C) : ULiftHom.objUp A.objDown = A :=
  rfl

/--
Instance `ULiftHom.category` / 实例 `ULiftHom.category`

English:
instance ULiftHom.category
  signature: : Category.{max v₂ v₁} (ULiftHom.{v₂} C) where
  body: ULift.{v₂} A.objDown ⟶ B.objDown
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.down ≫ g.down⟩

中文:
实例 ULiftHom.category
  签名: : Category.{max v₂ v₁} (ULiftHom.{v₂} C) where
  定义体: ULift.{v₂} A.objDown ⟶ B.objDown
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.down ≫ g.down⟩

Depends on / 依赖: A.objDown, B.objDown, objDown
-/
instance ULiftHom.category : Category.{max v₂ v₁} (ULiftHom.{v₂} C) where
Hom A B := ULift.{v₂} A.objDown ⟶ B.objDown
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.down ≫ g.down⟩

/-- One half of the equivalence between `C` and `ULiftHom C`. -/
@[simps]
/--
Definition of `ULiftHom.up` / `ULiftHom.up` 的定义

English:
definition ULiftHom.up
  signature: : C ⥤ ULiftHom C where
  body: ULiftHom.objUp
  map f := ⟨f⟩

中文:
定义 ULiftHom.up
  签名: : C ⥤ ULiftHom C where
  定义体: ULiftHom.objUp
  map f := ⟨f⟩

Depends on / 依赖: ULiftHom, ULiftHom.objUp
-/
def ULiftHom.up : C ⥤ ULiftHom C where
  obj := ULiftHom.objUp
  map f := ⟨f⟩

/-- One half of the equivalence between `C` and `ULiftHom C`. -/
@[simps]
/--
Definition of `ULiftHom.down` / `ULiftHom.down` 的定义

English:
definition ULiftHom.down
  signature: : ULiftHom C ⥤ C where
  body: ULiftHom.objDown
  map f := f.down

中文:
定义 ULiftHom.down
  签名: : ULiftHom C ⥤ C where
  定义体: ULiftHom.objDown
  map f := f.down

Depends on / 依赖: ULiftHom, ULiftHom.objDown, objDown
-/
def ULiftHom.down : ULiftHom C ⥤ C where
  obj := ULiftHom.objDown
  map f := f.down

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `ULiftHom.equiv` / `ULiftHom.equiv` 的定义

English:
definition ULiftHom.equiv
  signature: : C ≌ ULiftHom C where
  body: ULiftHom.up
  inverse := ULiftHom.down
  unitIso := NatIso.ofComponents fun _ => eqToIso rfl
  counitIso := NatIso.ofComponents fun _ => eqToIso rfl

中文:
定义 ULiftHom.equiv
  签名: : C ≌ ULiftHom C where
  定义体: ULiftHom.up
  inverse := ULiftHom.down
  unitIso := NatIso.ofComponents fun _ => eqToIso rfl
  counitIso := NatIso.ofComponents fun _ => eqToIso rfl

Depends on / 依赖: ULiftHom, ULiftHom.up
-/
def ULiftHom.equiv : C ≌ ULiftHom C where
  functor := ULiftHom.up
  inverse := ULiftHom.down
  unitIso := NatIso.ofComponents fun _ => eqToIso rfl
  counitIso := NatIso.ofComponents fun _ => eqToIso rfl

end ULiftHom

/-- `AsSmall C` is a small category equivalent to `C`.
  More specifically, if `C : Type u` is endowed with `Category.{v} C`, then
  `AsSmall.{w} C : Type (max w v u)` is endowed with an instance of a small category.

  The objects and morphisms of `AsSmall C` are defined by applying `ULift` to the
  objects and morphisms of `C`.

  Note: We require a category instance for this definition in order to have direct
  access to the universe level `v`.
-/
@[nolint unusedArguments]
/--
Definition of `AsSmall.` / `AsSmall.` 的定义

English:
definition AsSmall.{w,
  signature: v, u} (D
  body: ULift.{max w v} D

中文:
定义 AsSmall.{w,
  签名: v, u} (D
  定义体: ULift.{max w v} D
-/
def AsSmall.{w, v, u} (D : Type u) [Category.{v} D] := ULift.{max w v} D

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SmallCategory (AsSmall.{w₁} C)
  body: ULift.{max w₁ u₁} X.down ⟶ Y.down
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.down ≫ g.down⟩

中文:
实例 :
  签名: SmallCategory (AsSmall.{w₁} C)
  定义体: ULift.{max w₁ u₁} X.down ⟶ Y.down
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.down ≫ g.down⟩

Depends on / 依赖: X.down, Y.down
-/
instance : SmallCategory (AsSmall.{w₁} C) where
Hom X Y := ULift.{max w₁ u₁} X.down ⟶ Y.down
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.down ≫ g.down⟩

/-- One half of the equivalence between `C` and `AsSmall C`. -/
@[simps]
/--
Definition of `AsSmall.up` / `AsSmall.up` 的定义

English:
definition AsSmall.up
  signature: : C ⥤ AsSmall C where
  body: ⟨X⟩
  map f := ⟨f⟩

中文:
定义 AsSmall.up
  签名: : C ⥤ AsSmall C where
  定义体: ⟨X⟩
  map f := ⟨f⟩
-/
def AsSmall.up : C ⥤ AsSmall C where
  obj X := ⟨X⟩
  map f := ⟨f⟩

/-- One half of the equivalence between `C` and `AsSmall C`. -/
@[simps]
/--
Definition of `AsSmall.down` / `AsSmall.down` 的定义

English:
definition AsSmall.down
  signature: : AsSmall C ⥤ C where
  body: ULift.down X
  map f := f.down

@[reassoc]

中文:
定义 AsSmall.down
  签名: : AsSmall C ⥤ C where
  定义体: ULift.down X
  map f := f.down

@[reassoc]

Depends on / 依赖: ULift.down
-/
def AsSmall.down : AsSmall C ⥤ C where
  obj X := ULift.down X
  map f := f.down

@[reassoc]
/--
theorem `down_comp` / 定理 `down_comp`

English:
theorem down_comp
  given: {X Y Z : AsSmall C} (f : X ⟶ Y) (g : Y ⟶ Z)
  statement: (f ≫ g).down = f.down ≫ g.down
  proof: rfl

@[simp]

中文:
定理 down_comp
  条件: {X Y Z : AsSmall C} (f : X ⟶ Y) (g : Y ⟶ Z)
  结论: (f ≫ g).down = f.down ≫ g.down
  证明: rfl

@[simp]
-/
theorem down_comp {X Y Z : AsSmall C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).down = f.down ≫ g.down :=
  rfl

@[simp]
/--
theorem `eqToHom_down` / 定理 `eqToHom_down`

English:
theorem eqToHom_down
  given: {X Y : AsSmall C} (h : X = Y)
  proof: by
  subst h
  rfl

中文:
定理 eqToHom_down
  条件: {X Y : AsSmall C} (h : X = Y)
  证明: by
  subst h
  rfl
-/
theorem eqToHom_down {X Y : AsSmall C} (h : X = Y) :
    (eqToHom h).down = eqToHom (congrArg ULift.down h) := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The equivalence between `C` and `AsSmall C`. -/
@[simps]
/--
Definition of `AsSmall.equiv` / `AsSmall.equiv` 的定义

English:
definition AsSmall.equiv
  signature: : C ≌ AsSmall C where
  body: AsSmall.up
  inverse := AsSmall.down
  unitIso := NatIso.ofComponents fun _ => eqToIso rfl
counitIso := NatIso.ofComponents fun _ => eqToIso ULift.ext _ _ rfl

中文:
定义 AsSmall.equiv
  签名: : C ≌ AsSmall C where
  定义体: AsSmall.up
  inverse := AsSmall.down
  unitIso := NatIso.ofComponents fun _ => eqToIso rfl
counitIso := NatIso.ofComponents fun _ => eqToIso ULift.ext _ _ rfl

Depends on / 依赖: AsSmall, AsSmall.up
-/
def AsSmall.equiv : C ≌ AsSmall C where
  functor := AsSmall.up
  inverse := AsSmall.down
  unitIso := NatIso.ofComponents fun _ => eqToIso rfl
counitIso := NatIso.ofComponents fun _ => eqToIso ULift.ext _ _ rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: C] : Inhabited (AsSmall C)
  body: ⟨⟨default⟩⟩

中文:
实例 [Inhabited
  签名: C] : Inhabited (AsSmall C)
  定义体: ⟨⟨default⟩⟩
-/
instance [Inhabited C] : Inhabited (AsSmall C) :=
  ⟨⟨default⟩⟩

/--
Definition of `ULiftHomULiftCategory.objEquiv.` / `ULiftHomULiftCategory.objEquiv.` 的定义

English:
definition ULiftHomULiftCategory.objEquiv.{v',
  signature: u', u} {C
  body: Equiv.ulift.symm.trans ULiftHom.objEquiv

中文:
定义 ULiftHomULiftCategory.objEquiv.{v',
  签名: u', u} {C
  定义体: Equiv.ulift.symm.trans ULiftHom.objEquiv

Depends on / 依赖: Equiv.ulift.symm.trans, ULiftHom, ULiftHom.objEquiv, objEquiv
-/
def ULiftHomULiftCategory.objEquiv.{v', u', u} {C : Type u} :
    C ≃ ULiftHom.{v'} (ULift.{u'} C) :=
  Equiv.ulift.symm.trans ULiftHom.objEquiv

/--
Definition of `ULiftHomULiftCategory.equiv.` / `ULiftHomULiftCategory.equiv.` 的定义

English:
definition ULiftHomULiftCategory.equiv.{v',
  signature: u', v, u} (C
  body: ULift.equivalence.trans ULiftHom.equiv

中文:
定义 ULiftHomULiftCategory.equiv.{v',
  签名: u', v, u} (C
  定义体: ULift.equivalence.trans ULiftHom.equiv

Depends on / 依赖: ULift.equivalence.trans, ULiftHom, ULiftHom.equiv, equivalence
-/
def ULiftHomULiftCategory.equiv.{v', u', v, u} (C : Type u) [Category.{v} C] :
    C ≌ ULiftHom.{v'} (ULift.{u'} C) :=
  ULift.equivalence.trans ULiftHom.equiv

/--
Definition of `ULiftHomULiftCategory.equivCongrLeft.` / `ULiftHomULiftCategory.equivCongrLeft.` 的定义

English:
definition ULiftHomULiftCategory.equivCongrLeft.{v',
  signature: u'}
  body: F ⋙ ULift.upFunctor ⋙ ULiftHom.up
  invFun F := F ⋙ ULiftHom.down ⋙ ULift.downFunctor

中文:
定义 ULiftHomULiftCategory.equivCongrLeft.{v',
  签名: u'}
  定义体: F ⋙ ULift.upFunctor ⋙ ULiftHom.up
  invFun F := F ⋙ ULiftHom.down ⋙ ULift.downFunctor

Depends on / 依赖: ULift.upFunctor, ULiftHom, ULiftHom.up, upFunctor
-/
def ULiftHomULiftCategory.equivCongrLeft.{v', u'}
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] :
    (C ⥤ D) ≃ (C ⥤ (ULiftHom.{v'} (ULift.{u'} D))) where
  toFun F := F ⋙ ULift.upFunctor ⋙ ULiftHom.up
  invFun F := F ⋙ ULiftHom.down ⋙ ULift.downFunctor

end CategoryTheory
