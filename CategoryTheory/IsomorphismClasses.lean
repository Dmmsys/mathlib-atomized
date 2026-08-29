/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Objects of a category up to an isomorphism

`IsIsomorphic X Y := Nonempty (X ≅ Y)` is an equivalence relation on the objects of a category.
The quotient with respect to this relation defines a functor from our category to `Type`.
-/

@[expose] public section


universe v u

namespace CategoryTheory

section Category

variable {C : Type u} [Category.{v} C]

/--
Definition of `IsIsomorphic` / `IsIsomorphic` 的定义

English:
definition IsIsomorphic
  signature: : C -> C -> Prop
  body: fun X Y => Nonempty (X ≅ Y)

中文:
定义 IsIsomorphic
  签名: : C -> C -> 命题
  定义体: fun X Y => Nonempty (X ≅ Y)

Depends on / 依赖: Nonempty
-/
def IsIsomorphic : C -> C -> Prop := fun X Y => Nonempty (X ≅ Y)

variable (C)

/-- `IsIsomorphic` defines a setoid. -/
@[instance_reducible]
/--
Definition of `isIsomorphicSetoid` / `isIsomorphicSetoid` 的定义

English:
definition isIsomorphicSetoid
  signature: : Setoid C where
  body: IsIsomorphic
  iseqv := ⟨fun X => ⟨Iso.refl X⟩, fun ⟨α⟩ => ⟨α.symm⟩, fun ⟨α⟩ ⟨β⟩ => ⟨α.trans β⟩⟩

中文:
定义 isIsomorphicSetoid
  签名: : Setoid C where
  定义体: IsIsomorphic
  iseqv := ⟨fun X => ⟨Iso.refl X⟩, fun ⟨α⟩ => ⟨α.symm⟩, fun ⟨α⟩ ⟨β⟩ => ⟨α.trans β⟩⟩

Depends on / 依赖: IsIsomorphic
-/
def isIsomorphicSetoid : Setoid C where
  r := IsIsomorphic
  iseqv := ⟨fun X => ⟨Iso.refl X⟩, fun ⟨α⟩ => ⟨α.symm⟩, fun ⟨α⟩ ⟨β⟩ => ⟨α.trans β⟩⟩

end Category

/--
Definition of `isomorphismClasses` / `isomorphismClasses` 的定义

English:
definition isomorphismClasses
  signature: : Cat.{v, u} ⥤ Type u where
  body: Quotient (isIsomorphicSetoid C.α)
  map {_ _} F := ↾(Quot.map F.toFunctor.obj fun _ _ ⟨f⟩ => ⟨F.toFunctor.mapIso f⟩)
  map_id {C} := by -- Porting note: this used to be `tidy`
    ext x
    apply @Quot.recOn _ _ _ x
    all_goals cat_disch
  map_comp {C D E} f g := by -- Porting note(s): idem
    ex

中文:
定义 isomorphismClasses
  签名: : Cat.{v, u} ⥤ 类型u where
  定义体: Quotient (isIsomorphicSetoid C.α)
  map {_ _} F := ↾(Quot.map F.toFunctor.obj fun _ _ ⟨f⟩ => ⟨F.toFunctor.mapIso f⟩)
  map_id {C} := by -- Porting note: this used to be `tidy`
    ext x
    apply @Quot.recOn _ _ _ x
    all_goals cat_disch
  map_comp {C D E} f g := by -- Porting note(s): idem
    ex

Depends on / 依赖: Quotient, isIsomorphicSetoid
-/
def isomorphismClasses : Cat.{v, u} ⥤ Type u where
  obj C := Quotient (isIsomorphicSetoid C.α)
  map {_ _} F := ↾(Quot.map F.toFunctor.obj fun _ _ ⟨f⟩ => ⟨F.toFunctor.mapIso f⟩)
  map_id {C} := by -- Porting note: this used to be `tidy`
    ext x
    apply @Quot.recOn _ _ _ x
    all_goals cat_disch
  map_comp {C D E} f g := by -- Porting note(s): idem
    ext x
    apply @Quot.recOn _ _ _ x
    all_goals cat_disch

/--
theorem `Groupoid.isIsomorphic_iff_nonempty_hom` / 定理 `Groupoid.isIsomorphic_iff_nonempty_hom`

English:
theorem Groupoid.isIsomorphic_iff_nonempty_hom
  given: {C : Type u} [Groupoid.{v} C] {X Y : C}
  proof: (Groupoid.isoEquivHom X Y).nonempty_congr

中文:
定理 Groupoid.isIsomorphic_iff_nonempty_hom
  条件: {C : 类型u} [Groupoid.{v} C] {X Y : C}
  证明: (Groupoid.isoEquivHom X Y).nonempty_congr

Depends on / 依赖: Groupoid, Groupoid.isoEquivHom, isoEquivHom, nonempty_congr
-/
theorem Groupoid.isIsomorphic_iff_nonempty_hom {C : Type u} [Groupoid.{v} C] {X Y : C} :
    IsIsomorphic X Y ↔ Nonempty (X ⟶ Y) :=
  (Groupoid.isoEquivHom X Y).nonempty_congr

end CategoryTheory
