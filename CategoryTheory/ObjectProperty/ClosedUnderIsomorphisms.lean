/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import Mathlib.Order.Basic

/-! # Properties of objects which are closed under isomorphisms

Given a category `C` and `P : ObjectProperty C` (i.e. `P : C → Prop`),
this file introduces the type class `P.IsClosedUnderIsomorphisms`.

-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (P Q : ObjectProperty C)

namespace ObjectProperty

/--
Definition of `IsClosedUnderIsomorphisms` / `IsClosedUnderIsomorphisms` 的定义

English:
class IsClosedUnderIsomorphisms
  parameters: : Prop where
  axioms and operations (1):
    - of_iso({X Y : C} (_ : X ≅ Y) (_ : P X)) : P Y

中文:
类 IsClosedUnderIsomorphisms
  参数: : 命题 where
  公理与运算 (1 个):
    - of_iso({X Y : C} (_ : X ≅ Y) (_ : P X)) : P Y
-/
class IsClosedUnderIsomorphisms : Prop where
  of_iso {X Y : C} (_ : X ≅ Y) (_ : P X) : P Y

/--
lemma `prop_of_iso` / 引理 `prop_of_iso`

English:
lemma prop_of_iso
  given: [IsClosedUnderIsomorphisms P] {X Y : C} (e : X ≅ Y) (hX : P X)
  statement: P Y
  proof: IsClosedUnderIsomorphisms.of_iso e hX

中文:
引理 prop_of_iso
  条件: [IsClosedUnderIsomorphisms P] {X Y : C} (e : X ≅ Y) (hX : P X)
  结论: P Y
  证明: IsClosedUnderIsomorphisms.of_iso e hX

Depends on / 依赖: IsClosedUnderIsomorphisms, IsClosedUnderIsomorphisms.of_iso, of_iso
-/
lemma prop_of_iso [IsClosedUnderIsomorphisms P] {X Y : C} (e : X ≅ Y) (hX : P X) : P Y :=
  IsClosedUnderIsomorphisms.of_iso e hX

/--
lemma `prop_iff_of_iso` / 引理 `prop_iff_of_iso`

English:
lemma prop_iff_of_iso
  given: [IsClosedUnderIsomorphisms P] {X Y : C} (e : X ≅ Y)
  statement: P X ↔ P Y
  proof: ⟨prop_of_iso P e, prop_of_iso P e.symm⟩

中文:
引理 prop_iff_of_iso
  条件: [IsClosedUnderIsomorphisms P] {X Y : C} (e : X ≅ Y)
  结论: P X ↔ P Y
  证明: ⟨prop_of_iso P e, prop_of_iso P e.symm⟩

Depends on / 依赖: e.symm, prop_of_iso
-/
lemma prop_iff_of_iso [IsClosedUnderIsomorphisms P] {X Y : C} (e : X ≅ Y) : P X ↔ P Y :=
  ⟨prop_of_iso P e, prop_of_iso P e.symm⟩

/--
lemma `prop_of_isIso` / 引理 `prop_of_isIso`

English:
lemma prop_of_isIso
  given: [IsClosedUnderIsomorphisms P] {X Y : C} (f : X ⟶ Y) [IsIso f] (hX : P X)
  proof: prop_of_iso P (asIso f) hX

中文:
引理 prop_of_isIso
  条件: [IsClosedUnderIsomorphisms P] {X Y : C} (f : X ⟶ Y) [IsIso f] (hX : P X)
  证明: prop_of_iso P (asIso f) hX

Depends on / 依赖: prop_of_iso
-/
lemma prop_of_isIso [IsClosedUnderIsomorphisms P] {X Y : C} (f : X ⟶ Y) [IsIso f] (hX : P X) :
    P Y :=
  prop_of_iso P (asIso f) hX

/--
lemma `prop_iff_of_isIso` / 引理 `prop_iff_of_isIso`

English:
lemma prop_iff_of_isIso
  given: [IsClosedUnderIsomorphisms P] {X Y : C} (f : X ⟶ Y) [IsIso f]
  statement: P X ↔ P Y
  proof: prop_iff_of_iso P (asIso f)

中文:
引理 prop_iff_of_isIso
  条件: [IsClosedUnderIsomorphisms P] {X Y : C} (f : X ⟶ Y) [IsIso f]
  结论: P X ↔ P Y
  证明: prop_iff_of_iso P (asIso f)

Depends on / 依赖: prop_iff_of_iso
-/
lemma prop_iff_of_isIso [IsClosedUnderIsomorphisms P] {X Y : C} (f : X ⟶ Y) [IsIso f] : P X ↔ P Y :=
  prop_iff_of_iso P (asIso f)

/--
Definition of `isoClosure` / `isoClosure` 的定义

English:
definition isoClosure
  signature: : ObjectProperty C
  body: fun X => exists (Y : C) (_ : P Y), Nonempty (X ≅ Y)

中文:
定义 isoClosure
  签名: : Object命题erty C
  定义体: fun X => exists (Y : C) (_ : P Y), Nonempty (X ≅ Y)

Depends on / 依赖: Nonempty
-/
def isoClosure : ObjectProperty C := fun X => exists (Y : C) (_ : P Y), Nonempty (X ≅ Y)

/--
lemma `prop_isoClosure_iff` / 引理 `prop_isoClosure_iff`

English:
lemma prop_isoClosure_iff
  given: (X : C)
  proof: by rfl

中文:
引理 prop_isoClosure_iff
  条件: (X : C)
  证明: by rfl
-/
lemma prop_isoClosure_iff (X : C) :
    isoClosure P X ↔ exists (Y : C) (_ : P Y), Nonempty (X ≅ Y) := by rfl

variable {P} in
/--
lemma `prop_isoClosure` / 引理 `prop_isoClosure`

English:
lemma prop_isoClosure
  given: {X Y : C} (h : P X) (e : X ⟶ Y) [IsIso e]
  statement: isoClosure P Y
  proof: ⟨X, h, ⟨(asIso e).symm⟩⟩

中文:
引理 prop_isoClosure
  条件: {X Y : C} (h : P X) (e : X ⟶ Y) [IsIso e]
  结论: isoClosure P Y
  证明: ⟨X, h, ⟨(asIso e).symm⟩⟩
-/
lemma prop_isoClosure {X Y : C} (h : P X) (e : X ⟶ Y) [IsIso e] : isoClosure P Y :=
  ⟨X, h, ⟨(asIso e).symm⟩⟩

/--
lemma `le_isoClosure` / 引理 `le_isoClosure`

English:
lemma le_isoClosure
  statement: P <= isoClosure P
  proof: fun X hX => ⟨X, hX, ⟨Iso.refl X⟩⟩

中文:
引理 le_isoClosure
  结论: P <= isoClosure P
  证明: fun X hX => ⟨X, hX, ⟨Iso.refl X⟩⟩

Depends on / 依赖: Iso.refl
-/
lemma le_isoClosure : P <= isoClosure P :=
  fun X hX => ⟨X, hX, ⟨Iso.refl X⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.Nonempty]
  signature: : P.isoClosure.Nonempty
  body: .mono P.le_isoClosure

中文:
实例 [P.Nonempty]
  签名: : P.isoClosure.Nonempty
  定义体: .mono P.le_isoClosure

Depends on / 依赖: P.le_isoClosure, le_isoClosure
-/
instance [P.Nonempty] : P.isoClosure.Nonempty := .mono P.le_isoClosure

variable {P Q} in
/--
lemma `monotone_isoClosure` / 引理 `monotone_isoClosure`

English:
lemma monotone_isoClosure
  given: (h : P <= Q)
  statement: isoClosure P <= isoClosure Q
  proof: by
  rintro X ⟨X', hX', ⟨e⟩⟩
  exact ⟨X', h _ hX', ⟨e⟩⟩

中文:
引理 monotone_isoClosure
  条件: (h : P <= Q)
  结论: isoClosure P <= isoClosure Q
  证明: by
  rintro X ⟨X', hX', ⟨e⟩⟩
  exact ⟨X', h _ hX', ⟨e⟩⟩
-/
lemma monotone_isoClosure (h : P <= Q) : isoClosure P <= isoClosure Q := by
  rintro X ⟨X', hX', ⟨e⟩⟩
  exact ⟨X', h _ hX', ⟨e⟩⟩

/--
lemma `isoClosure_eq_self` / 引理 `isoClosure_eq_self`

English:
lemma isoClosure_eq_self
  given: [IsClosedUnderIsomorphisms P]
  statement: isoClosure P = P
  proof: by
  apply le_antisymm
  · intro X ⟨Y, hY, ⟨e⟩⟩
    exact prop_of_iso P e.symm hY
  · exact le_isoClosure P

中文:
引理 isoClosure_eq_self
  条件: [IsClosedUnderIsomorphisms P]
  结论: isoClosure P = P
  证明: by
  apply le_antisymm
  · intro X ⟨Y, hY, ⟨e⟩⟩
    exact prop_of_iso P e.symm hY
  · exact le_isoClosure P

Depends on / 依赖: e.symm, le_antisymm, le_isoClosure, prop_of_iso
-/
lemma isoClosure_eq_self [IsClosedUnderIsomorphisms P] : isoClosure P = P := by
  apply le_antisymm
  · intro X ⟨Y, hY, ⟨e⟩⟩
    exact prop_of_iso P e.symm hY
  · exact le_isoClosure P

/--
lemma `isoClosure_le_iff` / 引理 `isoClosure_le_iff`

English:
lemma isoClosure_le_iff
  given: [IsClosedUnderIsomorphisms Q]
  statement: isoClosure P <= Q ↔ P <= Q
  proof: ⟨(le_isoClosure P).trans,
    fun h => (monotone_isoClosure h).trans (by rw [isoClosure_eq_self])⟩

中文:
引理 isoClosure_le_iff
  条件: [IsClosedUnderIsomorphisms Q]
  结论: isoClosure P <= Q ↔ P <= Q
  证明: ⟨(le_isoClosure P).trans,
    fun h => (monotone_isoClosure h).trans (by rw [isoClosure_eq_self])⟩

Depends on / 依赖: isoClosure_eq_self, le_isoClosure, monotone_isoClosure
-/
lemma isoClosure_le_iff [IsClosedUnderIsomorphisms Q] : isoClosure P <= Q ↔ P <= Q :=
  ⟨(le_isoClosure P).trans,
    fun h => (monotone_isoClosure h).trans (by rw [isoClosure_eq_self])⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsClosedUnderIsomorphisms (isoClosure P)
  body: by
    rintro X Y e ⟨Z, hZ, ⟨f⟩⟩
    exact ⟨Z, hZ, ⟨e.symm.trans f⟩⟩

中文:
实例 :
  签名: IsClosedUnderIsomorphisms (isoClosure P)
  定义体: by
    rintro X Y e ⟨Z, hZ, ⟨f⟩⟩
    exact ⟨Z, hZ, ⟨e.symm.trans f⟩⟩

Depends on / 依赖: e.symm.trans
-/
instance : IsClosedUnderIsomorphisms (isoClosure P) where
  of_iso := by
    rintro X Y e ⟨Z, hZ, ⟨f⟩⟩
    exact ⟨Z, hZ, ⟨e.symm.trans f⟩⟩

/--
lemma `isClosedUnderIsomorphisms_iff_isoClosure_eq_self` / 引理 `isClosedUnderIsomorphisms_iff_isoClosure_eq_self`

English:
lemma isClosedUnderIsomorphisms_iff_isoClosure_eq_self
  proof: ⟨fun _ => isoClosure_eq_self _, fun h => by rw [← h]; infer_instance⟩

中文:
引理 isClosedUnderIsomorphisms_iff_isoClosure_eq_self
  证明: ⟨fun _ => isoClosure_eq_self _, fun h => by rw [← h]; infer_instance⟩

Depends on / 依赖: infer_instance, isoClosure_eq_self
-/
lemma isClosedUnderIsomorphisms_iff_isoClosure_eq_self :
    IsClosedUnderIsomorphisms P ↔ isoClosure P = P :=
  ⟨fun _ => isoClosure_eq_self _, fun h => by rw [← h]; infer_instance⟩

instance (F : C ⥤ D) : IsClosedUnderIsomorphisms (P.map F) where
  of_iso := by
    rintro _ _ e ⟨X, hX, ⟨e'⟩⟩
    exact ⟨X, hX, ⟨e' ≪≫ e⟩⟩

instance (F : D ⥤ C) [P.IsClosedUnderIsomorphisms] :
    IsClosedUnderIsomorphisms (P.inverseImage F) where
  of_iso e hX := P.prop_of_iso (F.mapIso e) hX

@[simp]
/--
lemma `isoClosure_strictMap` / 引理 `isoClosure_strictMap`

English:
lemma isoClosure_strictMap
  given: (F : C ⥤ D)
  proof: by
  refine le_antisymm ?_ ?_
  · rw [isoClosure_le_iff]
    exact P.strictMap_le_map F
  · rintro X ⟨Y, hY, ⟨e⟩⟩
    exact ⟨F.obj Y, ⟨Y, hY⟩, ⟨e.symm⟩⟩

@[simp]

中文:
引理 isoClosure_strictMap
  条件: (F : C ⥤ D)
  证明: by
  refine le_antisymm ?_ ?_
  · rw [isoClosure_le_iff]
    exact P.strictMap_le_map F
  · rintro X ⟨Y, hY, ⟨e⟩⟩
    exact ⟨F.obj Y, ⟨Y, hY⟩, ⟨e.symm⟩⟩

@[simp]

Depends on / 依赖: F.obj, P.strictMap_le_map, e.symm, isoClosure_le_iff, le_antisymm, strictMap_le_map
-/
lemma isoClosure_strictMap (F : C ⥤ D) :
    (P.strictMap F).isoClosure = P.map F := by
  refine le_antisymm ?_ ?_
  · rw [isoClosure_le_iff]
    exact P.strictMap_le_map F
  · rintro X ⟨Y, hY, ⟨e⟩⟩
    exact ⟨F.obj Y, ⟨Y, hY⟩, ⟨e.symm⟩⟩

@[simp]
/--
lemma `map_isoClosure` / 引理 `map_isoClosure`

English:
lemma map_isoClosure
  given: (F : C ⥤ D)
  proof: by
  refine le_antisymm ?_ (map_monotone P.le_isoClosure F)
  rintro X ⟨Y, ⟨Z, hZ, ⟨e⟩⟩, ⟨e'⟩⟩
  exact ⟨Z, hZ, ⟨F.mapIso e.symm ≪≫ e'⟩⟩

中文:
引理 map_isoClosure
  条件: (F : C ⥤ D)
  证明: by
  refine le_antisymm ?_ (map_monotone P.le_isoClosure F)
  rintro X ⟨Y, ⟨Z, hZ, ⟨e⟩⟩, ⟨e'⟩⟩
  exact ⟨Z, hZ, ⟨F.mapIso e.symm ≪≫ e'⟩⟩

Depends on / 依赖: F.mapIso, P.le_isoClosure, e.symm, le_antisymm, le_isoClosure, mapIso, map_monotone
-/
lemma map_isoClosure (F : C ⥤ D) :
    P.isoClosure.map F = P.map F := by
  refine le_antisymm ?_ (map_monotone P.le_isoClosure F)
  rintro X ⟨Y, ⟨Z, hZ, ⟨e⟩⟩, ⟨e'⟩⟩
  exact ⟨Z, hZ, ⟨F.mapIso e.symm ≪≫ e'⟩⟩

end ObjectProperty

end CategoryTheory
