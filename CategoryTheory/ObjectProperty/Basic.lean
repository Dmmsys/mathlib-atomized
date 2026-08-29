/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Iso
public import Mathlib.Order.Basic

/-!
# Properties of objects in a category

Given a category `C`, we introduce an abbreviation `ObjectProperty C`
for predicates `C → Prop`.

## TODO

* refactor the file `Limits.FullSubcategory` in order to rename `ClosedUnderLimitsOfShape`
  as `ObjectProperty.IsClosedUnderLimitsOfShape` (and make it a type class)
* refactor the file `Triangulated.Subcategory` in order to make it a type class
  regarding terms in `ObjectProperty C` when `C` is pretriangulated

-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory

/-- A property of objects in a category `C` is a predicate `C → Prop`. -/
@[nolint unusedArguments]
/--
Definition of `ObjectProperty` / `ObjectProperty` 的定义

English:
abbreviation ObjectProperty
  signature: (C : Type u) [CategoryStruct.{v} C]
  body: C -> Prop

中文:
缩写 ObjectProperty
  签名: (C : 类型u) [CategoryStruct.{v} C]
  定义体: C -> Prop
-/
abbrev ObjectProperty (C : Type u) [CategoryStruct.{v} C] : Type u := C -> Prop

namespace ObjectProperty

variable {C : Type u} {D : Type u'}

section

variable [CategoryStruct.{v} C] [CategoryStruct.{v'} D]

/--
lemma `le_def` / 引理 `le_def`

English:
lemma le_def
  given: {P Q : ObjectProperty C}
  proof: Iff.rfl

@[push]

中文:
引理 le_def
  条件: {P Q : ObjectProperty C}
  证明: Iff.rfl

@[push]

Depends on / 依赖: Iff.rfl
-/
lemma le_def {P Q : ObjectProperty C} :
    P <= Q ↔ forall (X : C), P X -> Q X := Iff.rfl

@[push]
/--
lemma `not_le_iff_exists` / 引理 `not_le_iff_exists`

English:
lemma not_le_iff_exists
  given: {P Q : ObjectProperty C}
  proof: by
  simp [le_def]

中文:
引理 not_le_iff_存在
  条件: {P Q : ObjectProperty C}
  证明: by
  simp [le_def]

Depends on / 依赖: P.mem_of_hasInductedTStructure, infer_instance, le_def, mem_of_hasInductedTStructure, t.triangleLEGE_distinguished, triangleLEGE_distinguished
-/
lemma not_le_iff_exists {P Q : ObjectProperty C} :
    ¬ P <= Q ↔ exists (X : C), P X ∧ ¬ Q X := by
  simp [le_def]

/-- The typeclass associated to `P : ObjectProperty C`. -/
@[mk_iff]
/--
Definition of `Is` / `Is` 的定义

English:
class Is
  parameters: (P : ObjectProperty C) (X : C)
  axioms and operations (1):
    - prop : P X

中文:
类 Is
  参数: (P : ObjectProperty C) (X : C)
  公理与运算 (1 个):
    - prop : P X
-/
class Is (P : ObjectProperty C) (X : C) : Prop where
  prop : P X

/--
lemma `prop_of_is` / 引理 `prop_of_is`

English:
lemma prop_of_is
  given: (P : ObjectProperty C) (X : C) [P.Is X]
  statement: P X
  proof: by rwa [← P.is_iff]

中文:
引理 prop_of_is
  条件: (P : ObjectProperty C) (X : C) [P.Is X]
  结论: P X
  证明: by rwa [← P.is_iff]

Depends on / 依赖: P.is_iff, is_iff
-/
lemma prop_of_is (P : ObjectProperty C) (X : C) [P.Is X] : P X := by rwa [← P.is_iff]

/--
lemma `is_of_prop` / 引理 `is_of_prop`

English:
lemma is_of_prop
  given: (P : ObjectProperty C) {X : C} (hX : P X)
  statement: P.Is X
  proof: by rwa [P.is_iff]

中文:
引理 is_of_prop
  条件: (P : ObjectProperty C) {X : C} (hX : P X)
  结论: P.Is X
  证明: by rwa [P.is_iff]

Depends on / 依赖: P.is_iff, is_iff
-/
lemma is_of_prop (P : ObjectProperty C) {X : C} (hX : P X) : P.Is X := by rwa [P.is_iff]

/-- `Nonempty P` is a typeclass saying there exists an object `X : C` that satisfies `P`. -/
@[mk_iff]
/--
Definition of `Nonempty` / `Nonempty` 的定义

English:
class Nonempty
  parameters: (P : ObjectProperty C)
  axioms and operations (1):
    - exists_prop : exists X, P X

中文:
类 非空
  参数: (P : ObjectProperty C)
  公理与运算 (1 个):
    - exists_prop : 存在 X, P X
-/
protected class Nonempty (P : ObjectProperty C) : Prop where
  exists_prop : exists X, P X

/--
lemma `exists_prop_of_nonempty` / 引理 `exists_prop_of_nonempty`

English:
lemma exists_prop_of_nonempty
  given: (P : ObjectProperty C) [P.Nonempty]
  statement: exists X, P X
  proof: Nonempty.exists_prop

中文:
引理 存在_prop_of_nonempty
  条件: (P : ObjectProperty C) [P.非空]
  结论: 存在 X, P X
  证明: Nonempty.exists_prop

Depends on / 依赖: Nonempty, Nonempty.exists_prop, exists_prop
-/
lemma exists_prop_of_nonempty (P : ObjectProperty C) [P.Nonempty] : exists X, P X :=
  Nonempty.exists_prop

/--
lemma `nonempty_of_prop` / 引理 `nonempty_of_prop`

English:
lemma nonempty_of_prop
  given: {P : ObjectProperty C} {X : C} (h : P X)
  statement: P.Nonempty
  proof: ⟨X, h⟩

中文:
引理 nonempty_of_prop
  条件: {P : ObjectProperty C} {X : C} (h : P X)
  结论: P.非空
  证明: ⟨X, h⟩
-/
lemma nonempty_of_prop {P : ObjectProperty C} {X : C} (h : P X) : P.Nonempty := ⟨X, h⟩

/--
Definition of `arbitrary` / `arbitrary` 的定义

English:
definition arbitrary
  signature: (P : ObjectProperty C) [P.Nonempty]
  body: (exists_prop_of_nonempty P).choose

中文:
定义 arbitrary
  签名: (P : ObjectProperty C) [P.非空]
  定义体: (exists_prop_of_nonempty P).choose

Depends on / 依赖: exists_prop_of_nonempty
-/
noncomputable def arbitrary (P : ObjectProperty C) [P.Nonempty] : C :=
  (exists_prop_of_nonempty P).choose

/--
lemma `prop_arbitrary` / 引理 `prop_arbitrary`

English:
lemma prop_arbitrary
  given: (P : ObjectProperty C) [P.Nonempty]
  statement: P P.arbitrary
  proof: (exists_prop_of_nonempty P).choose_spec

中文:
引理 prop_arbitrary
  条件: (P : ObjectProperty C) [P.非空]
  结论: P P.arbitrary
  证明: (exists_prop_of_nonempty P).choose_spec

Depends on / 依赖: choose_spec, exists_prop_of_nonempty
-/
lemma prop_arbitrary (P : ObjectProperty C) [P.Nonempty] : P P.arbitrary :=
  (exists_prop_of_nonempty P).choose_spec

/--
lemma `Nonempty.mono` / 引理 `Nonempty.mono`

English:
lemma Nonempty.mono
  given: {P Q : ObjectProperty C} [P.Nonempty] (hPQ : P <= Q)
  statement: Q.Nonempty
  proof: nonempty_of_prop (hPQ _ P.prop_arbitrary)

中文:
引理 非空.mono
  条件: {P Q : ObjectProperty C} [P.非空] (hPQ : P <= Q)
  结论: Q.非空
  证明: nonempty_of_prop (hPQ _ P.prop_arbitrary)

Depends on / 依赖: P.prop_arbitrary, nonempty_of_prop, prop_arbitrary
-/
lemma Nonempty.mono {P Q : ObjectProperty C} [P.Nonempty] (hPQ : P <= Q) : Q.Nonempty :=
  nonempty_of_prop (hPQ _ P.prop_arbitrary)

/--
lemma `nonempty_of_lt` / 引理 `nonempty_of_lt`

English:
lemma nonempty_of_lt
  given: {P Q : ObjectProperty C} (h : P < Q)
  statement: Q.Nonempty
  proof: nonempty_of_prop (not_le_iff_exists.mp (not_le_of_gt h)).choose_spec.1

中文:
引理 nonempty_of_lt
  条件: {P Q : ObjectProperty C} (h : P < Q)
  结论: Q.非空
  证明: nonempty_of_prop (not_le_iff_exists.mp (not_le_of_gt h)).choose_spec.1

Depends on / 依赖: choose_spec, nonempty_of_prop, not_le_iff_exists, not_le_iff_exists.mp, not_le_of_gt
-/
lemma nonempty_of_lt {P Q : ObjectProperty C} (h : P < Q) : Q.Nonempty :=
  nonempty_of_prop (not_le_iff_exists.mp (not_le_of_gt h)).choose_spec.1

section

variable {ι : Type u'} (X : ι -> C)

/--
Inductive type `ofObj` / 归纳类型 `ofObj`

English:
inductive ofObj
  parameters: : ObjectProperty C
  constructors (1):
    - mk: (i : ι) : ofObj (X i)

中文:
归纳类型 ofObj
  参数: : ObjectProperty C
  构造子 (1 个):
    - mk: (i : ι) : ofObj (X i)
-/
inductive ofObj : ObjectProperty C
  | mk (i : ι) : ofObj (X i)

@[simp]
/--
lemma `ofObj_apply` / 引理 `ofObj_apply`

English:
lemma ofObj_apply
  given: (i : ι)
  statement: ofObj X (X i)
  proof: ⟨i⟩

中文:
引理 ofObj_apply
  条件: (i : ι)
  结论: ofObj X (X i)
  证明: ⟨i⟩
-/
lemma ofObj_apply (i : ι) : ofObj X (X i) := ⟨i⟩

/--
lemma `ofObj_iff` / 引理 `ofObj_iff`

English:
lemma ofObj_iff
  given: (Y : C)
  statement: ofObj X Y ↔ exists i, X i = Y
  proof: by
  constructor
  · rintro ⟨i⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i⟩

中文:
引理 ofObj_iff
  条件: (Y : C)
  结论: ofObj X Y ↔ 存在 i, X i = Y
  证明: by
  constructor
  · rintro ⟨i⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i⟩
-/
lemma ofObj_iff (Y : C) : ofObj X Y ↔ exists i, X i = Y := by
  constructor
  · rintro ⟨i⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i⟩

/--
lemma `ofObj_le_iff` / 引理 `ofObj_le_iff`

English:
lemma ofObj_le_iff
  given: (P : ObjectProperty C)
  proof: ⟨fun h i => h _ (by simp), fun h => by rintro _ ⟨i⟩; exact h i⟩

中文:
引理 ofObj_le_iff
  条件: (P : ObjectProperty C)
  证明: ⟨fun h i => h _ (by simp), fun h => by rintro _ ⟨i⟩; exact h i⟩
-/
lemma ofObj_le_iff (P : ObjectProperty C) :
    ofObj X <= P ↔ forall i, P (X i) :=
  ⟨fun h i => h _ (by simp), fun h => by rintro _ ⟨i⟩; exact h i⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: ι] : (ofObj X).Nonempty
  body: nonempty_of_prop (ofObj_apply X (Classical.arbitrary ι))

中文:
实例 [非空
  签名: ι] : (ofObj X).非空
  定义体: nonempty_of_prop (ofObj_apply X (Classical.arbitrary ι))

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, nonempty_of_prop, ofObj_apply
-/
instance [Nonempty ι] : (ofObj X).Nonempty :=
  nonempty_of_prop (ofObj_apply X (Classical.arbitrary ι))

end

@[simp]
/--
lemma `ofObj_subtypeVal` / 引理 `ofObj_subtypeVal`

English:
lemma ofObj_subtypeVal
  given: (P : ObjectProperty C)
  proof: by
  ext X
  exact ⟨by rintro ⟨X, hX⟩; exact hX,
    fun hX => ofObj_apply Subtype.val ⟨X, hX⟩⟩

中文:
引理 ofObj_subtypeVal
  条件: (P : ObjectProperty C)
  证明: by
  ext X
  exact ⟨by rintro ⟨X, hX⟩; exact hX,
    fun hX => ofObj_apply Subtype.val ⟨X, hX⟩⟩

Depends on / 依赖: Subtype, Subtype.val, ofObj_apply
-/
lemma ofObj_subtypeVal (P : ObjectProperty C) :
    ofObj (Subtype.val : Subtype P -> C) = P := by
  ext X
  exact ⟨by rintro ⟨X, hX⟩; exact hX,
    fun hX => ofObj_apply Subtype.val ⟨X, hX⟩⟩

/--
Definition of `singleton` / `singleton` 的定义

English:
abbreviation singleton
  signature: (X : C)
  body: ofObj (fun (_ : Unit) => X)

@[simp]

中文:
缩写 singleton
  签名: (X : C)
  定义体: ofObj (fun (_ : Unit) => X)

@[simp]

Depends on / 依赖: infer_instance, truncLE
-/
abbrev singleton (X : C) : ObjectProperty C := ofObj (fun (_ : Unit) => X)

@[simp]
/--
lemma `singleton_iff` / 引理 `singleton_iff`

English:
lemma singleton_iff
  given: (X Y : C)
  statement: singleton X Y ↔ X = Y
  proof: by simp [ofObj_iff]

@[simp]

中文:
引理 singleton_iff
  条件: (X Y : C)
  结论: singleton X Y ↔ X = Y
  证明: by simp [ofObj_iff]

@[simp]

Depends on / 依赖: ofObj_iff
-/
lemma singleton_iff (X Y : C) : singleton X Y ↔ X = Y := by simp [ofObj_iff]

@[simp]
/--
lemma `singleton_le_iff` / 引理 `singleton_le_iff`

English:
lemma singleton_le_iff
  given: {X : C} {P : ObjectProperty C}
  proof: by
  simp [ofObj_le_iff]

中文:
引理 singleton_le_iff
  条件: {X : C} {P : ObjectProperty C}
  证明: by
  simp [ofObj_le_iff]

Depends on / 依赖: isLE_truncLE_obj, ofObj_le_iff, t.isLE_truncLE_obj
-/
lemma singleton_le_iff {X : C} {P : ObjectProperty C} :
    singleton X <= P ↔ P X := by
  simp [ofObj_le_iff]

/--
Definition of `pair` / `pair` 的定义

English:
definition pair
  signature: (X Y : C)
  body: ofObj (Sum.elim (fun (_ : Unit) => X) (fun (_ : Unit) => Y))

@[simp]

中文:
定义 pair
  签名: (X Y : C)
  定义体: ofObj (Sum.elim (fun (_ : Unit) => X) (fun (_ : Unit) => Y))

@[simp]

Depends on / 依赖: Sum.elim
-/
def pair (X Y : C) : ObjectProperty C :=
  ofObj (Sum.elim (fun (_ : Unit) => X) (fun (_ : Unit) => Y))

@[simp]
/--
lemma `pair_iff` / 引理 `pair_iff`

English:
lemma pair_iff
  given: (X Y Z : C)
  proof: by
  constructor
  · rintro ⟨_ | _⟩ <;> tauto
  · rintro (rfl | rfl); exacts [⟨Sum.inl .unit⟩, ⟨Sum.inr .unit⟩]

中文:
引理 pair_iff
  条件: (X Y Z : C)
  证明: by
  constructor
  · rintro ⟨_ | _⟩ <;> tauto
  · rintro (rfl | rfl); exacts [⟨Sum.inl .unit⟩, ⟨Sum.inr .unit⟩]

Depends on / 依赖: Sum.inl, Sum.inr, exacts, infer_instance, truncGT
-/
lemma pair_iff (X Y Z : C) :
    pair X Y Z ↔ X = Z ∨ Y = Z := by
  constructor
  · rintro ⟨_ | _⟩ <;> tauto
  · rintro (rfl | rfl); exacts [⟨Sum.inl .unit⟩, ⟨Sum.inr .unit⟩]

instance (X Y : C) : (pair X Y).Nonempty := inferInstanceAs (ofObj _).Nonempty

end

section

variable [Category.{v} C] [Category.{v'} D]

/--
Definition of `inverseImage` / `inverseImage` 的定义

English:
definition inverseImage
  signature: (P : ObjectProperty D) (F : C ⥤ D)
  body: fun X => P (F.obj X)

@[simp]

中文:
定义 inverseImage
  签名: (P : ObjectProperty D) (F : C ⥤ D)
  定义体: fun X => P (F.obj X)

@[simp]

Depends on / 依赖: F.obj
-/
def inverseImage (P : ObjectProperty D) (F : C ⥤ D) : ObjectProperty C :=
  fun X => P (F.obj X)

@[simp]
/--
lemma `prop_inverseImage_iff` / 引理 `prop_inverseImage_iff`

English:
lemma prop_inverseImage_iff
  given: (P : ObjectProperty D) (F : C ⥤ D) (X : C)
  proof: Iff.rfl

中文:
引理 prop_inverseImage_iff
  条件: (P : ObjectProperty D) (F : C ⥤ D) (X : C)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl, isGE_truncGT_obj, t.isGE_truncGT_obj
-/
lemma prop_inverseImage_iff (P : ObjectProperty D) (F : C ⥤ D) (X : C) :
    P.inverseImage F X ↔ P (F.obj X) := Iff.rfl

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (P : ObjectProperty C) (F : C ⥤ D)
  body: fun Y => exists (X : C), P X ∧ Nonempty (F.obj X ≅ Y)

中文:
定义 map
  签名: (P : ObjectProperty C) (F : C ⥤ D)
  定义体: fun Y => exists (X : C), P X ∧ Nonempty (F.obj X ≅ Y)

Depends on / 依赖: F.obj, Nonempty, isGE_truncGT_obj, t.isGE_truncGT_obj
-/
def map (P : ObjectProperty C) (F : C ⥤ D) : ObjectProperty D :=
  fun Y => exists (X : C), P X ∧ Nonempty (F.obj X ≅ Y)

/--
lemma `prop_map_iff` / 引理 `prop_map_iff`

English:
lemma prop_map_iff
  given: (P : ObjectProperty C) (F : C ⥤ D) (Y : D)
  proof: Iff.rfl

中文:
引理 prop_map_iff
  条件: (P : ObjectProperty C) (F : C ⥤ D) (Y : D)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma prop_map_iff (P : ObjectProperty C) (F : C ⥤ D) (Y : D) :
    P.map F Y ↔ exists (X : C), P X ∧ Nonempty (F.obj X ≅ Y) := Iff.rfl

/--
lemma `prop_map_obj` / 引理 `prop_map_obj`

English:
lemma prop_map_obj
  given: (P : ObjectProperty C) (F : C ⥤ D) {X : C} (hX : P X)
  proof: ⟨X, hX, ⟨Iso.refl _⟩⟩

中文:
引理 prop_map_obj
  条件: (P : ObjectProperty C) (F : C ⥤ D) {X : C} (hX : P X)
  证明: ⟨X, hX, ⟨Iso.refl _⟩⟩

Depends on / 依赖: Iso.refl
-/
lemma prop_map_obj (P : ObjectProperty C) (F : C ⥤ D) {X : C} (hX : P X) :
    P.map F (F.obj X) :=
  ⟨X, hX, ⟨Iso.refl _⟩⟩

instance (P : ObjectProperty C) (F : C ⥤ D) [P.Nonempty] : (P.map F).Nonempty :=
  nonempty_of_prop (P.prop_map_obj F P.prop_arbitrary)

/--
lemma `map_monotone` / 引理 `map_monotone`

English:
lemma map_monotone
  given: {P Q : ObjectProperty C} (h : P <= Q) (F : C ⥤ D)
  proof: by
  rintro X ⟨Y, hY, ⟨e⟩⟩
  exact ⟨Y, h _ hY, ⟨e⟩⟩

中文:
引理 map_monotone
  条件: {P Q : ObjectProperty C} (h : P <= Q) (F : C ⥤ D)
  证明: by
  rintro X ⟨Y, hY, ⟨e⟩⟩
  exact ⟨Y, h _ hY, ⟨e⟩⟩
-/
lemma map_monotone {P Q : ObjectProperty C} (h : P <= Q) (F : C ⥤ D) :
    P.map F <= Q.map F := by
  rintro X ⟨Y, hY, ⟨e⟩⟩
  exact ⟨Y, h _ hY, ⟨e⟩⟩

/--
Inductive type `strictMap` / 归纳类型 `strictMap`

English:
inductive strictMap
  parameters: (P : ObjectProperty C) (F : C ⥤ D)
  constructors (1):
    - mk: (X : C) (hX : P X) : strictMap P F (F.obj X)

中文:
归纳类型 strict映射
  参数: (P : ObjectProperty C) (F : C ⥤ D)
  构造子 (1 个):
    - mk: (X : C) (hX : P X) : strict映射 P F (F.obj X)
-/
inductive strictMap (P : ObjectProperty C) (F : C ⥤ D) : ObjectProperty D
  | mk (X : C) (hX : P X) : strictMap P F (F.obj X)

/--
lemma `strictMap_iff` / 引理 `strictMap_iff`

English:
lemma strictMap_iff
  given: (P : ObjectProperty C) (F : C ⥤ D) (Y : D)
  proof: ⟨by rintro ⟨X, hX⟩; exact ⟨X, hX, rfl⟩, by rintro ⟨X, hX, rfl⟩; exact ⟨X, hX⟩⟩

中文:
引理 strictMap_iff
  条件: (P : ObjectProperty C) (F : C ⥤ D) (Y : D)
  证明: ⟨by rintro ⟨X, hX⟩; exact ⟨X, hX, rfl⟩, by rintro ⟨X, hX, rfl⟩; exact ⟨X, hX⟩⟩
-/
lemma strictMap_iff (P : ObjectProperty C) (F : C ⥤ D) (Y : D) :
    P.strictMap F Y ↔ exists (X : C), P X ∧ F.obj X = Y :=
  ⟨by rintro ⟨X, hX⟩; exact ⟨X, hX, rfl⟩, by rintro ⟨X, hX, rfl⟩; exact ⟨X, hX⟩⟩

/--
lemma `strictMap_obj` / 引理 `strictMap_obj`

English:
lemma strictMap_obj
  given: (P : ObjectProperty C) (F : C ⥤ D) {X : C} (hX : P X)
  proof: ⟨X, hX⟩

中文:
引理 strictMap_obj
  条件: (P : ObjectProperty C) (F : C ⥤ D) {X : C} (hX : P X)
  证明: ⟨X, hX⟩
-/
lemma strictMap_obj (P : ObjectProperty C) (F : C ⥤ D) {X : C} (hX : P X) :
    P.strictMap F (F.obj X) :=
  ⟨X, hX⟩

instance (P : ObjectProperty C) (F : C ⥤ D) [P.Nonempty] : (P.strictMap F).Nonempty :=
  nonempty_of_prop (P.strictMap_obj F P.prop_arbitrary)

/--
lemma `strictMap_monotone` / 引理 `strictMap_monotone`

English:
lemma strictMap_monotone
  given: {P Q : ObjectProperty C} (h : P <= Q) (F : C ⥤ D)
  proof: by
  rintro _ ⟨X, hX⟩
  exact ⟨X, h _ hX⟩

中文:
引理 strictMap_monotone
  条件: {P Q : ObjectProperty C} (h : P <= Q) (F : C ⥤ D)
  证明: by
  rintro _ ⟨X, hX⟩
  exact ⟨X, h _ hX⟩
-/
lemma strictMap_monotone {P Q : ObjectProperty C} (h : P <= Q) (F : C ⥤ D) :
    P.strictMap F <= Q.strictMap F := by
  rintro _ ⟨X, hX⟩
  exact ⟨X, h _ hX⟩

/--
lemma `strictMap_le_map` / 引理 `strictMap_le_map`

English:
lemma strictMap_le_map
  given: (P : ObjectProperty C) (F : C ⥤ D)
  proof: by
  rintro _ ⟨X, hX⟩
  exact ⟨X, hX, ⟨Iso.refl _⟩⟩

@[simp]

中文:
引理 strictMap_le_map
  条件: (P : ObjectProperty C) (F : C ⥤ D)
  证明: by
  rintro _ ⟨X, hX⟩
  exact ⟨X, hX, ⟨Iso.refl _⟩⟩

@[simp]

Depends on / 依赖: Iso.refl
-/
lemma strictMap_le_map (P : ObjectProperty C) (F : C ⥤ D) :
    P.strictMap F <= P.map F := by
  rintro _ ⟨X, hX⟩
  exact ⟨X, hX, ⟨Iso.refl _⟩⟩

@[simp]
/--
lemma `strictMap_ofObj` / 引理 `strictMap_ofObj`

English:
lemma strictMap_ofObj
  given: {ι : Type u'} (X : ι -> C) (F : C ⥤ D)
  proof: by
  ext Y
  simp [ofObj_iff, strictMap_iff]

@[simp high]

中文:
引理 strictMap_ofObj
  条件: {ι : 类型u'} (X : ι -> C) (F : C ⥤ D)
  证明: by
  ext Y
  simp [ofObj_iff, strictMap_iff]

@[simp high]

Depends on / 依赖: ofObj_iff, strictMap_iff
-/
lemma strictMap_ofObj {ι : Type u'} (X : ι -> C) (F : C ⥤ D) :
    (ofObj X).strictMap F = ofObj (F.obj ∘ X) := by
  ext Y
  simp [ofObj_iff, strictMap_iff]

@[simp high]
/--
lemma `strictMap_singleton` / 引理 `strictMap_singleton`

English:
lemma strictMap_singleton
  given: (X : C) (F : C ⥤ D)
  proof: by
  ext
  simp [strictMap_iff]

中文:
引理 strictMap_singleton
  条件: (X : C) (F : C ⥤ D)
  证明: by
  ext
  simp [strictMap_iff]

Depends on / 依赖: strictMap_iff
-/
lemma strictMap_singleton (X : C) (F : C ⥤ D) :
    (singleton X).strictMap F = singleton (F.obj X) := by
  ext
  simp [strictMap_iff]

end

end ObjectProperty

end CategoryTheory
