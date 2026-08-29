/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Retract

/-! # Properties of objects which are stable under retracts

Given a category `C` and `P : ObjectProperty C` (i.e. `P : C → Prop`),
this file introduces the type class `P.IsStableUnderRetracts`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)

/--
Definition of `IsStableUnderRetracts` / `IsStableUnderRetracts` 的定义

English:
class IsStableUnderRetracts
  parameters: where
  axioms and operations (1):
    - of_retract({X Y : C} (_ : Retract X Y) (_ : P Y)) : P X

中文:
类 是StableUnderRetracts
  参数: where
  公理与运算 (1 个):
    - of_retract({X Y : C} (_ : 收缩 X Y) (_ : P Y)) : P X
-/
class IsStableUnderRetracts where
  of_retract {X Y : C} (_ : Retract X Y) (_ : P Y) : P X

/--
lemma `prop_of_retract` / 引理 `prop_of_retract`

English:
lemma prop_of_retract
  given: [IsStableUnderRetracts P] {X Y : C} (h : Retract X Y) (hY : P Y)
  statement: P X
  proof: IsStableUnderRetracts.of_retract h hY

中文:
引理 prop_of_retract
  条件: [是StableUnderRetracts P] {X Y : C} (h : 收缩 X Y) (hY : P Y)
  结论: P X
  证明: IsStableUnderRetracts.of_retract h hY

Depends on / 依赖: IsStableUnderRetracts, IsStableUnderRetracts.of_retract, of_retract
-/
lemma prop_of_retract [IsStableUnderRetracts P] {X Y : C} (h : Retract X Y) (hY : P Y) : P X :=
  IsStableUnderRetracts.of_retract h hY

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStableUnderRetracts (⊥ : ObjectProperty C)
  body: h

中文:
实例 :
  签名: 是StableUnderRetracts (⊥ : ObjectProperty C)
  定义体: h
-/
instance : IsStableUnderRetracts (⊥ : ObjectProperty C) where
  of_retract _ h := h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStableUnderRetracts (⊤ : ObjectProperty C)
  body: by trivial

中文:
实例 :
  签名: 是StableUnderRetracts (⊤ : ObjectProperty C)
  定义体: by trivial
-/
instance : IsStableUnderRetracts (⊤ : ObjectProperty C) where
  of_retract _ _ := by trivial

namespace IsStableUnderRetracts

open scoped ZeroObject

variable [P.IsStableUnderRetracts]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.IsClosedUnderIsomorphisms
  body: IsStableUnderRetracts.of_retract i.symm.retract h

中文:
实例 :
  签名: P.在同构下封闭
  定义体: IsStableUnderRetracts.of_retract i.symm.retract h

Depends on / 依赖: IsStableUnderRetracts, IsStableUnderRetracts.of_retract, i.symm.retract, of_retract, retract
-/
instance : P.IsClosedUnderIsomorphisms where
  of_iso i h := IsStableUnderRetracts.of_retract i.symm.retract h

-- see Note [lower instance priority]
instance (priority := 100) [HasZeroObject C] [P.Nonempty] : P.ContainsZero where
  exists_zero := ⟨0, isZero_zero _, of_retract ((isZero_zero _).retract _) P.prop_arbitrary⟩

@[deprecated instContainsZeroOfHasZeroObjectOfNonempty (since := "2026-04-03")]
/--
lemma `containsZero` / 引理 `containsZero`

English:
lemma containsZero
  given: [HasZeroObject C] {X : C} (h : P X)
  statement: P.ContainsZero where
  proof: ⟨0, isZero_zero _, of_retract ((isZero_zero _).retract X) h⟩

中文:
引理 containsZero
  条件: [有ZeroObject C] {X : C} (h : P X)
  结论: P.余ntainsZero where
  证明: ⟨0, isZero_zero _, of_retract ((isZero_zero _).retract X) h⟩

Depends on / 依赖: isZero_zero, of_retract, retract
-/
lemma containsZero [HasZeroObject C] {X : C} (h : P X) : P.ContainsZero where
  exists_zero := ⟨0, isZero_zero _, of_retract ((isZero_zero _).retract X) h⟩

/--
lemma `of_binaryBicone_left` / 引理 `of_binaryBicone_left`

English:
lemma of_binaryBicone_left
  given: [HasZeroMorphisms C] {X Y : C} (c : BinaryBicone X Y) (h : P c.pt)
  proof: of_retract c.retract_left h

中文:
引理 of_binaryBicone_left
  条件: [有ZeroMorphisms C] {X Y : C} (c : BinaryBicone X Y) (h : P c.pt)
  证明: of_retract c.retract_left h

Depends on / 依赖: c.retract_left, of_retract, retract_left
-/
lemma of_binaryBicone_left [HasZeroMorphisms C] {X Y : C} (c : BinaryBicone X Y) (h : P c.pt) :
    P X :=
  of_retract c.retract_left h

/--
lemma `of_binaryBicone_right` / 引理 `of_binaryBicone_right`

English:
lemma of_binaryBicone_right
  given: [HasZeroMorphisms C] {X Y : C} (c : BinaryBicone X Y) (h : P c.pt)
  proof: of_retract c.retract_right h

中文:
引理 of_binaryBicone_right
  条件: [有ZeroMorphisms C] {X Y : C} (c : BinaryBicone X Y) (h : P c.pt)
  证明: of_retract c.retract_right h

Depends on / 依赖: c.retract_right, of_retract, retract_right
-/
lemma of_binaryBicone_right [HasZeroMorphisms C] {X Y : C} (c : BinaryBicone X Y) (h : P c.pt) :
    P Y :=
  of_retract c.retract_right h

/--
lemma `of_biprod_left` / 引理 `of_biprod_left`

English:
lemma of_biprod_left
  given: [HasZeroMorphisms C] {X Y : C} [HasBinaryBiproduct X Y] (h : P (X ⊞ Y))
  proof: of_binaryBicone_left P (BinaryBiproduct.bicone X Y) h

中文:
引理 of_biprod_left
  条件: [有ZeroMorphisms C] {X Y : C} [有BinaryBiproduct X Y] (h : P (X ⊞ Y))
  证明: of_binaryBicone_left P (BinaryBiproduct.bicone X Y) h

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.bicone, bicone, of_binaryBicone_left
-/
lemma of_biprod_left [HasZeroMorphisms C] {X Y : C} [HasBinaryBiproduct X Y] (h : P (X ⊞ Y)) :
    P X :=
  of_binaryBicone_left P (BinaryBiproduct.bicone X Y) h

/--
lemma `of_biprod_right` / 引理 `of_biprod_right`

English:
lemma of_biprod_right
  given: [HasZeroMorphisms C] {X Y : C} [HasBinaryBiproduct X Y] (h : P (X ⊞ Y))
  proof: of_binaryBicone_right P (BinaryBiproduct.bicone X Y) h

中文:
引理 of_biprod_right
  条件: [有ZeroMorphisms C] {X Y : C} [有BinaryBiproduct X Y] (h : P (X ⊞ Y))
  证明: of_binaryBicone_right P (BinaryBiproduct.bicone X Y) h

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.bicone, bicone, of_binaryBicone_right
-/
lemma of_biprod_right [HasZeroMorphisms C] {X Y : C} [HasBinaryBiproduct X Y] (h : P (X ⊞ Y)) :
    P Y :=
  of_binaryBicone_right P (BinaryBiproduct.bicone X Y) h

/--
lemma `of_bicone` / 引理 `of_bicone`

English:
lemma of_bicone
  given: [HasZeroMorphisms C] {J : Type*} (F : J -> C) (c : Bicone F) (h : P c.pt) (j : J)
  proof: of_retract (c.retract j) h

中文:
引理 of_bicone
  条件: [有ZeroMorphisms C] {J : 类型} (F : J -> C) (c : Bicone F) (h : P c.pt) (j : J)
  证明: of_retract (c.retract j) h

Depends on / 依赖: c.retract, of_retract, retract
-/
lemma of_bicone [HasZeroMorphisms C] {J : Type*} (F : J -> C) (c : Bicone F) (h : P c.pt) (j : J) :
    P (F j) :=
  of_retract (c.retract j) h

/--
lemma `of_biproduct` / 引理 `of_biproduct`

English:
lemma of_biproduct
  statement: [HasZeroMorphisms C] {J : Type*} (F : J -> C) [HasBiproduct F] (h : P (⨁ F))
  proof: of_bicone P F (biproduct.bicone F) h j

中文:
引理 of_biproduct
  结论: [有ZeroMorphisms C] {J : 类型} (F : J -> C) [有Biproduct F] (h : P (⨁ F))
  证明: of_bicone P F (biproduct.bicone F) h j

Depends on / 依赖: bicone, biproduct, biproduct.bicone, of_bicone
-/
lemma of_biproduct [HasZeroMorphisms C] {J : Type*} (F : J -> C) [HasBiproduct F] (h : P (⨁ F))
    (j : J) : P (F j) :=
  of_bicone P F (biproduct.bicone F) h j

end IsStableUnderRetracts

/--
Definition of `retractClosure` / `retractClosure` 的定义

English:
definition retractClosure
  signature: : ObjectProperty C
  body: fun X => exists (Y : C) (_ : P Y), Nonempty (Retract X Y)

中文:
定义 retractClosure
  签名: : ObjectProperty C
  定义体: fun X => exists (Y : C) (_ : P Y), Nonempty (Retract X Y)

Depends on / 依赖: Nonempty, Retract
-/
def retractClosure : ObjectProperty C := fun X => exists (Y : C) (_ : P Y), Nonempty (Retract X Y)

/--
lemma `prop_retractClosure_iff` / 引理 `prop_retractClosure_iff`

English:
lemma prop_retractClosure_iff
  given: (X : C)
  proof: by rfl

中文:
引理 prop_retractClosure_iff
  条件: (X : C)
  证明: by rfl
-/
lemma prop_retractClosure_iff (X : C) :
    retractClosure P X ↔ exists (Y : C) (_ : P Y), Nonempty (Retract X Y) := by rfl

variable {P} in
/--
lemma `prop_retractClosure` / 引理 `prop_retractClosure`

English:
lemma prop_retractClosure
  given: {X Y : C} (h : P Y) (r : Retract X Y)
  statement: retractClosure P X
  proof: ⟨Y, h, ⟨r⟩⟩

中文:
引理 prop_retractClosure
  条件: {X Y : C} (h : P Y) (r : 收缩 X Y)
  结论: retractClosure P X
  证明: ⟨Y, h, ⟨r⟩⟩
-/
lemma prop_retractClosure {X Y : C} (h : P Y) (r : Retract X Y) : retractClosure P X :=
  ⟨Y, h, ⟨r⟩⟩

/--
lemma `le_retractClosure` / 引理 `le_retractClosure`

English:
lemma le_retractClosure
  statement: P <= retractClosure P
  proof: fun X hX => ⟨X, hX, ⟨Retract.refl X⟩⟩

中文:
引理 le_retractClosure
  结论: P <= retractClosure P
  证明: fun X hX => ⟨X, hX, ⟨Retract.refl X⟩⟩

Depends on / 依赖: Retract, Retract.refl
-/
lemma le_retractClosure : P <= retractClosure P :=
  fun X hX => ⟨X, hX, ⟨Retract.refl X⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.Nonempty]
  signature: : P.retractClosure.Nonempty
  body: .mono P.le_retractClosure

中文:
实例 [P.非空]
  签名: : P.retractClosure.非空
  定义体: .mono P.le_retractClosure

Depends on / 依赖: P.le_retractClosure, le_retractClosure
-/
instance [P.Nonempty] : P.retractClosure.Nonempty :=
  .mono P.le_retractClosure

variable {P Q} in
/--
lemma `monotone_retractClosure` / 引理 `monotone_retractClosure`

English:
lemma monotone_retractClosure
  given: (h : P <= Q)
  statement: retractClosure P <= retractClosure Q
  proof: by
  rintro X ⟨X', hX', ⟨e⟩⟩
  exact ⟨X', h _ hX', ⟨e⟩⟩

中文:
引理 monotone_retractClosure
  条件: (h : P <= Q)
  结论: retractClosure P <= retractClosure Q
  证明: by
  rintro X ⟨X', hX', ⟨e⟩⟩
  exact ⟨X', h _ hX', ⟨e⟩⟩
-/
lemma monotone_retractClosure (h : P <= Q) : retractClosure P <= retractClosure Q := by
  rintro X ⟨X', hX', ⟨e⟩⟩
  exact ⟨X', h _ hX', ⟨e⟩⟩

/--
lemma `retractClosure_eq_self` / 引理 `retractClosure_eq_self`

English:
lemma retractClosure_eq_self
  given: [IsStableUnderRetracts P]
  statement: retractClosure P = P
  proof: by
  apply le_antisymm
  · intro X ⟨Y, hY, ⟨e⟩⟩
    exact prop_of_retract P e hY
  · exact le_retractClosure P

@[simp]

中文:
引理 retractClosure_eq_self
  条件: [是StableUnderRetracts P]
  结论: retractClosure P = P
  证明: by
  apply le_antisymm
  · intro X ⟨Y, hY, ⟨e⟩⟩
    exact prop_of_retract P e hY
  · exact le_retractClosure P

@[simp]

Depends on / 依赖: le_antisymm, le_retractClosure, prop_of_retract
-/
lemma retractClosure_eq_self [IsStableUnderRetracts P] : retractClosure P = P := by
  apply le_antisymm
  · intro X ⟨Y, hY, ⟨e⟩⟩
    exact prop_of_retract P e hY
  · exact le_retractClosure P

@[simp]
/--
lemma `retractClosure_bot` / 引理 `retractClosure_bot`

English:
lemma retractClosure_bot
  statement: retractClosure (⊥ : ObjectProperty C) = ⊥
  proof: retractClosure_eq_self _

@[simp]

中文:
引理 retractClosure_bot
  结论: retractClosure (⊥ : ObjectProperty C) = ⊥
  证明: retractClosure_eq_self _

@[simp]

Depends on / 依赖: retractClosure_eq_self
-/
lemma retractClosure_bot : retractClosure (⊥ : ObjectProperty C) = ⊥ :=
  retractClosure_eq_self _

@[simp]
/--
lemma `retractClosure_top` / 引理 `retractClosure_top`

English:
lemma retractClosure_top
  statement: retractClosure (⊤ : ObjectProperty C) = ⊤
  proof: retractClosure_eq_self _

中文:
引理 retractClosure_top
  结论: retractClosure (⊤ : ObjectProperty C) = ⊤
  证明: retractClosure_eq_self _

Depends on / 依赖: retractClosure_eq_self
-/
lemma retractClosure_top : retractClosure (⊤ : ObjectProperty C) = ⊤ :=
  retractClosure_eq_self _

/--
lemma `retractClosure_le_iff` / 引理 `retractClosure_le_iff`

English:
lemma retractClosure_le_iff
  given: (Q : ObjectProperty C) [IsStableUnderRetracts Q]
  proof: ⟨(le_retractClosure P).trans,
    fun h => (monotone_retractClosure h).trans (by rw [retractClosure_eq_self])⟩

中文:
引理 retractClosure_le_iff
  条件: (Q : ObjectProperty C) [是StableUnderRetracts Q]
  证明: ⟨(le_retractClosure P).trans,
    fun h => (monotone_retractClosure h).trans (by rw [retractClosure_eq_self])⟩

Depends on / 依赖: le_retractClosure, monotone_retractClosure, retractClosure_eq_self
-/
lemma retractClosure_le_iff (Q : ObjectProperty C) [IsStableUnderRetracts Q] :
    retractClosure P <= Q ↔ P <= Q :=
  ⟨(le_retractClosure P).trans,
    fun h => (monotone_retractClosure h).trans (by rw [retractClosure_eq_self])⟩

/--
lemma `retractClosure_isoClosure` / 引理 `retractClosure_isoClosure`

English:
lemma retractClosure_isoClosure
  proof: by
  refine le_antisymm ?_ (monotone_retractClosure P.le_isoClosure)
  rintro Y ⟨X, ⟨X', hX', ⟨e⟩⟩, ⟨h⟩⟩
  exact ⟨_, hX', ⟨h.trans (Retract.ofIso e)⟩⟩

中文:
引理 retractClosure_isoClosure
  证明: by
  refine le_antisymm ?_ (monotone_retractClosure P.le_isoClosure)
  rintro Y ⟨X, ⟨X', hX', ⟨e⟩⟩, ⟨h⟩⟩
  exact ⟨_, hX', ⟨h.trans (Retract.ofIso e)⟩⟩

Depends on / 依赖: P.le_isoClosure, Retract, Retract.ofIso, h.trans, le_antisymm, le_isoClosure, monotone_retractClosure
-/
lemma retractClosure_isoClosure :
    P.isoClosure.retractClosure = P.retractClosure := by
  refine le_antisymm ?_ (monotone_retractClosure P.le_isoClosure)
  rintro Y ⟨X, ⟨X', hX', ⟨e⟩⟩, ⟨h⟩⟩
  exact ⟨_, hX', ⟨h.trans (Retract.ofIso e)⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStableUnderRetracts (retractClosure P)
  body: by
    rintro X Y r₁ ⟨Z, hZ, ⟨r₂⟩⟩
    refine ⟨Z, hZ, ⟨r₁.trans r₂⟩⟩

@[simp]

中文:
实例 :
  签名: 是StableUnderRetracts (retractClosure P)
  定义体: by
    rintro X Y r₁ ⟨Z, hZ, ⟨r₂⟩⟩
    refine ⟨Z, hZ, ⟨r₁.trans r₂⟩⟩

@[simp]
-/
instance : IsStableUnderRetracts (retractClosure P) where
  of_retract := by
    rintro X Y r₁ ⟨Z, hZ, ⟨r₂⟩⟩
    refine ⟨Z, hZ, ⟨r₁.trans r₂⟩⟩

@[simp]
/--
lemma `retractClosure_retractClosure` / 引理 `retractClosure_retractClosure`

English:
lemma retractClosure_retractClosure
  proof: retractClosure_eq_self P.retractClosure

中文:
引理 retractClosure_retractClosure
  证明: retractClosure_eq_self P.retractClosure

Depends on / 依赖: P.retractClosure, retractClosure, retractClosure_eq_self
-/
lemma retractClosure_retractClosure :
    P.retractClosure.retractClosure = P.retractClosure :=
  retractClosure_eq_self P.retractClosure

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ObjectProperty.EssentiallySmall.{w}
  signature: P] [LocallySmall.{w} C] :
  body: by
    obtain ⟨Q, _, h₁, h₂⟩ := ObjectProperty.EssentiallySmall.exists_small_le.{w} P
    let α := Σ (X : Subtype Q), { p : X.1 ⟶ X.1 // p ≫ p = p }
    let g {X Y : C} (h : Retract Y X) (hX : Q X) : α := ⟨⟨X, hX⟩, h.r ≫ h.i, by simp⟩
    let R (a : α) : Prop := exists (X Y : C) (h : Retract Y X) (hX : Q X), g h hX = a
    choose X Y h hX using fun (a : Subtype R) => a.2
    refine ⟨.ofObj Y, inferInstance, (monotone_retractClosure h₂).trans ?_⟩
    rw [retractClosure_isoClosure]
    rintro y ⟨x, hx, ⟨r⟩⟩
    obtain ⟨a, h₁, h₂⟩ : exists (a : Subtype R) (h₁ : Q (X a)), g (h a) h₁ = g r hx := by
      obtain ⟨_, hr⟩ := hX ⟨⟨⟨_, hx⟩, r.r ≫ r.i, by simp⟩, ⟨_, _, r, hx, rfl⟩⟩
      exact ⟨_, _, hr⟩
    obtain rfl : x = X a := Subtype.ext_iff.1 (congr_arg Sigma.fst h₂.symm)
    have hri : (h a).r ≫ (h a).i = r.r ≫ r.i := by
      rw [Sigma.ext_iff]; rw [heq_eq_eq] at h₂
      exact Subtype.ext_iff.1 h₂.2
    exact ⟨_, ⟨a.1, a.2⟩, ⟨{
      hom := r.i ≫ (h a).r
      inv := (h a).i ≫ r.r
      hom_inv_id := by simp [reassoc_of% hri]
      inv_hom_id := by simp [← reassoc_of% hri]
    }⟩⟩

中文:
实例 [ObjectProperty.EssentiallySmall.{w}
  签名: P] [LocallySmall.{w} C] :
  定义体: by
    obtain ⟨Q, _, h₁, h₂⟩ := ObjectProperty.EssentiallySmall.exists_small_le.{w} P
    let α := Σ (X : Subtype Q), { p : X.1 ⟶ X.1 // p ≫ p = p }
    let g {X Y : C} (h : Retract Y X) (hX : Q X) : α := ⟨⟨X, hX⟩, h.r ≫ h.i, by simp⟩
    let R (a : α) : Prop := exists (X Y : C) (h : Retract Y X) (hX : Q X), g h hX = a
    choose X Y h hX using fun (a : Subtype R) => a.2
    refine ⟨.ofObj Y, inferInstance, (monotone_retractClosure h₂).trans ?_⟩
    rw [retractClosure_isoClosure]
    rintro y ⟨x, hx, ⟨r⟩⟩
    obtain ⟨a, h₁, h₂⟩ : exists (a : Subtype R) (h₁ : Q (X a)), g (h a) h₁ = g r hx := by
      obtain ⟨_, hr⟩ := hX ⟨⟨⟨_, hx⟩, r.r ≫ r.i, by simp⟩, ⟨_, _, r, hx, rfl⟩⟩
      exact ⟨_, _, hr⟩
    obtain rfl : x = X a := Subtype.ext_iff.1 (congr_arg Sigma.fst h₂.symm)
    have hri : (h a).r ≫ (h a).i = r.r ≫ r.i := by
      rw [Sigma.ext_iff]; rw [heq_eq_eq] at h₂
      exact Subtype.ext_iff.1 h₂.2
    exact ⟨_, ⟨a.1, a.2⟩, ⟨{
      hom := r.i ≫ (h a).r
      inv := (h a).i ≫ r.r
      hom_inv_id := by simp [reassoc_of% hri]
      inv_hom_id := by simp [← reassoc_of% hri]
    }⟩⟩

Depends on / 依赖: EssentiallySmall, ObjectProperty, ObjectProperty.EssentiallySmall.exists_small_le, Retract, Subtype, exists_small_le, monotone_retractClosure, retractClosure_isoClosure
-/
instance [ObjectProperty.EssentiallySmall.{w} P] [LocallySmall.{w} C] :
    ObjectProperty.EssentiallySmall.{w} P.retractClosure where
  exists_small_le' := by
    obtain ⟨Q, _, h₁, h₂⟩ := ObjectProperty.EssentiallySmall.exists_small_le.{w} P
    let α := Σ (X : Subtype Q), { p : X.1 ⟶ X.1 // p ≫ p = p }
    let g {X Y : C} (h : Retract Y X) (hX : Q X) : α := ⟨⟨X, hX⟩, h.r ≫ h.i, by simp⟩
    let R (a : α) : Prop := exists (X Y : C) (h : Retract Y X) (hX : Q X), g h hX = a
    choose X Y h hX using fun (a : Subtype R) => a.2
    refine ⟨.ofObj Y, inferInstance, (monotone_retractClosure h₂).trans ?_⟩
    rw [retractClosure_isoClosure]
    rintro y ⟨x, hx, ⟨r⟩⟩
    obtain ⟨a, h₁, h₂⟩ : exists (a : Subtype R) (h₁ : Q (X a)), g (h a) h₁ = g r hx := by
      obtain ⟨_, hr⟩ := hX ⟨⟨⟨_, hx⟩, r.r ≫ r.i, by simp⟩, ⟨_, _, r, hx, rfl⟩⟩
      exact ⟨_, _, hr⟩
    obtain rfl : x = X a := Subtype.ext_iff.1 (congr_arg Sigma.fst h₂.symm)
    have hri : (h a).r ≫ (h a).i = r.r ≫ r.i := by
      rw [Sigma.ext_iff]; rw [heq_eq_eq] at h₂
      exact Subtype.ext_iff.1 h₂.2
    exact ⟨_, ⟨a.1, a.2⟩, ⟨{
      hom := r.i ≫ (h a).r
      inv := (h a).i ≫ r.r
      hom_inv_id := by simp [reassoc_of% hri]
      inv_hom_id := by simp [← reassoc_of% hri]
    }⟩⟩

end CategoryTheory.ObjectProperty
