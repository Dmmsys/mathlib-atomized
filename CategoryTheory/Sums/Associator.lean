/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Sums.Basic

/-!
# Associator for binary disjoint union of categories.

The associator functor `((C ⊕ D) ⊕ E) ⥤ (C ⊕ (D ⊕ E))` and its inverse form an equivalence.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory

open Sum Functor

namespace CategoryTheory.sum

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
  (E : Type u₃) [Category.{v₃} E]

/--
Definition of `associator` / `associator` 的定义

English:
definition associator
  signature: : (C oplus D) oplus E ⥤ C oplus (D oplus E)
  body: (inl_ C (D oplus E) |>.sum' <| inl_ D E ⋙ inr_ C (D oplus E)).sum' inr_ D E ⋙ inr_ C (D oplus E)

@[simp]

中文:
定义 associator
  签名: : (C oplus D) oplus E ⥤ C oplus (D oplus E)
  定义体: (inl_ C (D oplus E) |>.sum' <| inl_ D E ⋙ inr_ C (D oplus E)).sum' inr_ D E ⋙ inr_ C (D oplus E)

@[simp]

Depends on / 依赖: inl_, inr_
-/
def associator : (C oplus D) oplus E ⥤ C oplus (D oplus E) :=
(inl_ C (D oplus E) |>.sum' <| inl_ D E ⋙ inr_ C (D oplus E)).sum' inr_ D E ⋙ inr_ C (D oplus E)

@[simp]
/--
theorem `associator_obj_inl_inl` / 定理 `associator_obj_inl_inl`

English:
theorem associator_obj_inl_inl
  given: (X)
  statement: (associator C D E).obj (inl (inl X)) = inl X
  proof: rfl

@[simp]

中文:
定理 associator_obj_inl_inl
  条件: (X)
  结论: (associator C D E).obj (inl (inl X)) = inl X
  证明: rfl

@[simp]
-/
theorem associator_obj_inl_inl (X) : (associator C D E).obj (inl (inl X)) = inl X :=
  rfl

@[simp]
/--
theorem `associator_obj_inl_inr` / 定理 `associator_obj_inl_inr`

English:
theorem associator_obj_inl_inr
  given: (X)
  statement: (associator C D E).obj (inl (inr X)) = inr (inl X)
  proof: rfl

@[simp]

中文:
定理 associator_obj_inl_inr
  条件: (X)
  结论: (associator C D E).obj (inl (inr X)) = inr (inl X)
  证明: rfl

@[simp]
-/
theorem associator_obj_inl_inr (X) : (associator C D E).obj (inl (inr X)) = inr (inl X) :=
  rfl

@[simp]
/--
theorem `associator_obj_inr` / 定理 `associator_obj_inr`

English:
theorem associator_obj_inr
  given: (X)
  statement: (associator C D E).obj (inr X) = inr (inr X)
  proof: rfl

@[simp]

中文:
定理 associator_obj_inr
  条件: (X)
  结论: (associator C D E).obj (inr X) = inr (inr X)
  证明: rfl

@[simp]
-/
theorem associator_obj_inr (X) : (associator C D E).obj (inr X) = inr (inr X) :=
  rfl

@[simp]
/--
theorem `associator_map_inl_inl` / 定理 `associator_map_inl_inl`

English:
theorem associator_map_inl_inl
  given: {X Y : C} (f : X ⟶ Y)
  proof: rfl

中文:
定理 associator_map_inl_inl
  条件: {X Y : C} (f : X ⟶ Y)
  证明: rfl
-/
theorem associator_map_inl_inl {X Y : C} (f : X ⟶ Y) :
    (associator C D E).map ((inl_ _ _).map ((inl_ _ _).map f)) = (inl_ _ _).map f :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `associator_map_inl_inr` / 定理 `associator_map_inl_inr`

English:
theorem associator_map_inl_inr
  given: {X Y : D} (f : X ⟶ Y)
  proof: by
  simp [associator]

中文:
定理 associator_map_inl_inr
  条件: {X Y : D} (f : X ⟶ Y)
  证明: by
  simp [associator]

Depends on / 依赖: associator
-/
theorem associator_map_inl_inr {X Y : D} (f : X ⟶ Y) :
    (associator C D E).map ((inl_ _ _).map ((inr_ _ _).map f)) =
    (inr_ _ _).map ((inl_ _ _).map f) := by
  simp [associator]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `associator_map_inr` / 定理 `associator_map_inr`

English:
theorem associator_map_inr
  given: {X Y : E} (f : X ⟶ Y)
  proof: by
  simp [associator]

中文:
定理 associator_map_inr
  条件: {X Y : E} (f : X ⟶ Y)
  证明: by
  simp [associator]

Depends on / 依赖: associator
-/
theorem associator_map_inr {X Y : E} (f : X ⟶ Y) :
    (associator C D E).map ((inr_ _ _).map f) = (inr_ _ _).map ((inr_ _ _).map f) := by
  simp [associator]

/-- Characterizing the composition of the associator and the left inclusion. -/
@[simps!]
/--
Definition of `inlCompAssociator` / `inlCompAssociator` 的定义

English:
definition inlCompAssociator
  signature: :
  body: inl_ (C oplus D) E ⋙ associator C D E ≅ inl_ C (D oplus E)
  (Functor.inlCompSum' _ _)

中文:
定义 inlCompAssociator
  签名: :
  定义体: inl_ (C oplus D) E ⋙ associator C D E ≅ inl_ C (D oplus E)
  (Functor.inlCompSum' _ _)

Depends on / 依赖: associator, inl_
-/
def inlCompAssociator :
.sum' inl_ D E ⋙ inr_ C (D oplus E) := inl_ (C oplus D) E ⋙ associator C D E ≅ inl_ C (D oplus E)
  (Functor.inlCompSum' _ _)

/-- Characterizing the composition of the associator and the right inclusion. -/
@[simps!]
/--
Definition of `inrCompAssociator` / `inrCompAssociator` 的定义

English:
definition inrCompAssociator
  signature: : inr_ (C oplus D) E ⋙ associator C D E ≅ inr_ D E ⋙ inr_ C (D oplus E)
  body: (Functor.inrCompSum' _ _)

中文:
定义 inrCompAssociator
  签名: : inr_ (C oplus D) E ⋙ associator C D E ≅ inr_ D E ⋙ inr_ C (D oplus E)
  定义体: (Functor.inrCompSum' _ _)

Depends on / 依赖: Functor, Functor.inrCompSum, inrCompSum
-/
def inrCompAssociator : inr_ (C oplus D) E ⋙ associator C D E ≅ inr_ D E ⋙ inr_ C (D oplus E) :=
  (Functor.inrCompSum' _ _)

/-- Further characterizing the composition of the associator and the left inclusion. -/
@[simps!]
/--
Definition of `inlCompInlCompAssociator` / `inlCompInlCompAssociator` 的定义

English:
definition inlCompInlCompAssociator
  signature: : inl_ C D ⋙ inl_ (C oplus D) E ⋙ associator C D E ≅ inl_ C (D oplus E)
  body: isoWhiskerLeft (inl_ _ _) (inlCompAssociator C D E) ≪≫ Functor.inlCompSum' _ _

中文:
定义 inlCompInlCompAssociator
  签名: : inl_ C D ⋙ inl_ (C oplus D) E ⋙ associator C D E ≅ inl_ C (D oplus E)
  定义体: isoWhiskerLeft (inl_ _ _) (inlCompAssociator C D E) ≪≫ Functor.inlCompSum' _ _

Depends on / 依赖: Functor, Functor.inlCompSum, inlCompAssociator, inlCompSum, inl_, isoWhiskerLeft
-/
def inlCompInlCompAssociator : inl_ C D ⋙ inl_ (C oplus D) E ⋙ associator C D E ≅ inl_ C (D oplus E) :=
  isoWhiskerLeft (inl_ _ _) (inlCompAssociator C D E) ≪≫ Functor.inlCompSum' _ _

/-- Further characterizing the composition of the associator and the left inclusion. -/
@[simps!]
/--
Definition of `inrCompInlCompAssociator` / `inrCompInlCompAssociator` 的定义

English:
definition inrCompInlCompAssociator
  signature: :
  body: isoWhiskerLeft (inr_ _ _) (inlCompAssociator C D E) ≪≫ Functor.inrCompSum' _ _

中文:
定义 inrCompInlCompAssociator
  签名: :
  定义体: isoWhiskerLeft (inr_ _ _) (inlCompAssociator C D E) ≪≫ Functor.inrCompSum' _ _

Depends on / 依赖: Functor, Functor.inrCompSum, inlCompAssociator, inrCompSum, inr_, isoWhiskerLeft
-/
def inrCompInlCompAssociator :
    inr_ C D ⋙ inl_ (C oplus D) E ⋙ associator C D E ≅ inl_ D E ⋙ inr_ C (D oplus E) :=
  isoWhiskerLeft (inr_ _ _) (inlCompAssociator C D E) ≪≫ Functor.inrCompSum' _ _

/--
Definition of `inverseAssociator` / `inverseAssociator` 的定义

English:
definition inverseAssociator
  signature: : C oplus (D oplus E) ⥤ (C oplus D) oplus E
  body: .sum' (inr_ C D ⋙ inl_ (C oplus D) E).sum' inr_ (C oplus D) E inl_ C D ⋙ inl_ (C oplus D) E

@[simp]

中文:
定义 inverseAssociator
  签名: : C oplus (D oplus E) ⥤ (C oplus D) oplus E
  定义体: .sum' (inr_ C D ⋙ inl_ (C oplus D) E).sum' inr_ (C oplus D) E inl_ C D ⋙ inl_ (C oplus D) E

@[simp]

Depends on / 依赖: inl_, inr_
-/
def inverseAssociator : C oplus (D oplus E) ⥤ (C oplus D) oplus E :=
.sum' (inr_ C D ⋙ inl_ (C oplus D) E).sum' inr_ (C oplus D) E inl_ C D ⋙ inl_ (C oplus D) E

@[simp]
/--
theorem `inverseAssociator_obj_inl` / 定理 `inverseAssociator_obj_inl`

English:
theorem inverseAssociator_obj_inl
  given: (X)
  statement: (inverseAssociator C D E).obj (inl X) = inl (inl X)
  proof: rfl

@[simp]

中文:
定理 inverseAssociator_obj_inl
  条件: (X)
  结论: (inverseAssociator C D E).obj (inl X) = inl (inl X)
  证明: rfl

@[simp]
-/
theorem inverseAssociator_obj_inl (X) : (inverseAssociator C D E).obj (inl X) = inl (inl X) :=
  rfl

@[simp]
/--
theorem `inverseAssociator_obj_inr_inl` / 定理 `inverseAssociator_obj_inr_inl`

English:
theorem inverseAssociator_obj_inr_inl
  given: (X)
  proof: rfl

@[simp]

中文:
定理 inverseAssociator_obj_inr_inl
  条件: (X)
  证明: rfl

@[simp]
-/
theorem inverseAssociator_obj_inr_inl (X) :
    (inverseAssociator C D E).obj (inr (inl X)) = inl (inr X) :=
  rfl

@[simp]
/--
theorem `inverseAssociator_obj_inr_inr` / 定理 `inverseAssociator_obj_inr_inr`

English:
theorem inverseAssociator_obj_inr_inr
  given: (X)
  statement: (inverseAssociator C D E).obj (inr (inr X)) = inr X
  proof: rfl

中文:
定理 inverseAssociator_obj_inr_inr
  条件: (X)
  结论: (inverseAssociator C D E).obj (inr (inr X)) = inr X
  证明: rfl
-/
theorem inverseAssociator_obj_inr_inr (X) : (inverseAssociator C D E).obj (inr (inr X)) = inr X :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `inverseAssociator_map_inl` / 定理 `inverseAssociator_map_inl`

English:
theorem inverseAssociator_map_inl
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  simp [inverseAssociator]

中文:
定理 inverseAssociator_map_inl
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  simp [inverseAssociator]

Depends on / 依赖: inverseAssociator
-/
theorem inverseAssociator_map_inl {X Y : C} (f : X ⟶ Y) :
    (inverseAssociator C D E).map ((inl_ _ _).map f) = (inl_ _ _).map ((inl_ _ _).map f) := by
  simp [inverseAssociator]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `inverseAssociator_map_inr_inl` / 定理 `inverseAssociator_map_inr_inl`

English:
theorem inverseAssociator_map_inr_inl
  given: {X Y : D} (f : X ⟶ Y)
  proof: by
  simp [inverseAssociator]

@[simp]

中文:
定理 inverseAssociator_map_inr_inl
  条件: {X Y : D} (f : X ⟶ Y)
  证明: by
  simp [inverseAssociator]

@[simp]

Depends on / 依赖: inverseAssociator
-/
theorem inverseAssociator_map_inr_inl {X Y : D} (f : X ⟶ Y) :
    (inverseAssociator C D E).map ((inr_ _ _).map ((inl_ _ _).map f)) =
    (inl_ _ _).map ((inr_ _ _).map f) := by
  simp [inverseAssociator]

@[simp]
/--
theorem `inverseAssociator_map_inr_inr` / 定理 `inverseAssociator_map_inr_inr`

English:
theorem inverseAssociator_map_inr_inr
  given: {X Y : E} (f : X ⟶ Y)
  proof: rfl

中文:
定理 inverseAssociator_map_inr_inr
  条件: {X Y : E} (f : X ⟶ Y)
  证明: rfl
-/
theorem inverseAssociator_map_inr_inr {X Y : E} (f : X ⟶ Y) :
    (inverseAssociator C D E).map ((inr_ _ _).map ((inr_ _ _).map f)) =
    (inr_ _ _).map f :=
  rfl

/-- Characterizing the composition of the inverse of the associator and the left inclusion. -/
@[simps!]
/--
Definition of `inlCompInverseAssociator` / `inlCompInverseAssociator` 的定义

English:
definition inlCompInverseAssociator
  signature: :
  body: Functor.inlCompSum' _ _

中文:
定义 inlCompInverseAssociator
  签名: :
  定义体: Functor.inlCompSum' _ _

Depends on / 依赖: Functor, Functor.inlCompSum, inlCompSum
-/
def inlCompInverseAssociator :
    inl_ C (D oplus E) ⋙ inverseAssociator C D E ≅ inl_ C D ⋙ inl_ (C oplus D) E :=
  Functor.inlCompSum' _ _

/-- Characterizing the composition of the inverse of the associator and the right inclusion. -/
@[simps!]
/--
Definition of `inrCompInverseAssociator` / `inrCompInverseAssociator` 的定义

English:
definition inrCompInverseAssociator
  signature: :
  body: Functor.inrCompSum' _ _

中文:
定义 inrCompInverseAssociator
  签名: :
  定义体: Functor.inrCompSum' _ _

Depends on / 依赖: Functor, Functor.inrCompSum, inrCompSum
-/
def inrCompInverseAssociator :
inr_ C (D oplus E) ⋙ inverseAssociator C D E ≅ (inr_ C D ⋙ inl_ (C oplus D) E).sum' inr_ (C oplus D) E :=
  Functor.inrCompSum' _ _

/-- Further characterizing the composition of the inverse of the associator and the right
inclusion. -/
@[simps!]
/--
Definition of `inlCompInrCompInverseAssociator` / `inlCompInrCompInverseAssociator` 的定义

English:
definition inlCompInrCompInverseAssociator
  signature: :
  body: isoWhiskerLeft (inl_ _ _) (inrCompInverseAssociator C D E) ≪≫ Functor.inlCompSum' _ _

中文:
定义 inlCompInrCompInverseAssociator
  签名: :
  定义体: isoWhiskerLeft (inl_ _ _) (inrCompInverseAssociator C D E) ≪≫ Functor.inlCompSum' _ _

Depends on / 依赖: Functor, Functor.inlCompSum, inlCompSum, inl_, inrCompInverseAssociator, isoWhiskerLeft
-/
def inlCompInrCompInverseAssociator :
    inl_ D E ⋙ inr_ C (D oplus E) ⋙ inverseAssociator C D E ≅ inr_ C D ⋙ inl_ (C oplus D) E :=
  isoWhiskerLeft (inl_ _ _) (inrCompInverseAssociator C D E) ≪≫ Functor.inlCompSum' _ _

/-- Further characterizing the composition of the inverse of the associator and the right
inclusion. -/
@[simps!]
/--
Definition of `inrCompInrCompInverseAssociator` / `inrCompInrCompInverseAssociator` 的定义

English:
definition inrCompInrCompInverseAssociator
  signature: :
  body: isoWhiskerLeft (inr_ _ _) (inrCompInverseAssociator C D E) ≪≫ Functor.inrCompSum' _ _

中文:
定义 inrCompInrCompInverseAssociator
  签名: :
  定义体: isoWhiskerLeft (inr_ _ _) (inrCompInverseAssociator C D E) ≪≫ Functor.inrCompSum' _ _

Depends on / 依赖: Functor, Functor.inrCompSum, inrCompInverseAssociator, inrCompSum, inr_, isoWhiskerLeft
-/
def inrCompInrCompInverseAssociator :
    inr_ D E ⋙ inr_ C (D oplus E) ⋙ inverseAssociator C D E ≅ inr_ (C oplus D) E :=
  isoWhiskerLeft (inr_ _ _) (inrCompInverseAssociator C D E) ≪≫ Functor.inrCompSum' _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence of categories expressing associativity of sums of categories.
-/
@[simps functor inverse]
/--
Definition of `associativity` / `associativity` 的定义

English:
definition associativity
  signature: : (C oplus D) oplus E ≌ C oplus (D oplus E) where
  body: associator C D E
  inverse := inverseAssociator C D E
  unitIso := Functor.sumIsoExt
    (Functor.sumIsoExt
      ((Functor.associator _ _ _).symm ≪≫ Functor.rightUnitor _ ≪≫
        (isoWhiskerRight (inlCompInlCompAssociator C D E) (inverseAssociator C D E) ≪≫
          inlCompInverseAssociator C D

中文:
定义 associativity
  签名: : (C oplus D) oplus E ≌ C oplus (D oplus E) where
  定义体: associator C D E
  inverse := inverseAssociator C D E
  unitIso := Functor.sumIsoExt
    (Functor.sumIsoExt
      ((Functor.associator _ _ _).symm ≪≫ Functor.rightUnitor _ ≪≫
        (isoWhiskerRight (inlCompInlCompAssociator C D E) (inverseAssociator C D E) ≪≫
          inlCompInverseAssociator C D

Depends on / 依赖: associator
-/
def associativity : (C oplus D) oplus E ≌ C oplus (D oplus E) where
  functor := associator C D E
  inverse := inverseAssociator C D E
  unitIso := Functor.sumIsoExt
    (Functor.sumIsoExt
      ((Functor.associator _ _ _).symm ≪≫ Functor.rightUnitor _ ≪≫
        (isoWhiskerRight (inlCompInlCompAssociator C D E) (inverseAssociator C D E) ≪≫
          inlCompInverseAssociator C D E).symm ≪≫ Functor.associator _ _ _ ≪≫
          isoWhiskerLeft _ (Functor.associator _ _ _))
      ((Functor.associator _ _ _).symm ≪≫ Functor.rightUnitor _ ≪≫
        (isoWhiskerRight (inrCompInlCompAssociator C D E) (inverseAssociator C D E) ≪≫
          Functor.associator _ _ _ ≪≫
          inlCompInrCompInverseAssociator C D E).symm ≪≫
        Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Functor.associator _ _ _)))
    (Functor.rightUnitor _ ≪≫
      (isoWhiskerRight (inrCompAssociator C D E) (inverseAssociator C D E) ≪≫
        Functor.associator _ _ _ ≪≫ inrCompInrCompInverseAssociator C D E).symm ≪≫
      Functor.associator _ _ _)
  counitIso := Functor.sumIsoExt
    ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (inlCompInverseAssociator C D E) (associator C D E) ≪≫
      Functor.associator _ _ _ ≪≫ inlCompInlCompAssociator C D E ≪≫ (Functor.rightUnitor _).symm)
    (Functor.sumIsoExt
      ((Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (Functor.associator _ _ _ ≪≫
          inlCompInrCompInverseAssociator C D E) (associator C D E) ≪≫
        Functor.associator _ _ _ ≪≫ inrCompInlCompAssociator C D E ≪≫
        (Functor.rightUnitor _).symm ≪≫ Functor.associator _ _ _)
      ((Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (Functor.associator _ _ _ ≪≫
          inrCompInrCompInverseAssociator C D E) (associator C D E) ≪≫
        inrCompAssociator C D E ≪≫ isoWhiskerLeft _ (Functor.rightUnitor _).symm))
  functor_unitIso_comp x := match x with
    | inl (inl c) => by simp [inlCompInlCompAssociator, inlCompInverseAssociator]
    | inl (inr d) => by simp [inrCompInlCompAssociator, inlCompInrCompInverseAssociator]
    | inr e => by simp [inrCompAssociator, inrCompInrCompInverseAssociator]

/--
Instance `associatorIsEquivalence` / 实例 `associatorIsEquivalence`

English:
instance associatorIsEquivalence
  signature: : (associator C D E).IsEquivalence
  body: (by infer_instance : (associativity C D E).functor.IsEquivalence)

中文:
实例 associatorIsEquivalence
  签名: : (associator C D E).IsEquivalence
  定义体: (by infer_instance : (associativity C D E).functor.IsEquivalence)

Depends on / 依赖: IsEquivalence, associativity, functor, functor.IsEquivalence, infer_instance
-/
instance associatorIsEquivalence : (associator C D E).IsEquivalence :=
  (by infer_instance : (associativity C D E).functor.IsEquivalence)

/--
Instance `inverseAssociatorIsEquivalence` / 实例 `inverseAssociatorIsEquivalence`

English:
instance inverseAssociatorIsEquivalence
  signature: : (inverseAssociator C D E).IsEquivalence
  body: (by infer_instance : (associativity C D E).inverse.IsEquivalence)

中文:
实例 inverseAssociatorIsEquivalence
  签名: : (inverseAssociator C D E).IsEquivalence
  定义体: (by infer_instance : (associativity C D E).inverse.IsEquivalence)

Depends on / 依赖: IsEquivalence, associativity, infer_instance, inverse, inverse.IsEquivalence
-/
instance inverseAssociatorIsEquivalence : (inverseAssociator C D E).IsEquivalence :=
  (by infer_instance : (associativity C D E).inverse.IsEquivalence)

-- TODO unitors?
-- TODO pentagon natural transformation? ...satisfying?
end CategoryTheory.sum
