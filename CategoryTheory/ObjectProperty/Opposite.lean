/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.CategoryTheory.Opposites

/-!
# The opposite of a property of objects

-/

@[expose] public section

universe v u

namespace CategoryTheory.ObjectProperty

open Opposite

variable {C : Type u}

section

variable [CategoryStruct.{v} C]

/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: (P : ObjectProperty C)
  body: fun X => P X.unop

中文:
定义 op
  签名: (P : Object命题erty C)
  定义体: fun X => P X.unop
-/
protected def op (P : ObjectProperty C) : ObjectProperty Cᵒᵖ :=
  fun X => P X.unop

/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: (P : ObjectProperty Cᵒᵖ)
  body: fun X => P (op X)

@[simp]

中文:
定义 unop
  签名: (P : Object命题erty Cᵒᵖ)
  定义体: fun X => P (op X)

@[simp]
-/
protected def unop (P : ObjectProperty Cᵒᵖ) : ObjectProperty C :=
  fun X => P (op X)

@[simp]
/--
lemma `op_iff` / 引理 `op_iff`

English:
lemma op_iff
  given: (P : ObjectProperty C) (X : Cᵒᵖ)
  proof: Iff.rfl

@[simp]

中文:
引理 op_iff
  条件: (P : Object命题erty C) (X : Cᵒᵖ)
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
lemma op_iff (P : ObjectProperty C) (X : Cᵒᵖ) :
    P.op X ↔ P X.unop := Iff.rfl

@[simp]
/--
lemma `unop_iff` / 引理 `unop_iff`

English:
lemma unop_iff
  given: (P : ObjectProperty Cᵒᵖ) (X : C)
  proof: Iff.rfl

中文:
引理 unop_iff
  条件: (P : Object命题erty Cᵒᵖ) (X : C)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma unop_iff (P : ObjectProperty Cᵒᵖ) (X : C) :
    P.unop X ↔ P (op X) := Iff.rfl

instance (P : ObjectProperty C) [P.Nonempty] : P.op.Nonempty :=
  ⟨op P.arbitrary, P.prop_arbitrary⟩

instance (P : ObjectProperty Cᵒᵖ) [P.Nonempty] : P.unop.Nonempty :=
  ⟨P.arbitrary.unop, P.prop_arbitrary⟩

@[simp]
/--
lemma `op_unop` / 引理 `op_unop`

English:
lemma op_unop
  given: (P : ObjectProperty Cᵒᵖ)
  statement: P.unop.op = P
  proof: rfl

@[simp]

中文:
引理 op_unop
  条件: (P : Object命题erty Cᵒᵖ)
  结论: P.unop.op = P
  证明: rfl

@[simp]
-/
lemma op_unop (P : ObjectProperty Cᵒᵖ) : P.unop.op = P := rfl

@[simp]
/--
lemma `unop_op` / 引理 `unop_op`

English:
lemma unop_op
  given: (P : ObjectProperty C)
  statement: P.op.unop = P
  proof: rfl

中文:
引理 unop_op
  条件: (P : Object命题erty C)
  结论: P.op.unop = P
  证明: rfl
-/
lemma unop_op (P : ObjectProperty C) : P.op.unop = P := rfl

/--
lemma `op_injective` / 引理 `op_injective`

English:
lemma op_injective
  given: {P Q : ObjectProperty C} (h : P.op = Q.op)
  statement: P = Q
  proof: by
  rw [← P.unop_op]; rw [← Q.unop_op]; rw [h]

中文:
引理 op_injective
  条件: {P Q : Object命题erty C} (h : P.op = Q.op)
  结论: P = Q
  证明: by
  rw [← P.unop_op]; rw [← Q.unop_op]; rw [h]

Depends on / 依赖: P.unop_op, Q.unop_op, unop_op
-/
lemma op_injective {P Q : ObjectProperty C} (h : P.op = Q.op) : P = Q := by
  rw [← P.unop_op]; rw [← Q.unop_op]; rw [h]

/--
lemma `unop_injective` / 引理 `unop_injective`

English:
lemma unop_injective
  given: {P Q : ObjectProperty Cᵒᵖ} (h : P.unop = Q.unop)
  statement: P = Q
  proof: by
  rw [← P.op_unop]; rw [← Q.op_unop]; rw [h]

中文:
引理 unop_injective
  条件: {P Q : Object命题erty Cᵒᵖ} (h : P.unop = Q.unop)
  结论: P = Q
  证明: by
  rw [← P.op_unop]; rw [← Q.op_unop]; rw [h]

Depends on / 依赖: P.op_unop, Q.op_unop, op_unop
-/
lemma unop_injective {P Q : ObjectProperty Cᵒᵖ} (h : P.unop = Q.unop) : P = Q := by
  rw [← P.op_unop]; rw [← Q.op_unop]; rw [h]

/--
lemma `op_injective_iff` / 引理 `op_injective_iff`

English:
lemma op_injective_iff
  given: {P Q : ObjectProperty C}
  proof: ⟨op_injective, by rintro rfl; rfl⟩

中文:
引理 op_injective_iff
  条件: {P Q : Object命题erty C}
  证明: ⟨op_injective, by rintro rfl; rfl⟩

Depends on / 依赖: op_injective
-/
lemma op_injective_iff {P Q : ObjectProperty C} :
    P.op = Q.op ↔ P = Q :=
  ⟨op_injective, by rintro rfl; rfl⟩

/--
lemma `unop_injective_iff` / 引理 `unop_injective_iff`

English:
lemma unop_injective_iff
  given: {P Q : ObjectProperty Cᵒᵖ}
  proof: ⟨unop_injective, by rintro rfl; rfl⟩

中文:
引理 unop_injective_iff
  条件: {P Q : Object命题erty Cᵒᵖ}
  证明: ⟨unop_injective, by rintro rfl; rfl⟩

Depends on / 依赖: unop_injective
-/
lemma unop_injective_iff {P Q : ObjectProperty Cᵒᵖ} :
    P.unop = Q.unop ↔ P = Q :=
  ⟨unop_injective, by rintro rfl; rfl⟩

/--
lemma `op_monotone` / 引理 `op_monotone`

English:
lemma op_monotone
  given: {P Q : ObjectProperty C} (h : P <= Q)
  statement: P.op <= Q.op
  proof: fun _ hX => h _ hX

中文:
引理 op_monotone
  条件: {P Q : Object命题erty C} (h : P <= Q)
  结论: P.op <= Q.op
  证明: fun _ hX => h _ hX
-/
lemma op_monotone {P Q : ObjectProperty C} (h : P <= Q) : P.op <= Q.op :=
  fun _ hX => h _ hX

/--
lemma `unop_monotone` / 引理 `unop_monotone`

English:
lemma unop_monotone
  given: {P Q : ObjectProperty Cᵒᵖ} (h : P <= Q)
  statement: P.unop <= Q.unop
  proof: fun _ hX => h _ hX

@[simp]

中文:
引理 unop_monotone
  条件: {P Q : Object命题erty Cᵒᵖ} (h : P <= Q)
  结论: P.unop <= Q.unop
  证明: fun _ hX => h _ hX

@[simp]
-/
lemma unop_monotone {P Q : ObjectProperty Cᵒᵖ} (h : P <= Q) : P.unop <= Q.unop :=
  fun _ hX => h _ hX

@[simp]
/--
lemma `op_monotone_iff` / 引理 `op_monotone_iff`

English:
lemma op_monotone_iff
  given: {P Q : ObjectProperty C}
  statement: P.op <= Q.op ↔ P <= Q
  proof: ⟨unop_monotone, op_monotone⟩

@[simp]

中文:
引理 op_monotone_iff
  条件: {P Q : Object命题erty C}
  结论: P.op <= Q.op ↔ P <= Q
  证明: ⟨unop_monotone, op_monotone⟩

@[simp]

Depends on / 依赖: op_monotone, unop_monotone
-/
lemma op_monotone_iff {P Q : ObjectProperty C} : P.op <= Q.op ↔ P <= Q :=
  ⟨unop_monotone, op_monotone⟩

@[simp]
/--
lemma `unop_monotone_iff` / 引理 `unop_monotone_iff`

English:
lemma unop_monotone_iff
  given: {P Q : ObjectProperty Cᵒᵖ}
  statement: P.unop <= Q.unop ↔ P <= Q
  proof: ⟨op_monotone, unop_monotone⟩

中文:
引理 unop_monotone_iff
  条件: {P Q : Object命题erty Cᵒᵖ}
  结论: P.unop <= Q.unop ↔ P <= Q
  证明: ⟨op_monotone, unop_monotone⟩

Depends on / 依赖: op_monotone, unop_monotone
-/
lemma unop_monotone_iff {P Q : ObjectProperty Cᵒᵖ} : P.unop <= Q.unop ↔ P <= Q :=
  ⟨op_monotone, unop_monotone⟩

/--
Definition of `subtypeOpEquiv` / `subtypeOpEquiv` 的定义

English:
definition subtypeOpEquiv
  signature: (P : ObjectProperty C)
  body: ⟨x.1.unop, x.2⟩
  invFun x := ⟨op x.1, x.2⟩

@[simp]

中文:
定义 subtypeOpEquiv
  签名: (P : Object命题erty C)
  定义体: ⟨x.1.unop, x.2⟩
  invFun x := ⟨op x.1, x.2⟩

@[simp]
-/
def subtypeOpEquiv (P : ObjectProperty C) :
    Subtype P.op ≃ Subtype P where
  toFun x := ⟨x.1.unop, x.2⟩
  invFun x := ⟨op x.1, x.2⟩

@[simp]
/--
lemma `op_ofObj` / 引理 `op_ofObj`

English:
lemma op_ofObj
  given: {ι : Type*} (X : ι -> C)
  statement: (ofObj X).op = ofObj (fun i => op (X i))
  proof: by
  ext Z
  simp only [op_iff, ofObj_iff]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [hi]⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [← hi]⟩

@[simp]

中文:
引理 op_ofObj
  条件: {ι : 类型} (X : ι -> C)
  结论: (ofObj X).op = ofObj (fun i => op (X i))
  证明: by
  ext Z
  simp only [op_iff, ofObj_iff]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [hi]⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [← hi]⟩

@[simp]

Depends on / 依赖: ofObj_iff, op_iff
-/
lemma op_ofObj {ι : Type*} (X : ι -> C) : (ofObj X).op = ofObj (fun i => op (X i)) := by
  ext Z
  simp only [op_iff, ofObj_iff]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [hi]⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [← hi]⟩

@[simp]
/--
lemma `unop_ofObj` / 引理 `unop_ofObj`

English:
lemma unop_ofObj
  given: {ι : Type*} (X : ι -> Cᵒᵖ)
  statement: (ofObj X).unop = ofObj (fun i => (X i).unop)
  proof: op_injective ((op_ofObj _).symm)

@[simp high]

中文:
引理 unop_ofObj
  条件: {ι : 类型} (X : ι -> Cᵒᵖ)
  结论: (ofObj X).unop = ofObj (fun i => (X i).unop)
  证明: op_injective ((op_ofObj _).symm)

@[simp high]

Depends on / 依赖: op_injective, op_ofObj
-/
lemma unop_ofObj {ι : Type*} (X : ι -> Cᵒᵖ) : (ofObj X).unop = ofObj (fun i => (X i).unop) :=
  op_injective ((op_ofObj _).symm)

@[simp high]
/--
lemma `op_singleton` / 引理 `op_singleton`

English:
lemma op_singleton
  given: (X : C)
  proof: by
  simp

@[simp high]

中文:
引理 op_singleton
  条件: (X : C)
  证明: by
  simp

@[simp high]
-/
lemma op_singleton (X : C) :
    (singleton X).op = singleton (op X) := by
  simp

@[simp high]
/--
lemma `unop_singleton` / 引理 `unop_singleton`

English:
lemma unop_singleton
  given: (X : Cᵒᵖ)
  proof: by
  simp

中文:
引理 unop_singleton
  条件: (X : Cᵒᵖ)
  证明: by
  simp
-/
lemma unop_singleton (X : Cᵒᵖ) :
    (singleton X).unop = singleton X.unop := by
  simp

end

section

variable [Category.{v} C]

instance (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] :
    P.op.IsClosedUnderIsomorphisms where
  of_iso e hX := P.prop_of_iso e.symm.unop hX

instance (P : ObjectProperty Cᵒᵖ) [P.IsClosedUnderIsomorphisms] :
    P.unop.IsClosedUnderIsomorphisms where
  of_iso e hX := P.prop_of_iso e.symm.op hX

/--
lemma `op_isoClosure` / 引理 `op_isoClosure`

English:
lemma op_isoClosure
  given: (P : ObjectProperty C)
  proof: by
  ext ⟨X⟩
  exact ⟨fun ⟨Y, h, ⟨e⟩⟩ => ⟨op Y, h, ⟨e.op.symm⟩⟩,
    fun ⟨Y, h, ⟨e⟩⟩ => ⟨Y.unop, h, ⟨e.unop.symm⟩⟩⟩

中文:
引理 op_isoClosure
  条件: (P : Object命题erty C)
  证明: by
  ext ⟨X⟩
  exact ⟨fun ⟨Y, h, ⟨e⟩⟩ => ⟨op Y, h, ⟨e.op.symm⟩⟩,
    fun ⟨Y, h, ⟨e⟩⟩ => ⟨Y.unop, h, ⟨e.unop.symm⟩⟩⟩

Depends on / 依赖: Y.unop, e.op.symm, e.unop.symm
-/
lemma op_isoClosure (P : ObjectProperty C) :
    P.isoClosure.op = P.op.isoClosure := by
  ext ⟨X⟩
  exact ⟨fun ⟨Y, h, ⟨e⟩⟩ => ⟨op Y, h, ⟨e.op.symm⟩⟩,
    fun ⟨Y, h, ⟨e⟩⟩ => ⟨Y.unop, h, ⟨e.unop.symm⟩⟩⟩

/--
lemma `unop_isoClosure` / 引理 `unop_isoClosure`

English:
lemma unop_isoClosure
  given: (P : ObjectProperty Cᵒᵖ)
  proof: by
  rw [← op_injective_iff]; rw [P.unop.op_isoClosure]; rw [op_unop]; rw [op_unop]

中文:
引理 unop_isoClosure
  条件: (P : Object命题erty Cᵒᵖ)
  证明: by
  rw [← op_injective_iff]; rw [P.unop.op_isoClosure]; rw [op_unop]; rw [op_unop]

Depends on / 依赖: P.unop.op_isoClosure, op_injective_iff, op_isoClosure, op_unop
-/
lemma unop_isoClosure (P : ObjectProperty Cᵒᵖ) :
    P.isoClosure.unop = P.unop.isoClosure := by
  rw [← op_injective_iff]; rw [P.unop.op_isoClosure]; rw [op_unop]; rw [op_unop]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given `P : ObjectProperty C`, this is the equivalence between `P.op.FullSubcategory`
and `P.FullSubcategoryᵒᵖ`. -/
@[simps]
/--
Definition of `opEquivalence` / `opEquivalence` 的定义

English:
definition opEquivalence
  signature: (P : ObjectProperty C)
  body: (P.lift P.op.ι.leftOp (fun X => X.unop.property)).rightOp
  inverse := P.op.lift P.ι.op (fun X => X.unop.property)
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp X := Quiver.Hom.unop_inj (by cat_disch)

@[simp]

中文:
定义 opEquivalence
  签名: (P : Object命题erty C)
  定义体: (P.lift P.op.ι.leftOp (fun X => X.unop.property)).rightOp
  inverse := P.op.lift P.ι.op (fun X => X.unop.property)
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp X := Quiver.Hom.unop_inj (by cat_disch)

@[simp]

Depends on / 依赖: P.lift, P.op, X.unop.property, leftOp, property, rightOp
-/
def opEquivalence (P : ObjectProperty C) : P.op.FullSubcategory ≌ P.FullSubcategoryᵒᵖ where
  functor := (P.lift P.op.ι.leftOp (fun X => X.unop.property)).rightOp
  inverse := P.op.lift P.ι.op (fun X => X.unop.property)
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp X := Quiver.Hom.unop_inj (by cat_disch)

@[simp]
/--
lemma `op_inf` / 引理 `op_inf`

English:
lemma op_inf
  given: (P Q : ObjectProperty C)
  statement: (P ⊓ Q).op = P.op ⊓ Q.op
  proof: rfl

@[simp]

中文:
引理 op_inf
  条件: (P Q : Object命题erty C)
  结论: (P ⊓ Q).op = P.op ⊓ Q.op
  证明: rfl

@[simp]
-/
lemma op_inf (P Q : ObjectProperty C) : (P ⊓ Q).op = P.op ⊓ Q.op := rfl

@[simp]
/--
lemma `op_sup` / 引理 `op_sup`

English:
lemma op_sup
  given: (P Q : ObjectProperty C)
  statement: (P ⊔ Q).op = P.op ⊔ Q.op
  proof: rfl

@[simp]

中文:
引理 op_sup
  条件: (P Q : Object命题erty C)
  结论: (P ⊔ Q).op = P.op ⊔ Q.op
  证明: rfl

@[simp]
-/
lemma op_sup (P Q : ObjectProperty C) : (P ⊔ Q).op = P.op ⊔ Q.op := rfl

@[simp]
/--
lemma `unop_inf` / 引理 `unop_inf`

English:
lemma unop_inf
  given: (P Q : ObjectProperty Cᵒᵖ)
  statement: (P ⊓ Q).unop = P.unop ⊓ Q.unop
  proof: rfl

@[simp]

中文:
引理 unop_inf
  条件: (P Q : Object命题erty Cᵒᵖ)
  结论: (P ⊓ Q).unop = P.unop ⊓ Q.unop
  证明: rfl

@[simp]
-/
lemma unop_inf (P Q : ObjectProperty Cᵒᵖ) : (P ⊓ Q).unop = P.unop ⊓ Q.unop := rfl

@[simp]
/--
lemma `unop_sup` / 引理 `unop_sup`

English:
lemma unop_sup
  given: (P Q : ObjectProperty Cᵒᵖ)
  statement: (P ⊔ Q).unop = P.unop ⊔ Q.unop
  proof: rfl

中文:
引理 unop_sup
  条件: (P Q : Object命题erty Cᵒᵖ)
  结论: (P ⊔ Q).unop = P.unop ⊔ Q.unop
  证明: rfl
-/
lemma unop_sup (P Q : ObjectProperty Cᵒᵖ) : (P ⊔ Q).unop = P.unop ⊔ Q.unop := rfl

end

end CategoryTheory.ObjectProperty
