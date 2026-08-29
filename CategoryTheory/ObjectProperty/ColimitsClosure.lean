/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.LimitsClosure
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape

/-!
# Closure of a property of objects under colimits of certain shapes

In this file, given a property `P` of objects in a category `C` and
family of categories `J : α → Type _`, we introduce the closure
`P.colimitsClosure J` of `P` under colimits of shapes `J a` for all `a : α`,
and under certain smallness assumptions, we show that it is essentially small.

(We deduce these results about the closure under colimits by dualising the
results in the file `Mathlib/CategoryTheory/ObjectProperty/LimitsClosure.lean`.)

-/

public section

universe w w' t v' u' v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)
  {α : Type t} (J : α -> Type u') [forall a, Category.{v'} (J a)]

/--
Inductive type `colimitsClosure` / 归纳类型 `colimitsClosure`

English:
inductive colimitsClosure
  parameters: : ObjectProperty C
  constructors (3):
    - of_mem: (X : C) (hX : P X) : colimitsClosure X
    - of_isoClosure: {X Y : C} (e : X ≅ Y) (hX : colimitsClosure X) : colimitsClosure Y
    - of_colimitPresentation: {X : C} {a : α} (pres : ColimitPresentation (J a) X) (h : forall j, colimitsClosure (pres.diag.obj j)) : colimitsClosure X

中文:
归纳类型 colimitsClosure
  参数: : ObjectProperty C
  构造子 (3 个):
    - of_mem: (X : C) (hX : P X) : colimitsClosure X
    - of_isoClosure: {X Y : C} (e : X ≅ Y) (hX : colimitsClosure X) : colimitsClosure Y
    - of_colimitPresentation: {X : C} {a : α} (pres : 余limitPresentation (J a) X) (h : 对任意 j, colimitsClosure (pres.diag.obj j)) : colimitsClosure X
-/
inductive colimitsClosure : ObjectProperty C
  | of_mem (X : C) (hX : P X) : colimitsClosure X
  | of_isoClosure {X Y : C} (e : X ≅ Y) (hX : colimitsClosure X) : colimitsClosure Y
  | of_colimitPresentation {X : C} {a : α} (pres : ColimitPresentation (J a) X)
      (h : forall j, colimitsClosure (pres.diag.obj j)) : colimitsClosure X

@[simp]
/--
lemma `le_colimitsClosure` / 引理 `le_colimitsClosure`

English:
lemma le_colimitsClosure
  statement: P <= P.colimitsClosure J
  proof: fun X hX => .of_mem X hX

中文:
引理 le_colimitsClosure
  结论: P <= P.colimitsClosure J
  证明: fun X hX => .of_mem X hX

Depends on / 依赖: of_mem
-/
lemma le_colimitsClosure : P <= P.colimitsClosure J :=
  fun X hX => .of_mem X hX

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.Nonempty]
  signature: : (P.colimitsClosure J).Nonempty
  body: .mono (P.le_colimitsClosure J)

中文:
实例 [P.非空]
  签名: : (P.colimitsClosure J).非空
  定义体: .mono (P.le_colimitsClosure J)

Depends on / 依赖: P.le_colimitsClosure, le_colimitsClosure
-/
instance [P.Nonempty] : (P.colimitsClosure J).Nonempty :=
  .mono (P.le_colimitsClosure J)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (P.colimitsClosure J).IsClosedUnderIsomorphisms
  body: .of_isoClosure e hX

中文:
实例 :
  签名: (P.colimitsClosure J).在同构下封闭
  定义体: .of_isoClosure e hX

Depends on / 依赖: of_isoClosure
-/
instance : (P.colimitsClosure J).IsClosedUnderIsomorphisms where
  of_iso e hX := .of_isoClosure e hX

instance (a : α) : (P.colimitsClosure J).IsClosedUnderColimitsOfShape (J a) where
  colimitsOfShape_le := by
    rintro X ⟨hX⟩
    exact .of_colimitPresentation hX.toColimitPresentation hX.prop_diag_obj

variable {P J} in
/--
lemma `colimitsClosure_le` / 引理 `colimitsClosure_le`

English:
lemma colimitsClosure_le
  statement: {Q : ObjectProperty C} [Q.IsClosedUnderIsomorphisms]
  proof: by
  intro X hX
  induction hX with
  | of_mem X hX => exact h _ hX
  | of_isoClosure e hX hX' => exact Q.prop_of_iso e hX'
  | of_colimitPresentation pres h h' => exact Q.prop_of_isColimit pres.isColimit h'

中文:
引理 colimitsClosure_le
  结论: {Q : ObjectProperty C} [Q.在同构下封闭]
  证明: by
  intro X hX
  induction hX with
  | of_mem X hX => exact h _ hX
  | of_isoClosure e hX hX' => exact Q.prop_of_iso e hX'
  | of_colimitPresentation pres h h' => exact Q.prop_of_isColimit pres.isColimit h'

Depends on / 依赖: Q.prop_of_isColimit, Q.prop_of_iso, isColimit, of_colimitPresentation, of_isoClosure, of_mem, pres.isColimit, prop_of_isColimit, prop_of_iso
-/
lemma colimitsClosure_le {Q : ObjectProperty C} [Q.IsClosedUnderIsomorphisms]
    [forall (a : α), Q.IsClosedUnderColimitsOfShape (J a)] (h : P <= Q) :
    P.colimitsClosure J <= Q := by
  intro X hX
  induction hX with
  | of_mem X hX => exact h _ hX
  | of_isoClosure e hX hX' => exact Q.prop_of_iso e hX'
  | of_colimitPresentation pres h h' => exact Q.prop_of_isColimit pres.isColimit h'

variable {P} in
/--
lemma `colimitsClosure_monotone` / 引理 `colimitsClosure_monotone`

English:
lemma colimitsClosure_monotone
  given: {Q : ObjectProperty C} (h : P <= Q)
  proof: colimitsClosure_le (h.trans (Q.le_colimitsClosure J))

中文:
引理 colimitsClosure_monotone
  条件: {Q : ObjectProperty C} (h : P <= Q)
  证明: colimitsClosure_le (h.trans (Q.le_colimitsClosure J))

Depends on / 依赖: Q.le_colimitsClosure, colimitsClosure_le, h.trans, le_colimitsClosure
-/
lemma colimitsClosure_monotone {Q : ObjectProperty C} (h : P <= Q) :
    P.colimitsClosure J <= Q.colimitsClosure J :=
  colimitsClosure_le (h.trans (Q.le_colimitsClosure J))

/--
lemma `colimitsClosure_eq_self` / 引理 `colimitsClosure_eq_self`

English:
lemma colimitsClosure_eq_self
  statement: [P.IsClosedUnderIsomorphisms]
  proof: le_antisymm (colimitsClosure_le (le_refl P)) (P.le_colimitsClosure J)

@[simp]

中文:
引理 colimitsClosure_eq_self
  结论: [P.在同构下封闭]
  证明: le_antisymm (colimitsClosure_le (le_refl P)) (P.le_colimitsClosure J)

@[simp]

Depends on / 依赖: P.le_colimitsClosure, colimitsClosure_le, le_antisymm, le_colimitsClosure, le_refl
-/
lemma colimitsClosure_eq_self [P.IsClosedUnderIsomorphisms]
    [forall (a : α), P.IsClosedUnderColimitsOfShape (J a)] : P.colimitsClosure J = P :=
  le_antisymm (colimitsClosure_le (le_refl P)) (P.le_colimitsClosure J)

@[simp]
/--
lemma `colimitsClosure_bot` / 引理 `colimitsClosure_bot`

English:
lemma colimitsClosure_bot
  given: [forall (a : α), Nonempty (J a)]
  proof: colimitsClosure_eq_self _ _

@[simp]

中文:
引理 colimitsClosure_bot
  条件: [对任意 (a : α), 非空 (J a)]
  证明: colimitsClosure_eq_self _ _

@[simp]

Depends on / 依赖: colimitsClosure_eq_self
-/
lemma colimitsClosure_bot [forall (a : α), Nonempty (J a)] :
    colimitsClosure (⊥ : ObjectProperty C) J = ⊥ :=
  colimitsClosure_eq_self _ _

@[simp]
/--
lemma `colimitsClosure_top` / 引理 `colimitsClosure_top`

English:
lemma colimitsClosure_top
  statement: colimitsClosure (⊤ : ObjectProperty C) J = ⊤
  proof: colimitsClosure_eq_self _ _

中文:
引理 colimitsClosure_top
  结论: colimitsClosure (⊤ : ObjectProperty C) J = ⊤
  证明: colimitsClosure_eq_self _ _

Depends on / 依赖: colimitsClosure_eq_self, infer_instance, truncLE
-/
lemma colimitsClosure_top : colimitsClosure (⊤ : ObjectProperty C) J = ⊤ :=
  colimitsClosure_eq_self _ _

/--
lemma `colimitsClosure_isoClosure` / 引理 `colimitsClosure_isoClosure`

English:
lemma colimitsClosure_isoClosure
  proof: by
  refine le_antisymm (colimitsClosure_le ?_)
    (colimitsClosure_monotone _ P.le_isoClosure)
  rw [isoClosure_le_iff]
  exact le_colimitsClosure P J

中文:
引理 colimitsClosure_isoClosure
  证明: by
  refine le_antisymm (colimitsClosure_le ?_)
    (colimitsClosure_monotone _ P.le_isoClosure)
  rw [isoClosure_le_iff]
  exact le_colimitsClosure P J

Depends on / 依赖: P.le_isoClosure, colimitsClosure_le, colimitsClosure_monotone, infer_instance, isoClosure_le_iff, le_antisymm, le_colimitsClosure, le_isoClosure, truncGT
-/
lemma colimitsClosure_isoClosure :
    P.isoClosure.colimitsClosure J = P.colimitsClosure J := by
  refine le_antisymm (colimitsClosure_le ?_)
    (colimitsClosure_monotone _ P.le_isoClosure)
  rw [isoClosure_le_iff]
  exact le_colimitsClosure P J

/--
Definition of `colimitClosure` / `colimitClosure` 的定义

English:
abbreviation colimitClosure
  signature: (J : Type*) [Category* J]
  body: P.colimitsClosure (fun (_ : Unit) => J)

中文:
缩写 colimitClosure
  签名: (J : 类型) [范畴* J]
  定义体: P.colimitsClosure (fun (_ : Unit) => J)

Depends on / 依赖: P.colimitsClosure, colimitsClosure
-/
abbrev colimitClosure (J : Type*) [Category* J] : ObjectProperty C :=
  P.colimitsClosure (fun (_ : Unit) => J)

instance (J : Type*) [Category* J] : (P.colimitClosure J).IsClosedUnderColimitsOfShape J :=
  P.instIsClosedUnderColimitsOfShapeColimitsClosure _ ()

/--
lemma `colimitsClosure_eq_unop_limitsClosure` / 引理 `colimitsClosure_eq_unop_limitsClosure`

English:
lemma colimitsClosure_eq_unop_limitsClosure
  proof: by
  refine le_antisymm ?_ ?_
  · apply colimitsClosure_le
    rw [← op_monotone_iff]; rw [op_unop]
    apply le_limitsClosure
  · rw [← op_monotone_iff, op_unop]
    apply limitsClosure_le
    rw [op_monotone_iff]
    apply le_colimitsClosure

中文:
引理 colimitsClosure_eq_unop_limitsClosure
  证明: by
  refine le_antisymm ?_ ?_
  · apply colimitsClosure_le
    rw [← op_monotone_iff]; rw [op_unop]
    apply le_limitsClosure
  · rw [← op_monotone_iff, op_unop]
    apply limitsClosure_le
    rw [op_monotone_iff]
    apply le_colimitsClosure

Depends on / 依赖: colimitsClosure_le, le_antisymm, le_colimitsClosure, le_limitsClosure, limitsClosure_le, op_monotone_iff, op_unop
-/
lemma colimitsClosure_eq_unop_limitsClosure :
    P.colimitsClosure J = (P.op.limitsClosure (fun a => (J a)ᵒᵖ)).unop := by
  refine le_antisymm ?_ ?_
  · apply colimitsClosure_le
    rw [← op_monotone_iff]; rw [op_unop]
    apply le_limitsClosure
  · rw [← op_monotone_iff, op_unop]
    apply limitsClosure_le
    rw [op_monotone_iff]
    apply le_colimitsClosure

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ObjectProperty.EssentiallySmall.{w}
  signature: P] [LocallySmall.{w} C] [Small.{w} α]
  body: by
  rw [colimitsClosure_eq_unop_limitsClosure]
  have (a : α) : Small.{w} (J a)ᵒᵖ := Opposite.small
  infer_instance

中文:
实例 [ObjectProperty.EssentiallySmall.{w}
  签名: P] [LocallySmall.{w} C] [Small.{w} α]
  定义体: by
  rw [colimitsClosure_eq_unop_limitsClosure]
  have (a : α) : Small.{w} (J a)ᵒᵖ := Opposite.small
  infer_instance

Depends on / 依赖: Opposite, Opposite.small, colimitsClosure_eq_unop_limitsClosure, infer_instance
-/
instance [ObjectProperty.EssentiallySmall.{w} P] [LocallySmall.{w} C] [Small.{w} α]
    [forall a, Small.{w} (J a)] [forall a, LocallySmall.{w} (J a)] :
    ObjectProperty.EssentiallySmall.{w} (P.colimitsClosure J) := by
  rw [colimitsClosure_eq_unop_limitsClosure]
  have (a : α) : Small.{w} (J a)ᵒᵖ := Opposite.small
  infer_instance

end CategoryTheory.ObjectProperty
