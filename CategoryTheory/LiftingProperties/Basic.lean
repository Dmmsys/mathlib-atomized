/-
Copyright (c) 2021 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach, Joël Riou
-/
module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Retract

/-!
# Lifting properties

This file defines the lifting property of two morphisms in a category and
shows basic properties of this notion.

## Main results
- `HasLiftingProperty`: the definition of the lifting property

## Tags
lifting property

## TODO
1) direct/inverse images, adjunctions

-/

@[expose] public section

universe v

namespace CategoryTheory

open Category

variable {C : Type*} [Category* C] {A B B' X Y Y' : C} (i : A ⟶ B) (i' : B ⟶ B') (p : X ⟶ Y)
  (p' : Y ⟶ Y')

to_dual_name_hint Left Right, A Y, B X, I P

set_option linter.translate.warnInvalid false in
/-- `HasLiftingProperty i p` means that `i` has the left lifting
property with respect to `p`, or equivalently that `p` has
the right lifting property with respect to `i`. -/
@[to_dual self (reorder := A Y, B X, i p)]
/--
Definition of `HasLiftingProperty` / `HasLiftingProperty` 的定义

English:
class HasLiftingProperty
  parameters: : Prop where
  axioms and operations (1):
    - sq_hasLift : forall {f : A ⟶ X} {g : B ⟶ Y} (sq : CommSq f i p g), sq.HasLift

中文:
类 HasLiftingProperty
  参数: : 命题 where
  公理与运算 (1 个):
    - sq_hasLift : 对任意 {f : A ⟶ X} {g : B ⟶ Y} (sq : CommSq f i p g), sq.HasLift

Depends on / 依赖: HasLiftingProperty, HasLiftingProperty.mk, sq_hasLift
-/
class HasLiftingProperty : Prop where
  /-- Unique field expressing that any commutative square built from `f` and `g` has a lift -/
  sq_hasLift : forall {f : A ⟶ X} {g : B ⟶ Y} (sq : CommSq f i p g), sq.HasLift

attribute [to_dual self] HasLiftingProperty.sq_hasLift
attribute [to_dual self (reorder := A Y, B X, i p, sq_hasLift (f g))] HasLiftingProperty.mk

@[to_dual self]
instance (priority := 100) sq_hasLift_of_hasLiftingProperty {f : A ⟶ X} {g : B ⟶ Y}
    (sq : CommSq f i p g) [hip : HasLiftingProperty i p] : sq.HasLift := hip.sq_hasLift _

namespace HasLiftingProperty

variable {i p}

@[to_dual self]
/--
theorem `op` / 定理 `op`

English:
theorem op
  given: (h : HasLiftingProperty i p)
  statement: HasLiftingProperty p.op i.op
  proof: ⟨fun {f} {g} sq => by
    simp only [CommSq.HasLift.iff_unop, Quiver.Hom.unop_op]
    infer_instance⟩

@[to_dual self]

中文:
定理 op
  条件: (h : HasLifting命题erty i p)
  结论: HasLifting命题erty p.op i.op
  证明: ⟨fun {f} {g} sq => by
    simp only [CommSq.HasLift.iff_unop, Quiver.Hom.unop_op]
    infer_instance⟩

@[to_dual self]

Depends on / 依赖: CommSq, CommSq.HasLift.iff_unop, HasLift, Quiver, Quiver.Hom.unop_op, iff_unop, infer_instance, unop_op
-/
theorem op (h : HasLiftingProperty i p) : HasLiftingProperty p.op i.op :=
  ⟨fun {f} {g} sq => by
    simp only [CommSq.HasLift.iff_unop, Quiver.Hom.unop_op]
    infer_instance⟩

@[to_dual self]
/--
theorem `unop` / 定理 `unop`

English:
theorem unop
  given: {A B X Y : Cᵒᵖ} {i : A ⟶ B} {p : X ⟶ Y} (h : HasLiftingProperty i p)
  proof: ⟨fun {f} {g} sq => by
    rw [CommSq.HasLift.iff_op]
    simp only [Quiver.Hom.op_unop]
    infer_instance⟩

@[to_dual self]

中文:
定理 unop
  条件: {A B X Y : Cᵒᵖ} {i : A ⟶ B} {p : X ⟶ Y} (h : HasLifting命题erty i p)
  证明: ⟨fun {f} {g} sq => by
    rw [CommSq.HasLift.iff_op]
    simp only [Quiver.Hom.op_unop]
    infer_instance⟩

@[to_dual self]

Depends on / 依赖: CommSq, CommSq.HasLift.iff_op, HasLift, Quiver, Quiver.Hom.op_unop, iff_op, infer_instance, op_unop
-/
theorem unop {A B X Y : Cᵒᵖ} {i : A ⟶ B} {p : X ⟶ Y} (h : HasLiftingProperty i p) :
    HasLiftingProperty p.unop i.unop :=
  ⟨fun {f} {g} sq => by
    rw [CommSq.HasLift.iff_op]
    simp only [Quiver.Hom.op_unop]
    infer_instance⟩

@[to_dual self]
/--
theorem `iff_op` / 定理 `iff_op`

English:
theorem iff_op
  statement: HasLiftingProperty i p ↔ HasLiftingProperty p.op i.op
  proof: ⟨op, unop⟩

@[to_dual self]

中文:
定理 iff_op
  结论: HasLifting命题erty i p ↔ HasLifting命题erty p.op i.op
  证明: ⟨op, unop⟩

@[to_dual self]
-/
theorem iff_op : HasLiftingProperty i p ↔ HasLiftingProperty p.op i.op :=
  ⟨op, unop⟩

@[to_dual self]
/--
theorem `iff_unop` / 定理 `iff_unop`

English:
theorem iff_unop
  given: {A B X Y : Cᵒᵖ} (i : A ⟶ B) (p : X ⟶ Y)
  proof: ⟨unop, op⟩

中文:
定理 iff_unop
  条件: {A B X Y : Cᵒᵖ} (i : A ⟶ B) (p : X ⟶ Y)
  证明: ⟨unop, op⟩
-/
theorem iff_unop {A B X Y : Cᵒᵖ} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty i p ↔ HasLiftingProperty p.unop i.unop :=
  ⟨unop, op⟩

variable (i p)

@[to_dual]
instance (priority := 100) of_left_iso [IsIso i] : HasLiftingProperty i p :=
  ⟨fun {f} {g} sq =>
    CommSq.HasLift.mk'
      { l := inv i ≫ f
        fac_left := by simp only [IsIso.hom_inv_id_assoc]
        fac_right := by simp only [sq.w, assoc, IsIso.inv_hom_id_assoc] }⟩

@[to_dual]
/--
Instance `of_comp_left` / 实例 `of_comp_left`

English:
instance of_comp_left
  signature: [HasLiftingProperty i p] [HasLiftingProperty i' p]
  body: ⟨fun {f} {g} sq => by
    have fac := sq.w
    rw [assoc] at fac
    exact
      CommSq.HasLift.mk'
        { l := (CommSq.mk (CommSq.mk fac).fac_right).lift
          fac_left := by simp only [assoc, CommSq.fac_left]
          fac_right := by simp only [CommSq.fac_right] }⟩

中文:
实例 of_comp_left
  签名: [HasLifting命题erty i p] [HasLifting命题erty i' p]
  定义体: ⟨fun {f} {g} sq => by
    have fac := sq.w
    rw [assoc] at fac
    exact
      CommSq.HasLift.mk'
        { l := (CommSq.mk (CommSq.mk fac).fac_right).lift
          fac_left := by simp only [assoc, CommSq.fac_left]
          fac_right := by simp only [CommSq.fac_right] }⟩

Depends on / 依赖: CommSq, CommSq.HasLift.mk, CommSq.fac_left, CommSq.fac_right, CommSq.mk, HasLift, fac_left, fac_right, sq.w
-/
instance of_comp_left [HasLiftingProperty i p] [HasLiftingProperty i' p] :
    HasLiftingProperty (i ≫ i') p :=
  ⟨fun {f} {g} sq => by
    have fac := sq.w
    rw [assoc] at fac
    exact
      CommSq.HasLift.mk'
        { l := (CommSq.mk (CommSq.mk fac).fac_right).lift
          fac_left := by simp only [assoc, CommSq.fac_left]
          fac_right := by simp only [CommSq.fac_right] }⟩

set_option backward.isDefEq.respectTransparency false in
@[to_dual (reorder := i i' e p)]
/--
theorem `of_arrow_iso_left` / 定理 `of_arrow_iso_left`

English:
theorem of_arrow_iso_left
  statement: {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'}
  proof: by
  rw [Arrow.iso_w' e]
  infer_instance

@[to_dual (reorder := i i' e p)]

中文:
定理 of_arrow_iso_left
  结论: {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'}
  证明: by
  rw [Arrow.iso_w' e]
  infer_instance

@[to_dual (reorder := i i' e p)]

Depends on / 依赖: Arrow.iso_w, infer_instance, iso_w
-/
theorem of_arrow_iso_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'}
    (e : Arrow.mk i ≅ Arrow.mk i') (p : X ⟶ Y) [hip : HasLiftingProperty i p] :
    HasLiftingProperty i' p := by
  rw [Arrow.iso_w' e]
  infer_instance

@[to_dual (reorder := i i' e p)]
/--
theorem `iff_of_arrow_iso_left` / 定理 `iff_of_arrow_iso_left`

English:
theorem iff_of_arrow_iso_left
  statement: {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'}
  proof: by
  constructor <;> intro
  exacts [of_arrow_iso_left e p, of_arrow_iso_left e.symm p]

中文:
定理 iff_of_arrow_iso_left
  结论: {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'}
  证明: by
  constructor <;> intro
  exacts [of_arrow_iso_left e p, of_arrow_iso_left e.symm p]

Depends on / 依赖: e.symm, exacts, of_arrow_iso_left
-/
theorem iff_of_arrow_iso_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'}
    (e : Arrow.mk i ≅ Arrow.mk i') (p : X ⟶ Y) :
    HasLiftingProperty i p ↔ HasLiftingProperty i' p := by
  constructor <;> intro
  exacts [of_arrow_iso_left e p, of_arrow_iso_left e.symm p]

end HasLiftingProperty

set_option backward.isDefEq.respectTransparency false in
@[to_dual]
/--
lemma `RetractArrow.rightLiftingProperty` / 引理 `RetractArrow.rightLiftingProperty`

English:
lemma RetractArrow.rightLiftingProperty
  proof: fun {u v} sq =>
    have sq' : CommSq (u ≫ h.i.left) g f (v ≫ h.i.right) :=
      ⟨by rw [← sq.w_assoc, Category.assoc, RetractArrow.i_w]⟩
    ⟨⟨{ l := sq'.lift ≫ h.r.left}⟩⟩

中文:
引理 RetractArrow.rightLiftingProperty
  证明: fun {u v} sq =>
    have sq' : CommSq (u ≫ h.i.left) g f (v ≫ h.i.right) :=
      ⟨by rw [← sq.w_assoc, Category.assoc, RetractArrow.i_w]⟩
    ⟨⟨{ l := sq'.lift ≫ h.r.left}⟩⟩
-/
lemma RetractArrow.rightLiftingProperty
    {X Y Z W X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (h : RetractArrow f' f) (g : Z ⟶ W) [HasLiftingProperty g f] : HasLiftingProperty g f' where
  sq_hasLift := fun {u v} sq =>
    have sq' : CommSq (u ≫ h.i.left) g f (v ≫ h.i.right) :=
      ⟨by rw [← sq.w_assoc, Category.assoc, RetractArrow.i_w]⟩
    ⟨⟨{ l := sq'.lift ≫ h.r.left}⟩⟩

namespace Arrow

/-- Given a morphism `φ : f ⟶ g` in the category `Arrow C`, this is an
abbreviation for the `CommSq.LiftStruct` structure for
the square corresponding to `φ`. -/
@[to_dual self]
/--
Definition of `LiftStruct` / `LiftStruct` 的定义

English:
abbreviation LiftStruct
  signature: {f g : Arrow C} (φ : f ⟶ g)
  body: (CommSq.mk φ.w).LiftStruct

中文:
缩写 LiftStruct
  签名: {f g : Arrow C} (φ : f ⟶ g)
  定义体: (CommSq.mk φ.w).LiftStruct

Depends on / 依赖: CommSq, CommSq.mk, LiftStruct
-/
abbrev LiftStruct {f g : Arrow C} (φ : f ⟶ g) := (CommSq.mk φ.w).LiftStruct

set_option backward.isDefEq.respectTransparency false in
@[to_dual self]
/--
lemma `hasLiftingProperty_iff` / 引理 `hasLiftingProperty_iff`

English:
lemma hasLiftingProperty_iff
  given: {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)
  proof: by
  constructor
  · intro _ φ
    have sq : CommSq φ.left i p φ.right := CommSq.mk φ.w
    exact ⟨{ l := sq.lift }⟩
  · intro h
    exact ⟨fun {f g} sq => ⟨h (Arrow.homMk f g sq.w)⟩⟩

中文:
引理 hasLiftingProperty_iff
  条件: {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)
  证明: by
  constructor
  · intro _ φ
    have sq : CommSq φ.left i p φ.right := CommSq.mk φ.w
    exact ⟨{ l := sq.lift }⟩
  · intro h
    exact ⟨fun {f g} sq => ⟨h (Arrow.homMk f g sq.w)⟩⟩

Depends on / 依赖: Arrow.homMk, CommSq, CommSq.mk, sq.lift, sq.w
-/
lemma hasLiftingProperty_iff {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty i p ↔
      forall (φ : Arrow.mk i ⟶ Arrow.mk p), Nonempty (LiftStruct φ) := by
  constructor
  · intro _ φ
    have sq : CommSq φ.left i p φ.right := CommSq.mk φ.w
    exact ⟨{ l := sq.lift }⟩
  · intro h
    exact ⟨fun {f g} sq => ⟨h (Arrow.homMk f g sq.w)⟩⟩

end Arrow

/-- Given morphisms `i : A ⟶ B`, `p : X ⟶ Y`, `t : A ⟶ X`,
this is the property that a lifting exists for all squares
with `i` on left, `p` on the right and `t` on the top. -/
@[to_dual (rename := t -> b) (reorder := i p)
/-- Given morphisms `i : A ⟶ B`, `p : X ⟶ Y`, `b : B ⟶ Y`,
this is the property that a lifting exists for all squares
with `i` on left, `p` on the right and `b` on the bottom. -/]
/--
Definition of `HasLiftingPropertyFixedTop` / `HasLiftingPropertyFixedTop` 的定义

English:
definition HasLiftingPropertyFixedTop
  signature: (t : A ⟶ X)
  body: forall (b : B ⟶ Y) (sq : CommSq t i p b), sq.HasLift

中文:
定义 HasLiftingPropertyFixedTop
  签名: (t : A ⟶ X)
  定义体: forall (b : B ⟶ Y) (sq : CommSq t i p b), sq.HasLift

Depends on / 依赖: CommSq, HasLift, sq.HasLift
-/
def HasLiftingPropertyFixedTop (t : A ⟶ X) : Prop :=
  forall (b : B ⟶ Y) (sq : CommSq t i p b), sq.HasLift

end CategoryTheory
