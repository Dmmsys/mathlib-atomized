/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!

# Lifting properties and adjunction

In this file, we obtain `Adjunction.HasLiftingProperty_iff`, which states
that when we have an adjunction `adj : G ⊣ F` between two functors `G : C ⥤ D`
and `F : D ⥤ C`, then a morphism of the form `G.map i` has the left lifting
property in `D` with respect to a morphism `p` if and only the morphism `i`
has the left lifting property in `C` with respect to `F.map p`.

-/

@[expose] public section


namespace CategoryTheory

open Category

variable {C D : Type*} [Category* C] [Category* D] {G : C ⥤ D} {F : D ⥤ C}

to_dual_name_hint Left Right

namespace CommSq

section

variable {A B : C} {X Y : D} {i : A ⟶ B} {p : X ⟶ Y} {u : G.obj A ⟶ X} {v : G.obj B ⟶ Y}

/-- When we have an adjunction `G ⊣ F`, any commutative square where the left
map is of the form `G.map i` and the right map is `p` has an "adjoint" commutative
square whose left map is `i` and whose right map is `F.map p`. -/
@[to_dual
/-- When we have an adjunction `G ⊣ F`, any commutative square where the left
map is of the form `i` and the right map is `F.map p` has an "adjoint" commutative
square whose left map is `G.map i` and whose right map is `p`. -/]
/--
theorem `right_adjoint` / 定理 `right_adjoint`

English:
theorem right_adjoint
  given: (sq : CommSq u (G.map i) p v) (adj : G ⊣ F)
  proof: ⟨by
    simp only [Adjunction.homEquiv_unit, assoc, ← F.map_comp, sq.w]
    rw [F.map_comp]; rw [Adjunction.unit_naturality_assoc]⟩

中文:
定理 right_adjoint
  条件: (sq : 交换Sq u (G.map i) p v) (adj : G ⊣ F)
  证明: ⟨by
    simp only [Adjunction.homEquiv_unit, assoc, ← F.map_comp, sq.w]
    rw [F.map_comp]; rw [Adjunction.unit_naturality_assoc]⟩

Depends on / 依赖: Adjunction, Adjunction.homEquiv_unit, Adjunction.unit_naturality_assoc, F.map_comp, homEquiv_unit, map_comp, sq.w, unit_naturality_assoc
-/
theorem right_adjoint (sq : CommSq u (G.map i) p v) (adj : G ⊣ F) :
    CommSq (adj.homEquiv _ _ u) i (F.map p) (adj.homEquiv _ _ v) :=
  ⟨by
    simp only [Adjunction.homEquiv_unit, assoc, ← F.map_comp, sq.w]
    rw [F.map_comp]; rw [Adjunction.unit_naturality_assoc]⟩

variable (sq : CommSq u (G.map i) p v) (adj : G ⊣ F)

/-- The liftings of a commutative are in bijection with the liftings of its (right)
adjoint square. -/
@[to_dual
/-- The liftings of a commutative are in bijection with the liftings of its (left)
adjoint square. -/]
/--
Definition of `rightAdjointLiftStructEquiv` / `rightAdjointLiftStructEquiv` 的定义

English:
definition rightAdjointLiftStructEquiv
  signature: : sq.LiftStruct ≃ (sq.right_adjoint adj).LiftStruct where
  body: { l := adj.homEquiv _ _ l.l
      fac_left := by rw [← adj.homEquiv_naturality_left, l.fac_left]
      fac_right := by rw [← Adjunction.homEquiv_naturality_right, l.fac_right] }
  invFun l :=
    { l := (adj.homEquiv _ _).symm l.l
      fac_left := by
        rw [← Adjunction.homEquiv_naturality_left_symm]; rw [l.fac_left]
        apply (adj.homEquiv _ _).left_inv
      fac_right := by
        rw [← Adjunction.homEquiv_naturality_right_symm]; rw [l.fac_right]
        apply (adj.homEquiv _ _).left_inv }
  left_inv := by cat_disch
  right_inv := by cat_disch

中文:
定义 rightAdjointLiftStructEquiv
  签名: : sq.LiftStruct ≃ (sq.right_adjoint adj).LiftStruct where
  定义体: { l := adj.homEquiv _ _ l.l
      fac_left := by rw [← adj.homEquiv_naturality_left, l.fac_left]
      fac_right := by rw [← Adjunction.homEquiv_naturality_right, l.fac_right] }
  invFun l :=
    { l := (adj.homEquiv _ _).symm l.l
      fac_left := by
        rw [← Adjunction.homEquiv_naturality_left_symm]; rw [l.fac_left]
        apply (adj.homEquiv _ _).left_inv
      fac_right := by
        rw [← Adjunction.homEquiv_naturality_right_symm]; rw [l.fac_right]
        apply (adj.homEquiv _ _).left_inv }
  left_inv := by cat_disch
  right_inv := by cat_disch

Depends on / 依赖: Adjunction, Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right_symm, adj.homEquiv, adj.homEquiv_naturality_left, cat_disch, fac_left, fac_right, homEquiv, homEquiv_naturality_left, homEquiv_naturality_left_symm, homEquiv_naturality_right, homEquiv_naturality_right_symm, invFun, l.fac_left, l.fac_right, left_inv, right_inv
-/
def rightAdjointLiftStructEquiv : sq.LiftStruct ≃ (sq.right_adjoint adj).LiftStruct where
  toFun l :=
    { l := adj.homEquiv _ _ l.l
      fac_left := by rw [← adj.homEquiv_naturality_left, l.fac_left]
      fac_right := by rw [← Adjunction.homEquiv_naturality_right, l.fac_right] }
  invFun l :=
    { l := (adj.homEquiv _ _).symm l.l
      fac_left := by
        rw [← Adjunction.homEquiv_naturality_left_symm]; rw [l.fac_left]
        apply (adj.homEquiv _ _).left_inv
      fac_right := by
        rw [← Adjunction.homEquiv_naturality_right_symm]; rw [l.fac_right]
        apply (adj.homEquiv _ _).left_inv }
  left_inv := by cat_disch
  right_inv := by cat_disch

/-- A (right) adjoint square has a lifting if and only if the original square has a lifting. -/
@[to_dual
/-- A (left) adjoint square has a lifting if and only if the original square has a lifting. -/]
/--
theorem `right_adjoint_hasLift_iff` / 定理 `right_adjoint_hasLift_iff`

English:
theorem right_adjoint_hasLift_iff
  statement: HasLift (sq.right_adjoint adj) ↔ HasLift sq
  proof: by
  simp only [HasLift.iff]
  exact Equiv.nonempty_congr (sq.rightAdjointLiftStructEquiv adj).symm

@[to_dual]

中文:
定理 right_adjoint_hasLift_iff
  结论: 有Lift (sq.right_adjoint adj) ↔ 有Lift sq
  证明: by
  simp only [HasLift.iff]
  exact Equiv.nonempty_congr (sq.rightAdjointLiftStructEquiv adj).symm

@[to_dual]

Depends on / 依赖: Equiv.nonempty_congr, HasLift, HasLift.iff, nonempty_congr, rightAdjointLiftStructEquiv, sq.rightAdjointLiftStructEquiv
-/
theorem right_adjoint_hasLift_iff : HasLift (sq.right_adjoint adj) ↔ HasLift sq := by
  simp only [HasLift.iff]
  exact Equiv.nonempty_congr (sq.rightAdjointLiftStructEquiv adj).symm

@[to_dual]
/--
Instance `instHasLiftRightAdjoin` / 实例 `instHasLiftRightAdjoin`

English:
instance instHasLiftRightAdjoin
  signature: [HasLift sq]
  body: by
  rw [right_adjoint_hasLift_iff]
  infer_instance

中文:
实例 instHasLiftRightAdjoin
  签名: [有Lift sq]
  定义体: by
  rw [right_adjoint_hasLift_iff]
  infer_instance

Depends on / 依赖: infer_instance, right_adjoint_hasLift_iff
-/
instance instHasLiftRightAdjoin [HasLift sq] : HasLift (sq.right_adjoint adj) := by
  rw [right_adjoint_hasLift_iff]
  infer_instance

end

end CommSq

namespace Adjunction

@[to_dual none]
/--
theorem `hasLiftingProperty_iff` / 定理 `hasLiftingProperty_iff`

English:
theorem hasLiftingProperty_iff
  given: (adj : G ⊣ F) {A B : C} {X Y : D} (i : A ⟶ B) (p : X ⟶ Y)
  proof: by
  constructor <;> intro <;> constructor <;> intro f g sq
  · rw [← sq.left_adjoint_hasLift_iff adj]
    infer_instance
  · rw [← sq.right_adjoint_hasLift_iff adj]
    infer_instance

中文:
定理 hasLiftingProperty_iff
  条件: (adj : G ⊣ F) {A B : C} {X Y : D} (i : A ⟶ B) (p : X ⟶ Y)
  证明: by
  constructor <;> intro <;> constructor <;> intro f g sq
  · rw [← sq.left_adjoint_hasLift_iff adj]
    infer_instance
  · rw [← sq.right_adjoint_hasLift_iff adj]
    infer_instance

Depends on / 依赖: infer_instance, left_adjoint_hasLift_iff, right_adjoint_hasLift_iff, sq.left_adjoint_hasLift_iff, sq.right_adjoint_hasLift_iff
-/
theorem hasLiftingProperty_iff (adj : G ⊣ F) {A B : C} {X Y : D} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty (G.map i) p ↔ HasLiftingProperty i (F.map p) := by
  constructor <;> intro <;> constructor <;> intro f g sq
  · rw [← sq.left_adjoint_hasLift_iff adj]
    infer_instance
  · rw [← sq.right_adjoint_hasLift_iff adj]
    infer_instance

end Adjunction

end CategoryTheory
