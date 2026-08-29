/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.GuitartExact.VerticalComposition

/-!
# The opposite of a Guitart exact square

A `2`-square is Guitart exact iff the opposite (transposed) `2`-square
is Guitart exact.

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Category

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}

namespace TwoSquare

variable (w : TwoSquare T L R B)

section

variable {X₃ : C₃ᵒᵖ} {X₂ : C₂ᵒᵖ} (g : B.op.obj X₃ ⟶ R.op.obj X₂)

namespace structuredArrowRightwardsOpEquivalence

/-- Auxiliary definition for `structuredArrowRightwardsOpEquivalence`. -/
@[simps!]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: :
  body: CostructuredArrowDownwards.mk _ _ f.unop.right.left.unop
      f.unop.right.hom.unop f.unop.hom.left.unop
      (Quiver.Hom.op_inj (by simpa using! CostructuredArrow.w f.unop.hom))
  map {f f'} φ :=
    CostructuredArrow.homMk
      (StructuredArrow.homMk (φ.unop.right.left.unop)
        (Quiver.Hom

中文:
定义 functor
  签名: :
  定义体: CostructuredArrowDownwards.mk _ _ f.unop.right.left.unop
      f.unop.right.hom.unop f.unop.hom.left.unop
      (Quiver.Hom.op_inj (by simpa using! CostructuredArrow.w f.unop.hom))
  map {f f'} φ :=
    CostructuredArrow.homMk
      (StructuredArrow.homMk (φ.unop.right.left.unop)
        (Quiver.Hom

Depends on / 依赖: CostructuredArrowDownwards, CostructuredArrowDownwards.mk, f.unop.right.left.unop
-/
def functor :
    (w.op.StructuredArrowRightwards g)ᵒᵖ ⥤
      w.CostructuredArrowDownwards g.unop where
  obj f := CostructuredArrowDownwards.mk _ _ f.unop.right.left.unop
      f.unop.right.hom.unop f.unop.hom.left.unop
      (Quiver.Hom.op_inj (by simpa using! CostructuredArrow.w f.unop.hom))
  map {f f'} φ :=
    CostructuredArrow.homMk
      (StructuredArrow.homMk (φ.unop.right.left.unop)
        (Quiver.Hom.op_inj (CostructuredArrow.w φ.unop.right))) (by
          ext
          exact Quiver.Hom.op_inj
            ((CostructuredArrow.proj _ _).congr_map (StructuredArrow.w φ.unop)))

/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: :
  body: Opposite.op
    (StructuredArrowRightwards.mk _ _ (Opposite.op f.left.right)
      f.hom.right.op f.left.hom.op (Quiver.Hom.unop_inj (StructuredArrow.w f.hom)))
  map {f f'} φ :=
    (StructuredArrow.homMk
      (CostructuredArrow.homMk (φ.left.right.op)
        (Quiver.Hom.unop_inj (by exact Struct

中文:
定义 inverse
  签名: :
  定义体: Opposite.op
    (StructuredArrowRightwards.mk _ _ (Opposite.op f.left.right)
      f.hom.right.op f.left.hom.op (Quiver.Hom.unop_inj (StructuredArrow.w f.hom)))
  map {f f'} φ :=
    (StructuredArrow.homMk
      (CostructuredArrow.homMk (φ.left.right.op)
        (Quiver.Hom.unop_inj (by exact Struct

Depends on / 依赖: Opposite, Opposite.op
-/
def inverse :
    w.CostructuredArrowDownwards g.unop ⥤
      (w.op.StructuredArrowRightwards g)ᵒᵖ where
  obj f := Opposite.op
    (StructuredArrowRightwards.mk _ _ (Opposite.op f.left.right)
      f.hom.right.op f.left.hom.op (Quiver.Hom.unop_inj (StructuredArrow.w f.hom)))
  map {f f'} φ :=
    (StructuredArrow.homMk
      (CostructuredArrow.homMk (φ.left.right.op)
        (Quiver.Hom.unop_inj (by exact StructuredArrow.w φ.left)))
          (by
            ext
            exact Quiver.Hom.unop_inj
              ((StructuredArrow.proj _ _).congr_map (CostructuredArrow.w φ)))).op

end structuredArrowRightwardsOpEquivalence

set_option backward.isDefEq.respectTransparency false in
/-- If `w : TwoSquare T L R B`, and `g : B.op.obj X₃ ⟶ R.op.obj X₂`, this is
the obvious equivalence of categories between
`(w.op.StructuredArrowRightwards g)ᵒᵖ` and `w.CostructuredArrowDownwards g.unop`. -/
@[simps]
/--
Definition of `structuredArrowRightwardsOpEquivalence` / `structuredArrowRightwardsOpEquivalence` 的定义

English:
definition structuredArrowRightwardsOpEquivalence
  signature: :
  body: structuredArrowRightwardsOpEquivalence.functor w g
  inverse := structuredArrowRightwardsOpEquivalence.inverse w g
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 structuredArrowRightwardsOpEquivalence
  签名: :
  定义体: structuredArrowRightwardsOpEquivalence.functor w g
  inverse := structuredArrowRightwardsOpEquivalence.inverse w g
  unitIso := Iso.refl _
  counitIso := Iso.refl _

Depends on / 依赖: functor, structuredArrowRightwardsOpEquivalence, structuredArrowRightwardsOpEquivalence.functor
-/
def structuredArrowRightwardsOpEquivalence :
    (w.op.StructuredArrowRightwards g)ᵒᵖ ≌
      w.CostructuredArrowDownwards g.unop where
  functor := structuredArrowRightwardsOpEquivalence.functor w g
  inverse := structuredArrowRightwardsOpEquivalence.inverse w g
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [w.GuitartExact]
  signature: : w.op.GuitartExact
  body: by
  rw [guitartExact_iff_isConnected_rightwards]
  intro X₃ X₂ g
  rw [← isConnected_op_iff_isConnected]; rw [isConnected_iff_of_equivalence (w.structuredArrowRightwardsOpEquivalence g)]
  infer_instance

中文:
实例 [w.GuitartExact]
  签名: : w.op.GuitartExact
  定义体: by
  rw [guitartExact_iff_isConnected_rightwards]
  intro X₃ X₂ g
  rw [← isConnected_op_iff_isConnected]; rw [isConnected_iff_of_equivalence (w.structuredArrowRightwardsOpEquivalence g)]
  infer_instance

Depends on / 依赖: guitartExact_iff_isConnected_rightwards, infer_instance, isConnected_iff_of_equivalence, isConnected_op_iff_isConnected, structuredArrowRightwardsOpEquivalence, w.structuredArrowRightwardsOpEquivalence
-/
instance [w.GuitartExact] : w.op.GuitartExact := by
  rw [guitartExact_iff_isConnected_rightwards]
  intro X₃ X₂ g
  rw [← isConnected_op_iff_isConnected]; rw [isConnected_iff_of_equivalence (w.structuredArrowRightwardsOpEquivalence g)]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `guitartExact_op_iff` / 引理 `guitartExact_op_iff`

English:
lemma guitartExact_op_iff
  statement: w.op.GuitartExact ↔ w.GuitartExact
  proof: by
  constructor
  · intro
    let w₁ : TwoSquare T (opOp C₁) (opOp C₂) T.op.op := 𝟙 _
    let w₂ : TwoSquare B.op.op (unopUnop C₃) (unopUnop C₄) B := 𝟙 _
    have : w = (w₁ ≫ᵥ w.op.op) ≫ᵥ w₂ := by cat_disch
    rw [this]
    infer_instance
  · intro
    infer_instance

中文:
引理 guitartExact_op_iff
  结论: w.op.GuitartExact ↔ w.GuitartExact
  证明: by
  constructor
  · intro
    let w₁ : TwoSquare T (opOp C₁) (opOp C₂) T.op.op := 𝟙 _
    let w₂ : TwoSquare B.op.op (unopUnop C₃) (unopUnop C₄) B := 𝟙 _
    have : w = (w₁ ≫ᵥ w.op.op) ≫ᵥ w₂ := by cat_disch
    rw [this]
    infer_instance
  · intro
    infer_instance

Depends on / 依赖: B.op.op, T.op.op, TwoSquare, cat_disch, hasPullback_op_iff_hasPushout, infer_instance, unopUnop, w.op.op
-/
lemma guitartExact_op_iff : w.op.GuitartExact ↔ w.GuitartExact := by
  constructor
  · intro
    let w₁ : TwoSquare T (opOp C₁) (opOp C₂) T.op.op := 𝟙 _
    let w₂ : TwoSquare B.op.op (unopUnop C₃) (unopUnop C₄) B := 𝟙 _
    have : w = (w₁ ≫ᵥ w.op.op) ≫ᵥ w₂ := by cat_disch
    rw [this]
    infer_instance
  · intro
    infer_instance

/--
Instance `guitartExact_id'` / 实例 `guitartExact_id'`

English:
instance guitartExact_id'
  signature: (F : C₁ ⥤ C₂)
  body: by
  rw [← guitartExact_op_iff]
  apply guitartExact_id

中文:
实例 guitartExact_id'
  签名: (F : C₁ ⥤ C₂)
  定义体: by
  rw [← guitartExact_op_iff]
  apply guitartExact_id

Depends on / 依赖: guitartExact_id, guitartExact_op_iff, hasPullback_unop_iff_hasPushout
-/
instance guitartExact_id' (F : C₁ ⥤ C₂) :
    GuitartExact (TwoSquare.mk F (𝟭 C₁) (𝟭 C₂) F (𝟙 F)) := by
  rw [← guitartExact_op_iff]
  apply guitartExact_id

/--
Instance `guitartExact_of_isEquivalence_of_isIso'` / 实例 `guitartExact_of_isEquivalence_of_isIso'`

English:
instance guitartExact_of_isEquivalence_of_isIso'
  body: by
  rw [← guitartExact_op_iff]
  infer_instance

中文:
实例 guitartExact_of_isEquivalence_of_isIso'
  定义体: by
  rw [← guitartExact_op_iff]
  infer_instance

Depends on / 依赖: guitartExact_op_iff, infer_instance
-/
instance guitartExact_of_isEquivalence_of_isIso'
    [T.IsEquivalence] [B.IsEquivalence] [IsIso w.natTrans] : GuitartExact w := by
  rw [← guitartExact_op_iff]
  infer_instance

end TwoSquare

end CategoryTheory
