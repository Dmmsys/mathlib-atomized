/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Pullbacks and pushouts in `C` and `Cᵒᵖ`

We construct pullbacks and pushouts in the opposite categories.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {J : Type u₂} [Category.{v₂} J]

/--
Instance `hasPullbacks_opposite` / 实例 `hasPullbacks_opposite`

English:
instance hasPullbacks_opposite
  signature: [HasPushouts C]
  body: by
  have : HasColimitsOfShape WalkingCospanᵒᵖ C :=
    hasColimitsOfShape_of_equivalence walkingCospanOpEquiv.symm
  apply hasLimitsOfShape_op_of_hasColimitsOfShape

中文:
实例 hasPullbacks_opposite
  签名: [有Pushouts C]
  定义体: by
  have : HasColimitsOfShape WalkingCospanᵒᵖ C :=
    hasColimitsOfShape_of_equivalence walkingCospanOpEquiv.symm
  apply hasLimitsOfShape_op_of_hasColimitsOfShape

Depends on / 依赖: HasColimitsOfShape, hasColimitsOfShape_of_equivalence, hasLimitsOfShape_op_of_hasColimitsOfShape, walkingCospanOpEquiv, walkingCospanOpEquiv.symm
-/
instance hasPullbacks_opposite [HasPushouts C] : HasPullbacks Cᵒᵖ := by
  have : HasColimitsOfShape WalkingCospanᵒᵖ C :=
    hasColimitsOfShape_of_equivalence walkingCospanOpEquiv.symm
  apply hasLimitsOfShape_op_of_hasColimitsOfShape

/--
Instance `hasPushouts_opposite` / 实例 `hasPushouts_opposite`

English:
instance hasPushouts_opposite
  signature: [HasPullbacks C]
  body: by
  have : HasLimitsOfShape WalkingSpanᵒᵖ C :=
    hasLimitsOfShape_of_equivalence walkingSpanOpEquiv.symm
  infer_instance

中文:
实例 hasPushouts_opposite
  签名: [有Pullbacks C]
  定义体: by
  have : HasLimitsOfShape WalkingSpanᵒᵖ C :=
    hasLimitsOfShape_of_equivalence walkingSpanOpEquiv.symm
  infer_instance

Depends on / 依赖: HasLimitsOfShape, hasLimitsOfShape_of_equivalence, infer_instance, walkingSpanOpEquiv, walkingSpanOpEquiv.symm
-/
instance hasPushouts_opposite [HasPullbacks C] : HasPushouts Cᵒᵖ := by
  have : HasLimitsOfShape WalkingSpanᵒᵖ C :=
    hasLimitsOfShape_of_equivalence walkingSpanOpEquiv.symm
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical isomorphism relating `Span f.op g.op` and `(Cospan f g).op` -/
@[simps!]
/--
Definition of `spanOp` / `spanOp` 的定义

English:
definition spanOp
  signature: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  body: NatIso.ofComponents (fun
    | .none => .refl _
    | .left => .refl _
    | .right => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)

中文:
定义 spanOp
  签名: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  定义体: NatIso.ofComponents (fun
    | .none => .refl _
    | .left => .refl _
    | .right => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)

Depends on / 依赖: NatIso, NatIso.ofComponents, cat_disch, ofComponents
-/
def spanOp {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    span f.op g.op ≅ walkingCospanOpEquiv.inverse ⋙ (cospan f g).op :=
  NatIso.ofComponents (fun
    | .none => .refl _
    | .left => .refl _
    | .right => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical isomorphism relating `span f.unop g.unop` and `(cospan f g).leftOp` -/
@[simps!]
/--
Definition of `spanUnop` / `spanUnop` 的定义

English:
definition spanUnop
  signature: {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z)
  body: NatIso.ofComponents (fun
    | .none => .refl _
    | .left => .refl _
    | .right => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)

中文:
定义 spanUnop
  签名: {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z)
  定义体: NatIso.ofComponents (fun
    | .none => .refl _
    | .left => .refl _
    | .right => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)

Depends on / 依赖: NatIso, NatIso.ofComponents, cat_disch, ofComponents
-/
def spanUnop {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) :
    span f.unop g.unop ≅ walkingCospanOpEquiv.inverse ⋙ (cospan f g).leftOp :=
  NatIso.ofComponents (fun
    | .none => .refl _
    | .left => .refl _
    | .right => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)

/-- The canonical isomorphism relating `(Cospan f g).op` and `Span f.op g.op` -/
@[simps!]
/--
Definition of `opCospan` / `opCospan` 的定义

English:
definition opCospan
  signature: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  body: calc
    (cospan f g).op ≅ 𝟭 _ ⋙ (cospan f g).op := .refl _
    _ ≅ (walkingCospanOpEquiv.functor ⋙ walkingCospanOpEquiv.inverse) ⋙ (cospan f g).op :=
      isoWhiskerRight walkingCospanOpEquiv.unitIso _
    _ ≅ walkingCospanOpEquiv.functor ⋙ walkingCospanOpEquiv.inverse ⋙ (cospan f g).op :=
      F

中文:
定义 opCospan
  签名: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  定义体: calc
    (cospan f g).op ≅ 𝟭 _ ⋙ (cospan f g).op := .refl _
    _ ≅ (walkingCospanOpEquiv.functor ⋙ walkingCospanOpEquiv.inverse) ⋙ (cospan f g).op :=
      isoWhiskerRight walkingCospanOpEquiv.unitIso _
    _ ≅ walkingCospanOpEquiv.functor ⋙ walkingCospanOpEquiv.inverse ⋙ (cospan f g).op :=
      F

Depends on / 依赖: Functor, Functor.associator, associator, cospan, f.op, functor, g.op, inverse, isoWhiskerLeft, isoWhiskerRight, spanOp, unitIso, walkingCospanOpEquiv, walkingCospanOpEquiv.functor, walkingCospanOpEquiv.inverse, walkingCospanOpEquiv.unitIso
-/
def opCospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (cospan f g).op ≅ walkingCospanOpEquiv.functor ⋙ span f.op g.op :=
  calc
    (cospan f g).op ≅ 𝟭 _ ⋙ (cospan f g).op := .refl _
    _ ≅ (walkingCospanOpEquiv.functor ⋙ walkingCospanOpEquiv.inverse) ⋙ (cospan f g).op :=
      isoWhiskerRight walkingCospanOpEquiv.unitIso _
    _ ≅ walkingCospanOpEquiv.functor ⋙ walkingCospanOpEquiv.inverse ⋙ (cospan f g).op :=
      Functor.associator _ _ _
    _ ≅ walkingCospanOpEquiv.functor ⋙ span f.op g.op := isoWhiskerLeft _ (spanOp f g).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical isomorphism relating `Cospan f.op g.op` and `(Span f g).op` -/
@[simps!]
/--
Definition of `cospanOp` / `cospanOp` 的定义

English:
definition cospanOp
  signature: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  body: NatIso.ofComponents (fun
    | .none => .refl _
    | .left => .refl _
    | .right => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)

中文:
定义 cospanOp
  签名: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  定义体: NatIso.ofComponents (fun
    | .none => .refl _
    | .left => .refl _
    | .right => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)

Depends on / 依赖: NatIso, NatIso.ofComponents, cat_disch, ofComponents
-/
def cospanOp {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    cospan f.op g.op ≅ walkingSpanOpEquiv.inverse ⋙ (span f g).op :=
  NatIso.ofComponents (fun
    | .none => .refl _
    | .left => .refl _
    | .right => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical isomorphism relating `cospan f.unop g.unop` and `(span f g).leftOp` -/
@[simps!]
/--
Definition of `cospanUnop` / `cospanUnop` 的定义

English:
definition cospanUnop
  signature: {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : X ⟶ Z)
  body: NatIso.ofComponents (fun
    | .none => .refl _
    | .left => .refl _
    | .right => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)

中文:
定义 cospanUnop
  签名: {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : X ⟶ Z)
  定义体: NatIso.ofComponents (fun
    | .none => .refl _
    | .left => .refl _
    | .right => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)

Depends on / 依赖: NatIso, NatIso.ofComponents, cat_disch, ofComponents
-/
def cospanUnop {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : X ⟶ Z) :
    cospan f.unop g.unop ≅ walkingSpanOpEquiv.inverse ⋙ (span f g).leftOp :=
  NatIso.ofComponents (fun
    | .none => .refl _
    | .left => .refl _
    | .right => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)

/-- The canonical isomorphism relating `(Span f g).op` and `Cospan f.op g.op` -/
@[simps!]
/--
Definition of `opSpan` / `opSpan` 的定义

English:
definition opSpan
  signature: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  body: calc
    (span f g).op ≅ 𝟭 _ ⋙ (span f g).op := .refl _
    _ ≅ (walkingSpanOpEquiv.functor ⋙ walkingSpanOpEquiv.inverse) ⋙ (span f g).op :=
      isoWhiskerRight walkingSpanOpEquiv.unitIso _
    _ ≅ walkingSpanOpEquiv.functor ⋙ walkingSpanOpEquiv.inverse ⋙ (span f g).op :=
      Functor.associator 

中文:
定义 opSpan
  签名: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  定义体: calc
    (span f g).op ≅ 𝟭 _ ⋙ (span f g).op := .refl _
    _ ≅ (walkingSpanOpEquiv.functor ⋙ walkingSpanOpEquiv.inverse) ⋙ (span f g).op :=
      isoWhiskerRight walkingSpanOpEquiv.unitIso _
    _ ≅ walkingSpanOpEquiv.functor ⋙ walkingSpanOpEquiv.inverse ⋙ (span f g).op :=
      Functor.associator 

Depends on / 依赖: Functor, Functor.associator, associator, cospan, cospanOp, f.op, functor, g.op, inverse, isoWhiskerLeft, isoWhiskerRight, unitIso, walkingSpanOpEquiv, walkingSpanOpEquiv.functor, walkingSpanOpEquiv.inverse, walkingSpanOpEquiv.unitIso
-/
def opSpan {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    (span f g).op ≅ walkingSpanOpEquiv.functor ⋙ cospan f.op g.op :=
  calc
    (span f g).op ≅ 𝟭 _ ⋙ (span f g).op := .refl _
    _ ≅ (walkingSpanOpEquiv.functor ⋙ walkingSpanOpEquiv.inverse) ⋙ (span f g).op :=
      isoWhiskerRight walkingSpanOpEquiv.unitIso _
    _ ≅ walkingSpanOpEquiv.functor ⋙ walkingSpanOpEquiv.inverse ⋙ (span f g).op :=
      Functor.associator _ _ _
    _ ≅ walkingSpanOpEquiv.functor ⋙ cospan f.op g.op := isoWhiskerLeft _ (cospanOp f g).symm

namespace PushoutCocone

/-- The obvious map `PushoutCocone f g → PullbackCone f.unop g.unop` -/
@[simps!]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g)
  body: Cocone.unop ((Cocone.precompose (opCospan f.unop g.unop).hom).obj
    (Cocone.whisker walkingCospanOpEquiv.functor c))

中文:
定义 unop
  签名: {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g)
  定义体: Cocone.unop ((Cocone.precompose (opCospan f.unop g.unop).hom).obj
    (Cocone.whisker walkingCospanOpEquiv.functor c))

Depends on / 依赖: Cocone, Cocone.precompose, Cocone.unop, Cocone.whisker, f.unop, functor, g.unop, opCospan, precompose, walkingCospanOpEquiv, walkingCospanOpEquiv.functor, whisker
-/
def unop {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    PullbackCone f.unop g.unop :=
  Cocone.unop ((Cocone.precompose (opCospan f.unop g.unop).hom).obj
    (Cocone.whisker walkingCospanOpEquiv.functor c))

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `unop_fst` / 定理 `unop_fst`

English:
theorem unop_fst
  given: {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g)
  proof: by simp

中文:
定理 unop_fst
  条件: {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g)
  证明: by simp
-/
theorem unop_fst {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    c.unop.fst = c.inl.unop := by simp

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `unop_snd` / 定理 `unop_snd`

English:
theorem unop_snd
  given: {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g)
  proof: by simp

中文:
定理 unop_snd
  条件: {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g)
  证明: by simp
-/
theorem unop_snd {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    c.unop.snd = c.inr.unop := by simp

/-- The obvious map `PushoutCocone f.op g.op → PullbackCone f g` -/
@[simps!]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g)
  body: (Cone.postcompose (cospanOp f g).symm.hom).obj
    (Cone.whisker walkingSpanOpEquiv.inverse (Cocone.op c))

中文:
定义 op
  签名: {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g)
  定义体: (Cone.postcompose (cospanOp f g).symm.hom).obj
    (Cone.whisker walkingSpanOpEquiv.inverse (Cocone.op c))

Depends on / 依赖: Cocone, Cocone.op, Cone.postcompose, Cone.whisker, cospanOp, inverse, postcompose, symm.hom, walkingSpanOpEquiv, walkingSpanOpEquiv.inverse, whisker
-/
def op {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : PullbackCone f.op g.op :=
  (Cone.postcompose (cospanOp f g).symm.hom).obj
    (Cone.whisker walkingSpanOpEquiv.inverse (Cocone.op c))

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `op_fst` / 定理 `op_fst`

English:
theorem op_fst
  given: {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g)
  proof: by simp

中文:
定理 op_fst
  条件: {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g)
  证明: by simp
-/
theorem op_fst {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    c.op.fst = c.inl.op := by simp

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `op_snd` / 定理 `op_snd`

English:
theorem op_snd
  given: {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g)
  proof: by simp

中文:
定理 op_snd
  条件: {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g)
  证明: by simp
-/
theorem op_snd {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    c.op.snd = c.inr.op := by simp

end PushoutCocone

namespace PullbackCone

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The obvious map `PullbackCone f g → PushoutCocone f.unop g.unop` -/
@[simps!]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g)
  body: Cone.unop
    ((Cone.postcompose (opSpan f.unop g.unop).symm.hom).obj
      (Cone.whisker walkingSpanOpEquiv.functor c))

中文:
定义 unop
  签名: {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g)
  定义体: Cone.unop
    ((Cone.postcompose (opSpan f.unop g.unop).symm.hom).obj
      (Cone.whisker walkingSpanOpEquiv.functor c))

Depends on / 依赖: Cone.postcompose, Cone.unop, Cone.whisker, f.unop, functor, g.unop, opSpan, postcompose, symm.hom, walkingSpanOpEquiv, walkingSpanOpEquiv.functor, whisker
-/
def unop {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    PushoutCocone f.unop g.unop :=
  Cone.unop
    ((Cone.postcompose (opSpan f.unop g.unop).symm.hom).obj
      (Cone.whisker walkingSpanOpEquiv.functor c))

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `unop_inl` / 定理 `unop_inl`

English:
theorem unop_inl
  given: {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g)
  proof: by simp

中文:
定理 unop_inl
  条件: {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g)
  证明: by simp
-/
theorem unop_inl {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    c.unop.inl = c.fst.unop := by simp

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `unop_inr` / 定理 `unop_inr`

English:
theorem unop_inr
  given: {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g)
  proof: by simp

中文:
定理 unop_inr
  条件: {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g)
  证明: by simp
-/
theorem unop_inr {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    c.unop.inr = c.snd.unop := by simp

/-- The obvious map `PullbackCone f g → PushoutCocone f.op g.op` -/
@[simps!]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g)
  body: (Cocone.precompose (spanOp f g).hom).obj
    (Cocone.whisker walkingCospanOpEquiv.inverse (Cone.op c))

中文:
定义 op
  签名: {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g)
  定义体: (Cocone.precompose (spanOp f g).hom).obj
    (Cocone.whisker walkingCospanOpEquiv.inverse (Cone.op c))

Depends on / 依赖: Cocone, Cocone.precompose, Cocone.whisker, Cone.op, inverse, precompose, spanOp, walkingCospanOpEquiv, walkingCospanOpEquiv.inverse, whisker
-/
def op {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : PushoutCocone f.op g.op :=
  (Cocone.precompose (spanOp f g).hom).obj
    (Cocone.whisker walkingCospanOpEquiv.inverse (Cone.op c))

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `op_inl` / 定理 `op_inl`

English:
theorem op_inl
  given: {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g)
  proof: by simp

中文:
定理 op_inl
  条件: {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g)
  证明: by simp
-/
theorem op_inl {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    c.op.inl = c.fst.op := by simp

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `op_inr` / 定理 `op_inr`

English:
theorem op_inr
  given: {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g)
  proof: by simp

中文:
定理 op_inr
  条件: {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g)
  证明: by simp
-/
theorem op_inr {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    c.op.inr = c.snd.op := by simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `opUnopIso` / `opUnopIso` 的定义

English:
definition opUnopIso
  signature: {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g)
  body: PullbackCone.ext (Iso.refl _) (by simp) (by simp)

中文:
定义 opUnopIso
  签名: {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g)
  定义体: PullbackCone.ext (Iso.refl _) (by simp) (by simp)

Depends on / 依赖: Iso.refl, PullbackCone, PullbackCone.ext
-/
def opUnopIso {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : c.op.unop ≅ c :=
  PullbackCone.ext (Iso.refl _) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `unopOpIso` / `unopOpIso` 的定义

English:
definition unopOpIso
  signature: {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g)
  body: PullbackCone.ext (Iso.refl _) (by simp) (by simp)

中文:
定义 unopOpIso
  签名: {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g)
  定义体: PullbackCone.ext (Iso.refl _) (by simp) (by simp)

Depends on / 依赖: Iso.refl, PullbackCone, PullbackCone.ext
-/
def unopOpIso {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : c.unop.op ≅ c :=
  PullbackCone.ext (Iso.refl _) (by simp) (by simp)

end PullbackCone

namespace PushoutCocone

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `opUnopIso` / `opUnopIso` 的定义

English:
definition opUnopIso
  signature: {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g)
  body: PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

中文:
定义 opUnopIso
  签名: {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g)
  定义体: PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

Depends on / 依赖: Iso.refl, PushoutCocone, PushoutCocone.ext
-/
def opUnopIso {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : c.op.unop ≅ c :=
  PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `unopOpIso` / `unopOpIso` 的定义

English:
definition unopOpIso
  signature: {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g)
  body: PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

中文:
定义 unopOpIso
  签名: {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g)
  定义体: PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

Depends on / 依赖: Iso.refl, PushoutCocone, PushoutCocone.ext
-/
def unopOpIso {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : c.unop.op ≅ c :=
  PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

/-- A pushout cone is a colimit cocone if and only if the corresponding pullback cone
in the opposite category is a limit cone. -/
noncomputable -- just for performance; compilation takes several seconds
/--
Definition of `isColimitEquivIsLimitOp` / `isColimitEquivIsLimitOp` 的定义

English:
definition isColimitEquivIsLimitOp
  signature: {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g)
  body: by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    exact (IsLimit.postcomposeHomEquiv _ _).invFun
      ((IsLimit.whiskerEquivalenceEquiv walkingSpanOpEquiv.symm).toFun h.op)
  · intro h
    exact (IsColimit.equivIsoColimit c.opUnopIso).toFun
      (((IsLimit.postcomposeHomEquiv _ _).invFu

中文:
定义 isColimitEquivIsLimitOp
  签名: {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g)
  定义体: by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    exact (IsLimit.postcomposeHomEquiv _ _).invFun
      ((IsLimit.whiskerEquivalenceEquiv walkingSpanOpEquiv.symm).toFun h.op)
  · intro h
    exact (IsColimit.equivIsoColimit c.opUnopIso).toFun
      (((IsLimit.postcomposeHomEquiv _ _).invFu

Depends on / 依赖: IsColimit, IsColimit.equivIsoColimit, IsLimit, IsLimit.postcomposeHomEquiv, IsLimit.whiskerEquivalenceEquiv, c.opUnopIso, equivIsoColimit, equivOfSubsingletonOfSubsingleton, h.op, invFun, opUnopIso, postcomposeHomEquiv, walkingSpanOpEquiv, walkingSpanOpEquiv.symm, whiskerEquivalenceEquiv
-/
def isColimitEquivIsLimitOp {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    IsColimit c ≃ IsLimit c.op := by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    exact (IsLimit.postcomposeHomEquiv _ _).invFun
      ((IsLimit.whiskerEquivalenceEquiv walkingSpanOpEquiv.symm).toFun h.op)
  · intro h
    exact (IsColimit.equivIsoColimit c.opUnopIso).toFun
      (((IsLimit.postcomposeHomEquiv _ _).invFun
        ((IsLimit.whiskerEquivalenceEquiv _).toFun h)).unop)

/-- A pushout cone is a colimit cocone in `Cᵒᵖ` if and only if the corresponding pullback cone
in `C` is a limit cone. -/
noncomputable -- just for performance; compilation takes several seconds
/--
Definition of `isColimitEquivIsLimitUnop` / `isColimitEquivIsLimitUnop` 的定义

English:
definition isColimitEquivIsLimitUnop
  signature: {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g)
  body: by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    exact ((IsColimit.precomposeHomEquiv _ _).invFun
      ((IsColimit.whiskerEquivalenceEquiv _).toFun h)).unop
  · intro h
    exact (IsColimit.equivIsoColimit c.unopOpIso).toFun
      ((IsColimit.precomposeHomEquiv _ _).invFun
      ((IsCol

中文:
定义 isColimitEquivIsLimitUnop
  签名: {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g)
  定义体: by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    exact ((IsColimit.precomposeHomEquiv _ _).invFun
      ((IsColimit.whiskerEquivalenceEquiv _).toFun h)).unop
  · intro h
    exact (IsColimit.equivIsoColimit c.unopOpIso).toFun
      ((IsColimit.precomposeHomEquiv _ _).invFun
      ((IsCol

Depends on / 依赖: IsColimit, IsColimit.equivIsoColimit, IsColimit.precomposeHomEquiv, IsColimit.whiskerEquivalenceEquiv, c.unopOpIso, equivIsoColimit, equivOfSubsingletonOfSubsingleton, h.op, invFun, precomposeHomEquiv, unopOpIso, walkingCospanOpEquiv, walkingCospanOpEquiv.symm, whiskerEquivalenceEquiv
-/
def isColimitEquivIsLimitUnop {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    IsColimit c ≃ IsLimit c.unop := by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    exact ((IsColimit.precomposeHomEquiv _ _).invFun
      ((IsColimit.whiskerEquivalenceEquiv _).toFun h)).unop
  · intro h
    exact (IsColimit.equivIsoColimit c.unopOpIso).toFun
      ((IsColimit.precomposeHomEquiv _ _).invFun
      ((IsColimit.whiskerEquivalenceEquiv walkingCospanOpEquiv.symm).toFun h.op))

end PushoutCocone

namespace PullbackCone

/--
Definition of `isLimitEquivIsColimitOp` / `isLimitEquivIsColimitOp` 的定义

English:
definition isLimitEquivIsColimitOp
  signature: {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g)
  body: (IsLimit.equivIsoLimit c.opUnopIso).symm.trans c.op.isColimitEquivIsLimitUnop.symm

中文:
定义 isLimitEquivIsColimitOp
  签名: {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g)
  定义体: (IsLimit.equivIsoLimit c.opUnopIso).symm.trans c.op.isColimitEquivIsLimitUnop.symm

Depends on / 依赖: IsLimit, IsLimit.equivIsoLimit, c.op.isColimitEquivIsLimitUnop.symm, c.opUnopIso, equivIsoLimit, isColimitEquivIsLimitUnop, opUnopIso, symm.trans
-/
def isLimitEquivIsColimitOp {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    IsLimit c ≃ IsColimit c.op :=
  (IsLimit.equivIsoLimit c.opUnopIso).symm.trans c.op.isColimitEquivIsLimitUnop.symm

/--
Definition of `isLimitEquivIsColimitUnop` / `isLimitEquivIsColimitUnop` 的定义

English:
definition isLimitEquivIsColimitUnop
  signature: {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g)
  body: (IsLimit.equivIsoLimit c.unopOpIso).symm.trans c.unop.isColimitEquivIsLimitOp.symm

中文:
定义 isLimitEquivIsColimitUnop
  签名: {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g)
  定义体: (IsLimit.equivIsoLimit c.unopOpIso).symm.trans c.unop.isColimitEquivIsLimitOp.symm

Depends on / 依赖: IsLimit, IsLimit.equivIsoLimit, c.unop.isColimitEquivIsLimitOp.symm, c.unopOpIso, equivIsoLimit, isColimitEquivIsLimitOp, symm.trans, unopOpIso
-/
def isLimitEquivIsColimitUnop {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    IsLimit c ≃ IsColimit c.unop :=
  (IsLimit.equivIsoLimit c.unopOpIso).symm.trans c.unop.isColimitEquivIsLimitOp.symm

end PullbackCone

section Pullback

open Opposite

@[simp]
/--
lemma `hasPushout_op_iff_hasPullback` / 引理 `hasPushout_op_iff_hasPullback`

English:
lemma hasPushout_op_iff_hasPullback
  given: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  proof: by
  rw [HasPushout]; rw [hasColimit_iff_of_iso (spanOp f g)]; rw [hasColimit_inverse_equivalence_comp_iff]; rw [hasColimit_op_iff_hasLimit]

@[simp]

中文:
引理 hasPushout_op_iff_hasPullback
  条件: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  证明: by
  rw [HasPushout]; rw [hasColimit_iff_of_iso (spanOp f g)]; rw [hasColimit_inverse_equivalence_comp_iff]; rw [hasColimit_op_iff_hasLimit]

@[simp]

Depends on / 依赖: HasPushout, hasColimit_iff_of_iso, hasColimit_inverse_equivalence_comp_iff, hasColimit_op_iff_hasLimit, spanOp
-/
lemma hasPushout_op_iff_hasPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasPushout f.op g.op ↔ HasPullback f g := by
  rw [HasPushout]; rw [hasColimit_iff_of_iso (spanOp f g)]; rw [hasColimit_inverse_equivalence_comp_iff]; rw [hasColimit_op_iff_hasLimit]

@[simp]
/--
lemma `hasPushout_unop_iff_hasPullback` / 引理 `hasPushout_unop_iff_hasPullback`

English:
lemma hasPushout_unop_iff_hasPullback
  given: {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z)
  proof: by
  rw [HasPushout]; rw [hasColimit_iff_of_iso (spanUnop f g)]; rw [hasColimit_inverse_equivalence_comp_iff]; rw [hasColimit_leftOp_iff_hasLimit]

中文:
引理 hasPushout_unop_iff_hasPullback
  条件: {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z)
  证明: by
  rw [HasPushout]; rw [hasColimit_iff_of_iso (spanUnop f g)]; rw [hasColimit_inverse_equivalence_comp_iff]; rw [hasColimit_leftOp_iff_hasLimit]

Depends on / 依赖: HasPushout, hasColimit_iff_of_iso, hasColimit_inverse_equivalence_comp_iff, hasColimit_leftOp_iff_hasLimit, spanUnop
-/
lemma hasPushout_unop_iff_hasPullback {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasPushout f.unop g.unop ↔ HasPullback f g := by
  rw [HasPushout]; rw [hasColimit_iff_of_iso (spanUnop f g)]; rw [hasColimit_inverse_equivalence_comp_iff]; rw [hasColimit_leftOp_iff_hasLimit]

instance {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : HasPushout f.op g.op := by
  rwa [hasPushout_op_iff_hasPullback]

instance {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : HasPushout f.unop g.unop := by
  rwa [hasPushout_unop_iff_hasPullback]

/--
Definition of `pullbackIsoUnopPushout` / `pullbackIsoUnopPushout` 的定义

English:
definition pullbackIsoUnopPushout
  signature: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [h : HasPullback f g]
  body: IsLimit.conePointUniqueUpToIso (@limit.isLimit _ _ _ _ _ h)
    ((PushoutCocone.isColimitEquivIsLimitUnop _) (colimit.isColimit (span f.op g.op)))

中文:
定义 pullbackIsoUnopPushout
  签名: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [h : HasPullback f g]
  定义体: IsLimit.conePointUniqueUpToIso (@limit.isLimit _ _ _ _ _ h)
    ((PushoutCocone.isColimitEquivIsLimitUnop _) (colimit.isColimit (span f.op g.op)))

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, PushoutCocone, PushoutCocone.isColimitEquivIsLimitUnop, colimit, colimit.isColimit, conePointUniqueUpToIso, f.op, g.op, isColimit, isColimitEquivIsLimitUnop, isLimit, limit.isLimit
-/
noncomputable def pullbackIsoUnopPushout {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [h : HasPullback f g] :
    pullback f g ≅ unop (pushout f.op g.op) :=
  IsLimit.conePointUniqueUpToIso (@limit.isLimit _ _ _ _ _ h)
    ((PushoutCocone.isColimitEquivIsLimitUnop _) (colimit.isColimit (span f.op g.op)))

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
theorem `pullbackIsoUnopPushout_inv_fst` / 定理 `pullbackIsoUnopPushout_inv_fst`

English:
theorem pullbackIsoUnopPushout_inv_fst
  given: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  proof: (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp [unop_id (X := { unop := X })])

中文:
定理 pullbackIsoUnopPushout_inv_fst
  条件: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  证明: (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp [unop_id (X := { unop := X })])

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso_inv_comp, conePointUniqueUpToIso_inv_comp, unop_id
-/
theorem pullbackIsoUnopPushout_inv_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    (pullbackIsoUnopPushout f g).inv ≫ pullback.fst f g = (pushout.inl f.op g.op).unop :=
  (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp [unop_id (X := { unop := X })])

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
theorem `pullbackIsoUnopPushout_inv_snd` / 定理 `pullbackIsoUnopPushout_inv_snd`

English:
theorem pullbackIsoUnopPushout_inv_snd
  given: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  proof: (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp [unop_id (X := { unop := Y })])

@[reassoc (attr := simp)]

中文:
定理 pullbackIsoUnopPushout_inv_snd
  条件: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  证明: (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp [unop_id (X := { unop := Y })])

@[reassoc (attr := simp)]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso_inv_comp, conePointUniqueUpToIso_inv_comp, unop_id
-/
theorem pullbackIsoUnopPushout_inv_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    (pullbackIsoUnopPushout f g).inv ≫ pullback.snd f g = (pushout.inr f.op g.op).unop :=
  (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp [unop_id (X := { unop := Y })])

@[reassoc (attr := simp)]
/--
theorem `pullbackIsoUnopPushout_hom_inl` / 定理 `pullbackIsoUnopPushout_hom_inl`

English:
theorem pullbackIsoUnopPushout_hom_inl
  given: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  proof: Quiver.Hom.unop_inj by simp [← pullbackIsoUnopPushout_inv_fst]

@[reassoc (attr := simp)]

中文:
定理 pullbackIsoUnopPushout_hom_inl
  条件: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  证明: Quiver.Hom.unop_inj by simp [← pullbackIsoUnopPushout_inv_fst]

@[reassoc (attr := simp)]

Depends on / 依赖: Quiver, Quiver.Hom.unop_inj, pullbackIsoUnopPushout_inv_fst, unop_inj
-/
theorem pullbackIsoUnopPushout_hom_inl {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    pushout.inl f.op g.op ≫ (pullbackIsoUnopPushout f g).hom.op = (pullback.fst f g).op :=
Quiver.Hom.unop_inj by simp [← pullbackIsoUnopPushout_inv_fst]

@[reassoc (attr := simp)]
/--
theorem `pullbackIsoUnopPushout_hom_inr` / 定理 `pullbackIsoUnopPushout_hom_inr`

English:
theorem pullbackIsoUnopPushout_hom_inr
  given: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  proof: Quiver.Hom.unop_inj by simp [← pullbackIsoUnopPushout_inv_snd]

中文:
定理 pullbackIsoUnopPushout_hom_inr
  条件: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  证明: Quiver.Hom.unop_inj by simp [← pullbackIsoUnopPushout_inv_snd]

Depends on / 依赖: Quiver, Quiver.Hom.unop_inj, pullbackIsoUnopPushout_inv_snd, unop_inj
-/
theorem pullbackIsoUnopPushout_hom_inr {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    pushout.inr f.op g.op ≫ (pullbackIsoUnopPushout f g).hom.op = (pullback.snd f g).op :=
Quiver.Hom.unop_inj by simp [← pullbackIsoUnopPushout_inv_snd]

/--
Definition of `pullbackIsoOpPushout` / `pullbackIsoOpPushout` 的定义

English:
definition pullbackIsoOpPushout
  signature: {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [h : HasPullback f g]
  body: IsLimit.conePointUniqueUpToIso (@limit.isLimit _ _ _ _ _ h)
    ((PushoutCocone.isColimitEquivIsLimitOp _) (colimit.isColimit (span f.unop g.unop)))

中文:
定义 pullbackIsoOpPushout
  签名: {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [h : HasPullback f g]
  定义体: IsLimit.conePointUniqueUpToIso (@limit.isLimit _ _ _ _ _ h)
    ((PushoutCocone.isColimitEquivIsLimitOp _) (colimit.isColimit (span f.unop g.unop)))

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, PushoutCocone, PushoutCocone.isColimitEquivIsLimitOp, colimit, colimit.isColimit, conePointUniqueUpToIso, f.unop, g.unop, isColimit, isColimitEquivIsLimitOp, isLimit, limit.isLimit
-/
noncomputable def pullbackIsoOpPushout {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [h : HasPullback f g] :
    pullback f g ≅ op (pushout f.unop g.unop) :=
  IsLimit.conePointUniqueUpToIso (@limit.isLimit _ _ _ _ _ h)
    ((PushoutCocone.isColimitEquivIsLimitOp _) (colimit.isColimit (span f.unop g.unop)))

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
theorem `pullbackIsoOpPushout_inv_fst` / 定理 `pullbackIsoOpPushout_inv_fst`

English:
theorem pullbackIsoOpPushout_inv_fst
  given: {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  proof: (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp)

中文:
定理 pullbackIsoOpPushout_inv_fst
  条件: {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  证明: (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp)

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso_inv_comp, conePointUniqueUpToIso_inv_comp
-/
theorem pullbackIsoOpPushout_inv_fst {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    (pullbackIsoOpPushout f g).inv ≫ pullback.fst f g = (pushout.inl f.unop g.unop).op :=
  (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
theorem `pullbackIsoOpPushout_inv_snd` / 定理 `pullbackIsoOpPushout_inv_snd`

English:
theorem pullbackIsoOpPushout_inv_snd
  given: {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  proof: (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp)

@[reassoc (attr := simp)]

中文:
定理 pullbackIsoOpPushout_inv_snd
  条件: {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  证明: (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp)

@[reassoc (attr := simp)]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso_inv_comp, conePointUniqueUpToIso_inv_comp
-/
theorem pullbackIsoOpPushout_inv_snd {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    (pullbackIsoOpPushout f g).inv ≫ pullback.snd f g = (pushout.inr f.unop g.unop).op :=
  (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp)

@[reassoc (attr := simp)]
/--
theorem `pullbackIsoOpPushout_hom_inl` / 定理 `pullbackIsoOpPushout_hom_inl`

English:
theorem pullbackIsoOpPushout_hom_inl
  given: {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  proof: Quiver.Hom.op_inj by simp [← pullbackIsoOpPushout_inv_fst]

@[reassoc (attr := simp)]

中文:
定理 pullbackIsoOpPushout_hom_inl
  条件: {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  证明: Quiver.Hom.op_inj by simp [← pullbackIsoOpPushout_inv_fst]

@[reassoc (attr := simp)]

Depends on / 依赖: Quiver, Quiver.Hom.op_inj, op_inj, pullbackIsoOpPushout_inv_fst
-/
theorem pullbackIsoOpPushout_hom_inl {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    pushout.inl _ _ ≫ (pullbackIsoOpPushout f g).hom.unop = (pullback.fst f g).unop :=
Quiver.Hom.op_inj by simp [← pullbackIsoOpPushout_inv_fst]

@[reassoc (attr := simp)]
/--
theorem `pullbackIsoOpPushout_hom_inr` / 定理 `pullbackIsoOpPushout_hom_inr`

English:
theorem pullbackIsoOpPushout_hom_inr
  given: {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  proof: Quiver.Hom.op_inj by simp [← pullbackIsoOpPushout_inv_snd]

中文:
定理 pullbackIsoOpPushout_hom_inr
  条件: {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
  证明: Quiver.Hom.op_inj by simp [← pullbackIsoOpPushout_inv_snd]

Depends on / 依赖: Quiver, Quiver.Hom.op_inj, op_inj, pullbackIsoOpPushout_inv_snd
-/
theorem pullbackIsoOpPushout_hom_inr {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    pushout.inr _ _ ≫ (pullbackIsoOpPushout f g).hom.unop = (pullback.snd f g).unop :=
Quiver.Hom.op_inj by simp [← pullbackIsoOpPushout_inv_snd]

end Pullback

section Pushout

@[simp]
/--
lemma `hasPullback_op_iff_hasPushout` / 引理 `hasPullback_op_iff_hasPushout`

English:
lemma hasPullback_op_iff_hasPushout
  given: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  proof: by
  rw [HasPullback]; rw [hasLimit_iff_of_iso (cospanOp f g)]; rw [hasLimit_inverse_equivalence_comp_iff]; rw [hasLimit_op_iff_hasColimit]

@[simp]

中文:
引理 hasPullback_op_iff_hasPushout
  条件: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  证明: by
  rw [HasPullback]; rw [hasLimit_iff_of_iso (cospanOp f g)]; rw [hasLimit_inverse_equivalence_comp_iff]; rw [hasLimit_op_iff_hasColimit]

@[simp]

Depends on / 依赖: HasPullback, cospanOp, hasLimit_iff_of_iso, hasLimit_inverse_equivalence_comp_iff, hasLimit_op_iff_hasColimit
-/
lemma hasPullback_op_iff_hasPushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    HasPullback f.op g.op ↔ HasPushout f g := by
  rw [HasPullback]; rw [hasLimit_iff_of_iso (cospanOp f g)]; rw [hasLimit_inverse_equivalence_comp_iff]; rw [hasLimit_op_iff_hasColimit]

@[simp]
/--
lemma `hasPullback_unop_iff_hasPushout` / 引理 `hasPullback_unop_iff_hasPushout`

English:
lemma hasPullback_unop_iff_hasPushout
  given: {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : X ⟶ Z)
  proof: by
  rw [HasPullback]; rw [hasLimit_iff_of_iso (cospanUnop f g)]; rw [hasLimit_inverse_equivalence_comp_iff]; rw [hasLimit_leftOp_iff_hasColimit]

中文:
引理 hasPullback_unop_iff_hasPushout
  条件: {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : X ⟶ Z)
  证明: by
  rw [HasPullback]; rw [hasLimit_iff_of_iso (cospanUnop f g)]; rw [hasLimit_inverse_equivalence_comp_iff]; rw [hasLimit_leftOp_iff_hasColimit]

Depends on / 依赖: HasPullback, cospanUnop, hasLimit_iff_of_iso, hasLimit_inverse_equivalence_comp_iff, hasLimit_leftOp_iff_hasColimit
-/
lemma hasPullback_unop_iff_hasPushout {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : X ⟶ Z) :
    HasPullback f.unop g.unop ↔ HasPushout f g := by
  rw [HasPullback]; rw [hasLimit_iff_of_iso (cospanUnop f g)]; rw [hasLimit_inverse_equivalence_comp_iff]; rw [hasLimit_leftOp_iff_hasColimit]

instance {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : HasPullback f.op g.op := by
  rwa [hasPullback_op_iff_hasPushout]

instance {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : HasPullback f.unop g.unop := by
  rwa [hasPullback_unop_iff_hasPushout]

/--
Definition of `pushoutIsoUnopPullback` / `pushoutIsoUnopPullback` 的定义

English:
definition pushoutIsoUnopPullback
  signature: {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [h : HasPushout f g]
  body: IsColimit.coconePointUniqueUpToIso (@colimit.isColimit _ _ _ _ _ h)
    ((PullbackCone.isLimitEquivIsColimitUnop _) (limit.isLimit (cospan f.op g.op)))

中文:
定义 pushoutIsoUnopPullback
  签名: {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [h : HasPushout f g]
  定义体: IsColimit.coconePointUniqueUpToIso (@colimit.isColimit _ _ _ _ _ h)
    ((PullbackCone.isLimitEquivIsColimitUnop _) (limit.isLimit (cospan f.op g.op)))

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, PullbackCone, PullbackCone.isLimitEquivIsColimitUnop, coconePointUniqueUpToIso, colimit, colimit.isColimit, cospan, f.op, g.op, isColimit, isLimit, isLimitEquivIsColimitUnop, limit.isLimit
-/
noncomputable def pushoutIsoUnopPullback {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [h : HasPushout f g] :
    pushout f g ≅ unop (pullback f.op g.op) :=
  IsColimit.coconePointUniqueUpToIso (@colimit.isColimit _ _ _ _ _ h)
    ((PullbackCone.isLimitEquivIsColimitUnop _) (limit.isLimit (cospan f.op g.op)))

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
theorem `pushoutIsoUnopPullback_inl_hom` / 定理 `pushoutIsoUnopPullback_inl_hom`

English:
theorem pushoutIsoUnopPullback_inl_hom
  given: {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
  proof: (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

中文:
定理 pushoutIsoUnopPullback_inl_hom
  条件: {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
  证明: (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

Depends on / 依赖: IsColimit, IsColimit.comp_coconePointUniqueUpToIso_hom, comp_coconePointUniqueUpToIso_hom
-/
theorem pushoutIsoUnopPullback_inl_hom {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] :
    pushout.inl _ _ ≫ (pushoutIsoUnopPullback f g).hom = (pullback.fst f.op g.op).unop :=
  (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
theorem `pushoutIsoUnopPullback_inr_hom` / 定理 `pushoutIsoUnopPullback_inr_hom`

English:
theorem pushoutIsoUnopPullback_inr_hom
  given: {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
  proof: (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

@[simp]

中文:
定理 pushoutIsoUnopPullback_inr_hom
  条件: {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
  证明: (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

@[simp]

Depends on / 依赖: IsColimit, IsColimit.comp_coconePointUniqueUpToIso_hom, comp_coconePointUniqueUpToIso_hom
-/
theorem pushoutIsoUnopPullback_inr_hom {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] :
    pushout.inr _ _ ≫ (pushoutIsoUnopPullback f g).hom = (pullback.snd f.op g.op).unop :=
  (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

@[simp]
/--
theorem `pushoutIsoUnopPullback_inv_fst` / 定理 `pushoutIsoUnopPullback_inv_fst`

English:
theorem pushoutIsoUnopPullback_inv_fst
  given: {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
  proof: Quiver.Hom.unop_inj by simp [← pushoutIsoUnopPullback_inl_hom]

@[simp]

中文:
定理 pushoutIsoUnopPullback_inv_fst
  条件: {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
  证明: Quiver.Hom.unop_inj by simp [← pushoutIsoUnopPullback_inl_hom]

@[simp]

Depends on / 依赖: Quiver, Quiver.Hom.unop_inj, pushoutIsoUnopPullback_inl_hom, unop_inj
-/
theorem pushoutIsoUnopPullback_inv_fst {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] :
    (pushoutIsoUnopPullback f g).inv.op ≫ pullback.fst f.op g.op = (pushout.inl f g).op :=
Quiver.Hom.unop_inj by simp [← pushoutIsoUnopPullback_inl_hom]

@[simp]
/--
theorem `pushoutIsoUnopPullback_inv_snd` / 定理 `pushoutIsoUnopPullback_inv_snd`

English:
theorem pushoutIsoUnopPullback_inv_snd
  given: {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
  proof: Quiver.Hom.unop_inj by simp [← pushoutIsoUnopPullback_inr_hom]

中文:
定理 pushoutIsoUnopPullback_inv_snd
  条件: {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
  证明: Quiver.Hom.unop_inj by simp [← pushoutIsoUnopPullback_inr_hom]

Depends on / 依赖: Quiver, Quiver.Hom.unop_inj, pushoutIsoUnopPullback_inr_hom, unop_inj
-/
theorem pushoutIsoUnopPullback_inv_snd {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] :
    (pushoutIsoUnopPullback f g).inv.op ≫ pullback.snd f.op g.op = (pushout.inr f g).op :=
Quiver.Hom.unop_inj by simp [← pushoutIsoUnopPullback_inr_hom]

/--
Definition of `pushoutIsoOpPullback` / `pushoutIsoOpPullback` 的定义

English:
definition pushoutIsoOpPullback
  signature: {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [h : HasPushout f g]
  body: IsColimit.coconePointUniqueUpToIso (@colimit.isColimit _ _ _ _ _ h)
    ((PullbackCone.isLimitEquivIsColimitOp _) (limit.isLimit (cospan f.unop g.unop)))

中文:
定义 pushoutIsoOpPullback
  签名: {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [h : HasPushout f g]
  定义体: IsColimit.coconePointUniqueUpToIso (@colimit.isColimit _ _ _ _ _ h)
    ((PullbackCone.isLimitEquivIsColimitOp _) (limit.isLimit (cospan f.unop g.unop)))

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, PullbackCone, PullbackCone.isLimitEquivIsColimitOp, coconePointUniqueUpToIso, colimit, colimit.isColimit, cospan, f.unop, g.unop, isColimit, isLimit, isLimitEquivIsColimitOp, limit.isLimit
-/
noncomputable def pushoutIsoOpPullback {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [h : HasPushout f g] :
    pushout f g ≅ op (pullback f.unop g.unop) :=
  IsColimit.coconePointUniqueUpToIso (@colimit.isColimit _ _ _ _ _ h)
    ((PullbackCone.isLimitEquivIsColimitOp _) (limit.isLimit (cospan f.unop g.unop)))

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
theorem `pushoutIsoOpPullback_inl_hom` / 定理 `pushoutIsoOpPullback_inl_hom`

English:
theorem pushoutIsoOpPullback_inl_hom
  given: {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
  proof: (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

中文:
定理 pushoutIsoOpPullback_inl_hom
  条件: {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
  证明: (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

Depends on / 依赖: IsColimit, IsColimit.comp_coconePointUniqueUpToIso_hom, comp_coconePointUniqueUpToIso_hom
-/
theorem pushoutIsoOpPullback_inl_hom {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] :
    pushout.inl _ _ ≫ (pushoutIsoOpPullback f g).hom = (pullback.fst f.unop g.unop).op :=
  (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
theorem `pushoutIsoOpPullback_inr_hom` / 定理 `pushoutIsoOpPullback_inr_hom`

English:
theorem pushoutIsoOpPullback_inr_hom
  given: {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
  proof: (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

@[simp]

中文:
定理 pushoutIsoOpPullback_inr_hom
  条件: {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
  证明: (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

@[simp]

Depends on / 依赖: IsColimit, IsColimit.comp_coconePointUniqueUpToIso_hom, comp_coconePointUniqueUpToIso_hom
-/
theorem pushoutIsoOpPullback_inr_hom {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] :
    pushout.inr _ _ ≫ (pushoutIsoOpPullback f g).hom = (pullback.snd f.unop g.unop).op :=
  (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

@[simp]
/--
theorem `pushoutIsoOpPullback_inv_fst` / 定理 `pushoutIsoOpPullback_inv_fst`

English:
theorem pushoutIsoOpPullback_inv_fst
  given: {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
  proof: Quiver.Hom.op_inj by simp [← pushoutIsoOpPullback_inl_hom]

@[simp]

中文:
定理 pushoutIsoOpPullback_inv_fst
  条件: {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
  证明: Quiver.Hom.op_inj by simp [← pushoutIsoOpPullback_inl_hom]

@[simp]

Depends on / 依赖: Quiver, Quiver.Hom.op_inj, op_inj, pushoutIsoOpPullback_inl_hom
-/
theorem pushoutIsoOpPullback_inv_fst {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] :
    (pushoutIsoOpPullback f g).inv.unop ≫ pullback.fst f.unop g.unop = (pushout.inl f g).unop :=
Quiver.Hom.op_inj by simp [← pushoutIsoOpPullback_inl_hom]

@[simp]
/--
theorem `pushoutIsoOpPullback_inv_snd` / 定理 `pushoutIsoOpPullback_inv_snd`

English:
theorem pushoutIsoOpPullback_inv_snd
  given: {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
  proof: Quiver.Hom.op_inj by simp [← pushoutIsoOpPullback_inr_hom]

中文:
定理 pushoutIsoOpPullback_inv_snd
  条件: {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
  证明: Quiver.Hom.op_inj by simp [← pushoutIsoOpPullback_inr_hom]

Depends on / 依赖: Quiver, Quiver.Hom.op_inj, op_inj, pushoutIsoOpPullback_inr_hom
-/
theorem pushoutIsoOpPullback_inv_snd {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] :
    (pushoutIsoOpPullback f g).inv.unop ≫ pullback.snd f.unop g.unop = (pushout.inr f g).unop :=
Quiver.Hom.op_inj by simp [← pushoutIsoOpPullback_inr_hom]

end Pushout

section Map

set_option backward.isDefEq.respectTransparency false in
/--
lemma `op_pullbackMap` / 引理 `op_pullbackMap`

English:
lemma op_pullbackMap
  statement: {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
  proof: by
  rw [Iso.eq_inv_comp]
  ext <;> simp [← op_comp]

中文:
引理 op_pullbackMap
  结论: {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
  证明: by
  rw [Iso.eq_inv_comp]
  ext <;> simp [← op_comp]

Depends on / 依赖: Iso.eq_inv_comp, eq_inv_comp, op_comp
-/
lemma op_pullbackMap {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
    (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂]
    (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (eq₁) (eq₂) :
    (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂).op =
      (pushoutIsoOpPullback _ _).inv ≫
        pushout.map g₁.op g₂.op f₁.op f₂.op i₁.op i₂.op i₃.op
        (by simp [eq₁, ← op_comp]) (by simp [eq₂, ← op_comp]) ≫
        (pushoutIsoOpPullback _ _).hom := by
  rw [Iso.eq_inv_comp]
  ext <;> simp [← op_comp]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `op_pushoutMap` / 引理 `op_pushoutMap`

English:
lemma op_pushoutMap
  statement: {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂]
  proof: by
  rw [← Category.assoc]; rw [← Iso.comp_inv_eq]
  ext <;> simp [← op_comp]

中文:
引理 op_pushoutMap
  结论: {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂]
  证明: by
  rw [← Category.assoc]; rw [← Iso.comp_inv_eq]
  ext <;> simp [← op_comp]

Depends on / 依赖: Category, Category.assoc, Iso.comp_inv_eq, comp_inv_eq, op_comp
-/
lemma op_pushoutMap {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂]
    (g₁ : T ⟶ Y) (g₂ : T ⟶ Z) [HasPushout g₁ g₂]
    (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₁ = i₃ ≫ g₁)
    (eq₂ : f₂ ≫ i₂ = i₃ ≫ g₂) :
    (pushout.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂).op =
      (pullbackIsoOpPushout _ _).inv ≫
        pullback.map g₁.op g₂.op f₁.op f₂.op i₁.op i₂.op i₃.op
        (by simp [eq₁, ← op_comp]) (by simp [eq₂, ← op_comp]) ≫
        (pullbackIsoOpPushout _ _).hom := by
  rw [← Category.assoc]; rw [← Iso.comp_inv_eq]
  ext <;> simp [← op_comp]

end Map

end Limits

namespace CommSq
open Limits

variable {C : Type*} [Category* C]
variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `coneOp` / `coneOp` 的定义

English:
definition coneOp
  signature: (p : CommSq f g h i)
  body: PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

中文:
定义 coneOp
  签名: (p : 交换Sq f g h i)
  定义体: PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

Depends on / 依赖: Iso.refl, PushoutCocone, PushoutCocone.ext
-/
def coneOp (p : CommSq f g h i) : p.cone.op ≅ p.flip.op.cocone :=
  PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `coconeOp` / `coconeOp` 的定义

English:
definition coconeOp
  signature: (p : CommSq f g h i)
  body: PullbackCone.ext (Iso.refl _) (by simp) (by simp)

中文:
定义 coconeOp
  签名: (p : 交换Sq f g h i)
  定义体: PullbackCone.ext (Iso.refl _) (by simp) (by simp)

Depends on / 依赖: Iso.refl, PullbackCone, PullbackCone.ext
-/
def coconeOp (p : CommSq f g h i) : p.cocone.op ≅ p.flip.op.cone :=
  PullbackCone.ext (Iso.refl _) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `coneUnop` / `coneUnop` 的定义

English:
definition coneUnop
  signature: {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} (p : CommSq f g h i)
  body: PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

中文:
定义 coneUnop
  签名: {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} (p : 交换Sq f g h i)
  定义体: PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

Depends on / 依赖: Iso.refl, PushoutCocone, PushoutCocone.ext
-/
def coneUnop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} (p : CommSq f g h i) :
    p.cone.unop ≅ p.flip.unop.cocone :=
  PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `coconeUnop` / `coconeUnop` 的定义

English:
definition coconeUnop
  signature: {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
  body: PullbackCone.ext (Iso.refl _) (by simp) (by simp)

中文:
定义 coconeUnop
  签名: {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
  定义体: PullbackCone.ext (Iso.refl _) (by simp) (by simp)

Depends on / 依赖: Iso.refl, PullbackCone, PullbackCone.ext
-/
def coconeUnop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (p : CommSq f g h i) : p.cocone.unop ≅ p.flip.unop.cone :=
  PullbackCone.ext (Iso.refl _) (by simp) (by simp)

end CommSq

end CategoryTheory
