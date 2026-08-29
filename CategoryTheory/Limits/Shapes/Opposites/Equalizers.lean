/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Pullbacks

/-!
# Equalizers and coequalizers in `C` and `Cᵒᵖ`

We construct equalizers and coequalizers in the opposite categories.

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
Instance `hasEqualizers_opposite` / 实例 `hasEqualizers_opposite`

English:
instance hasEqualizers_opposite
  signature: [HasCoequalizers C]
  body: haveI : HasColimitsOfShape WalkingParallelPairᵒᵖ C :=
    hasColimitsOfShape_of_equivalence walkingParallelPairOpEquiv
  hasLimitsOfShape_op_of_hasColimitsOfShape

中文:
实例 hasEqualizers_opposite
  签名: [HasCoequalizers C]
  定义体: haveI : HasColimitsOfShape WalkingParallelPairᵒᵖ C :=
    hasColimitsOfShape_of_equivalence walkingParallelPairOpEquiv
  hasLimitsOfShape_op_of_hasColimitsOfShape

Depends on / 依赖: HasColimitsOfShape, hasColimitsOfShape_of_equivalence, hasLimitsOfShape_op_of_hasColimitsOfShape, walkingParallelPairOpEquiv
-/
instance hasEqualizers_opposite [HasCoequalizers C] : HasEqualizers Cᵒᵖ :=
  haveI : HasColimitsOfShape WalkingParallelPairᵒᵖ C :=
    hasColimitsOfShape_of_equivalence walkingParallelPairOpEquiv
  hasLimitsOfShape_op_of_hasColimitsOfShape

/--
Instance `hasCoequalizers_opposite` / 实例 `hasCoequalizers_opposite`

English:
instance hasCoequalizers_opposite
  signature: [HasEqualizers C]
  body: haveI : HasLimitsOfShape WalkingParallelPairᵒᵖ C :=
    hasLimitsOfShape_of_equivalence walkingParallelPairOpEquiv
  hasColimitsOfShape_op_of_hasLimitsOfShape

中文:
实例 hasCoequalizers_opposite
  签名: [HasEqualizers C]
  定义体: haveI : HasLimitsOfShape WalkingParallelPairᵒᵖ C :=
    hasLimitsOfShape_of_equivalence walkingParallelPairOpEquiv
  hasColimitsOfShape_op_of_hasLimitsOfShape

Depends on / 依赖: HasLimitsOfShape, hasColimitsOfShape_op_of_hasLimitsOfShape, hasLimitsOfShape_of_equivalence, walkingParallelPairOpEquiv
-/
instance hasCoequalizers_opposite [HasEqualizers C] : HasCoequalizers Cᵒᵖ :=
  haveI : HasLimitsOfShape WalkingParallelPairᵒᵖ C :=
    hasLimitsOfShape_of_equivalence walkingParallelPairOpEquiv
  hasColimitsOfShape_op_of_hasLimitsOfShape

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `parallelPairOpIso` / `parallelPairOpIso` 的定义

English:
definition parallelPairOpIso
  signature: {X Y : C} (f g : X ⟶ Y)
  body: NatIso.ofComponents (fun
    | .zero => .refl _
    | .one => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)

@[simp]

中文:
定义 parallelPairOpIso
  签名: {X Y : C} (f g : X ⟶ Y)
  定义体: NatIso.ofComponents (fun
    | .zero => .refl _
    | .one => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)

@[simp]

Depends on / 依赖: NatIso, NatIso.ofComponents, cat_disch, ofComponents
-/
def parallelPairOpIso {X Y : C} (f g : X ⟶ Y) :
    parallelPair f.op g.op ≅ walkingParallelPairOpEquiv.functor ⋙ (parallelPair f g).op :=
  NatIso.ofComponents (fun
    | .zero => .refl _
    | .one => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)

@[simp]
/--
lemma `parallelPairOpIso_hom_app_zero` / 引理 `parallelPairOpIso_hom_app_zero`

English:
lemma parallelPairOpIso_hom_app_zero
  given: {X Y : C} (f g : X ⟶ Y)
  proof: rfl

@[simp]

中文:
引理 parallelPairOpIso_hom_app_zero
  条件: {X Y : C} (f g : X ⟶ Y)
  证明: rfl

@[simp]
-/
lemma parallelPairOpIso_hom_app_zero {X Y : C} (f g : X ⟶ Y) :
    (parallelPairOpIso f g).hom.app WalkingParallelPair.zero = 𝟙 _ := rfl

@[simp]
/--
lemma `parallelPairOpIso_hom_app_one` / 引理 `parallelPairOpIso_hom_app_one`

English:
lemma parallelPairOpIso_hom_app_one
  given: {X Y : C} (f g : X ⟶ Y)
  proof: rfl

@[simp]

中文:
引理 parallelPairOpIso_hom_app_one
  条件: {X Y : C} (f g : X ⟶ Y)
  证明: rfl

@[simp]
-/
lemma parallelPairOpIso_hom_app_one {X Y : C} (f g : X ⟶ Y) :
    (parallelPairOpIso f g).hom.app WalkingParallelPair.one = 𝟙 _ := rfl

@[simp]
/--
lemma `parallelPairOpIso_inv_app_zero` / 引理 `parallelPairOpIso_inv_app_zero`

English:
lemma parallelPairOpIso_inv_app_zero
  given: {X Y : C} (f g : X ⟶ Y)
  proof: rfl

@[simp]

中文:
引理 parallelPairOpIso_inv_app_zero
  条件: {X Y : C} (f g : X ⟶ Y)
  证明: rfl

@[simp]
-/
lemma parallelPairOpIso_inv_app_zero {X Y : C} (f g : X ⟶ Y) :
    (parallelPairOpIso f g).inv.app WalkingParallelPair.zero = 𝟙 _ := rfl

@[simp]
/--
lemma `parallelPairOpIso_inv_app_one` / 引理 `parallelPairOpIso_inv_app_one`

English:
lemma parallelPairOpIso_inv_app_one
  given: {X Y : C} (f g : X ⟶ Y)
  proof: rfl

中文:
引理 parallelPairOpIso_inv_app_one
  条件: {X Y : C} (f g : X ⟶ Y)
  证明: rfl
-/
lemma parallelPairOpIso_inv_app_one {X Y : C} (f g : X ⟶ Y) :
    (parallelPairOpIso f g).inv.app WalkingParallelPair.one = 𝟙 _ := rfl

/--
Definition of `opParallelPairIso` / `opParallelPairIso` 的定义

English:
definition opParallelPairIso
  signature: {X Y : C} (f g : X ⟶ Y)
  body: calc
    (parallelPair f g).op ≅ 𝟭 _ ⋙ (parallelPair f g).op := .refl _
    _ ≅ (walkingParallelPairOpEquiv.inverse ⋙ walkingParallelPairOpEquiv.functor) ⋙ _ :=
      isoWhiskerRight walkingParallelPairOpEquiv.symm.unitIso _
    _ ≅ walkingParallelPairOpEquiv.inverse ⋙ walkingParallelPairOpEquiv.fun

中文:
定义 opParallelPairIso
  签名: {X Y : C} (f g : X ⟶ Y)
  定义体: calc
    (parallelPair f g).op ≅ 𝟭 _ ⋙ (parallelPair f g).op := .refl _
    _ ≅ (walkingParallelPairOpEquiv.inverse ⋙ walkingParallelPairOpEquiv.functor) ⋙ _ :=
      isoWhiskerRight walkingParallelPairOpEquiv.symm.unitIso _
    _ ≅ walkingParallelPairOpEquiv.inverse ⋙ walkingParallelPairOpEquiv.fun

Depends on / 依赖: Functor, Functor.associator, associator, f.op, functor, g.op, inverse, isoWhiskerLeft, isoWhiskerRight, parallelPair, parallelPairOpIso, unitIso, walkingParallelPairOpEquiv, walkingParallelPairOpEquiv.functor, walkingParallelPairOpEquiv.inverse, walkingParallelPairOpEquiv.symm.unitIso
-/
def opParallelPairIso {X Y : C} (f g : X ⟶ Y) :
    (parallelPair f g).op ≅ walkingParallelPairOpEquiv.inverse ⋙ parallelPair f.op g.op :=
  calc
    (parallelPair f g).op ≅ 𝟭 _ ⋙ (parallelPair f g).op := .refl _
    _ ≅ (walkingParallelPairOpEquiv.inverse ⋙ walkingParallelPairOpEquiv.functor) ⋙ _ :=
      isoWhiskerRight walkingParallelPairOpEquiv.symm.unitIso _
    _ ≅ walkingParallelPairOpEquiv.inverse ⋙ walkingParallelPairOpEquiv.functor ⋙ _ :=
      Functor.associator _ _ _
    _ ≅ walkingParallelPairOpEquiv.inverse ⋙ parallelPair f.op g.op :=
      isoWhiskerLeft _ (parallelPairOpIso f g).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `opParallelPairIso_hom_app_zero` / 引理 `opParallelPairIso_hom_app_zero`

English:
lemma opParallelPairIso_hom_app_zero
  given: {X Y : C} (f g : X ⟶ Y)
  proof: by
  simp [opParallelPairIso]

中文:
引理 opParallelPairIso_hom_app_zero
  条件: {X Y : C} (f g : X ⟶ Y)
  证明: by
  simp [opParallelPairIso]

Depends on / 依赖: opParallelPairIso
-/
lemma opParallelPairIso_hom_app_zero {X Y : C} (f g : X ⟶ Y) :
    (opParallelPairIso f g).hom.app (op WalkingParallelPair.zero) = 𝟙 _ := by
  simp [opParallelPairIso]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `opParallelPairIso_hom_app_one` / 引理 `opParallelPairIso_hom_app_one`

English:
lemma opParallelPairIso_hom_app_one
  given: {X Y : C} (f g : X ⟶ Y)
  proof: by
  simp [opParallelPairIso]

中文:
引理 opParallelPairIso_hom_app_one
  条件: {X Y : C} (f g : X ⟶ Y)
  证明: by
  simp [opParallelPairIso]

Depends on / 依赖: opParallelPairIso
-/
lemma opParallelPairIso_hom_app_one {X Y : C} (f g : X ⟶ Y) :
    (opParallelPairIso f g).hom.app (op WalkingParallelPair.one) = 𝟙 _ := by
  simp [opParallelPairIso]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `opParallelPairIso_inv_app_zero` / 引理 `opParallelPairIso_inv_app_zero`

English:
lemma opParallelPairIso_inv_app_zero
  given: {X Y : C} (f g : X ⟶ Y)
  proof: by
  simp [opParallelPairIso]

中文:
引理 opParallelPairIso_inv_app_zero
  条件: {X Y : C} (f g : X ⟶ Y)
  证明: by
  simp [opParallelPairIso]

Depends on / 依赖: opParallelPairIso
-/
lemma opParallelPairIso_inv_app_zero {X Y : C} (f g : X ⟶ Y) :
    (opParallelPairIso f g).inv.app (op WalkingParallelPair.zero) = 𝟙 _ := by
  simp [opParallelPairIso]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `opParallelPairIso_inv_app_one` / 引理 `opParallelPairIso_inv_app_one`

English:
lemma opParallelPairIso_inv_app_one
  given: {X Y : C} (f g : X ⟶ Y)
  proof: by
  simp [opParallelPairIso]

中文:
引理 opParallelPairIso_inv_app_one
  条件: {X Y : C} (f g : X ⟶ Y)
  证明: by
  simp [opParallelPairIso]

Depends on / 依赖: opParallelPairIso
-/
lemma opParallelPairIso_inv_app_one {X Y : C} (f g : X ⟶ Y) :
    (opParallelPairIso f g).inv.app (op WalkingParallelPair.one) = 𝟙 _ := by
  simp [opParallelPairIso]

namespace Cofork

/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g)
  body: Cocone.unop ((Cocone.precompose (opParallelPairIso f.unop g.unop).hom).obj
    (Cocone.whisker walkingParallelPairOpEquiv.inverse c))

中文:
定义 unop
  签名: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : 余叉 f g)
  定义体: Cocone.unop ((Cocone.precompose (opParallelPairIso f.unop g.unop).hom).obj
    (Cocone.whisker walkingParallelPairOpEquiv.inverse c))

Depends on / 依赖: Cocone, Cocone.precompose, Cocone.unop, Cocone.whisker, f.unop, g.unop, inverse, opParallelPairIso, precompose, walkingParallelPairOpEquiv, walkingParallelPairOpEquiv.inverse, whisker
-/
def unop {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g) : Fork f.unop g.unop :=
  Cocone.unop ((Cocone.precompose (opParallelPairIso f.unop g.unop).hom).obj
    (Cocone.whisker walkingParallelPairOpEquiv.inverse c))

set_option backward.defeqAttrib.useBackward true in
/--
lemma `unop_π_app_one` / 引理 `unop_π_app_one`

English:
lemma unop_π_app_one
  given: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g)
  proof: by
  simp [unop]

中文:
引理 unop_π_app_one
  条件: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : 余叉 f g)
  证明: by
  simp [unop]
-/
lemma unop_π_app_one {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g) :
    c.unop.π.app .one = Quiver.Hom.unop (c.ι.app .zero) := by
  simp [unop]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `unop_π_app_zero` / 引理 `unop_π_app_zero`

English:
lemma unop_π_app_zero
  given: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g)
  proof: by
  simp [unop]

中文:
引理 unop_π_app_zero
  条件: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : 余叉 f g)
  证明: by
  simp [unop]
-/
lemma unop_π_app_zero {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g) :
    c.unop.π.app .zero = Quiver.Hom.unop (c.ι.app .one) := by
  simp [unop]

set_option backward.defeqAttrib.useBackward true in
/--
theorem `unop_ι` / 定理 `unop_ι`

English:
theorem unop_ι
  given: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g)
  proof: by simp [Cofork.unop, Fork.ι]

中文:
定理 unop_ι
  条件: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : 余叉 f g)
  证明: by simp [Cofork.unop, Fork.ι]

Depends on / 依赖: Cofork, Cofork.unop
-/
theorem unop_ι {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g) :
    c.unop.ι = c.π.unop := by simp [Cofork.unop, Fork.ι]

/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: {X Y : C} {f g : X ⟶ Y} (c : Cofork f g)
  body: (Cone.postcompose (parallelPairOpIso f g).symm.hom).obj
    (Cone.whisker walkingParallelPairOpEquiv.functor (Cocone.op c))

中文:
定义 op
  签名: {X Y : C} {f g : X ⟶ Y} (c : 余叉 f g)
  定义体: (Cone.postcompose (parallelPairOpIso f g).symm.hom).obj
    (Cone.whisker walkingParallelPairOpEquiv.functor (Cocone.op c))

Depends on / 依赖: Cocone, Cocone.op, Cone.postcompose, Cone.whisker, functor, parallelPairOpIso, postcompose, symm.hom, walkingParallelPairOpEquiv, walkingParallelPairOpEquiv.functor, whisker
-/
def op {X Y : C} {f g : X ⟶ Y} (c : Cofork f g) : Fork f.op g.op :=
  (Cone.postcompose (parallelPairOpIso f g).symm.hom).obj
    (Cone.whisker walkingParallelPairOpEquiv.functor (Cocone.op c))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `op_π_app_one` / 引理 `op_π_app_one`

English:
lemma op_π_app_one
  given: {X Y : C} {f g : X ⟶ Y} (c : Cofork f g)
  proof: by
  simp [op]

中文:
引理 op_π_app_one
  条件: {X Y : C} {f g : X ⟶ Y} (c : 余叉 f g)
  证明: by
  simp [op]
-/
lemma op_π_app_one {X Y : C} {f g : X ⟶ Y} (c : Cofork f g) :
    c.op.π.app .one = Quiver.Hom.op (c.ι.app .zero) := by
  simp [op]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `op_π_app_zero` / 引理 `op_π_app_zero`

English:
lemma op_π_app_zero
  given: {X Y : C} {f g : X ⟶ Y} (c : Cofork f g)
  proof: by
  simp [op]

中文:
引理 op_π_app_zero
  条件: {X Y : C} {f g : X ⟶ Y} (c : 余叉 f g)
  证明: by
  simp [op]
-/
lemma op_π_app_zero {X Y : C} {f g : X ⟶ Y} (c : Cofork f g) :
    c.op.π.app .zero = Quiver.Hom.op (c.ι.app .one) := by
  simp [op]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `op_ι` / 定理 `op_ι`

English:
theorem op_ι
  given: {X Y : C} {f g : X ⟶ Y} (c : Cofork f g)
  proof: by simp [Cofork.op, Fork.ι]

中文:
定理 op_ι
  条件: {X Y : C} {f g : X ⟶ Y} (c : 余叉 f g)
  证明: by simp [Cofork.op, Fork.ι]

Depends on / 依赖: Cofork, Cofork.op
-/
theorem op_ι {X Y : C} {f g : X ⟶ Y} (c : Cofork f g) :
    c.op.ι = c.π.op := by simp [Cofork.op, Fork.ι]

end Cofork

namespace Fork

/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g)
  body: Cone.unop ((Cone.postcompose (opParallelPairIso f.unop g.unop).symm.hom).obj
    (Cone.whisker walkingParallelPairOpEquiv.inverse c))

中文:
定义 unop
  签名: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : 叉 f g)
  定义体: Cone.unop ((Cone.postcompose (opParallelPairIso f.unop g.unop).symm.hom).obj
    (Cone.whisker walkingParallelPairOpEquiv.inverse c))

Depends on / 依赖: Cone.postcompose, Cone.unop, Cone.whisker, f.unop, g.unop, inverse, opParallelPairIso, postcompose, symm.hom, walkingParallelPairOpEquiv, walkingParallelPairOpEquiv.inverse, whisker
-/
def unop {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g) : Cofork f.unop g.unop :=
  Cone.unop ((Cone.postcompose (opParallelPairIso f.unop g.unop).symm.hom).obj
    (Cone.whisker walkingParallelPairOpEquiv.inverse c))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `unop_ι_app_one` / 引理 `unop_ι_app_one`

English:
lemma unop_ι_app_one
  given: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g)
  proof: by
  simp [unop]

中文:
引理 unop_ι_app_one
  条件: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : 叉 f g)
  证明: by
  simp [unop]

Depends on / 依赖: createsLimitOfReflectsIso, limitConeLiftsToLimit
-/
lemma unop_ι_app_one {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g) :
    c.unop.ι.app .one = Quiver.Hom.unop (c.π.app .zero) := by
  simp [unop]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `unop_ι_app_zero` / 引理 `unop_ι_app_zero`

English:
lemma unop_ι_app_zero
  given: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g)
  proof: by
  simp [unop]

中文:
引理 unop_ι_app_zero
  条件: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : 叉 f g)
  证明: by
  simp [unop]
-/
lemma unop_ι_app_zero {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g) :
    c.unop.ι.app .zero = Quiver.Hom.unop (c.π.app .one) := by
  simp [unop]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `unop_π` / 定理 `unop_π`

English:
theorem unop_π
  given: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g)
  proof: by simp [Fork.unop, Cofork.π]

中文:
定理 unop_π
  条件: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : 叉 f g)
  证明: by simp [Fork.unop, Cofork.π]

Depends on / 依赖: Cofork, Fork.unop
-/
theorem unop_π {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g) :
    c.unop.π = c.ι.unop := by simp [Fork.unop, Cofork.π]

/-- The obvious map `Fork f g → Cofork f.op g.op` -/
@[simps!]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: {X Y : C} {f g : X ⟶ Y} (c : Fork f g)
  body: (Cocone.precompose (parallelPairOpIso f g).hom).obj
    (Cocone.whisker walkingParallelPairOpEquiv.functor (Cone.op c))

中文:
定义 op
  签名: {X Y : C} {f g : X ⟶ Y} (c : 叉 f g)
  定义体: (Cocone.precompose (parallelPairOpIso f g).hom).obj
    (Cocone.whisker walkingParallelPairOpEquiv.functor (Cone.op c))

Depends on / 依赖: Cocone, Cocone.precompose, Cocone.whisker, Cone.op, functor, parallelPairOpIso, precompose, walkingParallelPairOpEquiv, walkingParallelPairOpEquiv.functor, whisker
-/
def op {X Y : C} {f g : X ⟶ Y} (c : Fork f g) : Cofork f.op g.op :=
  (Cocone.precompose (parallelPairOpIso f g).hom).obj
    (Cocone.whisker walkingParallelPairOpEquiv.functor (Cone.op c))

set_option backward.defeqAttrib.useBackward true in
/--
lemma `op_ι_app_one` / 引理 `op_ι_app_one`

English:
lemma op_ι_app_one
  given: {X Y : C} {f g : X ⟶ Y} (c : Fork f g)
  proof: by
  simp [op]

中文:
引理 op_ι_app_one
  条件: {X Y : C} {f g : X ⟶ Y} (c : 叉 f g)
  证明: by
  simp [op]
-/
lemma op_ι_app_one {X Y : C} {f g : X ⟶ Y} (c : Fork f g) :
    c.op.ι.app .one = Quiver.Hom.op (c.π.app .zero) := by
  simp [op]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `op_ι_app_zero` / 引理 `op_ι_app_zero`

English:
lemma op_ι_app_zero
  given: {X Y : C} {f g : X ⟶ Y} (c : Fork f g)
  proof: by
  simp [op]

中文:
引理 op_ι_app_zero
  条件: {X Y : C} {f g : X ⟶ Y} (c : 叉 f g)
  证明: by
  simp [op]
-/
lemma op_ι_app_zero {X Y : C} {f g : X ⟶ Y} (c : Fork f g) :
    c.op.ι.app .zero = Quiver.Hom.op (c.π.app .one) := by
  simp [op]

set_option backward.defeqAttrib.useBackward true in
/--
theorem `op_π` / 定理 `op_π`

English:
theorem op_π
  given: {X Y : C} {f g : X ⟶ Y} (c : Fork f g)
  proof: by simp [Fork.op, Cofork.π]

中文:
定理 op_π
  条件: {X Y : C} {f g : X ⟶ Y} (c : 叉 f g)
  证明: by simp [Fork.op, Cofork.π]

Depends on / 依赖: Cofork, Fork.op
-/
theorem op_π {X Y : C} {f g : X ⟶ Y} (c : Fork f g) :
    c.op.π = c.ι.op := by simp [Fork.op, Cofork.π]

end Fork

namespace Cofork

set_option backward.isDefEq.respectTransparency false in
/--
theorem `op_unop_π` / 定理 `op_unop_π`

English:
theorem op_unop_π
  given: {X Y : C} {f g : X ⟶ Y} (c : Cofork f g)
  statement: c.op.unop.π = c.π
  proof: by
  simp [Fork.unop_π, Cofork.op_ι]

中文:
定理 op_unop_π
  条件: {X Y : C} {f g : X ⟶ Y} (c : 余叉 f g)
  结论: c.op.unop.π = c.π
  证明: by
  simp [Fork.unop_π, Cofork.op_ι]

Depends on / 依赖: Cofork, Cofork.op_, Fork.unop_
-/
theorem op_unop_π {X Y : C} {f g : X ⟶ Y} (c : Cofork f g) : c.op.unop.π = c.π := by
  simp [Fork.unop_π, Cofork.op_ι]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `unop_op_π` / 定理 `unop_op_π`

English:
theorem unop_op_π
  given: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g)
  statement: c.unop.op.π = c.π
  proof: by
  simp [Fork.op_π, Cofork.unop_ι]

中文:
定理 unop_op_π
  条件: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : 余叉 f g)
  结论: c.unop.op.π = c.π
  证明: by
  simp [Fork.op_π, Cofork.unop_ι]

Depends on / 依赖: Cofork, Cofork.unop_, Fork.op_
-/
theorem unop_op_π {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g) : c.unop.op.π = c.π := by
  simp [Fork.op_π, Cofork.unop_ι]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `opUnopIso` / `opUnopIso` 的定义

English:
definition opUnopIso
  signature: {X Y : C} {f g : X ⟶ Y} (c : Cofork f g)
  body: Cofork.ext (Iso.refl _) (by simp [op_unop_π])

中文:
定义 opUnopIso
  签名: {X Y : C} {f g : X ⟶ Y} (c : 余叉 f g)
  定义体: Cofork.ext (Iso.refl _) (by simp [op_unop_π])

Depends on / 依赖: Cofork, Cofork.ext, Iso.refl
-/
def opUnopIso {X Y : C} {f g : X ⟶ Y} (c : Cofork f g) : c.op.unop ≅ c :=
  Cofork.ext (Iso.refl _) (by simp [op_unop_π])

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `unopOpIso` / `unopOpIso` 的定义

English:
definition unopOpIso
  signature: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g)
  body: Cofork.ext (Iso.refl _) (by simp [unop_op_π])

中文:
定义 unopOpIso
  签名: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : 余叉 f g)
  定义体: Cofork.ext (Iso.refl _) (by simp [unop_op_π])

Depends on / 依赖: Cofork, Cofork.ext, Iso.refl
-/
def unopOpIso {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g) : c.unop.op ≅ c :=
  Cofork.ext (Iso.refl _) (by simp [unop_op_π])

end Cofork

namespace Fork

set_option backward.isDefEq.respectTransparency false in
/--
theorem `op_unop_ι` / 定理 `op_unop_ι`

English:
theorem op_unop_ι
  given: {X Y : C} {f g : X ⟶ Y} (c : Fork f g)
  statement: c.op.unop.ι = c.ι
  proof: by
  simp [Cofork.unop_ι, Fork.op_π]

中文:
定理 op_unop_ι
  条件: {X Y : C} {f g : X ⟶ Y} (c : 叉 f g)
  结论: c.op.unop.ι = c.ι
  证明: by
  simp [Cofork.unop_ι, Fork.op_π]

Depends on / 依赖: Cofork, Cofork.unop_, Fork.op_
-/
theorem op_unop_ι {X Y : C} {f g : X ⟶ Y} (c : Fork f g) : c.op.unop.ι = c.ι := by
  simp [Cofork.unop_ι, Fork.op_π]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `unop_op_ι` / 定理 `unop_op_ι`

English:
theorem unop_op_ι
  given: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g)
  statement: c.unop.op.ι = c.ι
  proof: by
  simp [Fork.unop_π, Cofork.op_ι]

中文:
定理 unop_op_ι
  条件: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : 叉 f g)
  结论: c.unop.op.ι = c.ι
  证明: by
  simp [Fork.unop_π, Cofork.op_ι]

Depends on / 依赖: Cofork, Cofork.op_, Fork.unop_
-/
theorem unop_op_ι {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g) : c.unop.op.ι = c.ι := by
  simp [Fork.unop_π, Cofork.op_ι]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `opUnopIso` / `opUnopIso` 的定义

English:
definition opUnopIso
  signature: {X Y : C} {f g : X ⟶ Y} (c : Fork f g)
  body: Fork.ext (Iso.refl _) (by simp [op_unop_ι])

中文:
定义 opUnopIso
  签名: {X Y : C} {f g : X ⟶ Y} (c : 叉 f g)
  定义体: Fork.ext (Iso.refl _) (by simp [op_unop_ι])

Depends on / 依赖: Fork.ext, Iso.refl
-/
def opUnopIso {X Y : C} {f g : X ⟶ Y} (c : Fork f g) : c.op.unop ≅ c :=
  Fork.ext (Iso.refl _) (by simp [op_unop_ι])

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `unopOpIso` / `unopOpIso` 的定义

English:
definition unopOpIso
  signature: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g)
  body: Fork.ext (Iso.refl _) (by simp [unop_op_ι])

中文:
定义 unopOpIso
  签名: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : 叉 f g)
  定义体: Fork.ext (Iso.refl _) (by simp [unop_op_ι])

Depends on / 依赖: Fork.ext, Iso.refl
-/
def unopOpIso {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g) : c.unop.op ≅ c :=
  Fork.ext (Iso.refl _) (by simp [unop_op_ι])

end Fork

namespace Cofork

/-- A cofork is a colimit cocone if and only if the corresponding fork in the opposite category is
a limit cone. -/
noncomputable -- just for performance; compilation takes several seconds
/--
Definition of `isColimitEquivIsLimitOp` / `isColimitEquivIsLimitOp` 的定义

English:
definition isColimitEquivIsLimitOp
  signature: {X Y : C} {f g : X ⟶ Y} (c : Cofork f g)
  body: by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    exact (IsLimit.postcomposeHomEquiv _ _).invFun ((IsLimit.whiskerEquivalenceEquiv _).toFun h.op)
  · intro h
    exact (IsColimit.equivIsoColimit c.opUnopIso).toFun (((IsLimit.postcomposeHomEquiv _ _).invFun
      ((IsLimit.whiskerEquivalen

中文:
定义 isColimitEquivIsLimitOp
  签名: {X Y : C} {f g : X ⟶ Y} (c : 余叉 f g)
  定义体: by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    exact (IsLimit.postcomposeHomEquiv _ _).invFun ((IsLimit.whiskerEquivalenceEquiv _).toFun h.op)
  · intro h
    exact (IsColimit.equivIsoColimit c.opUnopIso).toFun (((IsLimit.postcomposeHomEquiv _ _).invFun
      ((IsLimit.whiskerEquivalen

Depends on / 依赖: IsColimit, IsColimit.equivIsoColimit, IsLimit, IsLimit.postcomposeHomEquiv, IsLimit.whiskerEquivalenceEquiv, c.opUnopIso, equivIsoColimit, equivOfSubsingletonOfSubsingleton, h.op, invFun, opUnopIso, postcomposeHomEquiv, walkingParallelPairOpEquiv, walkingParallelPairOpEquiv.symm, whiskerEquivalenceEquiv
-/
def isColimitEquivIsLimitOp {X Y : C} {f g : X ⟶ Y} (c : Cofork f g) :
    IsColimit c ≃ IsLimit c.op := by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    exact (IsLimit.postcomposeHomEquiv _ _).invFun ((IsLimit.whiskerEquivalenceEquiv _).toFun h.op)
  · intro h
    exact (IsColimit.equivIsoColimit c.opUnopIso).toFun (((IsLimit.postcomposeHomEquiv _ _).invFun
      ((IsLimit.whiskerEquivalenceEquiv walkingParallelPairOpEquiv.symm).toFun h)).unop)

/-- A cofork is a colimit cocone in `Cᵒᵖ` if and only if the corresponding fork in `C` is
a limit cone. -/
noncomputable -- just for performance; compilation takes several seconds
/--
Definition of `isColimitEquivIsLimitUnop` / `isColimitEquivIsLimitUnop` 的定义

English:
definition isColimitEquivIsLimitUnop
  signature: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g)
  body: by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    exact ((IsColimit.precomposeHomEquiv _ _).invFun
      ((IsColimit.whiskerEquivalenceEquiv walkingParallelPairOpEquiv.symm).toFun h)).unop
  · intro h
    exact (IsColimit.equivIsoColimit c.unopOpIso).toFun
      ((IsColimit.precomposeHomE

中文:
定义 isColimitEquivIsLimitUnop
  签名: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : 余叉 f g)
  定义体: by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    exact ((IsColimit.precomposeHomEquiv _ _).invFun
      ((IsColimit.whiskerEquivalenceEquiv walkingParallelPairOpEquiv.symm).toFun h)).unop
  · intro h
    exact (IsColimit.equivIsoColimit c.unopOpIso).toFun
      ((IsColimit.precomposeHomE

Depends on / 依赖: IsColimit, IsColimit.equivIsoColimit, IsColimit.precomposeHomEquiv, IsColimit.whiskerEquivalenceEquiv, c.unopOpIso, equivIsoColimit, equivOfSubsingletonOfSubsingleton, h.op, invFun, precomposeHomEquiv, unopOpIso, walkingParallelPairOpEquiv, walkingParallelPairOpEquiv.symm, whiskerEquivalenceEquiv
-/
def isColimitEquivIsLimitUnop {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Cofork f g) :
    IsColimit c ≃ IsLimit c.unop := by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    exact ((IsColimit.precomposeHomEquiv _ _).invFun
      ((IsColimit.whiskerEquivalenceEquiv walkingParallelPairOpEquiv.symm).toFun h)).unop
  · intro h
    exact (IsColimit.equivIsoColimit c.unopOpIso).toFun
      ((IsColimit.precomposeHomEquiv _ _).invFun ((IsColimit.whiskerEquivalenceEquiv _).toFun h.op))

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ofπOpIsoOfι` / `ofπOpIsoOfι` 的定义

English:
definition ofπOpIsoOfι
  signature: {X Y P : C} {f g : X ⟶ Y} (π π' : Y ⟶ P) (w : f ≫ π = g ≫ π)
  body: Fork.ext (Iso.refl _) (by simp [Cofork.op_ι, h])

中文:
定义 ofπOpIsoOfι
  签名: {X Y P : C} {f g : X ⟶ Y} (π π' : Y ⟶ P) (w : f ≫ π = g ≫ π)
  定义体: Fork.ext (Iso.refl _) (by simp [Cofork.op_ι, h])

Depends on / 依赖: Cofork, Cofork.op_, Fork.ext, Iso.refl
-/
def ofπOpIsoOfι {X Y P : C} {f g : X ⟶ Y} (π π' : Y ⟶ P) (w : f ≫ π = g ≫ π)
    (w' : π'.op ≫ f.op = π'.op ≫ g.op) (h : π = π') :
    (Cofork.ofπ π w).op ≅ Fork.ofι π'.op w' :=
  Fork.ext (Iso.refl _) (by simp [Cofork.op_ι, h])

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ofπUnopIsoOfι` / `ofπUnopIsoOfι` 的定义

English:
definition ofπUnopIsoOfι
  signature: {X Y P : Cᵒᵖ} {f g : X ⟶ Y} (π π' : Y ⟶ P) (w : f ≫ π = g ≫ π)
  body: Fork.ext (Iso.refl _) (by simp [Cofork.unop_ι, h])

中文:
定义 ofπUnopIsoOfι
  签名: {X Y P : Cᵒᵖ} {f g : X ⟶ Y} (π π' : Y ⟶ P) (w : f ≫ π = g ≫ π)
  定义体: Fork.ext (Iso.refl _) (by simp [Cofork.unop_ι, h])

Depends on / 依赖: Cofork, Cofork.unop_, Fork.ext, Iso.refl
-/
def ofπUnopIsoOfι {X Y P : Cᵒᵖ} {f g : X ⟶ Y} (π π' : Y ⟶ P) (w : f ≫ π = g ≫ π)
    (w' : π'.unop ≫ f.unop = π'.unop ≫ g.unop) (h : π = π') :
    (Cofork.ofπ π w).unop ≅ Fork.ofι π'.unop w' :=
  Fork.ext (Iso.refl _) (by simp [Cofork.unop_ι, h])

/--
Definition of `isColimitOfπEquivIsLimitOp` / `isColimitOfπEquivIsLimitOp` 的定义

English:
definition isColimitOfπEquivIsLimitOp
  signature: {X Y P : C} {f g : X ⟶ Y} (π π' : Y ⟶ P) (w : f ≫ π = g ≫ π)
  body: (Cofork.ofπ π w).isColimitEquivIsLimitOp.trans (IsLimit.equivIsoLimit (ofπOpIsoOfι π π' w w' h))

中文:
定义 isColimitOfπEquivIsLimitOp
  签名: {X Y P : C} {f g : X ⟶ Y} (π π' : Y ⟶ P) (w : f ≫ π = g ≫ π)
  定义体: (Cofork.ofπ π w).isColimitEquivIsLimitOp.trans (IsLimit.equivIsoLimit (ofπOpIsoOfι π π' w w' h))

Depends on / 依赖: Cofork, Cofork.of, IsLimit, IsLimit.equivIsoLimit, equivIsoLimit, isColimitEquivIsLimitOp, isColimitEquivIsLimitOp.trans
-/
def isColimitOfπEquivIsLimitOp {X Y P : C} {f g : X ⟶ Y} (π π' : Y ⟶ P) (w : f ≫ π = g ≫ π)
    (w' : π'.op ≫ f.op = π'.op ≫ g.op) (h : π = π') :
    IsColimit (Cofork.ofπ π w) ≃ IsLimit (Fork.ofι π'.op w') :=
  (Cofork.ofπ π w).isColimitEquivIsLimitOp.trans (IsLimit.equivIsoLimit (ofπOpIsoOfι π π' w w' h))

/--
Definition of `isColimitOfπEquivIsLimitUnop` / `isColimitOfπEquivIsLimitUnop` 的定义

English:
definition isColimitOfπEquivIsLimitUnop
  signature: {X Y P : Cᵒᵖ} {f g : X ⟶ Y} (π π' : Y ⟶ P) (w : f ≫ π = g ≫ π)
  body: (Cofork.ofπ π w).isColimitEquivIsLimitUnop.trans
    (IsLimit.equivIsoLimit (ofπUnopIsoOfι π π' w w' h))

中文:
定义 isColimitOfπEquivIsLimitUnop
  签名: {X Y P : Cᵒᵖ} {f g : X ⟶ Y} (π π' : Y ⟶ P) (w : f ≫ π = g ≫ π)
  定义体: (Cofork.ofπ π w).isColimitEquivIsLimitUnop.trans
    (IsLimit.equivIsoLimit (ofπUnopIsoOfι π π' w w' h))

Depends on / 依赖: Cofork, Cofork.of, IsLimit, IsLimit.equivIsoLimit, equivIsoLimit, isColimitEquivIsLimitUnop, isColimitEquivIsLimitUnop.trans
-/
def isColimitOfπEquivIsLimitUnop {X Y P : Cᵒᵖ} {f g : X ⟶ Y} (π π' : Y ⟶ P) (w : f ≫ π = g ≫ π)
    (w' : π'.unop ≫ f.unop = π'.unop ≫ g.unop) (h : π = π') :
    IsColimit (Cofork.ofπ π w) ≃ IsLimit (Fork.ofι π'.unop w') :=
  (Cofork.ofπ π w).isColimitEquivIsLimitUnop.trans
    (IsLimit.equivIsoLimit (ofπUnopIsoOfι π π' w w' h))

end Cofork

namespace Fork

/--
Definition of `isLimitEquivIsColimitOp` / `isLimitEquivIsColimitOp` 的定义

English:
definition isLimitEquivIsColimitOp
  signature: {X Y : C} {f g : X ⟶ Y} (c : Fork f g)
  body: (IsLimit.equivIsoLimit c.opUnopIso).symm.trans c.op.isColimitEquivIsLimitUnop.symm

中文:
定义 isLimitEquivIsColimitOp
  签名: {X Y : C} {f g : X ⟶ Y} (c : 叉 f g)
  定义体: (IsLimit.equivIsoLimit c.opUnopIso).symm.trans c.op.isColimitEquivIsLimitUnop.symm

Depends on / 依赖: IsLimit, IsLimit.equivIsoLimit, c.op.isColimitEquivIsLimitUnop.symm, c.opUnopIso, equivIsoLimit, isColimitEquivIsLimitUnop, opUnopIso, symm.trans
-/
def isLimitEquivIsColimitOp {X Y : C} {f g : X ⟶ Y} (c : Fork f g) :
    IsLimit c ≃ IsColimit c.op :=
  (IsLimit.equivIsoLimit c.opUnopIso).symm.trans c.op.isColimitEquivIsLimitUnop.symm

/--
Definition of `isLimitEquivIsColimitUnop` / `isLimitEquivIsColimitUnop` 的定义

English:
definition isLimitEquivIsColimitUnop
  signature: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g)
  body: (IsLimit.equivIsoLimit c.unopOpIso).symm.trans c.unop.isColimitEquivIsLimitOp.symm

中文:
定义 isLimitEquivIsColimitUnop
  签名: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : 叉 f g)
  定义体: (IsLimit.equivIsoLimit c.unopOpIso).symm.trans c.unop.isColimitEquivIsLimitOp.symm

Depends on / 依赖: IsLimit, IsLimit.equivIsoLimit, c.unop.isColimitEquivIsLimitOp.symm, c.unopOpIso, equivIsoLimit, isColimitEquivIsLimitOp, symm.trans, unopOpIso
-/
def isLimitEquivIsColimitUnop {X Y : Cᵒᵖ} {f g : X ⟶ Y} (c : Fork f g) :
    IsLimit c ≃ IsColimit c.unop :=
  (IsLimit.equivIsoLimit c.unopOpIso).symm.trans c.unop.isColimitEquivIsLimitOp.symm

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `ofιOpIsoOfπ` / `ofιOpIsoOfπ` 的定义

English:
definition ofιOpIsoOfπ
  signature: {X Y P : C} {f g : X ⟶ Y} (ι ι' : P ⟶ X) (w : ι ≫ f = ι ≫ g)
  body: Cofork.ext (Iso.refl _) (by simp [Fork.op_π, h])

中文:
定义 ofιOpIsoOfπ
  签名: {X Y P : C} {f g : X ⟶ Y} (ι ι' : P ⟶ X) (w : ι ≫ f = ι ≫ g)
  定义体: Cofork.ext (Iso.refl _) (by simp [Fork.op_π, h])

Depends on / 依赖: Cofork, Cofork.ext, Fork.op_, Iso.refl
-/
def ofιOpIsoOfπ {X Y P : C} {f g : X ⟶ Y} (ι ι' : P ⟶ X) (w : ι ≫ f = ι ≫ g)
    (w' : f.op ≫ ι'.op = g.op ≫ ι'.op) (h : ι = ι') :
    (Fork.ofι ι w).op ≅ Cofork.ofπ ι'.op w' :=
  Cofork.ext (Iso.refl _) (by simp [Fork.op_π, h])

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ofιUnopIsoOfπ` / `ofιUnopIsoOfπ` 的定义

English:
definition ofιUnopIsoOfπ
  signature: {X Y P : Cᵒᵖ} {f g : X ⟶ Y} (ι ι' : P ⟶ X) (w : ι ≫ f = ι ≫ g)
  body: Cofork.ext (Iso.refl _) (by simp [Fork.unop_π, h])

中文:
定义 ofιUnopIsoOfπ
  签名: {X Y P : Cᵒᵖ} {f g : X ⟶ Y} (ι ι' : P ⟶ X) (w : ι ≫ f = ι ≫ g)
  定义体: Cofork.ext (Iso.refl _) (by simp [Fork.unop_π, h])

Depends on / 依赖: Cofork, Cofork.ext, Fork.unop_, Iso.refl
-/
def ofιUnopIsoOfπ {X Y P : Cᵒᵖ} {f g : X ⟶ Y} (ι ι' : P ⟶ X) (w : ι ≫ f = ι ≫ g)
    (w' : f.unop ≫ ι'.unop = g.unop ≫ ι'.unop) (h : ι = ι') :
    (Fork.ofι ι w).unop ≅ Cofork.ofπ ι'.unop w' :=
  Cofork.ext (Iso.refl _) (by simp [Fork.unop_π, h])

/--
Definition of `isLimitOfιEquivIsColimitOp` / `isLimitOfιEquivIsColimitOp` 的定义

English:
definition isLimitOfιEquivIsColimitOp
  signature: {X Y P : C} {f g : X ⟶ Y} (ι ι' : P ⟶ X) (w : ι ≫ f = ι ≫ g)
  body: (Fork.ofι ι w).isLimitEquivIsColimitOp.trans (IsColimit.equivIsoColimit (ofιOpIsoOfπ ι ι' w w' h))

中文:
定义 isLimitOfιEquivIsColimitOp
  签名: {X Y P : C} {f g : X ⟶ Y} (ι ι' : P ⟶ X) (w : ι ≫ f = ι ≫ g)
  定义体: (Fork.ofι ι w).isLimitEquivIsColimitOp.trans (IsColimit.equivIsoColimit (ofιOpIsoOfπ ι ι' w w' h))

Depends on / 依赖: Fork.of, IsColimit, IsColimit.equivIsoColimit, equivIsoColimit, isLimitEquivIsColimitOp, isLimitEquivIsColimitOp.trans
-/
def isLimitOfιEquivIsColimitOp {X Y P : C} {f g : X ⟶ Y} (ι ι' : P ⟶ X) (w : ι ≫ f = ι ≫ g)
    (w' : f.op ≫ ι'.op = g.op ≫ ι'.op) (h : ι = ι') :
    IsLimit (Fork.ofι ι w) ≃ IsColimit (Cofork.ofπ ι'.op w') :=
  (Fork.ofι ι w).isLimitEquivIsColimitOp.trans (IsColimit.equivIsoColimit (ofιOpIsoOfπ ι ι' w w' h))

/--
Definition of `isLimitOfιEquivIsColimitUnop` / `isLimitOfιEquivIsColimitUnop` 的定义

English:
definition isLimitOfιEquivIsColimitUnop
  signature: {X Y P : Cᵒᵖ} {f g : X ⟶ Y} (ι ι' : P ⟶ X) (w : ι ≫ f = ι ≫ g)
  body: (Fork.ofι ι w).isLimitEquivIsColimitUnop.trans
    (IsColimit.equivIsoColimit (ofιUnopIsoOfπ ι ι' w w' h))

中文:
定义 isLimitOfιEquivIsColimitUnop
  签名: {X Y P : Cᵒᵖ} {f g : X ⟶ Y} (ι ι' : P ⟶ X) (w : ι ≫ f = ι ≫ g)
  定义体: (Fork.ofι ι w).isLimitEquivIsColimitUnop.trans
    (IsColimit.equivIsoColimit (ofιUnopIsoOfπ ι ι' w w' h))

Depends on / 依赖: Fork.of, IsColimit, IsColimit.equivIsoColimit, equivIsoColimit, isLimitEquivIsColimitUnop, isLimitEquivIsColimitUnop.trans
-/
def isLimitOfιEquivIsColimitUnop {X Y P : Cᵒᵖ} {f g : X ⟶ Y} (ι ι' : P ⟶ X) (w : ι ≫ f = ι ≫ g)
    (w' : f.unop ≫ ι'.unop = g.unop ≫ ι'.unop) (h : ι = ι') :
    IsLimit (Fork.ofι ι w) ≃ IsColimit (Cofork.ofπ ι'.unop w') :=
  (Fork.ofι ι w).isLimitEquivIsColimitUnop.trans
    (IsColimit.equivIsoColimit (ofιUnopIsoOfπ ι ι' w w' h))

end Fork

namespace Cofork

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isColimitCoforkPushoutEquivIsColimitForkOpPullback` / `isColimitCoforkPushoutEquivIsColimitForkOpPullback` 的定义

English:
definition isColimitCoforkPushoutEquivIsColimitForkOpPullback
  body: Fork.isLimitOfIsos _ (Cofork.isColimitOfπEquivIsLimitOp f f
    pullback.condition (by simp only [← op_comp, pullback.condition]) rfl h) _ (.refl _)
      (pullbackIsoUnopPushout f f).op.symm (.refl _)
        (by simp [← op_comp]) (by simp [← op_comp]) (by simp)
  invFun h := Cofork.isColimitOfIsos

中文:
定义 isColimitCoforkPushoutEquivIsColimitForkOpPullback
  定义体: Fork.isLimitOfIsos _ (Cofork.isColimitOfπEquivIsLimitOp f f
    pullback.condition (by simp only [← op_comp, pullback.condition]) rfl h) _ (.refl _)
      (pullbackIsoUnopPushout f f).op.symm (.refl _)
        (by simp [← op_comp]) (by simp [← op_comp]) (by simp)
  invFun h := Cofork.isColimitOfIsos

Depends on / 依赖: Cofork, Cofork.isColimitOf, Fork.isLimitOfIsos, isLimitOfIsos
-/
def isColimitCoforkPushoutEquivIsColimitForkOpPullback
    {X Y : C} {f : X ⟶ Y} [HasPullback f f] :
    IsColimit (Cofork.ofπ f pullback.condition) ≃ IsLimit (Fork.ofι f.op pushout.condition) where
  toFun h := Fork.isLimitOfIsos _ (Cofork.isColimitOfπEquivIsLimitOp f f
    pullback.condition (by simp only [← op_comp, pullback.condition]) rfl h) _ (.refl _)
      (pullbackIsoUnopPushout f f).op.symm (.refl _)
        (by simp [← op_comp]) (by simp [← op_comp]) (by simp)
  invFun h := Cofork.isColimitOfIsos _ (Fork.isLimitOfιEquivIsColimitUnop f.op f.op
    pushout.condition (by rw [← unop_comp, ← unop_comp, pushout.condition]) rfl h) _
      (pullbackIsoUnopPushout f f).symm (.refl _) (.refl _) (by simp) (by simp) (by simp)
  left_inv := by cat_disch
  right_inv := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isColimitCoforkPushoutEquivIsColimitForkUnopPullback` / `isColimitCoforkPushoutEquivIsColimitForkUnopPullback` 的定义

English:
definition isColimitCoforkPushoutEquivIsColimitForkUnopPullback
  body: Fork.isLimitOfIsos _ (Cofork.isColimitOfπEquivIsLimitUnop f f pullback.condition
    (by simp only [← unop_comp, pullback.condition]) rfl h) _ (.refl _)
      (pullbackIsoOpPushout f f).unop.symm (.refl _)
        (by simp [← unop_comp]) (by simp [← unop_comp]) (by simp)
  invFun h :=
    Cofork.isC

中文:
定义 isColimitCoforkPushoutEquivIsColimitForkUnopPullback
  定义体: Fork.isLimitOfIsos _ (Cofork.isColimitOfπEquivIsLimitUnop f f pullback.condition
    (by simp only [← unop_comp, pullback.condition]) rfl h) _ (.refl _)
      (pullbackIsoOpPushout f f).unop.symm (.refl _)
        (by simp [← unop_comp]) (by simp [← unop_comp]) (by simp)
  invFun h :=
    Cofork.isC

Depends on / 依赖: Cofork, Cofork.isColimitOf, Fork.isLimitOfIsos, condition, isLimitOfIsos, pullback, pullback.condition
-/
def isColimitCoforkPushoutEquivIsColimitForkUnopPullback
    {X Y : Cᵒᵖ} {f : X ⟶ Y} [HasPullback f f] :
    IsColimit (Cofork.ofπ f pullback.condition) ≃ IsLimit (Fork.ofι f.unop pushout.condition) where
  toFun h := Fork.isLimitOfIsos _ (Cofork.isColimitOfπEquivIsLimitUnop f f pullback.condition
    (by simp only [← unop_comp, pullback.condition]) rfl h) _ (.refl _)
      (pullbackIsoOpPushout f f).unop.symm (.refl _)
        (by simp [← unop_comp]) (by simp [← unop_comp]) (by simp)
  invFun h :=
    Cofork.isColimitOfIsos _ (Fork.isLimitOfιEquivIsColimitOp f.unop f.unop pushout.condition
      (by rw [← op_comp, ← op_comp, pushout.condition]) rfl h) _
        (pullbackIsoOpPushout f f).symm (.refl _) (.refl _) (by simp) (by simp) (by simp)
  left_inv := by cat_disch
  right_inv := by cat_disch

end Cofork

namespace Fork

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isLimitForkPushoutEquivIsColimitForkOpPullback` / `isLimitForkPushoutEquivIsColimitForkOpPullback` 的定义

English:
definition isLimitForkPushoutEquivIsColimitForkOpPullback
  body: Cofork.isColimitOfIsos _ (Fork.isLimitOfιEquivIsColimitOp f f
    pushout.condition (by simp only [← op_comp, pushout.condition]) rfl h) _
      ((pushoutIsoUnopPullback f f).op.symm ≪≫ eqToIso rfl) (.refl _) (.refl _)
        (by simp) (by simp) (by simp)
  invFun h := by
    refine Fork.isLimitOfI

中文:
定义 isLimitForkPushoutEquivIsColimitForkOpPullback
  定义体: Cofork.isColimitOfIsos _ (Fork.isLimitOfιEquivIsColimitOp f f
    pushout.condition (by simp only [← op_comp, pushout.condition]) rfl h) _
      ((pushoutIsoUnopPullback f f).op.symm ≪≫ eqToIso rfl) (.refl _) (.refl _)
        (by simp) (by simp) (by simp)
  invFun h := by
    refine Fork.isLimitOfI

Depends on / 依赖: Cofork, Cofork.isColimitOfIsos, Fork.isLimitOf, isColimitOfIsos
-/
def isLimitForkPushoutEquivIsColimitForkOpPullback
    {X Y : C} {f : X ⟶ Y} [HasPushout f f] :
    IsLimit (Fork.ofι f pushout.condition) ≃ IsColimit (Cofork.ofπ f.op pullback.condition) where
  toFun h := Cofork.isColimitOfIsos _ (Fork.isLimitOfιEquivIsColimitOp f f
    pushout.condition (by simp only [← op_comp, pushout.condition]) rfl h) _
      ((pushoutIsoUnopPullback f f).op.symm ≪≫ eqToIso rfl) (.refl _) (.refl _)
        (by simp) (by simp) (by simp)
  invFun h := by
    refine Fork.isLimitOfIsos _ (Cofork.isColimitOfπEquivIsLimitUnop f.op f.op
      pullback.condition (by simp only [← unop_comp, pullback.condition]) rfl h) _ (.refl _)
        ((pushoutIsoUnopPullback f f).symm) (.refl _) ?_ ?_ (by simp)
    · rw [Iso.symm_hom, ← Quiver.Hom.unop_op (pushoutIsoUnopPullback f f).inv, ← unop_comp,
        pushoutIsoUnopPullback_inv_fst, Quiver.Hom.unop_op, Iso.refl_hom, Category.id_comp]
    · rw [Iso.symm_hom, ← Quiver.Hom.unop_op (pushoutIsoUnopPullback f f).inv, ← unop_comp,
        pushoutIsoUnopPullback_inv_snd, Quiver.Hom.unop_op, Iso.refl_hom, Category.id_comp]
  left_inv := by cat_disch
  right_inv := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isLimitForkPushoutEquivIsColimitForkUnopPullback` / `isLimitForkPushoutEquivIsColimitForkUnopPullback` 的定义

English:
definition isLimitForkPushoutEquivIsColimitForkUnopPullback
  body: Cofork.isColimitOfIsos _ (Fork.isLimitOfιEquivIsColimitUnop f f pushout.condition
    (by simp only [← unop_comp, pushout.condition]) rfl h) _
      ((pushoutIsoOpPullback f f).unop.symm ≪≫ eqToIso rfl) (.refl _) (.refl _)
        (by simp) (by simp) (by simp)
  invFun h := by
    refine Fork.isLimi

中文:
定义 isLimitForkPushoutEquivIsColimitForkUnopPullback
  定义体: Cofork.isColimitOfIsos _ (Fork.isLimitOfιEquivIsColimitUnop f f pushout.condition
    (by simp only [← unop_comp, pushout.condition]) rfl h) _
      ((pushoutIsoOpPullback f f).unop.symm ≪≫ eqToIso rfl) (.refl _) (.refl _)
        (by simp) (by simp) (by simp)
  invFun h := by
    refine Fork.isLimi

Depends on / 依赖: Cofork, Cofork.isColimitOfIsos, Fork.isLimitOf, condition, isColimitOfIsos, pushout, pushout.condition
-/
def isLimitForkPushoutEquivIsColimitForkUnopPullback
    {X Y : Cᵒᵖ} {f : X ⟶ Y} [HasPushout f f] :
    IsLimit (Fork.ofι f pushout.condition) ≃ IsColimit (Cofork.ofπ f.unop pullback.condition) where
  toFun h := Cofork.isColimitOfIsos _ (Fork.isLimitOfιEquivIsColimitUnop f f pushout.condition
    (by simp only [← unop_comp, pushout.condition]) rfl h) _
      ((pushoutIsoOpPullback f f).unop.symm ≪≫ eqToIso rfl) (.refl _) (.refl _)
        (by simp) (by simp) (by simp)
  invFun h := by
    refine Fork.isLimitOfIsos _ (Cofork.isColimitOfπEquivIsLimitOp f.unop f.unop pullback.condition
      (by simp only [← op_comp, pullback.condition]) rfl h) _ (.refl _)
        ((pushoutIsoOpPullback f f).symm) (.refl _) ?_ ?_ (by simp)
    · rw [Iso.symm_hom, ← Quiver.Hom.op_unop (pushoutIsoOpPullback f f).inv, ← op_comp,
        pushoutIsoOpPullback_inv_fst, Quiver.Hom.op_unop, Iso.refl_hom, Category.id_comp]
    · rw [Iso.symm_hom, ← Quiver.Hom.op_unop (pushoutIsoOpPullback f f).inv, ← op_comp,
        pushoutIsoOpPullback_inv_snd, Quiver.Hom.op_unop, Iso.refl_hom, Category.id_comp]
  left_inv := by cat_disch
  right_inv := by cat_disch

end Fork

end CategoryTheory.Limits
