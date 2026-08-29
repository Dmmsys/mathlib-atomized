/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.Equivalence

/-!

# Localization of the opposite category

If a functor `L : C ⥤ D` is a localization functor for `W : MorphismProperty C`, it
is shown in this file that `L.op : Cᵒᵖ ⥤ Dᵒᵖ` is also a localization functor.

-/

@[expose] public section


noncomputable section

open CategoryTheory CategoryTheory.Category

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {W : MorphismProperty C}

namespace Localization

/--
Definition of `StrictUniversalPropertyFixedTarget.op` / `StrictUniversalPropertyFixedTarget.op` 的定义

English:
definition StrictUniversalPropertyFixedTarget.op
  signature: {E : Type*} [Category* E]
  body: h.inverts.op
  lift F hF := (h.lift F.rightOp hF.rightOp).leftOp
  fac F hF := by
    convert! congr_arg Functor.leftOp (h.fac F.rightOp hF.rightOp)
  uniq F₁ F₂ eq := by
    suffices F₁.rightOp = F₂.rightOp by
      rw [← F₁.rightOp_leftOp_eq]; rw [← F₂.rightOp_leftOp_eq]; rw [this]
    have eq' := congr_arg Functor.rightOp eq
    exact h.uniq _ _ eq'

中文:
定义 StrictUniversalPropertyFixedTarget.op
  签名: {E : 类型} [范畴* E]
  定义体: h.inverts.op
  lift F hF := (h.lift F.rightOp hF.rightOp).leftOp
  fac F hF := by
    convert! congr_arg Functor.leftOp (h.fac F.rightOp hF.rightOp)
  uniq F₁ F₂ eq := by
    suffices F₁.rightOp = F₂.rightOp by
      rw [← F₁.rightOp_leftOp_eq]; rw [← F₂.rightOp_leftOp_eq]; rw [this]
    have eq' := congr_arg Functor.rightOp eq
    exact h.uniq _ _ eq'

Depends on / 依赖: h.inverts.op, inverts
-/
def StrictUniversalPropertyFixedTarget.op {E : Type*} [Category* E]
    (h : StrictUniversalPropertyFixedTarget L W Eᵒᵖ) :
    StrictUniversalPropertyFixedTarget L.op W.op E where
  inverts := h.inverts.op
  lift F hF := (h.lift F.rightOp hF.rightOp).leftOp
  fac F hF := by
    convert! congr_arg Functor.leftOp (h.fac F.rightOp hF.rightOp)
  uniq F₁ F₂ eq := by
    suffices F₁.rightOp = F₂.rightOp by
      rw [← F₁.rightOp_leftOp_eq]; rw [← F₂.rightOp_leftOp_eq]; rw [this]
    have eq' := congr_arg Functor.rightOp eq
    exact h.uniq _ _ eq'

/--
Instance `isLocalization_op` / 实例 `isLocalization_op`

English:
instance isLocalization_op
  signature: : W.Q.op.IsLocalization W.op
  body: Functor.IsLocalization.mk' W.Q.op W.op (strictUniversalPropertyFixedTargetQ W _).op
    (strictUniversalPropertyFixedTargetQ W _).op

中文:
实例 isLocalization_op
  签名: : W.Q.op.是Localization W.op
  定义体: Functor.IsLocalization.mk' W.Q.op W.op (strictUniversalPropertyFixedTargetQ W _).op
    (strictUniversalPropertyFixedTargetQ W _).op

Depends on / 依赖: Functor, Functor.IsLocalization.mk, IsLocalization, W.Q.op, W.op, strictUniversalPropertyFixedTargetQ
-/
instance isLocalization_op : W.Q.op.IsLocalization W.op :=
  Functor.IsLocalization.mk' W.Q.op W.op (strictUniversalPropertyFixedTargetQ W _).op
    (strictUniversalPropertyFixedTargetQ W _).op

end Localization

variable (L W)
variable [L.IsLocalization W]

namespace Functor

/--
Instance `IsLocalization.op` / 实例 `IsLocalization.op`

English:
instance IsLocalization.op
  signature: : L.op.IsLocalization W.op
  body: IsLocalization.of_equivalence_target W.Q.op W.op L.op (Localization.equivalenceFromModel L W).op
    (NatIso.op (Localization.qCompEquivalenceFromModelFunctorIso L W).symm)

中文:
实例 是Localization.op
  签名: : L.op.是Localization W.op
  定义体: IsLocalization.of_equivalence_target W.Q.op W.op L.op (Localization.equivalenceFromModel L W).op
    (NatIso.op (Localization.qCompEquivalenceFromModelFunctorIso L W).symm)

Depends on / 依赖: IsLocalization, IsLocalization.of_equivalence_target, L.op, Localization, Localization.equivalenceFromModel, Localization.qCompEquivalenceFromModelFunctorIso, NatIso, NatIso.op, W.Q.op, W.op, equivalenceFromModel, of_equivalence_target, qCompEquivalenceFromModelFunctorIso
-/
instance IsLocalization.op : L.op.IsLocalization W.op :=
  IsLocalization.of_equivalence_target W.Q.op W.op L.op (Localization.equivalenceFromModel L W).op
    (NatIso.op (Localization.qCompEquivalenceFromModelFunctorIso L W).symm)

set_option backward.defeqAttrib.useBackward true in
/--
Instance `IsLocalization.unop` / 实例 `IsLocalization.unop`

English:
instance IsLocalization.unop
  signature: (L : Cᵒᵖ ⥤ Dᵒᵖ) (W : MorphismProperty Cᵒᵖ)
  body: have : CatCommSq (opOpEquivalence C).functor L.op L.unop
    (opOpEquivalence D).functor := ⟨Iso.refl _⟩
  of_equivalences L.op W.op L.unop W.unop
    (opOpEquivalence C) (opOpEquivalence D)
    (fun _ _ _ hf => MorphismProperty.le_isoClosure _ _ hf)
    (fun _ _ _ hf => by
      have := Localization.inverts L W _ hf
      dsimp
      infer_instance)

@[simp]

中文:
实例 是Localization.unop
  签名: (L : Cᵒᵖ ⥤ Dᵒᵖ) (W : MorphismProperty Cᵒᵖ)
  定义体: have : CatCommSq (opOpEquivalence C).functor L.op L.unop
    (opOpEquivalence D).functor := ⟨Iso.refl _⟩
  of_equivalences L.op W.op L.unop W.unop
    (opOpEquivalence C) (opOpEquivalence D)
    (fun _ _ _ hf => MorphismProperty.le_isoClosure _ _ hf)
    (fun _ _ _ hf => by
      have := Localization.inverts L W _ hf
      dsimp
      infer_instance)

@[simp]

Depends on / 依赖: CatCommSq, Iso.refl, L.op, L.unop, Localization, Localization.inverts, MorphismProperty, MorphismProperty.le_isoClosure, W.op, W.unop, functor, infer_instance, inverts, le_isoClosure, of_equivalences, opOpEquivalence
-/
instance IsLocalization.unop (L : Cᵒᵖ ⥤ Dᵒᵖ) (W : MorphismProperty Cᵒᵖ)
    [L.IsLocalization W] : L.unop.IsLocalization W.unop :=
  have : CatCommSq (opOpEquivalence C).functor L.op L.unop
    (opOpEquivalence D).functor := ⟨Iso.refl _⟩
  of_equivalences L.op W.op L.unop W.unop
    (opOpEquivalence C) (opOpEquivalence D)
    (fun _ _ _ hf => MorphismProperty.le_isoClosure _ _ hf)
    (fun _ _ _ hf => by
      have := Localization.inverts L W _ hf
      dsimp
      infer_instance)

@[simp]
/--
lemma `IsLocalization.op_iff` / 引理 `IsLocalization.op_iff`

English:
lemma IsLocalization.op_iff
  given: (L : C ⥤ D) (W : MorphismProperty C)
  proof: ⟨fun _ => inferInstanceAs (L.op.unop.IsLocalization W.op.unop),
    fun _ => inferInstance⟩

中文:
引理 是Localization.op_iff
  条件: (L : C ⥤ D) (W : MorphismProperty C)
  证明: ⟨fun _ => inferInstanceAs (L.op.unop.IsLocalization W.op.unop),
    fun _ => inferInstance⟩

Depends on / 依赖: IsLocalization, L.op.unop.IsLocalization, W.op.unop
-/
lemma IsLocalization.op_iff (L : C ⥤ D) (W : MorphismProperty C) :
    L.op.IsLocalization W.op ↔ L.IsLocalization W :=
  ⟨fun _ => inferInstanceAs (L.op.unop.IsLocalization W.op.unop),
    fun _ => inferInstance⟩

end Functor

namespace Localization

/--
lemma `isoOfHom_unop` / 引理 `isoOfHom_unop`

English:
lemma isoOfHom_unop
  given: {X Y : Cᵒᵖ} (w : X ⟶ Y) (hw : W.op w)
  proof: by ext; rfl

中文:
引理 isoOfHom_unop
  条件: {X Y : Cᵒᵖ} (w : X ⟶ Y) (hw : W.op w)
  证明: by ext; rfl
-/
lemma isoOfHom_unop {X Y : Cᵒᵖ} (w : X ⟶ Y) (hw : W.op w) :
    (isoOfHom L.op W.op w hw).unop = (isoOfHom L W w.unop hw) := by ext; rfl

/--
lemma `isoOfHom_op_inv` / 引理 `isoOfHom_op_inv`

English:
lemma isoOfHom_op_inv
  given: {X Y : Cᵒᵖ} (w : X ⟶ Y) (hw : W.op w)
  proof: congr_arg Quiver.Hom.op (congr_arg Iso.inv (isoOfHom_unop L W w hw))

中文:
引理 isoOfHom_op_inv
  条件: {X Y : Cᵒᵖ} (w : X ⟶ Y) (hw : W.op w)
  证明: congr_arg Quiver.Hom.op (congr_arg Iso.inv (isoOfHom_unop L W w hw))

Depends on / 依赖: Iso.inv, Quiver, Quiver.Hom.op, congr_arg, isoOfHom_unop
-/
lemma isoOfHom_op_inv {X Y : Cᵒᵖ} (w : X ⟶ Y) (hw : W.op w) :
    (isoOfHom L.op W.op w hw).inv = (isoOfHom L W w.unop hw).inv.op :=
  congr_arg Quiver.Hom.op (congr_arg Iso.inv (isoOfHom_unop L W w hw))

end Localization

end CategoryTheory
