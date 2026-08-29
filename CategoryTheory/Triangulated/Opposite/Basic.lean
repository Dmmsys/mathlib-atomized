/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.Shift.Opposite
public import Mathlib.CategoryTheory.Shift.Pullback

/-!
# The shift on the opposite category of a pretriangulated category

Let `C` be a (pre)triangulated category. We already have a shift on `Cᵒᵖ` given
by `CategoryTheory.Shift.Opposite`, but this is not the shift that we want to
make `Cᵒᵖ` into a (pre)triangulated category.
The correct shift on `Cᵒᵖ` is obtained by combining the constructions in the files
`CategoryTheory.Shift.Opposite` and `CategoryTheory.Shift.Pullback`.
When the user opens `CategoryTheory.Pretriangulated.Opposite`, the
category `Cᵒᵖ` is equipped with the shift by `ℤ` such that
shifting by `n : ℤ` on `Cᵒᵖ` corresponds to the shift by
`-n` on `C`. This is actually a definitional equality, but the user
should not rely on this, and instead use the isomorphism
`shiftFunctorOpIso C n m hnm : shiftFunctor Cᵒᵖ n ≅ (shiftFunctor C m).op`
where `hnm : n + m = 0`.

Some compatibilities between the shifts on `C` and `Cᵒᵖ` are also expressed through
the equivalence of categories `opShiftFunctorEquivalence C n : Cᵒᵖ ≌ Cᵒᵖ` whose
functor is `shiftFunctor Cᵒᵖ n` and whose inverse functor is `(shiftFunctor C n).op`.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

open Category Limits Preadditive ZeroObject

variable (C : Type*) [Category* C]

namespace Pretriangulated

variable [HasShift C Int]

namespace Opposite

set_option backward.privateInPublic true in
/--
Definition of `OppositeShiftAux` / `OppositeShiftAux` 的定义

English:
abbreviation OppositeShiftAux
  body: PullbackShift (OppositeShift C Int)
    (AddMonoidHom.mk' (fun (n : Int) => -n) (by intros; lia))

中文:
缩写 OppositeShiftAux
  定义体: PullbackShift (OppositeShift C Int)
    (AddMonoidHom.mk' (fun (n : Int) => -n) (by intros; lia))
-/
private abbrev OppositeShiftAux :=
  PullbackShift (OppositeShift C Int)
    (AddMonoidHom.mk' (fun (n : Int) => -n) (by intros; lia))

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The category `Cᵒᵖ` is equipped with the shift such that the shift by `n` on `Cᵒᵖ`
corresponds to the shift by `-n` on `C`. -/
scoped instance : HasShift Cᵒᵖ Int :=
inferInstanceAs HasShift (OppositeShiftAux C) Int

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preadditive
  signature: C] [forall (n : Int), (shiftFunctor C n).Additive] (n
  body: inferInstanceAs (shiftFunctor (OppositeShiftAux C) n).Additive

中文:
实例 [Preadditive
  签名: C] [对任意 (n : 整数), (shiftFunctor C n).Additive] (n
  定义体: inferInstanceAs (shiftFunctor (OppositeShiftAux C) n).Additive

Depends on / 依赖: Additive, OppositeShiftAux, shiftFunctor
-/
instance [Preadditive C] [forall (n : Int), (shiftFunctor C n).Additive] (n : Int) :
    (shiftFunctor Cᵒᵖ n).Additive :=
inferInstanceAs (shiftFunctor (OppositeShiftAux C) n).Additive

end Opposite

open Pretriangulated.Opposite

/--
Definition of `shiftFunctorOpIso` / `shiftFunctorOpIso` 的定义

English:
definition shiftFunctorOpIso
  signature: (n m : Int) (hnm : n + m = 0)
  body: eqToIso (by
  obtain rfl : m = -n := by lia
  rfl)

中文:
定义 shiftFunctorOpIso
  签名: (n m : 整数) (hnm : n + m = 0)
  定义体: eqToIso (by
  obtain rfl : m = -n := by lia
  rfl)

Depends on / 依赖: eqToIso
-/
def shiftFunctorOpIso (n m : Int) (hnm : n + m = 0) :
    shiftFunctor Cᵒᵖ n ≅ (shiftFunctor C m).op := eqToIso (by
  obtain rfl : m = -n := by lia
  rfl)

variable {C}

/--
lemma `shiftFunctorZero_op_hom_app` / 引理 `shiftFunctorZero_op_hom_app`

English:
lemma shiftFunctorZero_op_hom_app
  given: (X : Cᵒᵖ)
  proof: rfl

中文:
引理 shiftFunctorZero_op_hom_app
  条件: (X : Cᵒᵖ)
  证明: rfl
-/
lemma shiftFunctorZero_op_hom_app (X : Cᵒᵖ) :
    (shiftFunctorZero Cᵒᵖ Int).hom.app X = (shiftFunctorOpIso C 0 0 (zero_add 0)).hom.app X ≫
      ((shiftFunctorZero C Int).inv.app X.unop).op := rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `shiftFunctorZero_op_inv_app` / 引理 `shiftFunctorZero_op_inv_app`

English:
lemma shiftFunctorZero_op_inv_app
  given: (X : Cᵒᵖ)
  proof: by
  rw [← cancel_epi ((shiftFunctorZero Cᵒᵖ Int).hom.app X)]; rw [Iso.hom_inv_id_app]; rw [shiftFunctorZero_op_hom_app]; rw [assoc]; rw [← op_comp_assoc]; rw [Iso.hom_inv_id_app]; rw [op_id]; rw [id_comp]; rw [Iso.hom_inv_id_app]

中文:
引理 shiftFunctorZero_op_inv_app
  条件: (X : Cᵒᵖ)
  证明: by
  rw [← cancel_epi ((shiftFunctorZero Cᵒᵖ Int).hom.app X)]; rw [Iso.hom_inv_id_app]; rw [shiftFunctorZero_op_hom_app]; rw [assoc]; rw [← op_comp_assoc]; rw [Iso.hom_inv_id_app]; rw [op_id]; rw [id_comp]; rw [Iso.hom_inv_id_app]

Depends on / 依赖: Iso.hom_inv_id_app, cancel_epi, hom.app, hom_inv_id_app, id_comp, op_comp_assoc, op_id, shiftFunctorZero, shiftFunctorZero_op_hom_app
-/
lemma shiftFunctorZero_op_inv_app (X : Cᵒᵖ) :
    (shiftFunctorZero Cᵒᵖ Int).inv.app X =
      ((shiftFunctorZero C Int).hom.app X.unop).op ≫
      (shiftFunctorOpIso C 0 0 (zero_add 0)).inv.app X := by
  rw [← cancel_epi ((shiftFunctorZero Cᵒᵖ Int).hom.app X)]; rw [Iso.hom_inv_id_app]; rw [shiftFunctorZero_op_hom_app]; rw [assoc]; rw [← op_comp_assoc]; rw [Iso.hom_inv_id_app]; rw [op_id]; rw [id_comp]; rw [Iso.hom_inv_id_app]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftFunctorAdd'_op_hom_app` / 引理 `shiftFunctorAdd'_op_hom_app`

English:
lemma shiftFunctorAdd'_op_hom_app
  statement: (X : Cᵒᵖ) (a₁ a₂ a₃ : Int) (h : a₁ + a₂ = a₃)
  proof: by
  erw [@pullbackShiftFunctorAdd'_hom_app (OppositeShift C Int) _ _ _ _ _ _ _ X
    a₁ a₂ a₃ h b₁ b₂ b₃ (by dsimp; lia) (by dsimp; lia) (by dsimp; lia)]
  rw [oppositeShiftFunctorAdd'_hom_app]
  rfl

中文:
引理 shiftFunctorAdd'_op_hom_app
  结论: (X : Cᵒᵖ) (a₁ a₂ a₃ : 整数) (h : a₁ + a₂ = a₃)
  证明: by
  erw [@pullbackShiftFunctorAdd'_hom_app (OppositeShift C Int) _ _ _ _ _ _ _ X
    a₁ a₂ a₃ h b₁ b₂ b₃ (by dsimp; lia) (by dsimp; lia) (by dsimp; lia)]
  rw [oppositeShiftFunctorAdd'_hom_app]
  rfl

Depends on / 依赖: OppositeShift, _hom_app, oppositeShiftFunctorAdd, pullbackShiftFunctorAdd
-/
lemma shiftFunctorAdd'_op_hom_app (X : Cᵒᵖ) (a₁ a₂ a₃ : Int) (h : a₁ + a₂ = a₃)
    (b₁ b₂ b₃ : Int) (h₁ : a₁ + b₁ = 0) (h₂ : a₂ + b₂ = 0) (h₃ : a₃ + b₃ = 0) :
    (shiftFunctorAdd' Cᵒᵖ a₁ a₂ a₃ h).hom.app X =
      (shiftFunctorOpIso C _ _ h₃).hom.app X ≫
        ((shiftFunctorAdd' C b₁ b₂ b₃ (by lia)).inv.app X.unop).op ≫
        (shiftFunctorOpIso C _ _ h₂).inv.app _ ≫
        (shiftFunctor Cᵒᵖ a₂).map ((shiftFunctorOpIso C _ _ h₁).inv.app X) := by
  erw [@pullbackShiftFunctorAdd'_hom_app (OppositeShift C Int) _ _ _ _ _ _ _ X
    a₁ a₂ a₃ h b₁ b₂ b₃ (by dsimp; lia) (by dsimp; lia) (by dsimp; lia)]
  rw [oppositeShiftFunctorAdd'_hom_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `shiftFunctorAdd'_op_inv_app` / 引理 `shiftFunctorAdd'_op_inv_app`

English:
lemma shiftFunctorAdd'_op_inv_app
  statement: (X : Cᵒᵖ) (a₁ a₂ a₃ : Int) (h : a₁ + a₂ = a₃)
  proof: by
  rw [← cancel_epi ((shiftFunctorAdd' Cᵒᵖ a₁ a₂ a₃ h).hom.app X)]; rw [Iso.hom_inv_id_app]; rw [shiftFunctorAdd'_op_hom_app X a₁ a₂ a₃ h b₁ b₂ b₃ h₁ h₂ h₃]; rw [assoc]; rw [assoc]; rw [assoc]; rw [← Functor.map_comp_assoc]; rw [Iso.inv_hom_id_app]
  erw [Functor.map_id, id_comp, Iso.inv_hom_id_ap

中文:
引理 shiftFunctorAdd'_op_inv_app
  结论: (X : Cᵒᵖ) (a₁ a₂ a₃ : 整数) (h : a₁ + a₂ = a₃)
  证明: by
  rw [← cancel_epi ((shiftFunctorAdd' Cᵒᵖ a₁ a₂ a₃ h).hom.app X)]; rw [Iso.hom_inv_id_app]; rw [shiftFunctorAdd'_op_hom_app X a₁ a₂ a₃ h b₁ b₂ b₃ h₁ h₂ h₃]; rw [assoc]; rw [assoc]; rw [assoc]; rw [← Functor.map_comp_assoc]; rw [Iso.inv_hom_id_app]
  erw [Functor.map_id, id_comp, Iso.inv_hom_id_ap
-/
lemma shiftFunctorAdd'_op_inv_app (X : Cᵒᵖ) (a₁ a₂ a₃ : Int) (h : a₁ + a₂ = a₃)
    (b₁ b₂ b₃ : Int) (h₁ : a₁ + b₁ = 0) (h₂ : a₂ + b₂ = 0) (h₃ : a₃ + b₃ = 0) :
    (shiftFunctorAdd' Cᵒᵖ a₁ a₂ a₃ h).inv.app X =
      (shiftFunctor Cᵒᵖ a₂).map ((shiftFunctorOpIso C _ _ h₁).hom.app X) ≫
      (shiftFunctorOpIso C _ _ h₂).hom.app _ ≫
      ((shiftFunctorAdd' C b₁ b₂ b₃ (by lia)).hom.app X.unop).op ≫
      (shiftFunctorOpIso C _ _ h₃).inv.app X := by
  rw [← cancel_epi ((shiftFunctorAdd' Cᵒᵖ a₁ a₂ a₃ h).hom.app X)]; rw [Iso.hom_inv_id_app]; rw [shiftFunctorAdd'_op_hom_app X a₁ a₂ a₃ h b₁ b₂ b₃ h₁ h₂ h₃]; rw [assoc]; rw [assoc]; rw [assoc]; rw [← Functor.map_comp_assoc]; rw [Iso.inv_hom_id_app]
  erw [Functor.map_id, id_comp, Iso.inv_hom_id_app_assoc]
  rw [← op_comp_assoc]; rw [Iso.hom_inv_id_app]; rw [op_id]; rw [id_comp]; rw [Iso.hom_inv_id_app]

/--
lemma `shiftFunctor_op_map` / 引理 `shiftFunctor_op_map`

English:
lemma shiftFunctor_op_map
  given: {K L : Cᵒᵖ} (φ : K ⟶ L) (n m : Int) (hnm : n + m = 0 := by lia)
  proof: (NatIso.naturality_2 (shiftFunctorOpIso C n m hnm) φ).symm

中文:
引理 shiftFunctor_op_map
  条件: {K L : Cᵒᵖ} (φ : K ⟶ L) (n m : 整数) (hnm : n + m = 0 := by lia)
  证明: (NatIso.naturality_2 (shiftFunctorOpIso C n m hnm) φ).symm

Depends on / 依赖: NatIso, NatIso.naturality_2, hom.app, inv.app, naturality_2, shiftFunctor, shiftFunctorOpIso
-/
lemma shiftFunctor_op_map {K L : Cᵒᵖ} (φ : K ⟶ L) (n m : Int) (hnm : n + m = 0 := by lia) :
    (shiftFunctor Cᵒᵖ n).map φ =
      (shiftFunctorOpIso C n m hnm).hom.app K ≫ ((shiftFunctor C m).map φ.unop).op ≫
        (shiftFunctorOpIso C n m hnm).inv.app L :=
  (NatIso.naturality_2 (shiftFunctorOpIso C n m hnm) φ).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
variable (C) in
/-- The autoequivalence `Cᵒᵖ ≌ Cᵒᵖ` whose functor is `shiftFunctor Cᵒᵖ n` and whose inverse
functor is `(shiftFunctor C n).op`. In most cases, it is not necessary to unfold the
definitions of the unit and counit isomorphisms: the compatibilities they satisfy
are stated as separate lemmas. -/
@[simps functor inverse, implicit_reducible]
/--
Definition of `opShiftFunctorEquivalence` / `opShiftFunctorEquivalence` 的定义

English:
definition opShiftFunctorEquivalence
  signature: (n : Int)
  body: shiftFunctor Cᵒᵖ n
  inverse := (shiftFunctor C n).op
  unitIso := NatIso.op (shiftFunctorCompIsoId C (-n) n n.add_left_neg) ≪≫
    Functor.isoWhiskerRight (shiftFunctorOpIso C n (-n) n.add_right_neg).symm (shiftFunctor C n).op
  counitIso := Functor.isoWhiskerLeft _ (shiftFunctorOpIso C n (-n) n.ad

中文:
定义 opShiftFunctorEquivalence
  签名: (n : 整数)
  定义体: shiftFunctor Cᵒᵖ n
  inverse := (shiftFunctor C n).op
  unitIso := NatIso.op (shiftFunctorCompIsoId C (-n) n n.add_left_neg) ≪≫
    Functor.isoWhiskerRight (shiftFunctorOpIso C n (-n) n.add_right_neg).symm (shiftFunctor C n).op
  counitIso := Functor.isoWhiskerLeft _ (shiftFunctorOpIso C n (-n) n.ad

Depends on / 依赖: shiftFunctor
-/
def opShiftFunctorEquivalence (n : Int) : Cᵒᵖ ≌ Cᵒᵖ where
  functor := shiftFunctor Cᵒᵖ n
  inverse := (shiftFunctor C n).op
  unitIso := NatIso.op (shiftFunctorCompIsoId C (-n) n n.add_left_neg) ≪≫
    Functor.isoWhiskerRight (shiftFunctorOpIso C n (-n) n.add_right_neg).symm (shiftFunctor C n).op
  counitIso := Functor.isoWhiskerLeft _ (shiftFunctorOpIso C n (-n) n.add_right_neg) ≪≫
    NatIso.op (shiftFunctorCompIsoId C n (-n) n.add_right_neg).symm
  functor_unitIso_comp X := Quiver.Hom.unop_inj (by
    dsimp [shiftFunctorOpIso]
    erw [comp_id, Functor.map_id, comp_id]
    change (shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).inv.app (X.unop⟦-n⟧) ≫
      ((shiftFunctorCompIsoId C (-n) n (neg_add_cancel n)).hom.app X.unop)⟦-n⟧' = 𝟙 _
    rw [shift_shiftFunctorCompIsoId_neg_add_cancel_hom_app n X.unop]; rw [Iso.inv_hom_id_app])

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `opShiftFunctorEquivalence_unitIso_hom_app` / 引理 `opShiftFunctorEquivalence_unitIso_hom_app`

English:
lemma opShiftFunctorEquivalence_unitIso_hom_app
  given: (X : Cᵒᵖ) (n m : Int) (hnm : n + m = 0 := by lia)
  proof: by
  obtain rfl : m = -n := by lia
  rfl

#adaptation_note

中文:
引理 opShiftFunctorEquivalence_unitIso_hom_app
  条件: (X : Cᵒᵖ) (n m : 整数) (hnm : n + m = 0 := by lia)
  证明: by
  obtain rfl : m = -n := by lia
  rfl

#adaptation_note

Depends on / 依赖: X.unop, hom.app, inv.app, opShiftFunctorEquivalence, shiftFunctorCompIsoId, shiftFunctorOpIso, unitIso, unitIso.hom.app
-/
lemma opShiftFunctorEquivalence_unitIso_hom_app (X : Cᵒᵖ) (n m : Int) (hnm : n + m = 0 := by lia) :
    (opShiftFunctorEquivalence C n).unitIso.hom.app X =
      ((shiftFunctorCompIsoId C m n (by lia)).hom.app X.unop).op ≫
        (((shiftFunctorOpIso C n m hnm).inv.app (X)).unop⟦n⟧').op := by
  obtain rfl : m = -n := by lia
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `opShiftFunctorEquivalence_unitIso_inv_app` / 引理 `opShiftFunctorEquivalence_unitIso_inv_app`

English:
lemma opShiftFunctorEquivalence_unitIso_inv_app
  given: (X : Cᵒᵖ) (n m : Int) (hnm : n + m = 0 := by lia)
  proof: by
  obtain rfl : m = -n := by lia
  rfl

#adaptation_note

中文:
引理 opShiftFunctorEquivalence_unitIso_inv_app
  条件: (X : Cᵒᵖ) (n m : 整数) (hnm : n + m = 0 := by lia)
  证明: by
  obtain rfl : m = -n := by lia
  rfl

#adaptation_note

Depends on / 依赖: X.unop, hom.app, inv.app, opShiftFunctorEquivalence, shiftFunctorCompIsoId, shiftFunctorOpIso, unitIso, unitIso.inv.app
-/
lemma opShiftFunctorEquivalence_unitIso_inv_app (X : Cᵒᵖ) (n m : Int) (hnm : n + m = 0 := by lia) :
    (opShiftFunctorEquivalence C n).unitIso.inv.app X =
      (((shiftFunctorOpIso C n m hnm).hom.app (X)).unop⟦n⟧').op ≫
      ((shiftFunctorCompIsoId C m n (by lia)).inv.app X.unop).op := by
  obtain rfl : m = -n := by lia
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `opShiftFunctorEquivalence_counitIso_hom_app` / 引理 `opShiftFunctorEquivalence_counitIso_hom_app`

English:
lemma opShiftFunctorEquivalence_counitIso_hom_app
  given: (X : Cᵒᵖ) (n m : Int) (hnm : n + m = 0 := by lia)
  proof: by
  obtain rfl : m = -n := by lia
  rfl

#adaptation_note

中文:
引理 opShiftFunctorEquivalence_counitIso_hom_app
  条件: (X : Cᵒᵖ) (n m : 整数) (hnm : n + m = 0 := by lia)
  证明: by
  obtain rfl : m = -n := by lia
  rfl

#adaptation_note

Depends on / 依赖: Opposite, Opposite.op, X.unop, counitIso, counitIso.hom.app, hom.app, inv.app, opShiftFunctorEquivalence, shiftFunctorCompIsoId, shiftFunctorOpIso
-/
lemma opShiftFunctorEquivalence_counitIso_hom_app (X : Cᵒᵖ) (n m : Int) (hnm : n + m = 0 := by lia) :
    (opShiftFunctorEquivalence C n).counitIso.hom.app X =
      (shiftFunctorOpIso C n m hnm).hom.app (Opposite.op (X.unop⟦n⟧)) ≫
        ((shiftFunctorCompIsoId C n m hnm).inv.app X.unop).op
        := by
  obtain rfl : m = -n := by lia
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `opShiftFunctorEquivalence_counitIso_inv_app` / 引理 `opShiftFunctorEquivalence_counitIso_inv_app`

English:
lemma opShiftFunctorEquivalence_counitIso_inv_app
  given: (X : Cᵒᵖ) (n m : Int) (hnm : n + m = 0 := by lia)
  proof: by
  obtain rfl : m = -n := by lia
  rfl

中文:
引理 opShiftFunctorEquivalence_counitIso_inv_app
  条件: (X : Cᵒᵖ) (n m : 整数) (hnm : n + m = 0 := by lia)
  证明: by
  obtain rfl : m = -n := by lia
  rfl

Depends on / 依赖: Opposite, Opposite.op, X.unop, counitIso, counitIso.inv.app, hom.app, inv.app, opShiftFunctorEquivalence, shiftFunctorCompIsoId, shiftFunctorOpIso
-/
lemma opShiftFunctorEquivalence_counitIso_inv_app (X : Cᵒᵖ) (n m : Int) (hnm : n + m = 0 := by lia) :
    (opShiftFunctorEquivalence C n).counitIso.inv.app X =
      ((shiftFunctorCompIsoId C n m hnm).hom.app X.unop).op ≫
        (shiftFunctorOpIso C n m hnm).inv.app (Opposite.op (X.unop⟦n⟧)) := by
  obtain rfl : m = -n := by lia
  rfl

/-! The naturality of the unit and counit isomorphisms are restated in the following
lemmas so as to mitigate the need for `erw`. -/

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `opShiftFunctorEquivalence_unitIso_hom_naturality` / 引理 `opShiftFunctorEquivalence_unitIso_hom_naturality`

English:
lemma opShiftFunctorEquivalence_unitIso_hom_naturality
  given: (n : Int) {X Y : Cᵒᵖ} (f : X ⟶ Y)
  proof: (opShiftFunctorEquivalence C n).unitIso.hom.naturality f

#adaptation_note

中文:
引理 opShiftFunctorEquivalence_unitIso_hom_naturality
  条件: (n : 整数) {X Y : Cᵒᵖ} (f : X ⟶ Y)
  证明: (opShiftFunctorEquivalence C n).unitIso.hom.naturality f

#adaptation_note

Depends on / 依赖: naturality, opShiftFunctorEquivalence, unitIso, unitIso.hom.naturality
-/
lemma opShiftFunctorEquivalence_unitIso_hom_naturality (n : Int) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    f ≫ (opShiftFunctorEquivalence C n).unitIso.hom.app Y =
      (opShiftFunctorEquivalence C n).unitIso.hom.app X ≫ (f⟦n⟧').unop⟦n⟧'.op :=
  (opShiftFunctorEquivalence C n).unitIso.hom.naturality f

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `opShiftFunctorEquivalence_unitIso_inv_naturality` / 引理 `opShiftFunctorEquivalence_unitIso_inv_naturality`

English:
lemma opShiftFunctorEquivalence_unitIso_inv_naturality
  given: (n : Int) {X Y : Cᵒᵖ} (f : X ⟶ Y)
  proof: (opShiftFunctorEquivalence C n).unitIso.inv.naturality f

#adaptation_note

中文:
引理 opShiftFunctorEquivalence_unitIso_inv_naturality
  条件: (n : 整数) {X Y : Cᵒᵖ} (f : X ⟶ Y)
  证明: (opShiftFunctorEquivalence C n).unitIso.inv.naturality f

#adaptation_note

Depends on / 依赖: naturality, opShiftFunctorEquivalence, unitIso, unitIso.inv.naturality
-/
lemma opShiftFunctorEquivalence_unitIso_inv_naturality (n : Int) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (f⟦n⟧').unop⟦n⟧'.op ≫ (opShiftFunctorEquivalence C n).unitIso.inv.app Y =
      (opShiftFunctorEquivalence C n).unitIso.inv.app X ≫ f :=
  (opShiftFunctorEquivalence C n).unitIso.inv.naturality f

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `opShiftFunctorEquivalence_counitIso_hom_naturality` / 引理 `opShiftFunctorEquivalence_counitIso_hom_naturality`

English:
lemma opShiftFunctorEquivalence_counitIso_hom_naturality
  given: (n : Int) {X Y : Cᵒᵖ} (f : X ⟶ Y)
  proof: (opShiftFunctorEquivalence C n).counitIso.hom.naturality f

中文:
引理 opShiftFunctorEquivalence_counitIso_hom_naturality
  条件: (n : 整数) {X Y : Cᵒᵖ} (f : X ⟶ Y)
  证明: (opShiftFunctorEquivalence C n).counitIso.hom.naturality f

Depends on / 依赖: counitIso, counitIso.hom.naturality, naturality, opShiftFunctorEquivalence
-/
lemma opShiftFunctorEquivalence_counitIso_hom_naturality (n : Int) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    f.unop⟦n⟧'.op⟦n⟧' ≫ (opShiftFunctorEquivalence C n).counitIso.hom.app Y =
      (opShiftFunctorEquivalence C n).counitIso.hom.app X ≫ f :=
  (opShiftFunctorEquivalence C n).counitIso.hom.naturality f

set_option backward.isDefEq.respectTransparency false in -- This is needed in CategoryTheory/Triangulated/Opposite/Triangle.lean
@[reassoc (attr := simp)]
/--
lemma `opShiftFunctorEquivalence_counitIso_inv_naturality` / 引理 `opShiftFunctorEquivalence_counitIso_inv_naturality`

English:
lemma opShiftFunctorEquivalence_counitIso_inv_naturality
  given: (n : Int) {X Y : Cᵒᵖ} (f : X ⟶ Y)
  proof: (opShiftFunctorEquivalence C n).counitIso.inv.naturality f

中文:
引理 opShiftFunctorEquivalence_counitIso_inv_naturality
  条件: (n : 整数) {X Y : Cᵒᵖ} (f : X ⟶ Y)
  证明: (opShiftFunctorEquivalence C n).counitIso.inv.naturality f

Depends on / 依赖: counitIso, counitIso.inv.naturality, naturality, opShiftFunctorEquivalence
-/
lemma opShiftFunctorEquivalence_counitIso_inv_naturality (n : Int) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    f ≫ (opShiftFunctorEquivalence C n).counitIso.inv.app Y =
      (opShiftFunctorEquivalence C n).counitIso.inv.app X ≫ f.unop⟦n⟧'.op⟦n⟧' :=
  (opShiftFunctorEquivalence C n).counitIso.inv.naturality f

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `opShiftFunctorEquivalence_zero_unitIso_hom_app` / 引理 `opShiftFunctorEquivalence_zero_unitIso_hom_app`

English:
lemma opShiftFunctorEquivalence_zero_unitIso_hom_app
  given: (X : Cᵒᵖ)
  proof: by
  apply Quiver.Hom.unop_inj
  dsimp [opShiftFunctorEquivalence]
  rw [shiftFunctorZero_op_inv_app]; rw [unop_comp]; rw [Quiver.Hom.unop_op]; rw [Functor.map_comp]; rw [shiftFunctorCompIsoId_zero_zero_hom_app]; rw [assoc]

中文:
引理 opShiftFunctorEquivalence_zero_unitIso_hom_app
  条件: (X : Cᵒᵖ)
  证明: by
  apply Quiver.Hom.unop_inj
  dsimp [opShiftFunctorEquivalence]
  rw [shiftFunctorZero_op_inv_app]; rw [unop_comp]; rw [Quiver.Hom.unop_op]; rw [Functor.map_comp]; rw [shiftFunctorCompIsoId_zero_zero_hom_app]; rw [assoc]

Depends on / 依赖: Functor, Functor.map_comp, Quiver, Quiver.Hom.unop_inj, Quiver.Hom.unop_op, map_comp, opShiftFunctorEquivalence, shiftFunctorCompIsoId_zero_zero_hom_app, shiftFunctorZero_op_inv_app, unop_comp, unop_inj, unop_op
-/
lemma opShiftFunctorEquivalence_zero_unitIso_hom_app (X : Cᵒᵖ) :
    (opShiftFunctorEquivalence C 0).unitIso.hom.app X =
      ((shiftFunctorZero C Int).hom.app X.unop).op ≫
      (((shiftFunctorZero Cᵒᵖ Int).inv.app X).unop⟦(0 : Int)⟧').op := by
  apply Quiver.Hom.unop_inj
  dsimp [opShiftFunctorEquivalence]
  rw [shiftFunctorZero_op_inv_app]; rw [unop_comp]; rw [Quiver.Hom.unop_op]; rw [Functor.map_comp]; rw [shiftFunctorCompIsoId_zero_zero_hom_app]; rw [assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `opShiftFunctorEquivalence_zero_unitIso_inv_app` / 引理 `opShiftFunctorEquivalence_zero_unitIso_inv_app`

English:
lemma opShiftFunctorEquivalence_zero_unitIso_inv_app
  given: (X : Cᵒᵖ)
  proof: by
  apply Quiver.Hom.unop_inj
  dsimp [opShiftFunctorEquivalence]
  rw [shiftFunctorZero_op_hom_app]; rw [unop_comp]; rw [Quiver.Hom.unop_op]; rw [Functor.map_comp]; rw [shiftFunctorCompIsoId_zero_zero_inv_app]; rw [assoc]

中文:
引理 opShiftFunctorEquivalence_zero_unitIso_inv_app
  条件: (X : Cᵒᵖ)
  证明: by
  apply Quiver.Hom.unop_inj
  dsimp [opShiftFunctorEquivalence]
  rw [shiftFunctorZero_op_hom_app]; rw [unop_comp]; rw [Quiver.Hom.unop_op]; rw [Functor.map_comp]; rw [shiftFunctorCompIsoId_zero_zero_inv_app]; rw [assoc]

Depends on / 依赖: Functor, Functor.map_comp, Quiver, Quiver.Hom.unop_inj, Quiver.Hom.unop_op, map_comp, opShiftFunctorEquivalence, shiftFunctorCompIsoId_zero_zero_inv_app, shiftFunctorZero_op_hom_app, unop_comp, unop_inj, unop_op
-/
lemma opShiftFunctorEquivalence_zero_unitIso_inv_app (X : Cᵒᵖ) :
    (opShiftFunctorEquivalence C 0).unitIso.inv.app X =
      (((shiftFunctorZero Cᵒᵖ Int).hom.app X).unop⟦(0 : Int)⟧').op ≫
        ((shiftFunctorZero C Int).inv.app X.unop).op := by
  apply Quiver.Hom.unop_inj
  dsimp [opShiftFunctorEquivalence]
  rw [shiftFunctorZero_op_hom_app]; rw [unop_comp]; rw [Quiver.Hom.unop_op]; rw [Functor.map_comp]; rw [shiftFunctorCompIsoId_zero_zero_inv_app]; rw [assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `opShiftFunctorEquivalence_add_unitIso_hom_app_eq` / 引理 `opShiftFunctorEquivalence_add_unitIso_hom_app_eq`

English:
lemma opShiftFunctorEquivalence_add_unitIso_hom_app_eq
  proof: by
  dsimp [opShiftFunctorEquivalence]
  simp only [shiftFunctorAdd'_op_inv_app _ n m p (by lia) _ _ _ (add_neg_cancel n)
    (add_neg_cancel m) (add_neg_cancel p), shiftFunctor_op_map _ m (-m),
    Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [Functor.map_id, Functor.map_id, Functor.map_id, Func

中文:
引理 opShiftFunctorEquivalence_add_unitIso_hom_app_eq
  证明: by
  dsimp [opShiftFunctorEquivalence]
  simp only [shiftFunctorAdd'_op_inv_app _ n m p (by lia) _ _ _ (add_neg_cancel n)
    (add_neg_cancel m) (add_neg_cancel p), shiftFunctor_op_map _ m (-m),
    Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [Functor.map_id, Functor.map_id, Functor.map_id, Func

Depends on / 依赖: Category, Category.asso, _op_inv_app, add_neg_cancel, hom.app, inv.app, opShiftFunctorEquivalence, shiftFunctorAdd, shiftFunctor_op_map, unitIso, unitIso.hom.app
-/
lemma opShiftFunctorEquivalence_add_unitIso_hom_app_eq
    (X : Cᵒᵖ) (m n p : Int) (h : m + n = p := by lia) :
    (opShiftFunctorEquivalence C p).unitIso.hom.app X =
      (opShiftFunctorEquivalence C n).unitIso.hom.app X ≫
      (((opShiftFunctorEquivalence C m).unitIso.hom.app (X⟦n⟧)).unop⟦n⟧').op ≫
      ((shiftFunctorAdd' C m n p h).hom.app _).op ≫
      (((shiftFunctorAdd' Cᵒᵖ n m p (by lia)).inv.app X).unop⟦p⟧').op := by
  dsimp [opShiftFunctorEquivalence]
  simp only [shiftFunctorAdd'_op_inv_app _ n m p (by lia) _ _ _ (add_neg_cancel n)
    (add_neg_cancel m) (add_neg_cancel p), shiftFunctor_op_map _ m (-m),
    Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [Functor.map_id, Functor.map_id, Functor.map_id, Functor.map_id,
    id_comp, id_comp, id_comp, comp_id, comp_id]
  dsimp
  rw [comp_id]; rw [shiftFunctorCompIsoId_add'_hom_app _ _ _ _ _ _
    (neg_add_cancel m) (neg_add_cancel n) (neg_add_cancel p) h]
  dsimp
  rw [Category.assoc]; rw [Category.assoc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `opShiftFunctorEquivalence_add_unitIso_inv_app_eq` / 引理 `opShiftFunctorEquivalence_add_unitIso_inv_app_eq`

English:
lemma opShiftFunctorEquivalence_add_unitIso_inv_app_eq
  proof: by
  rw [← cancel_mono ((opShiftFunctorEquivalence C p).unitIso.hom.app X)]; rw [Iso.inv_hom_id_app]; rw [opShiftFunctorEquivalence_add_unitIso_hom_app_eq _ _ _ _ h]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.inv_hom_id_app_assoc]
  apply Quiver.Hom.unop_inj
  dsimp
  si

中文:
引理 opShiftFunctorEquivalence_add_unitIso_inv_app_eq
  证明: by
  rw [← cancel_mono ((opShiftFunctorEquivalence C p).unitIso.hom.app X)]; rw [Iso.inv_hom_id_app]; rw [opShiftFunctorEquivalence_add_unitIso_hom_app_eq _ _ _ _ h]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.inv_hom_id_app_assoc]
  apply Quiver.Hom.unop_inj
  dsimp
  si

Depends on / 依赖: Category, Category.a, Category.assoc, Iso.inv_hom_id_app, cancel_mono, hom.app, inv.app, inv_hom_id_app, opShiftFunctorEquivalence, opShiftFunctorEquivalence_add_unitIso_hom_app_eq, shiftFunctorAdd, unitIso, unitIso.hom.app, unitIso.inv.app
-/
lemma opShiftFunctorEquivalence_add_unitIso_inv_app_eq
    (X : Cᵒᵖ) (m n p : Int) (h : m + n = p := by lia) :
    (opShiftFunctorEquivalence C p).unitIso.inv.app X =
      (((shiftFunctorAdd' Cᵒᵖ n m p (by lia)).hom.app X).unop⟦p⟧').op ≫
      ((shiftFunctorAdd' C m n p h).inv.app _).op ≫
      (((opShiftFunctorEquivalence C m).unitIso.inv.app (X⟦n⟧)).unop⟦n⟧').op ≫
      (opShiftFunctorEquivalence C n).unitIso.inv.app X := by
  rw [← cancel_mono ((opShiftFunctorEquivalence C p).unitIso.hom.app X)]; rw [Iso.inv_hom_id_app]; rw [opShiftFunctorEquivalence_add_unitIso_hom_app_eq _ _ _ _ h]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.inv_hom_id_app_assoc]
  apply Quiver.Hom.unop_inj
  dsimp
  simp only [Category.assoc,
    ← unop_comp, Iso.inv_hom_id_app, Functor.comp_obj, Functor.op_obj, unop_id,
    Functor.map_id, id_comp, ← Functor.map_comp, Iso.hom_inv_id_app]

/--
lemma `shift_unop_opShiftFunctorEquivalence_counitIso_inv_app` / 引理 `shift_unop_opShiftFunctorEquivalence_counitIso_inv_app`

English:
lemma shift_unop_opShiftFunctorEquivalence_counitIso_inv_app
  given: (X : Cᵒᵖ) (n : Int)
  proof: Quiver.Hom.op_inj ((opShiftFunctorEquivalence C n).unit_app_inverse X).symm

中文:
引理 shift_unop_opShiftFunctorEquivalence_counitIso_inv_app
  条件: (X : Cᵒᵖ) (n : 整数)
  证明: Quiver.Hom.op_inj ((opShiftFunctorEquivalence C n).unit_app_inverse X).symm

Depends on / 依赖: Quiver, Quiver.Hom.op_inj, opShiftFunctorEquivalence, op_inj, unit_app_inverse
-/
lemma shift_unop_opShiftFunctorEquivalence_counitIso_inv_app (X : Cᵒᵖ) (n : Int) :
    ((opShiftFunctorEquivalence C n).counitIso.inv.app X).unop⟦n⟧' =
      ((opShiftFunctorEquivalence C n).unitIso.hom.app ((Opposite.op ((X.unop)⟦n⟧)))).unop :=
  Quiver.Hom.op_inj ((opShiftFunctorEquivalence C n).unit_app_inverse X).symm

/--
lemma `shift_unop_opShiftFunctorEquivalence_counitIso_hom_app` / 引理 `shift_unop_opShiftFunctorEquivalence_counitIso_hom_app`

English:
lemma shift_unop_opShiftFunctorEquivalence_counitIso_hom_app
  given: (X : Cᵒᵖ) (n : Int)
  proof: Quiver.Hom.op_inj ((opShiftFunctorEquivalence C n).unitInv_app_inverse X).symm

中文:
引理 shift_unop_opShiftFunctorEquivalence_counitIso_hom_app
  条件: (X : Cᵒᵖ) (n : 整数)
  证明: Quiver.Hom.op_inj ((opShiftFunctorEquivalence C n).unitInv_app_inverse X).symm

Depends on / 依赖: Quiver, Quiver.Hom.op_inj, opShiftFunctorEquivalence, op_inj, unitInv_app_inverse
-/
lemma shift_unop_opShiftFunctorEquivalence_counitIso_hom_app (X : Cᵒᵖ) (n : Int) :
    ((opShiftFunctorEquivalence C n).counitIso.hom.app X).unop⟦n⟧' =
      ((opShiftFunctorEquivalence C n).unitIso.inv.app ((Opposite.op (X.unop⟦n⟧)))).unop :=
  Quiver.Hom.op_inj ((opShiftFunctorEquivalence C n).unitInv_app_inverse X).symm

/--
lemma `opShiftFunctorEquivalence_counitIso_inv_app_shift` / 引理 `opShiftFunctorEquivalence_counitIso_inv_app_shift`

English:
lemma opShiftFunctorEquivalence_counitIso_inv_app_shift
  given: (X : Cᵒᵖ) (n : Int)
  proof: (opShiftFunctorEquivalence C n).counitInv_app_functor X

中文:
引理 opShiftFunctorEquivalence_counitIso_inv_app_shift
  条件: (X : Cᵒᵖ) (n : 整数)
  证明: (opShiftFunctorEquivalence C n).counitInv_app_functor X

Depends on / 依赖: counitInv_app_functor, opShiftFunctorEquivalence
-/
lemma opShiftFunctorEquivalence_counitIso_inv_app_shift (X : Cᵒᵖ) (n : Int) :
    (opShiftFunctorEquivalence C n).counitIso.inv.app (X⟦n⟧) =
      ((opShiftFunctorEquivalence C n).unitIso.hom.app X)⟦n⟧' :=
  (opShiftFunctorEquivalence C n).counitInv_app_functor X

/--
lemma `opShiftFunctorEquivalence_counitIso_hom_app_shift` / 引理 `opShiftFunctorEquivalence_counitIso_hom_app_shift`

English:
lemma opShiftFunctorEquivalence_counitIso_hom_app_shift
  given: (X : Cᵒᵖ) (n : Int)
  proof: (opShiftFunctorEquivalence C n).counit_app_functor X

中文:
引理 opShiftFunctorEquivalence_counitIso_hom_app_shift
  条件: (X : Cᵒᵖ) (n : 整数)
  证明: (opShiftFunctorEquivalence C n).counit_app_functor X

Depends on / 依赖: counit_app_functor, opShiftFunctorEquivalence
-/
lemma opShiftFunctorEquivalence_counitIso_hom_app_shift (X : Cᵒᵖ) (n : Int) :
    (opShiftFunctorEquivalence C n).counitIso.hom.app (X⟦n⟧) =
      ((opShiftFunctorEquivalence C n).unitIso.inv.app X)⟦n⟧' :=
  (opShiftFunctorEquivalence C n).counit_app_functor X

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `shiftFunctorCompIsoId_op_hom_app` / 引理 `shiftFunctorCompIsoId_op_hom_app`

English:
lemma shiftFunctorCompIsoId_op_hom_app
  given: (X : Cᵒᵖ) (n m : Int) (hnm : n + m = 0 := by lia)
  proof: by
  simp [shiftFunctorCompIsoId, shiftFunctorZero_op_hom_app X,
    shiftFunctorAdd'_op_inv_app X n m 0 hnm m n 0 hnm (by lia) (add_zero 0)]

中文:
引理 shiftFunctorCompIsoId_op_hom_app
  条件: (X : Cᵒᵖ) (n m : 整数) (hnm : n + m = 0 := by lia)
  证明: by
  simp [shiftFunctorCompIsoId, shiftFunctorZero_op_hom_app X,
    shiftFunctorAdd'_op_inv_app X n m 0 hnm m n 0 hnm (by lia) (add_zero 0)]

Depends on / 依赖: Opposite, Opposite.op, X.unop, _op_inv_app, add_zero, hom.app, inv.app, shiftFunctorAdd, shiftFunctorCompIsoId, shiftFunctorOpIso, shiftFunctorZero_op_hom_app
-/
lemma shiftFunctorCompIsoId_op_hom_app (X : Cᵒᵖ) (n m : Int) (hnm : n + m = 0 := by lia) :
    (shiftFunctorCompIsoId Cᵒᵖ n m hnm).hom.app X =
      ((shiftFunctorOpIso C n m hnm).hom.app X)⟦m⟧' ≫
        (shiftFunctorOpIso C m n (by lia)).hom.app (Opposite.op (X.unop⟦m⟧)) ≫
          ((shiftFunctorCompIsoId C m n (by lia)).inv.app X.unop).op := by
  simp [shiftFunctorCompIsoId, shiftFunctorZero_op_hom_app X,
    shiftFunctorAdd'_op_inv_app X n m 0 hnm m n 0 hnm (by lia) (add_zero 0)]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `shiftFunctorCompIsoId_op_inv_app` / 引理 `shiftFunctorCompIsoId_op_inv_app`

English:
lemma shiftFunctorCompIsoId_op_inv_app
  given: (X : Cᵒᵖ) (n m : Int) (hnm : n + m = 0 := by lia)
  proof: by
  simp [shiftFunctorCompIsoId, shiftFunctorZero_op_inv_app X,
    shiftFunctorAdd'_op_hom_app X n m 0 hnm m n 0 hnm (by lia) (add_zero 0)]

中文:
引理 shiftFunctorCompIsoId_op_inv_app
  条件: (X : Cᵒᵖ) (n m : 整数) (hnm : n + m = 0 := by lia)
  证明: by
  simp [shiftFunctorCompIsoId, shiftFunctorZero_op_inv_app X,
    shiftFunctorAdd'_op_hom_app X n m 0 hnm m n 0 hnm (by lia) (add_zero 0)]

Depends on / 依赖: Opposite, Opposite.op, X.unop, _op_hom_app, add_zero, hom.app, inv.app, shiftFunctorAdd, shiftFunctorCompIsoId, shiftFunctorOpIso, shiftFunctorZero_op_inv_app
-/
lemma shiftFunctorCompIsoId_op_inv_app (X : Cᵒᵖ) (n m : Int) (hnm : n + m = 0 := by lia) :
    (shiftFunctorCompIsoId Cᵒᵖ n m hnm).inv.app X =
      ((shiftFunctorCompIsoId C m n (by omega)).hom.app X.unop).op ≫
        (shiftFunctorOpIso C m n (by omega)).inv.app (Opposite.op (X.unop⟦m⟧)) ≫
          ((shiftFunctorOpIso C n m hnm).inv.app X)⟦m⟧' := by
  simp [shiftFunctorCompIsoId, shiftFunctorZero_op_inv_app X,
    shiftFunctorAdd'_op_hom_app X n m 0 hnm m n 0 hnm (by lia) (add_zero 0)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `shift_opShiftFunctorEquivalence_counitIso_inv_app` / 引理 `shift_opShiftFunctorEquivalence_counitIso_inv_app`

English:
lemma shift_opShiftFunctorEquivalence_counitIso_inv_app
  proof: by
  obtain rfl : m = -n := by lia
  dsimp [opShiftFunctorEquivalence]
  simp only [shiftFunctor_op_map _ (-n) n, shiftFunctor_op_map _ n (-n),
    shiftFunctorComm_inv_app_of_add_eq_zero n (-n) (by lia), assoc,
    shiftFunctorCompIsoId_op_inv_app, shiftFunctorCompIsoId_op_hom_app,
    shift_shiftF

中文:
引理 shift_opShiftFunctorEquivalence_counitIso_inv_app
  证明: by
  obtain rfl : m = -n := by lia
  dsimp [opShiftFunctorEquivalence]
  simp only [shiftFunctor_op_map _ (-n) n, shiftFunctor_op_map _ n (-n),
    shiftFunctorComm_inv_app_of_add_eq_zero n (-n) (by lia), assoc,
    shiftFunctorCompIsoId_op_inv_app, shiftFunctorCompIsoId_op_hom_app,
    shift_shiftF

Depends on / 依赖: Opposite, Opposite.op, counitIso, counitIso.inv.app, hom.app, inv.app, opShiftFunctorEquivalence, shiftFunctorComm, shiftFunctorOpIso, shiftFunctor_op_map
-/
lemma shift_opShiftFunctorEquivalence_counitIso_inv_app
    (X : C) (m n : Int) (hmn : m + n = 0 := by lia) :
    ((opShiftFunctorEquivalence C n).counitIso.inv.app (Opposite.op X))⟦m⟧' =
      (opShiftFunctorEquivalence C n).counitIso.inv.app ((Opposite.op X)⟦m⟧) ≫
        (((shiftFunctorOpIso C m n hmn).hom.app (Opposite.op X)).unop⟦n⟧').op⟦n⟧' ≫
          ((shiftFunctorOpIso C m n hmn).inv.app (Opposite.op (X⟦n⟧)))⟦n⟧' ≫
            (shiftFunctorComm Cᵒᵖ n m).inv.app (Opposite.op (X⟦n⟧)) := by
  obtain rfl : m = -n := by lia
  dsimp [opShiftFunctorEquivalence]
  simp only [shiftFunctor_op_map _ (-n) n, shiftFunctor_op_map _ n (-n),
    shiftFunctorComm_inv_app_of_add_eq_zero n (-n) (by lia), assoc,
    shiftFunctorCompIsoId_op_inv_app, shiftFunctorCompIsoId_op_hom_app,
    shift_shiftFunctorCompIsoId_hom_app, op_comp, unop_comp, Quiver.Hom.unop_op,
    Functor.map_comp, Iso.inv_hom_id_app_assoc, Functor.op_obj]
  apply Quiver.Hom.unop_inj
  simp

/--
Definition of `opShiftFunctorEquivalenceSymmHomEquiv` / `opShiftFunctorEquivalenceSymmHomEquiv` 的定义

English:
definition opShiftFunctorEquivalenceSymmHomEquiv
  signature: {n : Int} {X Y : Cᵒᵖ}
  body: (opShiftFunctorEquivalence C n).symm.toAdjunction.homEquiv X Y

@[reassoc]

中文:
定义 opShiftFunctorEquivalenceSymmHomEquiv
  签名: {n : 整数} {X Y : Cᵒᵖ}
  定义体: (opShiftFunctorEquivalence C n).symm.toAdjunction.homEquiv X Y

@[reassoc]

Depends on / 依赖: homEquiv, opShiftFunctorEquivalence, symm.toAdjunction.homEquiv, toAdjunction
-/
def opShiftFunctorEquivalenceSymmHomEquiv {n : Int} {X Y : Cᵒᵖ} :
    (Opposite.op (X.unop⟦n⟧) ⟶ Y) ≃ (X ⟶ Y⟦n⟧) :=
  (opShiftFunctorEquivalence C n).symm.toAdjunction.homEquiv X Y

@[reassoc]
/--
lemma `opShiftFunctorEquivalenceSymmHomEquiv_apply` / 引理 `opShiftFunctorEquivalenceSymmHomEquiv_apply`

English:
lemma opShiftFunctorEquivalenceSymmHomEquiv_apply
  statement: {n : Int} {X Y : Cᵒᵖ}
  proof: rfl

@[reassoc]

中文:
引理 opShiftFunctorEquivalenceSymmHomEquiv_apply
  结论: {n : 整数} {X Y : Cᵒᵖ}
  证明: rfl

@[reassoc]
-/
lemma opShiftFunctorEquivalenceSymmHomEquiv_apply {n : Int} {X Y : Cᵒᵖ}
    (f : Opposite.op (X.unop⟦n⟧) ⟶ Y) :
    opShiftFunctorEquivalenceSymmHomEquiv f =
      (opShiftFunctorEquivalence C n).counitIso.inv.app X ≫ (shiftFunctor Cᵒᵖ n).map f := rfl

@[reassoc]
/--
lemma `opShiftFunctorEquivalenceSymmHomEquiv_left_inv` / 引理 `opShiftFunctorEquivalenceSymmHomEquiv_left_inv`

English:
lemma opShiftFunctorEquivalenceSymmHomEquiv_left_inv
  proof: Quiver.Hom.op_inj (opShiftFunctorEquivalenceSymmHomEquiv.left_inv f)

中文:
引理 opShiftFunctorEquivalenceSymmHomEquiv_left_inv
  证明: Quiver.Hom.op_inj (opShiftFunctorEquivalenceSymmHomEquiv.left_inv f)

Depends on / 依赖: Quiver, Quiver.Hom.op_inj, left_inv, opShiftFunctorEquivalenceSymmHomEquiv, opShiftFunctorEquivalenceSymmHomEquiv.left_inv, op_inj
-/
lemma opShiftFunctorEquivalenceSymmHomEquiv_left_inv
    {n : Int} {X Y : Cᵒᵖ} (f : Opposite.op (X.unop⟦n⟧) ⟶ Y) :
    ((opShiftFunctorEquivalence C n).unitIso.inv.app Y).unop ≫
      (opShiftFunctorEquivalenceSymmHomEquiv f).unop⟦n⟧' = f.unop :=
  Quiver.Hom.op_inj (opShiftFunctorEquivalenceSymmHomEquiv.left_inv f)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `shift_opShiftFunctorEquivalenceSymmHomEquiv_unop` / 引理 `shift_opShiftFunctorEquivalenceSymmHomEquiv_unop`

English:
lemma shift_opShiftFunctorEquivalenceSymmHomEquiv_unop
  proof: by
  rw [← opShiftFunctorEquivalenceSymmHomEquiv_left_inv]
  simp

中文:
引理 shift_opShiftFunctorEquivalenceSymmHomEquiv_unop
  证明: by
  rw [← opShiftFunctorEquivalenceSymmHomEquiv_left_inv]
  simp

Depends on / 依赖: opShiftFunctorEquivalenceSymmHomEquiv_left_inv
-/
lemma shift_opShiftFunctorEquivalenceSymmHomEquiv_unop
    {n : Int} {X Y : Cᵒᵖ} (f : Opposite.op (X.unop⟦n⟧) ⟶ Y) :
    (opShiftFunctorEquivalenceSymmHomEquiv f).unop⟦n⟧' =
      ((opShiftFunctorEquivalence C n).unitIso.hom.app Y).unop ≫ f.unop := by
  rw [← opShiftFunctorEquivalenceSymmHomEquiv_left_inv]
  simp

end Pretriangulated

end CategoryTheory
