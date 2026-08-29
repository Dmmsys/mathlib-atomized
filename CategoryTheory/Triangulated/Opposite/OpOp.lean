/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# The triangulated equivalence `Cᵒᵖᵒᵖ ≌ C`.

In this file, we show that if `C` is a pretriangulated category, then
the functors `opOp C : C ⥤ Cᵒᵖᵒᵖ` and `unopUnop C : Cᵒᵖᵒᵖ ⥤ C` are triangulated.
We also show that the unit and counit isomorphisms of the equivalence
`opOpEquivalence C : Cᵒᵖᵒᵖ ≌ C` are compatible with shifts, which is summarized
by the property `(opOpEquivalence C).IsTriangulated`.

-/

@[expose] public section

namespace CategoryTheory

open Opposite Pretriangulated.Opposite Limits

variable (C : Type*) [Category* C] [HasShift C Int]

namespace Pretriangulated

namespace Opposite

namespace OpOpCommShift

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `iso` / `iso` 的定义

English:
definition iso
  signature: (n : Int)
  body: NatIso.ofComponents
    (fun X => ((shiftFunctorOpIso C (-n) n (neg_add_cancel n)).app (op X)).op ≪≫
      (shiftFunctorOpIso Cᵒᵖ n (-n) (add_neg_cancel n)).symm.app (op (op X)))
    (fun f => Quiver.Hom.unop_inj (by
      simp [shiftFunctor_op_map _ n (-n), shiftFunctor_op_map _ (-n) n]))

中文:
定义 iso
  签名: (n : 整数)
  定义体: NatIso.ofComponents
    (fun X => ((shiftFunctorOpIso C (-n) n (neg_add_cancel n)).app (op X)).op ≪≫
      (shiftFunctorOpIso Cᵒᵖ n (-n) (add_neg_cancel n)).symm.app (op (op X)))
    (fun f => Quiver.Hom.unop_inj (by
      simp [shiftFunctor_op_map _ n (-n), shiftFunctor_op_map _ (-n) n]))

Depends on / 依赖: NatIso, NatIso.ofComponents, Quiver, Quiver.Hom.unop_inj, add_neg_cancel, neg_add_cancel, ofComponents, shiftFunctorOpIso, shiftFunctor_op_map, symm.app, unop_inj
-/
def iso (n : Int) :
    shiftFunctor C n ⋙ opOp C ≅ opOp C ⋙ shiftFunctor Cᵒᵖᵒᵖ n :=
  NatIso.ofComponents
    (fun X => ((shiftFunctorOpIso C (-n) n (neg_add_cancel n)).app (op X)).op ≪≫
      (shiftFunctorOpIso Cᵒᵖ n (-n) (add_neg_cancel n)).symm.app (op (op X)))
    (fun f => Quiver.Hom.unop_inj (by
      simp [shiftFunctor_op_map _ n (-n), shiftFunctor_op_map _ (-n) n]))

variable {C}

@[reassoc]
/--
lemma `iso_hom_app` / 引理 `iso_hom_app`

English:
lemma iso_hom_app
  given: (X : C) (n m : Int) (hnm : n + m = 0 := by lia)
  proof: by
  obtain rfl : m = -n := by lia
  rfl

@[reassoc]

中文:
引理 iso_hom_app
  条件: (X : C) (n m : 整数) (hnm : n + m = 0 := by lia)
  证明: by
  obtain rfl : m = -n := by lia
  rfl

@[reassoc]

Depends on / 依赖: hom.app, inv.app, shiftFunctorOpIso
-/
lemma iso_hom_app (X : C) (n m : Int) (hnm : n + m = 0 := by lia) :
    (iso C n).hom.app X =
      ((shiftFunctorOpIso C m n (by lia)).hom.app (op X)).op ≫
        (shiftFunctorOpIso Cᵒᵖ _ _ hnm).inv.app (op (op X)) := by
  obtain rfl : m = -n := by lia
  rfl

@[reassoc]
/--
lemma `iso_inv_app` / 引理 `iso_inv_app`

English:
lemma iso_inv_app
  given: (X : C) (n m : Int) (hnm : n + m = 0 := by lia)
  proof: by
  obtain rfl : m = -n := by lia
  rfl

中文:
引理 iso_inv_app
  条件: (X : C) (n m : 整数) (hnm : n + m = 0 := by lia)
  证明: by
  obtain rfl : m = -n := by lia
  rfl

Depends on / 依赖: hom.app, inv.app, shiftFunctorOpIso
-/
lemma iso_inv_app (X : C) (n m : Int) (hnm : n + m = 0 := by lia) :
    (iso C n).inv.app X =
      (shiftFunctorOpIso Cᵒᵖ _ _ hnm).hom.app (op (op X)) ≫
        ((shiftFunctorOpIso C m n (by lia)).inv.app (op X)).op := by
  obtain rfl : m = -n := by lia
  rfl

end OpOpCommShift

namespace UnopUnopCommShift

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `iso` / `iso` 的定义

English:
definition iso
  signature: (n : Int)
  body: NatIso.ofComponents
    (fun X => ((shiftFunctorOpIso Cᵒᵖ n (-n) (add_neg_cancel n)).app X).unop.unop ≪≫
      ((shiftFunctorOpIso C (-n) n (neg_add_cancel n)).symm.app X.unop).unop)
    (fun {X Y} f => Quiver.Hom.op_inj (by
      simp [shiftFunctor_op_map _ n (-n), shiftFunctor_op_map _ (-n) n]))

中文:
定义 iso
  签名: (n : 整数)
  定义体: NatIso.ofComponents
    (fun X => ((shiftFunctorOpIso Cᵒᵖ n (-n) (add_neg_cancel n)).app X).unop.unop ≪≫
      ((shiftFunctorOpIso C (-n) n (neg_add_cancel n)).symm.app X.unop).unop)
    (fun {X Y} f => Quiver.Hom.op_inj (by
      simp [shiftFunctor_op_map _ n (-n), shiftFunctor_op_map _ (-n) n]))

Depends on / 依赖: NatIso, NatIso.ofComponents, Quiver, Quiver.Hom.op_inj, X.unop, add_neg_cancel, neg_add_cancel, ofComponents, op_inj, shiftFunctorOpIso, shiftFunctor_op_map, symm.app, unop.unop
-/
def iso (n : Int) :
    shiftFunctor Cᵒᵖᵒᵖ n ⋙ unopUnop C ≅ unopUnop C ⋙ shiftFunctor C n :=
  NatIso.ofComponents
    (fun X => ((shiftFunctorOpIso Cᵒᵖ n (-n) (add_neg_cancel n)).app X).unop.unop ≪≫
      ((shiftFunctorOpIso C (-n) n (neg_add_cancel n)).symm.app X.unop).unop)
    (fun {X Y} f => Quiver.Hom.op_inj (by
      simp [shiftFunctor_op_map _ n (-n), shiftFunctor_op_map _ (-n) n]))

variable {C}

@[reassoc]
/--
lemma `iso_hom_app` / 引理 `iso_hom_app`

English:
lemma iso_hom_app
  given: (X : Cᵒᵖᵒᵖ) (n m : Int) (hnm : n + m = 0 := by lia)
  proof: by
  obtain rfl : m = -n := by lia
  rfl

@[reassoc]

中文:
引理 iso_hom_app
  条件: (X : Cᵒᵖᵒᵖ) (n m : 整数) (hnm : n + m = 0 := by lia)
  证明: by
  obtain rfl : m = -n := by lia
  rfl

@[reassoc]

Depends on / 依赖: X.unop, hom.app, inv.app, shiftFunctorOpIso, unop.unop
-/
lemma iso_hom_app (X : Cᵒᵖᵒᵖ) (n m : Int) (hnm : n + m = 0 := by lia) :
    (iso C n).hom.app X =
      ((shiftFunctorOpIso Cᵒᵖ n m hnm).hom.app X).unop.unop ≫
        ((shiftFunctorOpIso C m n (by lia)).inv.app X.unop).unop := by
  obtain rfl : m = -n := by lia
  rfl

@[reassoc]
/--
lemma `iso_inv_app` / 引理 `iso_inv_app`

English:
lemma iso_inv_app
  given: (X : Cᵒᵖᵒᵖ) (n m : Int) (hnm : n + m = 0 := by lia)
  proof: by
  obtain rfl : m = -n := by lia
  rfl

中文:
引理 iso_inv_app
  条件: (X : Cᵒᵖᵒᵖ) (n m : 整数) (hnm : n + m = 0 := by lia)
  证明: by
  obtain rfl : m = -n := by lia
  rfl

Depends on / 依赖: X.unop, hom.app, inv.app, shiftFunctorOpIso, unop.unop
-/
lemma iso_inv_app (X : Cᵒᵖᵒᵖ) (n m : Int) (hnm : n + m = 0 := by lia) :
    (iso C n).inv.app X =
      ((shiftFunctorOpIso C m n (by lia)).hom.app X.unop).unop ≫
        ((shiftFunctorOpIso Cᵒᵖ n m hnm).inv.app X).unop.unop := by
  obtain rfl : m = -n := by lia
  rfl

end UnopUnopCommShift

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open OpOpCommShift in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (opOp C).CommShift Int
  body: iso _
  commShiftIso_zero := by
    ext X
    refine Quiver.Hom.unop_inj (Quiver.Hom.unop_inj ?_)
    simp [iso_hom_app X 0 0, shiftFunctorZero_op_inv_app,
      shiftFunctorZero_op_hom_app]
  commShiftIso_add p q := by
    ext X
    refine Quiver.Hom.unop_inj (Quiver.Hom.unop_inj ?_)
    simp [← sh

中文:
实例 :
  签名: (opOp C).CommShift 整数
  定义体: iso _
  commShiftIso_zero := by
    ext X
    refine Quiver.Hom.unop_inj (Quiver.Hom.unop_inj ?_)
    simp [iso_hom_app X 0 0, shiftFunctorZero_op_inv_app,
      shiftFunctorZero_op_hom_app]
  commShiftIso_add p q := by
    ext X
    refine Quiver.Hom.unop_inj (Quiver.Hom.unop_inj ?_)
    simp [← sh
-/
instance : (opOp C).CommShift Int where
  commShiftIso := iso _
  commShiftIso_zero := by
    ext X
    refine Quiver.Hom.unop_inj (Quiver.Hom.unop_inj ?_)
    simp [iso_hom_app X 0 0, shiftFunctorZero_op_inv_app,
      shiftFunctorZero_op_hom_app]
  commShiftIso_add p q := by
    ext X
    refine Quiver.Hom.unop_inj (Quiver.Hom.unop_inj ?_)
    simp [← shiftFunctorAdd'_eq_shiftFunctorAdd, ← unop_comp_assoc, ← Functor.map_comp,
      fun X n => iso_hom_app X n (-n) (add_neg_cancel n),
      shiftFunctor_op_map _ q (-q),
      shiftFunctorAdd'_op_inv_app _ p q (p + q) rfl (-p) (-q) (-(p + q))
        (add_neg_cancel p) (add_neg_cancel q) (add_neg_cancel (p + q)),
      shiftFunctorAdd'_op_hom_app _ (-p) (-q) (-(p + q)) (by lia) p q (p + q)
        (neg_add_cancel p) (neg_add_cancel q) (neg_add_cancel (p + q))]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open UnopUnopCommShift in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (unopUnop C).CommShift Int
  body: iso _
  commShiftIso_zero := by
    ext X
    simp [iso_hom_app _ 0 0, shiftFunctorZero_op_inv_app,
      shiftFunctorZero_op_hom_app]
  commShiftIso_add p q := by
    ext X
    simp only [Functor.CommShift.isoAdd_hom_app, op_comp,
      ← shiftFunctorAdd'_eq_shiftFunctorAdd, Functor.map_comp,
     

中文:
实例 :
  签名: (unopUnop C).CommShift 整数
  定义体: iso _
  commShiftIso_zero := by
    ext X
    simp [iso_hom_app _ 0 0, shiftFunctorZero_op_inv_app,
      shiftFunctorZero_op_hom_app]
  commShiftIso_add p q := by
    ext X
    simp only [Functor.CommShift.isoAdd_hom_app, op_comp,
      ← shiftFunctorAdd'_eq_shiftFunctorAdd, Functor.map_comp,
     
-/
instance : (unopUnop C).CommShift Int where
  commShiftIso := iso _
  commShiftIso_zero := by
    ext X
    simp [iso_hom_app _ 0 0, shiftFunctorZero_op_inv_app,
      shiftFunctorZero_op_hom_app]
  commShiftIso_add p q := by
    ext X
    simp only [Functor.CommShift.isoAdd_hom_app, op_comp,
      ← shiftFunctorAdd'_eq_shiftFunctorAdd, Functor.map_comp,
      fun X n => iso_hom_app X n (-n) (add_neg_cancel n),
      shiftFunctorAdd'_op_hom_app _ p q (p + q) rfl (-p) (-q) (-(p + q))
        (add_neg_cancel p) (add_neg_cancel q) (add_neg_cancel (p + q)),
      shiftFunctorAdd'_op_inv_app _ (-p) (-q) (-(p + q)) (by lia) p q (p + q)
        (neg_add_cancel p) (neg_add_cancel q) (neg_add_cancel (p + q)),
      shiftFunctor_op_map _ (-q) q, shiftFunctor_op_map _ q (-q)]
    simp [← Functor.map_comp_assoc, ← unop_comp, ← unop_comp_assoc]

end Opposite

variable {C}

@[reassoc]
/--
lemma `commShiftIso_opOp_hom_app` / 引理 `commShiftIso_opOp_hom_app`

English:
lemma commShiftIso_opOp_hom_app
  given: (X : C) (n m : Int) (hnm : n + m = 0 := by lia)
  proof: OpOpCommShift.iso_hom_app ..

@[reassoc]

中文:
引理 commShiftIso_opOp_hom_app
  条件: (X : C) (n m : 整数) (hnm : n + m = 0 := by lia)
  证明: OpOpCommShift.iso_hom_app ..

@[reassoc]

Depends on / 依赖: OpOpCommShift, OpOpCommShift.iso_hom_app, commShiftIso, hom.app, inv.app, iso_hom_app, shiftFunctorOpIso
-/
lemma commShiftIso_opOp_hom_app (X : C) (n m : Int) (hnm : n + m = 0 := by lia) :
    ((opOp C).commShiftIso n).hom.app X =
      ((shiftFunctorOpIso C m n (by lia)).hom.app (op X)).op ≫
        (shiftFunctorOpIso Cᵒᵖ _ _ hnm).inv.app (op (op X)) :=
  OpOpCommShift.iso_hom_app ..

@[reassoc]
/--
lemma `commShiftIso_opOp_inv_app` / 引理 `commShiftIso_opOp_inv_app`

English:
lemma commShiftIso_opOp_inv_app
  given: (X : C) (n m : Int) (hnm : n + m = 0 := by lia)
  proof: OpOpCommShift.iso_inv_app ..

@[reassoc]

中文:
引理 commShiftIso_opOp_inv_app
  条件: (X : C) (n m : 整数) (hnm : n + m = 0 := by lia)
  证明: OpOpCommShift.iso_inv_app ..

@[reassoc]

Depends on / 依赖: OpOpCommShift, OpOpCommShift.iso_inv_app, commShiftIso, hom.app, inv.app, iso_inv_app, shiftFunctorOpIso
-/
lemma commShiftIso_opOp_inv_app (X : C) (n m : Int) (hnm : n + m = 0 := by lia) :
    ((opOp C).commShiftIso n).inv.app X =
      (shiftFunctorOpIso Cᵒᵖ _ _ hnm).hom.app (op (op X)) ≫
      ((shiftFunctorOpIso C m n (by lia)).inv.app (op X)).op :=
  OpOpCommShift.iso_inv_app ..

@[reassoc]
/--
lemma `commShiftIso_unopUnop_hom_app` / 引理 `commShiftIso_unopUnop_hom_app`

English:
lemma commShiftIso_unopUnop_hom_app
  given: (X : Cᵒᵖᵒᵖ) (n m : Int) (hnm : n + m = 0 := by lia)
  proof: UnopUnopCommShift.iso_hom_app ..

@[reassoc]

中文:
引理 commShiftIso_unopUnop_hom_app
  条件: (X : Cᵒᵖᵒᵖ) (n m : 整数) (hnm : n + m = 0 := by lia)
  证明: UnopUnopCommShift.iso_hom_app ..

@[reassoc]

Depends on / 依赖: UnopUnopCommShift, UnopUnopCommShift.iso_hom_app, X.unop, commShiftIso, hom.app, inv.app, iso_hom_app, shiftFunctorOpIso, unop.unop, unopUnop
-/
lemma commShiftIso_unopUnop_hom_app (X : Cᵒᵖᵒᵖ) (n m : Int) (hnm : n + m = 0 := by lia) :
    ((unopUnop C).commShiftIso n).hom.app X =
      ((shiftFunctorOpIso Cᵒᵖ n m hnm).hom.app X).unop.unop ≫
        ((shiftFunctorOpIso C m n (by lia)).inv.app X.unop).unop :=
  UnopUnopCommShift.iso_hom_app ..

@[reassoc]
/--
lemma `commShiftIso_unopUnop_inv_app` / 引理 `commShiftIso_unopUnop_inv_app`

English:
lemma commShiftIso_unopUnop_inv_app
  given: (X : Cᵒᵖᵒᵖ) (n m : Int) (hnm : n + m = 0 := by lia)
  proof: UnopUnopCommShift.iso_inv_app ..

中文:
引理 commShiftIso_unopUnop_inv_app
  条件: (X : Cᵒᵖᵒᵖ) (n m : 整数) (hnm : n + m = 0 := by lia)
  证明: UnopUnopCommShift.iso_inv_app ..

Depends on / 依赖: UnopUnopCommShift, UnopUnopCommShift.iso_inv_app, X.unop, commShiftIso, hom.app, inv.app, iso_inv_app, shiftFunctorOpIso, unop.unop, unopUnop
-/
lemma commShiftIso_unopUnop_inv_app (X : Cᵒᵖᵒᵖ) (n m : Int) (hnm : n + m = 0 := by lia) :
    ((unopUnop C).commShiftIso n).inv.app X =
      ((shiftFunctorOpIso C m n (by lia)).hom.app X.unop).unop ≫
        ((shiftFunctorOpIso Cᵒᵖ n m hnm).inv.app X).unop.unop :=
  UnopUnopCommShift.iso_inv_app ..

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (opOpEquivalence C).functor.CommShift Int
  body: inferInstanceAs ((unopUnop C).CommShift Int)

中文:
实例 :
  签名: (opOpEquivalence C).functor.CommShift 整数
  定义体: inferInstanceAs ((unopUnop C).CommShift Int)

Depends on / 依赖: CommShift, unopUnop
-/
instance : (opOpEquivalence C).functor.CommShift Int :=
  inferInstanceAs ((unopUnop C).CommShift Int)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (opOpEquivalence C).inverse.CommShift Int
  body: inferInstanceAs ((opOp C).CommShift Int)

中文:
实例 :
  签名: (opOpEquivalence C).inverse.CommShift 整数
  定义体: inferInstanceAs ((opOp C).CommShift Int)

Depends on / 依赖: CommShift
-/
instance : (opOpEquivalence C).inverse.CommShift Int :=
  inferInstanceAs ((opOp C).CommShift Int)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (opOpEquivalence C).CommShift Int
  body: Equivalence.CommShift.mk'' _ _
    { shift_comm n := by
        ext X
        simp [Functor.commShiftIso_comp_hom_app,
          commShiftIso_opOp_hom_app _ n (-n),
          commShiftIso_unopUnop_hom_app _ n (-n),
          ← unop_comp_assoc] }

中文:
实例 :
  签名: (opOpEquivalence C).CommShift 整数
  定义体: Equivalence.CommShift.mk'' _ _
    { shift_comm n := by
        ext X
        simp [Functor.commShiftIso_comp_hom_app,
          commShiftIso_opOp_hom_app _ n (-n),
          commShiftIso_unopUnop_hom_app _ n (-n),
          ← unop_comp_assoc] }

Depends on / 依赖: CommShift, Equivalence, Equivalence.CommShift.mk, Functor, Functor.commShiftIso_comp_hom_app, commShiftIso_comp_hom_app, commShiftIso_opOp_hom_app, commShiftIso_unopUnop_hom_app, shift_comm, unop_comp_assoc
-/
instance : (opOpEquivalence C).CommShift Int :=
  Equivalence.CommShift.mk'' _ _
    { shift_comm n := by
        ext X
        simp [Functor.commShiftIso_comp_hom_app,
          commShiftIso_opOp_hom_app _ n (-n),
          commShiftIso_unopUnop_hom_app _ n (-n),
          ← unop_comp_assoc] }

variable [Preadditive C] [HasZeroObject C] [forall (n : Int), (shiftFunctor C n).Additive]
  [Pretriangulated C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (opOp C).IsTriangulated
  body: by
    refine isomorphic_distinguished _ (op_distinguished _ (op_distinguished _ hT)) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (Quiver.Hom.unop_inj ?_))
    have := (shiftFunctorCompIsoId C (-1) 1 (neg_add_cancel 1)).inv.naturality T.mor₃
    dsimp

中文:
实例 :
  签名: (opOp C).IsTriangulated
  定义体: by
    refine isomorphic_distinguished _ (op_distinguished _ (op_distinguished _ hT)) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (Quiver.Hom.unop_inj ?_))
    have := (shiftFunctorCompIsoId C (-1) 1 (neg_add_cancel 1)).inv.naturality T.mor₃
    dsimp

Depends on / 依赖: Functor, Functor.op_obj, Iso.refl, Quiver, Quiver.Hom.unop_inj, T.mor, Triangle, Triangle.isoMk, add_neg_cancel, commShiftIso_opOp_hom_app, inv.naturality, isomorphic_distinguished, naturality, neg_add_cancel, opShiftFunctorEquivalence_counitIso_inv_app, op_distinguished, op_obj, shiftFunctorCompIsoId, shiftFunctor_op_map, unop_com
-/
instance : (opOp C).IsTriangulated where
  map_distinguished T hT := by
    refine isomorphic_distinguished _ (op_distinguished _ (op_distinguished _ hT)) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (Quiver.Hom.unop_inj ?_))
    have := (shiftFunctorCompIsoId C (-1) 1 (neg_add_cancel 1)).inv.naturality T.mor₃
    dsimp at this ⊢
    simp only [shiftFunctor_op_map _ 1 (-1), Functor.op_obj,
      unop_id, shiftFunctor_op_map _ (-1) 1,
      commShiftIso_opOp_hom_app _ 1 (-1),
      opShiftFunctorEquivalence_counitIso_inv_app _ 1 (-1) (add_neg_cancel 1),
      unop_comp, Quiver.Hom.unop_op, Category.assoc, ← op_comp, Iso.inv_hom_id_app_assoc,
      shiftFunctorCompIsoId_op_hom_app, Iso.unop_hom_inv_id_app_assoc, ← Functor.map_comp]
    simp [Functor.map_comp, shift_shiftFunctorCompIsoId_hom_app, ← reassoc_of% this]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (opOpEquivalence C).IsTriangulated
  body: .mk'' _ inferInstanceAs (opOp C).IsTriangulated

中文:
实例 :
  签名: (opOpEquivalence C).IsTriangulated
  定义体: .mk'' _ inferInstanceAs (opOp C).IsTriangulated

Depends on / 依赖: IsTriangulated
-/
instance : (opOpEquivalence C).IsTriangulated :=
.mk'' _ inferInstanceAs (opOp C).IsTriangulated

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (unopUnop C).IsTriangulated
  body: inferInstanceAs ((opOpEquivalence C).functor.IsTriangulated)

中文:
实例 :
  签名: (unopUnop C).IsTriangulated
  定义体: inferInstanceAs ((opOpEquivalence C).functor.IsTriangulated)

Depends on / 依赖: IsTriangulated, functor, functor.IsTriangulated, opOpEquivalence
-/
instance : (unopUnop C).IsTriangulated :=
  inferInstanceAs ((opOpEquivalence C).functor.IsTriangulated)

end Pretriangulated

end CategoryTheory
