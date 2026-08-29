/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# The (naive) shift on the opposite category

If `C` is a category equipped with a shift by a monoid `A`, the opposite category
can be equipped with a shift such that the shift functor by `n` is `(shiftFunctor C n).op`.
This is the "naive" opposite shift, which we shall set on a category `OppositeShift C A`,
which is a type synonym for `Cᵒᵖ`.

However, for the application to (pre)triangulated categories, we would like to
define the shift on `Cᵒᵖ` so that `shiftFunctor Cᵒᵖ n` for `n : ℤ` identifies to
`(shiftFunctor C (-n)).op` rather than `(shiftFunctor C n).op`. Then, the construction
of the shift on `Cᵒᵖ` shall combine the shift on `OppositeShift C A` and another
construction of the "pullback" of a shift by a monoid morphism like `n ↦ -n`.

If `F : C ⥤ D` is a functor between categories equipped with shifts by `A`, we define
a type synonym `OppositeShift.functor A F` for `F.op`. When `F` has a `CommShift` structure
by `A`, we define a `CommShift` structure by `A` on `OppositeShift.functor A F`. In this
way, we can make this an instance and reserve `F.op` for the `CommShift` instance by
the modified shift in the case of (pre)triangulated categories.

Similarly, if `τ` is a natural transformation between functors `F,G : C ⥤ D`, we define
a type synonym for `τ.op` called
`OppositeShift.natTrans A τ : OppositeShift.functor A F ⟶ OppositeShift.functor A G`.
When `τ` has a `CommShift` structure by `A` (i.e. is compatible with `CommShift` structures
on `F` and `G`), we define a `CommShift` structure by `A` on `OppositeShift.natTrans A τ`.

Finally, if we have an adjunction `F ⊣ G` (with `G : D ⥤ C`), we define a type synonym
`OppositeShift.adjunction A adj : OppositeShift.functor A G ⊣ OppositeShift.functor A F`
for `adj.op`, and we show that, if `adj` compatible with `CommShift` structures
on `F` and `G`, then `OppositeShift.adjunction A adj` is also compatible with the pulled back
`CommShift` structures.

Given a `CommShift` structure on a functor `F`, we define a `CommShift` structure on `F.op`
(and vice versa).
We also prove that, if an adjunction `F ⊣ G` is compatible with `CommShift` structures on
`F` and `G`, then the opposite adjunction `G.op ⊣ F.op` is compatible with the opposite
`CommShift` structures.

-/

@[expose] public section

namespace CategoryTheory

open Limits Category

section

variable (C : Type*) [Category* C] (A : Type*) [AddMonoid A] [HasShift C A]

namespace HasShift

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `mkShiftCoreOp` / `mkShiftCoreOp` 的定义

English:
definition mkShiftCoreOp
  signature: : ShiftMkCore Cᵒᵖ A where
  body: (shiftFunctor C n).op
  zero := (NatIso.op (shiftFunctorZero C A)).symm
  add a b := (NatIso.op (shiftFunctorAdd C a b)).symm
  assoc_hom_app m₁ m₂ m₃ X :=
    Quiver.Hom.unop_inj ((shiftFunctorAdd_assoc_inv_app m₁ m₂ m₃ X.unop).trans
      (by simp [shiftFunctorAdd']))
  zero_add_hom_app n X :=
   

中文:
定义 mkShiftCoreOp
  签名: : ShiftMkCore Cᵒᵖ A where
  定义体: (shiftFunctor C n).op
  zero := (NatIso.op (shiftFunctorZero C A)).symm
  add a b := (NatIso.op (shiftFunctorAdd C a b)).symm
  assoc_hom_app m₁ m₂ m₃ X :=
    Quiver.Hom.unop_inj ((shiftFunctorAdd_assoc_inv_app m₁ m₂ m₃ X.unop).trans
      (by simp [shiftFunctorAdd']))
  zero_add_hom_app n X :=
   

Depends on / 依赖: shiftFunctor
-/
def mkShiftCoreOp : ShiftMkCore Cᵒᵖ A where
  F n := (shiftFunctor C n).op
  zero := (NatIso.op (shiftFunctorZero C A)).symm
  add a b := (NatIso.op (shiftFunctorAdd C a b)).symm
  assoc_hom_app m₁ m₂ m₃ X :=
    Quiver.Hom.unop_inj ((shiftFunctorAdd_assoc_inv_app m₁ m₂ m₃ X.unop).trans
      (by simp [shiftFunctorAdd']))
  zero_add_hom_app n X :=
    Quiver.Hom.unop_inj ((shiftFunctorAdd_zero_add_inv_app n X.unop).trans (by simp))
  add_zero_hom_app n X :=
    Quiver.Hom.unop_inj ((shiftFunctorAdd_add_zero_inv_app n X.unop).trans (by simp))

end HasShift

/-- The category `OppositeShift C A` is the opposite category `Cᵒᵖ` equipped
with the naive shift: `shiftFunctor (OppositeShift C A) n` is `(shiftFunctor C n).op`. -/
@[nolint unusedArguments]
/--
Definition of `OppositeShift` / `OppositeShift` 的定义

English:
definition OppositeShift
  signature: (A : Type*) [AddMonoid A] [HasShift C A]
  body: Cᵒᵖ

中文:
定义 OppositeShift
  签名: (A : 类型) [加法幺半群 A] [有Shift C A]
  定义体: Cᵒᵖ
-/
def OppositeShift (A : Type*) [AddMonoid A] [HasShift C A] := Cᵒᵖ

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (OppositeShift C A)
  body: inferInstanceAs (Category Cᵒᵖ)

中文:
实例 :
  签名: 范畴 (OppositeShift C A)
  定义体: inferInstanceAs (Category Cᵒᵖ)

Depends on / 依赖: Category
-/
instance : Category (OppositeShift C A) := inferInstanceAs (Category Cᵒᵖ)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasShift (OppositeShift C A) A
  body: hasShiftMk Cᵒᵖ A (HasShift.mkShiftCoreOp C A)

中文:
实例 :
  签名: 有Shift (OppositeShift C A) A
  定义体: hasShiftMk Cᵒᵖ A (HasShift.mkShiftCoreOp C A)

Depends on / 依赖: HasShift, HasShift.mkShiftCoreOp, hasShiftMk, mkShiftCoreOp
-/
instance : HasShift (OppositeShift C A) A :=
  hasShiftMk Cᵒᵖ A (HasShift.mkShiftCoreOp C A)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroObject
  signature: C] : HasZeroObject (OppositeShift C A)
  body: by
  dsimp only [OppositeShift]
  infer_instance

中文:
实例 [有ZeroObject
  签名: C] : 有ZeroObject (OppositeShift C A)
  定义体: by
  dsimp only [OppositeShift]
  infer_instance

Depends on / 依赖: OppositeShift, infer_instance
-/
instance [HasZeroObject C] : HasZeroObject (OppositeShift C A) := by
  dsimp only [OppositeShift]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preadditive
  signature: C] : Preadditive (OppositeShift C A)
  body: inferInstanceAs (Preadditive Cᵒᵖ)

中文:
实例 [预加性
  签名: C] : 预加性 (OppositeShift C A)
  定义体: inferInstanceAs (Preadditive Cᵒᵖ)

Depends on / 依赖: Preadditive
-/
instance [Preadditive C] : Preadditive (OppositeShift C A) :=
  inferInstanceAs (Preadditive Cᵒᵖ)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preadditive
  signature: C] (n
  body: by
  change (shiftFunctor C n).op.Additive
  infer_instance

中文:
实例 [预加性
  签名: C] (n
  定义体: by
  change (shiftFunctor C n).op.Additive
  infer_instance

Depends on / 依赖: Additive, infer_instance, op.Additive, shiftFunctor
-/
instance [Preadditive C] (n : A) [(shiftFunctor C n).Additive] :
    (shiftFunctor (OppositeShift C A) n).Additive := by
  change (shiftFunctor C n).op.Additive
  infer_instance

/--
lemma `oppositeShiftFunctorZero_inv_app` / 引理 `oppositeShiftFunctorZero_inv_app`

English:
lemma oppositeShiftFunctorZero_inv_app
  given: (X : OppositeShift C A)
  proof: rfl

中文:
引理 oppositeShiftFunctorZero_inv_app
  条件: (X : OppositeShift C A)
  证明: rfl
-/
lemma oppositeShiftFunctorZero_inv_app (X : OppositeShift C A) :
    (shiftFunctorZero (OppositeShift C A) A).inv.app X =
      ((shiftFunctorZero C A).hom.app X.unop).op := rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `oppositeShiftFunctorZero_hom_app` / 引理 `oppositeShiftFunctorZero_hom_app`

English:
lemma oppositeShiftFunctorZero_hom_app
  given: (X : OppositeShift C A)
  proof: by
  rw [← cancel_mono ((shiftFunctorZero (OppositeShift C A) A).inv.app X)]; rw [Iso.hom_inv_id_app]; rw [oppositeShiftFunctorZero_inv_app]; rw [← op_comp]; rw [Iso.hom_inv_id_app]; rw [op_id]
  rfl

中文:
引理 oppositeShiftFunctorZero_hom_app
  条件: (X : OppositeShift C A)
  证明: by
  rw [← cancel_mono ((shiftFunctorZero (OppositeShift C A) A).inv.app X)]; rw [Iso.hom_inv_id_app]; rw [oppositeShiftFunctorZero_inv_app]; rw [← op_comp]; rw [Iso.hom_inv_id_app]; rw [op_id]
  rfl

Depends on / 依赖: Iso.hom_inv_id_app, OppositeShift, cancel_mono, hom_inv_id_app, inv.app, op_comp, op_id, oppositeShiftFunctorZero_inv_app, shiftFunctorZero
-/
lemma oppositeShiftFunctorZero_hom_app (X : OppositeShift C A) :
    (shiftFunctorZero (OppositeShift C A) A).hom.app X =
      ((shiftFunctorZero C A).inv.app X.unop).op := by
  rw [← cancel_mono ((shiftFunctorZero (OppositeShift C A) A).inv.app X)]; rw [Iso.hom_inv_id_app]; rw [oppositeShiftFunctorZero_inv_app]; rw [← op_comp]; rw [Iso.hom_inv_id_app]; rw [op_id]
  rfl

variable {C A}
variable (X : OppositeShift C A) (a b c : A) (h : a + b = c)

/--
lemma `oppositeShiftFunctorAdd_inv_app` / 引理 `oppositeShiftFunctorAdd_inv_app`

English:
lemma oppositeShiftFunctorAdd_inv_app
  proof: rfl

中文:
引理 oppositeShiftFunctorAdd_inv_app
  证明: rfl
-/
lemma oppositeShiftFunctorAdd_inv_app :
    (shiftFunctorAdd (OppositeShift C A) a b).inv.app X =
      ((shiftFunctorAdd C a b).hom.app X.unop).op := rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `oppositeShiftFunctorAdd_hom_app` / 引理 `oppositeShiftFunctorAdd_hom_app`

English:
lemma oppositeShiftFunctorAdd_hom_app
  proof: by
  rw [← cancel_mono ((shiftFunctorAdd (OppositeShift C A) a b).inv.app X)]; rw [Iso.hom_inv_id_app]; rw [oppositeShiftFunctorAdd_inv_app]; rw [← op_comp]; rw [Iso.hom_inv_id_app]; rw [op_id]
  rfl

中文:
引理 oppositeShiftFunctorAdd_hom_app
  证明: by
  rw [← cancel_mono ((shiftFunctorAdd (OppositeShift C A) a b).inv.app X)]; rw [Iso.hom_inv_id_app]; rw [oppositeShiftFunctorAdd_inv_app]; rw [← op_comp]; rw [Iso.hom_inv_id_app]; rw [op_id]
  rfl

Depends on / 依赖: Iso.hom_inv_id_app, OppositeShift, cancel_mono, hom_inv_id_app, inv.app, op_comp, op_id, oppositeShiftFunctorAdd_inv_app, shiftFunctorAdd
-/
lemma oppositeShiftFunctorAdd_hom_app :
    (shiftFunctorAdd (OppositeShift C A) a b).hom.app X =
      ((shiftFunctorAdd C a b).inv.app X.unop).op := by
  rw [← cancel_mono ((shiftFunctorAdd (OppositeShift C A) a b).inv.app X)]; rw [Iso.hom_inv_id_app]; rw [oppositeShiftFunctorAdd_inv_app]; rw [← op_comp]; rw [Iso.hom_inv_id_app]; rw [op_id]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `oppositeShiftFunctorAdd'_inv_app` / 引理 `oppositeShiftFunctorAdd'_inv_app`

English:
lemma oppositeShiftFunctorAdd'_inv_app
  proof: by
  subst h
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, oppositeShiftFunctorAdd_inv_app]

中文:
引理 oppositeShiftFunctorAdd'_inv_app
  证明: by
  subst h
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, oppositeShiftFunctorAdd_inv_app]

Depends on / 依赖: _eq_shiftFunctorAdd, oppositeShiftFunctorAdd_inv_app, shiftFunctorAdd
-/
lemma oppositeShiftFunctorAdd'_inv_app :
    (shiftFunctorAdd' (OppositeShift C A) a b c h).inv.app X =
      ((shiftFunctorAdd' C a b c h).hom.app X.unop).op := by
  subst h
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, oppositeShiftFunctorAdd_inv_app]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `oppositeShiftFunctorAdd'_hom_app` / 引理 `oppositeShiftFunctorAdd'_hom_app`

English:
lemma oppositeShiftFunctorAdd'_hom_app
  proof: by
  subst h
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, oppositeShiftFunctorAdd_hom_app]

中文:
引理 oppositeShiftFunctorAdd'_hom_app
  证明: by
  subst h
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, oppositeShiftFunctorAdd_hom_app]
-/
lemma oppositeShiftFunctorAdd'_hom_app :
    (shiftFunctorAdd' (OppositeShift C A) a b c h).hom.app X =
      ((shiftFunctorAdd' C a b c h).inv.app X.unop).op := by
  subst h
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, oppositeShiftFunctorAdd_hom_app]

end

variable {C D : Type*} [Category* C] [Category* D] (A : Type*) [AddMonoid A]
  [HasShift C A] [HasShift D A] (F : C ⥤ D)

/--
Definition of `OppositeShift.functor` / `OppositeShift.functor` 的定义

English:
definition OppositeShift.functor
  signature: : OppositeShift C A ⥤ OppositeShift D A
  body: F.op

中文:
定义 OppositeShift.functor
  签名: : OppositeShift C A ⥤ OppositeShift D A
  定义体: F.op

Depends on / 依赖: F.op
-/
def OppositeShift.functor : OppositeShift C A ⥤ OppositeShift D A := F.op

variable {F} in
/--
Definition of `OppositeShift.natTrans` / `OppositeShift.natTrans` 的定义

English:
definition OppositeShift.natTrans
  signature: {G : C ⥤ D} (τ : F ⟶ G)
  body: NatTrans.op τ

中文:
定义 OppositeShift.natTrans
  签名: {G : C ⥤ D} (τ : F ⟶ G)
  定义体: NatTrans.op τ

Depends on / 依赖: NatTrans, NatTrans.op
-/
def OppositeShift.natTrans {G : C ⥤ D} (τ : F ⟶ G) :
    OppositeShift.functor A G ⟶ OppositeShift.functor A F :=
  NatTrans.op τ

namespace Functor

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `commShiftOp` / 实例 `commShiftOp`

English:
instance commShiftOp
  signature: [CommShift F A]
  body: (NatIso.op (F.commShiftIso a)).symm
  commShiftIso_zero := by
    rw [commShiftIso_zero]
    ext
    simp only [op_obj, comp_obj, Iso.symm_hom, NatIso.op_inv, NatTrans.op_app,
      CommShift.isoZero_inv_app, op_comp, CommShift.isoZero_hom_app]
    erw [oppositeShiftFunctorZero_inv_app, oppositeShif

中文:
实例 commShiftOp
  签名: [交换Shift F A]
  定义体: (NatIso.op (F.commShiftIso a)).symm
  commShiftIso_zero := by
    rw [commShiftIso_zero]
    ext
    simp only [op_obj, comp_obj, Iso.symm_hom, NatIso.op_inv, NatTrans.op_app,
      CommShift.isoZero_inv_app, op_comp, CommShift.isoZero_hom_app]
    erw [oppositeShiftFunctorZero_inv_app, oppositeShif

Depends on / 依赖: F.commShiftIso, NatIso, NatIso.op, commShiftIso
-/
instance commShiftOp [CommShift F A] :
    CommShift (OppositeShift.functor A F) A where
  commShiftIso a := (NatIso.op (F.commShiftIso a)).symm
  commShiftIso_zero := by
    rw [commShiftIso_zero]
    ext
    simp only [op_obj, comp_obj, Iso.symm_hom, NatIso.op_inv, NatTrans.op_app,
      CommShift.isoZero_inv_app, op_comp, CommShift.isoZero_hom_app]
    erw [oppositeShiftFunctorZero_inv_app, oppositeShiftFunctorZero_hom_app]
    rfl
  commShiftIso_add a b := by
    rw [commShiftIso_add]
    ext
    simp only [op_obj, comp_obj, Iso.symm_hom, NatIso.op_inv, NatTrans.op_app,
      CommShift.isoAdd_inv_app, op_comp, Category.assoc, CommShift.isoAdd_hom_app]
    erw [oppositeShiftFunctorAdd_inv_app, oppositeShiftFunctorAdd_hom_app]
    rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `commShiftOp_iso_eq` / 引理 `commShiftOp_iso_eq`

English:
lemma commShiftOp_iso_eq
  given: [CommShift F A] (a : A)
  proof: rfl

中文:
引理 commShiftOp_iso_eq
  条件: [交换Shift F A] (a : A)
  证明: rfl
-/
lemma commShiftOp_iso_eq [CommShift F A] (a : A) :
    (OppositeShift.functor A F).commShiftIso a = (NatIso.op (F.commShiftIso a)).symm := rfl

set_option backward.isDefEq.respectTransparency false in
/--
Given a `CommShift` structure on `OppositeShift.functor F` (for the naive shifts on the opposite
categories), this is the corresponding `CommShift` structure on `F`.
-/
@[simps -isSimp, instance_reducible]
/--
Definition of `commShiftUnop` / `commShiftUnop` 的定义

English:
definition commShiftUnop
  body: NatIso.removeOp ((OppositeShift.functor A F).commShiftIso a).symm
  commShiftIso_zero := by
    rw [commShiftIso_zero]
    ext
    simp only [NatIso.removeOp_hom, Iso.symm_hom, NatTrans.removeOp_app,
      CommShift.isoZero_inv_app, unop_comp, CommShift.isoZero_hom_app]
    erw [oppositeShiftFunctor

中文:
定义 commShiftUnop
  定义体: NatIso.removeOp ((OppositeShift.functor A F).commShiftIso a).symm
  commShiftIso_zero := by
    rw [commShiftIso_zero]
    ext
    simp only [NatIso.removeOp_hom, Iso.symm_hom, NatTrans.removeOp_app,
      CommShift.isoZero_inv_app, unop_comp, CommShift.isoZero_hom_app]
    erw [oppositeShiftFunctor

Depends on / 依赖: NatIso, NatIso.removeOp, OppositeShift, OppositeShift.functor, commShiftIso, functor, removeOp
-/
def commShiftUnop
    [CommShift (OppositeShift.functor A F) A] : CommShift F A where
  commShiftIso a := NatIso.removeOp ((OppositeShift.functor A F).commShiftIso a).symm
  commShiftIso_zero := by
    rw [commShiftIso_zero]
    ext
    simp only [NatIso.removeOp_hom, Iso.symm_hom, NatTrans.removeOp_app,
      CommShift.isoZero_inv_app, unop_comp, CommShift.isoZero_hom_app]
    erw [oppositeShiftFunctorZero_hom_app, oppositeShiftFunctorZero_inv_app]
    rfl
  commShiftIso_add a b := by
    rw [commShiftIso_add]
    ext
    simp only [NatIso.removeOp_hom, Iso.symm_hom, NatTrans.removeOp_app,
      CommShift.isoAdd_inv_app, unop_comp, Category.assoc,
      CommShift.isoAdd_hom_app]
    erw [oppositeShiftFunctorAdd_hom_app, oppositeShiftFunctorAdd_inv_app]
    rfl

end Functor

namespace NatTrans

variable {F} {G : C ⥤ D} [F.CommShift A] [G.CommShift A]

open Opposite in
/--
Instance `commShift_op` / 实例 `commShift_op`

English:
instance commShift_op
  signature: (τ : F ⟶ G) [NatTrans.CommShift τ A]
  body: by
    ext
    rw [← cancel_mono (((OppositeShift.functor A F).commShiftIso _).inv.app _)]; rw [← cancel_epi (((OppositeShift.functor A G).commShiftIso _).inv.app _)]
    simp only [Functor.comp_obj, comp_app, Functor.whiskerRight_app, assoc,
      Iso.inv_hom_id_app_assoc, Functor.whiskerLeft_app, 

中文:
实例 commShift_op
  签名: (τ : F ⟶ G) [自然变换.交换Shift τ A]
  定义体: by
    ext
    rw [← cancel_mono (((OppositeShift.functor A F).commShiftIso _).inv.app _)]; rw [← cancel_epi (((OppositeShift.functor A G).commShiftIso _).inv.app _)]
    simp only [Functor.comp_obj, comp_app, Functor.whiskerRight_app, assoc,
      Iso.inv_hom_id_app_assoc, Functor.whiskerLeft_app, 

Depends on / 依赖: Functor, Functor.comp_obj, Functor.whiskerLeft_app, Functor.whiskerRight_app, IndepMatroid, IndepMatroid.matroid, IndepMatroid.ofFoo, Iso.hom_inv_id_app, Iso.inv_hom_id_app_assoc, MyIndep, NatTrans, NatTrans.shift_app_comm, OppositeShift, OppositeShift.functor, cancel_epi, cancel_mono, commShiftIso, comp_app, comp_id, comp_obj
-/
instance commShift_op (τ : F ⟶ G) [NatTrans.CommShift τ A] :
    NatTrans.CommShift (OppositeShift.natTrans A τ) A where
  shift_comm _ := by
    ext
    rw [← cancel_mono (((OppositeShift.functor A F).commShiftIso _).inv.app _)]; rw [← cancel_epi (((OppositeShift.functor A G).commShiftIso _).inv.app _)]
    simp only [Functor.comp_obj, comp_app, Functor.whiskerRight_app, assoc,
      Iso.inv_hom_id_app_assoc, Functor.whiskerLeft_app, Iso.hom_inv_id_app, comp_id]
    exact (op_inj_iff _ _).mpr (NatTrans.shift_app_comm τ _ (unop _))

end NatTrans

namespace NatTrans

variable (C) in
/--
Definition of `OppositeShift.natIsoId` / `OppositeShift.natIsoId` 的定义

English:
definition OppositeShift.natIsoId
  signature: : 𝟭 (OppositeShift C A) ≅ OppositeShift.functor A (𝟭 C)
  body: Iso.refl _

中文:
定义 OppositeShift.natIsoId
  签名: : 𝟭 (OppositeShift C A) ≅ OppositeShift.functor A (𝟭 C)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl, matroid, myIndepMatroid
-/
def OppositeShift.natIsoId : 𝟭 (OppositeShift C A) ≅ OppositeShift.functor A (𝟭 C) := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatTrans.CommShift (OppositeShift.natIsoId C A).hom A
  body: by
    ext
    dsimp [OppositeShift.natIsoId, Functor.commShiftOp_iso_eq]
    simp only [Functor.commShiftIso_id_hom_app, Functor.map_id,
      comp_id, Functor.commShiftIso_id_inv_app, CategoryTheory.op_id, id_comp]
    rfl

中文:
实例 :
  签名: 自然变换.交换Shift (OppositeShift.natIsoId C A).hom A
  定义体: by
    ext
    dsimp [OppositeShift.natIsoId, Functor.commShiftOp_iso_eq]
    simp only [Functor.commShiftIso_id_hom_app, Functor.map_id,
      comp_id, Functor.commShiftIso_id_inv_app, CategoryTheory.op_id, id_comp]
    rfl

Depends on / 依赖: CategoryTheory, CategoryTheory.op_id, Functor, Functor.commShiftIso_id_hom_app, Functor.commShiftIso_id_inv_app, Functor.commShiftOp_iso_eq, Functor.map_id, OppositeShift, OppositeShift.natIsoId, commShiftIso_id_hom_app, commShiftIso_id_inv_app, commShiftOp_iso_eq, comp_id, id_comp, map_id, natIsoId, op_id
-/
instance : NatTrans.CommShift (OppositeShift.natIsoId C A).hom A where
  shift_comm _ := by
    ext
    dsimp [OppositeShift.natIsoId, Functor.commShiftOp_iso_eq]
    simp only [Functor.commShiftIso_id_hom_app, Functor.map_id,
      comp_id, Functor.commShiftIso_id_inv_app, CategoryTheory.op_id, id_comp]
    rfl

variable {E : Type*} [Category* E] [HasShift E A] (G : D ⥤ E)

/--
Definition of `OppositeShift.natIsoComp` / `OppositeShift.natIsoComp` 的定义

English:
definition OppositeShift.natIsoComp
  signature: : OppositeShift.functor A (F ⋙ G) ≅
  body: Iso.refl _

中文:
定义 OppositeShift.natIsoComp
  签名: : OppositeShift.functor A (F ⋙ G) ≅
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def OppositeShift.natIsoComp : OppositeShift.functor A (F ⋙ G) ≅
    OppositeShift.functor A F ⋙ OppositeShift.functor A G := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.CommShift
  signature: A] [G.CommShift A] :
  body: by
    ext
    dsimp [OppositeShift.natIsoComp, Functor.commShiftOp_iso_eq]
    simp only [Functor.map_id, comp_id, id_comp]
    rfl

中文:
实例 [F.交换Shift
  签名: A] [G.交换Shift A] :
  定义体: by
    ext
    dsimp [OppositeShift.natIsoComp, Functor.commShiftOp_iso_eq]
    simp only [Functor.map_id, comp_id, id_comp]
    rfl

Depends on / 依赖: Functor, Functor.commShiftOp_iso_eq, Functor.map_id, OppositeShift, OppositeShift.natIsoComp, commShiftOp_iso_eq, comp_id, id_comp, map_id, natIsoComp
-/
instance [F.CommShift A] [G.CommShift A] :
    NatTrans.CommShift (OppositeShift.natIsoComp A F G).hom A where
  shift_comm _ := by
    ext
    dsimp [OppositeShift.natIsoComp, Functor.commShiftOp_iso_eq]
    simp only [Functor.map_id, comp_id, id_comp]
    rfl

end NatTrans

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
The adjunction `adj`, seen as an adjunction between `OppositeShift.functor G`
and `OppositeShift.functor F`.
-/
@[simps -isSimp]
/--
Definition of `OppositeShift.adjunction` / `OppositeShift.adjunction` 的定义

English:
definition OppositeShift.adjunction
  signature: {F} {G : D ⥤ C} (adj : F ⊣ G)
  body: (NatTrans.OppositeShift.natIsoId D A).hom ≫
    OppositeShift.natTrans A adj.counit ≫ (NatTrans.OppositeShift.natIsoComp A G F).hom
  counit := (NatTrans.OppositeShift.natIsoComp A F G).inv ≫
    OppositeShift.natTrans A adj.unit ≫ (NatTrans.OppositeShift.natIsoId C A).inv
  left_triangle_components

中文:
定义 OppositeShift.adjunction
  签名: {F} {G : D ⥤ C} (adj : F ⊣ G)
  定义体: (NatTrans.OppositeShift.natIsoId D A).hom ≫
    OppositeShift.natTrans A adj.counit ≫ (NatTrans.OppositeShift.natIsoComp A G F).hom
  counit := (NatTrans.OppositeShift.natIsoComp A F G).inv ≫
    OppositeShift.natTrans A adj.unit ≫ (NatTrans.OppositeShift.natIsoId C A).inv
  left_triangle_components

Depends on / 依赖: NatTrans, NatTrans.OppositeShift.natIsoId, OppositeShift, natIsoId
-/
def OppositeShift.adjunction {F} {G : D ⥤ C} (adj : F ⊣ G) :
    OppositeShift.functor A G ⊣ OppositeShift.functor A F where
  unit := (NatTrans.OppositeShift.natIsoId D A).hom ≫
    OppositeShift.natTrans A adj.counit ≫ (NatTrans.OppositeShift.natIsoComp A G F).hom
  counit := (NatTrans.OppositeShift.natIsoComp A F G).inv ≫
    OppositeShift.natTrans A adj.unit ≫ (NatTrans.OppositeShift.natIsoId C A).inv
  left_triangle_components _ := by
    dsimp [OppositeShift.natTrans, NatTrans.OppositeShift.natIsoComp,
      NatTrans.OppositeShift.natIsoId, OppositeShift.functor]
    simp only [comp_id, id_comp, Quiver.Hom.unop_op]
    rw [← op_comp]; rw [adj.right_triangle_components]
    rfl
  right_triangle_components _ := by
    dsimp [OppositeShift.natTrans, NatTrans.OppositeShift.natIsoComp,
      NatTrans.OppositeShift.natIsoId, OppositeShift.functor]
    simp only [comp_id, id_comp, Quiver.Hom.unop_op]
    rw [← op_comp]; rw [adj.left_triangle_components]
    rfl

namespace Adjunction

variable {F} {G : D ⥤ C} (adj : F ⊣ G)

/--
Instance `commShift_op` / 实例 `commShift_op`

English:
instance commShift_op
  signature: [F.CommShift A] [G.CommShift A] [adj.CommShift A]
  body: by dsimp [OppositeShift.adjunction]; infer_instance
  commShift_counit := by dsimp [OppositeShift.adjunction]; infer_instance

中文:
实例 commShift_op
  签名: [F.交换Shift A] [G.交换Shift A] [adj.交换Shift A]
  定义体: by dsimp [OppositeShift.adjunction]; infer_instance
  commShift_counit := by dsimp [OppositeShift.adjunction]; infer_instance

Depends on / 依赖: IndepMatroid, IndepMatroid.ofBdd, OppositeShift, OppositeShift.adjunction, adjunction, commShift_counit, exists_isBase, finite_of_encard_le_coe, hB.indep, hB.rankFinite_of_finite, h_bdd, infer_instance, matroid, matroid.exists_isBase, rankFinite_of_finite
-/
instance commShift_op [F.CommShift A] [G.CommShift A] [adj.CommShift A] :
    Adjunction.CommShift (OppositeShift.adjunction A adj) A where
  commShift_unit := by dsimp [OppositeShift.adjunction]; infer_instance
  commShift_counit := by dsimp [OppositeShift.adjunction]; infer_instance

end Adjunction

end CategoryTheory
