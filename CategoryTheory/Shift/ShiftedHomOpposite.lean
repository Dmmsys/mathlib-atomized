/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Basic
public import Mathlib.CategoryTheory.Shift.ShiftedHom

/-! # Shifted morphisms in the opposite category

If `C` is a category equipped with a shift by `ℤ`, `X` and `Y` are objects
of `C`, and `n : ℤ`, we define a bijection
`ShiftedHom.opEquiv : ShiftedHom X Y n ≃ ShiftedHom (Opposite.op Y) (Opposite.op X) n`.
We also introduce `ShiftedHom.opEquiv'` which produces a bijection
`ShiftedHom X Y a' ≃ (Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦n⟧)` when `n + a = a'`.
The compatibilities that are obtained shall be used in order to study
the homological functor `preadditiveYoneda.obj B : Cᵒᵖ ⥤ Type _` when `B` is an object
in a pretriangulated category `C`.

-/

@[expose] public section

namespace CategoryTheory

open Category Pretriangulated.Opposite Pretriangulated

variable {C : Type*} [Category* C] [HasShift C Int] {X Y Z : C}

namespace ShiftedHom

/--
Definition of `opEquiv` / `opEquiv` 的定义

English:
definition opEquiv
  signature: (n : Int)
  body: Quiver.Hom.opEquiv.trans
    ((opShiftFunctorEquivalence C n).symm.toAdjunction.homEquiv (Opposite.op Y) (Opposite.op X))

中文:
定义 opEquiv
  签名: (n : 整数)
  定义体: Quiver.Hom.opEquiv.trans
    ((opShiftFunctorEquivalence C n).symm.toAdjunction.homEquiv (Opposite.op Y) (Opposite.op X))

Depends on / 依赖: Opposite, Opposite.op, Quiver, Quiver.Hom.opEquiv.trans, homEquiv, opEquiv, opShiftFunctorEquivalence, symm.toAdjunction.homEquiv, toAdjunction
-/
noncomputable def opEquiv (n : Int) :
    ShiftedHom X Y n ≃ ShiftedHom (Opposite.op Y) (Opposite.op X) n :=
  Quiver.Hom.opEquiv.trans
    ((opShiftFunctorEquivalence C n).symm.toAdjunction.homEquiv (Opposite.op Y) (Opposite.op X))

/--
lemma `opEquiv_symm_apply` / 引理 `opEquiv_symm_apply`

English:
lemma opEquiv_symm_apply
  given: {n : Int} (f : ShiftedHom (Opposite.op Y) (Opposite.op X) n)
  proof: rfl

中文:
引理 opEquiv_symm_apply
  条件: {n : 整数} (f : ShiftedHom (Opposite.op Y) (Opposite.op X) n)
  证明: rfl
-/
lemma opEquiv_symm_apply {n : Int} (f : ShiftedHom (Opposite.op Y) (Opposite.op X) n) :
    (opEquiv n).symm f =
      ((opShiftFunctorEquivalence C n).unitIso.inv.app (Opposite.op X)).unop ≫ f.unop⟦n⟧' :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/--
lemma `opEquiv_symm_apply_comp` / 引理 `opEquiv_symm_apply_comp`

English:
lemma opEquiv_symm_apply_comp
  statement: {X Y : C} {a : Int}
  proof: by
  rw [ShiftedHom.opEquiv_symm_apply]; rw [ShiftedHom.opEquiv_symm_apply]; rw [ShiftedHom.comp]
  dsimp
  simp only [assoc, Functor.map_comp]

中文:
引理 opEquiv_symm_apply_comp
  结论: {X Y : C} {a : 整数}
  证明: by
  rw [ShiftedHom.opEquiv_symm_apply]; rw [ShiftedHom.opEquiv_symm_apply]; rw [ShiftedHom.comp]
  dsimp
  simp only [assoc, Functor.map_comp]

Depends on / 依赖: Functor, Functor.map_comp, ShiftedHom, ShiftedHom.comp, ShiftedHom.opEquiv_symm_apply, map_comp, opEquiv_symm_apply
-/
lemma opEquiv_symm_apply_comp {X Y : C} {a : Int}
    (f : ShiftedHom (Opposite.op X) (Opposite.op Y) a) {b : Int} {Z : C}
    (z : ShiftedHom X Z b) {c : Int} (h : b + a = c) :
    ((ShiftedHom.opEquiv a).symm f).comp z h =
      (ShiftedHom.opEquiv a).symm (z.op ≫ f) ≫
        (shiftFunctorAdd' C b a c h).inv.app Z := by
  rw [ShiftedHom.opEquiv_symm_apply]; rw [ShiftedHom.opEquiv_symm_apply]; rw [ShiftedHom.comp]
  dsimp
  simp only [assoc, Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `opEquiv_symm_comp` / 引理 `opEquiv_symm_comp`

English:
lemma opEquiv_symm_comp
  statement: {a b : Int}
  proof: by
  rw [opEquiv_symm_apply]; rw [opEquiv_symm_apply]; rw [opShiftFunctorEquivalence_add_unitIso_inv_app_eq _ _ _ _ (show a + b = c by lia)]; rw [comp]; rw [comp]
  dsimp
  rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [← Functor.map_comp]; rw [← unop_comp_assoc]; rw [Iso.inv_hom_id_app]
  dsim

中文:
引理 opEquiv_symm_comp
  结论: {a b : 整数}
  证明: by
  rw [opEquiv_symm_apply]; rw [opEquiv_symm_apply]; rw [opShiftFunctorEquivalence_add_unitIso_inv_app_eq _ _ _ _ (show a + b = c by lia)]; rw [comp]; rw [comp]
  dsimp
  rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [← Functor.map_comp]; rw [← unop_comp_assoc]; rw [Iso.inv_hom_id_app]
  dsim

Depends on / 依赖: Functor, Functor.map_comp, Functor.map_comp_assoc, Iso.inv_hom_id_app, NatTrans, NatTrans.naturality, NatTrans.naturality_assoc, id_comp, inv_hom_id_app, map_comp, map_comp_assoc, naturality, naturality_assoc, opEquiv_symm_apply, opShiftFunctorEquivalence_add_unitIso_inv_app_eq, unop_comp_assoc
-/
lemma opEquiv_symm_comp {a b : Int}
    (f : ShiftedHom (Opposite.op Z) (Opposite.op Y) a)
    (g : ShiftedHom (Opposite.op Y) (Opposite.op X) b)
    {c : Int} (h : b + a = c) :
    (opEquiv _).symm (f.comp g h) =
      ((opEquiv _).symm g).comp ((opEquiv _).symm f) (by lia) := by
  rw [opEquiv_symm_apply]; rw [opEquiv_symm_apply]; rw [opShiftFunctorEquivalence_add_unitIso_inv_app_eq _ _ _ _ (show a + b = c by lia)]; rw [comp]; rw [comp]
  dsimp
  rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [← Functor.map_comp]; rw [← unop_comp_assoc]; rw [Iso.inv_hom_id_app]
  dsimp
  rw [assoc]; rw [id_comp]; rw [Functor.map_comp]; rw [← NatTrans.naturality_assoc]; rw [← NatTrans.naturality]; rw [opEquiv_symm_apply]
  dsimp
  rw [← Functor.map_comp_assoc]; rw [← Functor.map_comp_assoc]; rw [← Functor.map_comp_assoc]
  rw [← unop_comp_assoc]
  erw [← NatTrans.naturality]
  rfl

/--
Definition of `opEquiv'` / `opEquiv'` 的定义

English:
definition opEquiv'
  signature: (n a a' : Int) (h : n + a = a')
  body: ((shiftFunctorAdd' C a n a' (by lia)).symm.app Y).homToEquiv.symm.trans (opEquiv n)

中文:
定义 opEquiv'
  签名: (n a a' : 整数) (h : n + a = a')
  定义体: ((shiftFunctorAdd' C a n a' (by lia)).symm.app Y).homToEquiv.symm.trans (opEquiv n)

Depends on / 依赖: homToEquiv, homToEquiv.symm.trans, opEquiv, shiftFunctorAdd, symm.app
-/
noncomputable def opEquiv' (n a a' : Int) (h : n + a = a') :
    ShiftedHom X Y a' ≃ (Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦n⟧) :=
  ((shiftFunctorAdd' C a n a' (by lia)).symm.app Y).homToEquiv.symm.trans (opEquiv n)

/--
lemma `opEquiv'_symm_apply` / 引理 `opEquiv'_symm_apply`

English:
lemma opEquiv'_symm_apply
  statement: {n a : Int} (f : Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦n⟧)
  proof: rfl

中文:
引理 opEquiv'_symm_apply
  结论: {n a : 整数} (f : Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦n⟧)
  证明: rfl
-/
lemma opEquiv'_symm_apply {n a : Int} (f : Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦n⟧)
    (a' : Int) (h : n + a = a') :
    (opEquiv' n a a' h).symm f =
      (opEquiv n).symm f ≫ (shiftFunctorAdd' C a n a' (by lia)).inv.app _ :=
  rfl

/--
lemma `opEquiv'_apply` / 引理 `opEquiv'_apply`

English:
lemma opEquiv'_apply
  given: {a' : Int} (f : ShiftedHom X Y a') (n a : Int) (h : n + a = a')
  proof: by
  rfl

中文:
引理 opEquiv'_apply
  条件: {a' : 整数} (f : ShiftedHom X Y a') (n a : 整数) (h : n + a = a')
  证明: by
  rfl
-/
lemma opEquiv'_apply {a' : Int} (f : ShiftedHom X Y a') (n a : Int) (h : n + a = a') :
    opEquiv' n a a' h f =
      opEquiv n (f ≫ (shiftFunctorAdd' C a n a' (by lia)).hom.app Y) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `opEquiv'_symm_op_opShiftFunctorEquivalence_counitIso_inv_app_op_shift` / 引理 `opEquiv'_symm_op_opShiftFunctorEquivalence_counitIso_inv_app_op_shift`

English:
lemma opEquiv'_symm_op_opShiftFunctorEquivalence_counitIso_inv_app_op_shift
  proof: by
  rw [opEquiv'_symm_apply]; rw [opEquiv_symm_apply]
  dsimp [comp]
  apply Quiver.Hom.op_inj
  simp only [assoc, Functor.map_comp, op_comp, Quiver.Hom.op_unop,
    opShiftFunctorEquivalence_unitIso_inv_naturality]
  erw [(opShiftFunctorEquivalence C n).inverse_counitInv_comp_assoc (Opposite.op Y)

中文:
引理 opEquiv'_symm_op_opShiftFunctorEquivalence_counitIso_inv_app_op_shift
  证明: by
  rw [opEquiv'_symm_apply]; rw [opEquiv_symm_apply]
  dsimp [comp]
  apply Quiver.Hom.op_inj
  simp only [assoc, Functor.map_comp, op_comp, Quiver.Hom.op_unop,
    opShiftFunctorEquivalence_unitIso_inv_naturality]
  erw [(opShiftFunctorEquivalence C n).inverse_counitInv_comp_assoc (Opposite.op Y)
-/
lemma opEquiv'_symm_op_opShiftFunctorEquivalence_counitIso_inv_app_op_shift
    {n m : Int} (f : ShiftedHom X Y n) (g : ShiftedHom Y Z m)
    (q : Int) (hq : n + m = q) :
    (opEquiv' n m q hq).symm
        (g.op ≫ (opShiftFunctorEquivalence C n).counitIso.inv.app _ ≫ f.op⟦n⟧') =
      f.comp g (by lia) := by
  rw [opEquiv'_symm_apply]; rw [opEquiv_symm_apply]
  dsimp [comp]
  apply Quiver.Hom.op_inj
  simp only [assoc, Functor.map_comp, op_comp, Quiver.Hom.op_unop,
    opShiftFunctorEquivalence_unitIso_inv_naturality]
  erw [(opShiftFunctorEquivalence C n).inverse_counitInv_comp_assoc (Opposite.op Y)]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `opEquiv'_symm_comp` / 引理 `opEquiv'_symm_comp`

English:
lemma opEquiv'_symm_comp
  statement: (f : Y ⟶ X) {n a : Int} (x : Opposite.op (Z⟦a⟧) ⟶ (Opposite.op X⟦n⟧))
  proof: Quiver.Hom.op_inj (by simp [opEquiv'_symm_apply, opEquiv_symm_apply])

中文:
引理 opEquiv'_symm_comp
  结论: (f : Y ⟶ X) {n a : 整数} (x : Opposite.op (Z⟦a⟧) ⟶ (Opposite.op X⟦n⟧))
  证明: Quiver.Hom.op_inj (by simp [opEquiv'_symm_apply, opEquiv_symm_apply])
-/
lemma opEquiv'_symm_comp (f : Y ⟶ X) {n a : Int} (x : Opposite.op (Z⟦a⟧) ⟶ (Opposite.op X⟦n⟧))
    (a' : Int) (h : n + a = a') :
    (opEquiv' n a a' h).symm (x ≫ f.op⟦n⟧') = f ≫ (opEquiv' n a a' h).symm x :=
  Quiver.Hom.op_inj (by simp [opEquiv'_symm_apply, opEquiv_symm_apply])

set_option backward.defeqAttrib.useBackward true in
/--
lemma `opEquiv'_zero_add_symm` / 引理 `opEquiv'_zero_add_symm`

English:
lemma opEquiv'_zero_add_symm
  given: (a : Int) (f : Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦(0 : Int)⟧)
  proof: by
  simp [opEquiv'_symm_apply, opEquiv_symm_apply, shiftFunctorAdd'_add_zero,
    opShiftFunctorEquivalence_zero_unitIso_inv_app]

中文:
引理 opEquiv'_zero_add_symm
  条件: (a : 整数) (f : Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦(0 : 整数)⟧)
  证明: by
  simp [opEquiv'_symm_apply, opEquiv_symm_apply, shiftFunctorAdd'_add_zero,
    opShiftFunctorEquivalence_zero_unitIso_inv_app]
-/
lemma opEquiv'_zero_add_symm (a : Int) (f : Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦(0 : Int)⟧) :
    (opEquiv' 0 a a (zero_add a)).symm f =
      ((shiftFunctorZero Cᵒᵖ Int).hom.app _).unop ≫ f.unop := by
  simp [opEquiv'_symm_apply, opEquiv_symm_apply, shiftFunctorAdd'_add_zero,
    opShiftFunctorEquivalence_zero_unitIso_inv_app]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `opEquiv'_add_symm` / 引理 `opEquiv'_add_symm`

English:
lemma opEquiv'_add_symm
  statement: (n m a a' a'' : Int) (ha' : n + a = a') (ha'' : m + a' = a'')
  proof: by
  simp only [opEquiv'_symm_apply, opEquiv_symm_apply,
    opShiftFunctorEquivalence_add_unitIso_inv_app_eq _ _ _ _ (add_comm n m)]
  dsimp
  simp only [assoc, Functor.map_comp, ← shiftFunctorAdd'_eq_shiftFunctorAdd,
    ← NatTrans.naturality_assoc,
    shiftFunctorAdd'_assoc_inv_app a n m a' (m +

中文:
引理 opEquiv'_add_symm
  结论: (n m a a' a'' : 整数) (ha' : n + a = a') (ha'' : m + a' = a'')
  证明: by
  simp only [opEquiv'_symm_apply, opEquiv_symm_apply,
    opShiftFunctorEquivalence_add_unitIso_inv_app_eq _ _ _ _ (add_comm n m)]
  dsimp
  simp only [assoc, Functor.map_comp, ← shiftFunctorAdd'_eq_shiftFunctorAdd,
    ← NatTrans.naturality_assoc,
    shiftFunctorAdd'_assoc_inv_app a n m a' (m +
-/
lemma opEquiv'_add_symm (n m a a' a'' : Int) (ha' : n + a = a') (ha'' : m + a' = a'')
    (x : (Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦m + n⟧)) :
    (opEquiv' (m + n) a a'' (by lia)).symm x =
      (opEquiv' m a' a'' ha'').symm ((opEquiv' n a a' ha').symm
        (x ≫ (shiftFunctorAdd Cᵒᵖ m n).hom.app _)).op := by
  simp only [opEquiv'_symm_apply, opEquiv_symm_apply,
    opShiftFunctorEquivalence_add_unitIso_inv_app_eq _ _ _ _ (add_comm n m)]
  dsimp
  simp only [assoc, Functor.map_comp, ← shiftFunctorAdd'_eq_shiftFunctorAdd,
    ← NatTrans.naturality_assoc,
    shiftFunctorAdd'_assoc_inv_app a n m a' (m + n) a'' (by lia) (by lia) (by lia)]
  rfl

section Preadditive

variable [Preadditive C] [forall (n : Int), (shiftFunctor C n).Additive]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `opEquiv_symm_add` / 引理 `opEquiv_symm_add`

English:
lemma opEquiv_symm_add
  given: {n : Int} (x y : ShiftedHom (Opposite.op Y) (Opposite.op X) n)
  proof: by
  dsimp [opEquiv_symm_apply]
  rw [← Preadditive.comp_add]; rw [← Functor.map_add]

中文:
引理 opEquiv_symm_add
  条件: {n : 整数} (x y : ShiftedHom (Opposite.op Y) (Opposite.op X) n)
  证明: by
  dsimp [opEquiv_symm_apply]
  rw [← Preadditive.comp_add]; rw [← Functor.map_add]

Depends on / 依赖: Functor, Functor.map_add, Preadditive, Preadditive.comp_add, comp_add, map_add, opEquiv_symm_apply
-/
lemma opEquiv_symm_add {n : Int} (x y : ShiftedHom (Opposite.op Y) (Opposite.op X) n) :
    (opEquiv n).symm (x + y) = (opEquiv n).symm x + (opEquiv n).symm y := by
  dsimp [opEquiv_symm_apply]
  rw [← Preadditive.comp_add]; rw [← Functor.map_add]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `opEquiv'_symm_add` / 引理 `opEquiv'_symm_add`

English:
lemma opEquiv'_symm_add
  statement: {n a : Int} (x y : (Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦n⟧))
  proof: by
  dsimp [opEquiv']
  rw [opEquiv_symm_add]; rw [Preadditive.add_comp]

中文:
引理 opEquiv'_symm_add
  结论: {n a : 整数} (x y : (Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦n⟧))
  证明: by
  dsimp [opEquiv']
  rw [opEquiv_symm_add]; rw [Preadditive.add_comp]
-/
lemma opEquiv'_symm_add {n a : Int} (x y : (Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦n⟧))
    (a' : Int) (h : n + a = a') :
    (opEquiv' n a a' h).symm (x + y) =
      (opEquiv' n a a' h).symm x + (opEquiv' n a a' h).symm y := by
  dsimp [opEquiv']
  rw [opEquiv_symm_add]; rw [Preadditive.add_comp]

end Preadditive

end ShiftedHom

end CategoryTheory
