/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Triangulated.Rotate
public import Mathlib.Algebra.Ring.NegOnePow

/-!
# The shift on the category of triangles

In this file, it is shown that if `C` is a preadditive category with
a shift by `ℤ`, then the category of triangles `Triangle C` is also
endowed with a shift. We also show that rotating triangles three times
identifies with the shift by `1`.

The shift on the category of triangles was also obtained by Adam Topaz,
Johan Commelin and Andrew Yang during the Liquid Tensor Experiment.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

universe v u

namespace CategoryTheory

open Category Preadditive

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasShift C Int]
  [forall (n : Int), (CategoryTheory.shiftFunctor C n).Additive]

namespace Pretriangulated

attribute [local simp] Triangle.eqToHom_hom₁ Triangle.eqToHom_hom₂ Triangle.eqToHom_hom₃
  shiftFunctorAdd_zero_add_hom_app shiftFunctorAdd_add_zero_hom_app
  shiftFunctorAdd'_eq_shiftFunctorAdd shift_shiftFunctorCompIsoId_inv_app

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The shift functor `Triangle C ⥤ Triangle C` by `n : ℤ` sends a triangle
to the triangle obtained by shifting the objects by `n` in `C` and by
multiplying the three morphisms by `(-1)^n`. -/
@[simps]
/--
Definition of `Triangle.shiftFunctor` / `Triangle.shiftFunctor` 的定义

English:
definition Triangle.shiftFunctor
  signature: (n : Int)
  body: Triangle.mk (n.negOnePow • T.mor₁⟦n⟧') (n.negOnePow • T.mor₂⟦n⟧')
    (n.negOnePow • T.mor₃⟦n⟧' ≫ (shiftFunctorComm C 1 n).hom.app T.obj₁)
  map f :=
    { hom₁ := f.hom₁⟦n⟧'
      hom₂ := f.hom₂⟦n⟧'
      hom₃ := f.hom₃⟦n⟧'
      comm₁ := by
        dsimp
        simp only [Linear.units_smul_comp, 

中文:
定义 Triangle.shiftFunctor
  签名: (n : 整数)
  定义体: Triangle.mk (n.negOnePow • T.mor₁⟦n⟧') (n.negOnePow • T.mor₂⟦n⟧')
    (n.negOnePow • T.mor₃⟦n⟧' ≫ (shiftFunctorComm C 1 n).hom.app T.obj₁)
  map f :=
    { hom₁ := f.hom₁⟦n⟧'
      hom₂ := f.hom₂⟦n⟧'
      hom₃ := f.hom₃⟦n⟧'
      comm₁ := by
        dsimp
        simp only [Linear.units_smul_comp, 

Depends on / 依赖: T.mor, Triangle, Triangle.mk, n.negOnePow, negOnePow
-/
noncomputable def Triangle.shiftFunctor (n : Int) : Triangle C ⥤ Triangle C where
  obj T := Triangle.mk (n.negOnePow • T.mor₁⟦n⟧') (n.negOnePow • T.mor₂⟦n⟧')
    (n.negOnePow • T.mor₃⟦n⟧' ≫ (shiftFunctorComm C 1 n).hom.app T.obj₁)
  map f :=
    { hom₁ := f.hom₁⟦n⟧'
      hom₂ := f.hom₂⟦n⟧'
      hom₃ := f.hom₃⟦n⟧'
      comm₁ := by
        dsimp
        simp only [Linear.units_smul_comp, Linear.comp_units_smul, ← Functor.map_comp, f.comm₁]
      comm₂ := by
        dsimp
        simp only [Linear.units_smul_comp, Linear.comp_units_smul, ← Functor.map_comp, f.comm₂]
      comm₃ := by
        dsimp
        rw [Linear.units_smul_comp]; rw [Linear.comp_units_smul]; rw [← Functor.map_comp_assoc]; rw [← f.comm₃]; rw [Functor.map_comp]; rw [assoc]; rw [assoc]; rw [dsimp% (shiftFunctorComm C 1 n).hom.naturality] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism `Triangle.shiftFunctor C 0 ≅ 𝟭 (Triangle C)`. -/
@[simps!]
/--
Definition of `Triangle.shiftFunctorZero` / `Triangle.shiftFunctorZero` 的定义

English:
definition Triangle.shiftFunctorZero
  signature: : Triangle.shiftFunctor C 0 ≅ 𝟭 _
  body: NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ ((CategoryTheory.shiftFunctorZero C Int).app _)
      ((CategoryTheory.shiftFunctorZero C Int).app _) ((CategoryTheory.shiftFunctorZero C Int).app _)
      (by simp) (by simp) (by
        dsimp
        simp only [one_smul, assoc, shiftFunctorComm_

中文:
定义 Triangle.shiftFunctorZero
  签名: : Triangle.shiftFunctor C 0 ≅ 𝟭 _
  定义体: NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ ((CategoryTheory.shiftFunctorZero C Int).app _)
      ((CategoryTheory.shiftFunctorZero C Int).app _) ((CategoryTheory.shiftFunctorZero C Int).app _)
      (by simp) (by simp) (by
        dsimp
        simp only [one_smul, assoc, shiftFunctorComm_

Depends on / 依赖: CategoryTheory, CategoryTheory.shiftFunctorZero, Functor, Functor.id_map, Functor.id_obj, Functor.map_comp, Functor.map_id, Iso.inv_hom_id_app, NatIso, NatIso.ofComponents, NatTrans, NatTrans.naturality, Triangle, Triangle.isoMk, cat_disch, comp_id, id_map, id_obj, inv_hom_id_app, map_comp
-/
noncomputable def Triangle.shiftFunctorZero : Triangle.shiftFunctor C 0 ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ ((CategoryTheory.shiftFunctorZero C Int).app _)
      ((CategoryTheory.shiftFunctorZero C Int).app _) ((CategoryTheory.shiftFunctorZero C Int).app _)
      (by simp) (by simp) (by
        dsimp
        simp only [one_smul, assoc, shiftFunctorComm_zero_hom_app,
          ← Functor.map_comp, Iso.inv_hom_id_app, Functor.id_obj, Functor.map_id,
          comp_id, NatTrans.naturality, Functor.id_map]))
    (by cat_disch)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism
`Triangle.shiftFunctor C n ≅ Triangle.shiftFunctor C a ⋙ Triangle.shiftFunctor C b`
when `a + b = n`. -/
@[simps!]
/--
Definition of `Triangle.shiftFunctorAdd'` / `Triangle.shiftFunctorAdd'` 的定义

English:
definition Triangle.shiftFunctorAdd'
  signature: (a b n : Int) (h : a + b = n)
  body: NatIso.ofComponents
    (fun T => Triangle.isoMk _ _
      ((CategoryTheory.shiftFunctorAdd' C a b n h).app _)
      ((CategoryTheory.shiftFunctorAdd' C a b n h).app _)
      ((CategoryTheory.shiftFunctorAdd' C a b n h).app _)
      (by
        subst h
        dsimp
        rw [Linear.units_smul_com

中文:
定义 Triangle.shiftFunctorAdd'
  签名: (a b n : 整数) (h : a + b = n)
  定义体: NatIso.ofComponents
    (fun T => Triangle.isoMk _ _
      ((CategoryTheory.shiftFunctorAdd' C a b n h).app _)
      ((CategoryTheory.shiftFunctorAdd' C a b n h).app _)
      ((CategoryTheory.shiftFunctorAdd' C a b n h).app _)
      (by
        subst h
        dsimp
        rw [Linear.units_smul_com

Depends on / 依赖: CategoryTheory, CategoryTheory.shiftFunctorAdd, Functor, Functor.comp_map, Functor.map_units_smul, Int.negOnePow_add, Linear, Linear.comp_units_smul, Linear.units_smul_comp, NatIso, NatIso.ofComponents, NatTra, NatTrans, NatTrans.naturality, Triangle, Triangle.isoMk, comp_map, comp_units_smul, map_units_smul, mul_comm
-/
noncomputable def Triangle.shiftFunctorAdd' (a b n : Int) (h : a + b = n) :
    Triangle.shiftFunctor C n ≅ Triangle.shiftFunctor C a ⋙ Triangle.shiftFunctor C b :=
  NatIso.ofComponents
    (fun T => Triangle.isoMk _ _
      ((CategoryTheory.shiftFunctorAdd' C a b n h).app _)
      ((CategoryTheory.shiftFunctorAdd' C a b n h).app _)
      ((CategoryTheory.shiftFunctorAdd' C a b n h).app _)
      (by
        subst h
        dsimp
        rw [Linear.units_smul_comp]; rw [NatTrans.naturality]; rw [Linear.comp_units_smul]; rw [Functor.comp_map]; rw [Functor.map_units_smul]; rw [Linear.comp_units_smul]; rw [smul_smul]; rw [Int.negOnePow_add]; rw [mul_comm])
      (by
        subst h
        dsimp
        rw [Linear.units_smul_comp]; rw [NatTrans.naturality]; rw [Linear.comp_units_smul]; rw [Functor.comp_map]; rw [Functor.map_units_smul]; rw [Linear.comp_units_smul]; rw [smul_smul]; rw [Int.negOnePow_add]; rw [mul_comm])
      (by
        subst h
        dsimp
        rw [Linear.units_smul_comp]; rw [Linear.comp_units_smul]; rw [Functor.map_units_smul]; rw [Linear.units_smul_comp]; rw [Linear.comp_units_smul]; rw [smul_smul]; rw [assoc]; rw [Functor.map_comp]; rw [assoc]; rw [← dsimp% (CategoryTheory.shiftFunctorAdd' C a b (a + b) rfl).hom.naturality_assoc]
        simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, Int.negOnePow_add,
          shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd_hom_app, add_comm a]))
    (by intros; ext <;> simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `rotateRotateRotateIso` / `rotateRotateRotateIso` 的定义

English:
definition rotateRotateRotateIso
  signature: :
  body: NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp))
    (by cat_disch)

中文:
定义 rotateRotateRotateIso
  签名: :
  定义体: NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp))
    (by cat_disch)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, Triangle, Triangle.isoMk, cat_disch, ofComponents
-/
noncomputable def rotateRotateRotateIso :
    rotate C ⋙ rotate C ⋙ rotate C ≅ Triangle.shiftFunctor C 1 :=
  NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp))
    (by cat_disch)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `invRotateInvRotateInvRotateIso` / `invRotateInvRotateInvRotateIso` 的定义

English:
definition invRotateInvRotateInvRotateIso
  signature: :
  body: NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp)
      (by simp)
      (by
        dsimp [shiftFunctorCompIsoId]
        simp [shiftFunctorComm_eq C _ _ _ (add_neg_cancel (1 : Int))]))
    (by cat_disch)

中文:
定义 invRotateInvRotateInvRotateIso
  签名: :
  定义体: NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp)
      (by simp)
      (by
        dsimp [shiftFunctorCompIsoId]
        simp [shiftFunctorComm_eq C _ _ _ (add_neg_cancel (1 : Int))]))
    (by cat_disch)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, Triangle, Triangle.isoMk, add_neg_cancel, cat_disch, ofComponents, shiftFunctorComm_eq, shiftFunctorCompIsoId
-/
noncomputable def invRotateInvRotateInvRotateIso :
    invRotate C ⋙ invRotate C ⋙ invRotate C ≅ Triangle.shiftFunctor C (-1) :=
  NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp)
      (by simp)
      (by
        dsimp [shiftFunctorCompIsoId]
        simp [shiftFunctorComm_eq C _ _ _ (add_neg_cancel (1 : Int))]))
    (by cat_disch)

/--
Definition of `invRotateIsoRotateRotateShiftFunctorNegOne` / `invRotateIsoRotateRotateShiftFunctorNegOne` 的定义

English:
definition invRotateIsoRotateRotateShiftFunctorNegOne
  signature: :
  body: calc
    invRotate C ≅ invRotate C ⋙ 𝟭 _ := (Functor.rightUnitor _).symm
    _ ≅ invRotate C ⋙ Triangle.shiftFunctor C 0 :=
          Functor.isoWhiskerLeft _ (Triangle.shiftFunctorZero C).symm
    _ ≅ invRotate C ⋙ Triangle.shiftFunctor C 1 ⋙ Triangle.shiftFunctor C (-1) :=
          Functor.isoWhi

中文:
定义 invRotateIsoRotateRotateShiftFunctorNegOne
  签名: :
  定义体: calc
    invRotate C ≅ invRotate C ⋙ 𝟭 _ := (Functor.rightUnitor _).symm
    _ ≅ invRotate C ⋙ Triangle.shiftFunctor C 0 :=
          Functor.isoWhiskerLeft _ (Triangle.shiftFunctorZero C).symm
    _ ≅ invRotate C ⋙ Triangle.shiftFunctor C 1 ⋙ Triangle.shiftFunctor C (-1) :=
          Functor.isoWhi

Depends on / 依赖: Functor, Functor.isoWhiskerLeft, Functor.isoWhiskerRight, Functor.rightUnitor, Triangle, Triangle.shiftFunctor, Triangle.shiftFunctorAdd, Triangle.shiftFunctorZero, add_neg_cancel, invRotate, isoWhiskerLeft, isoWhiskerRight, rightUnitor, rotate, rotateRotateRotateIso, shiftFunctor, shiftFunctorAdd, shiftFunctorZero
-/
noncomputable def invRotateIsoRotateRotateShiftFunctorNegOne :
    invRotate C ≅ rotate C ⋙ rotate C ⋙ Triangle.shiftFunctor C (-1) :=
  calc
    invRotate C ≅ invRotate C ⋙ 𝟭 _ := (Functor.rightUnitor _).symm
    _ ≅ invRotate C ⋙ Triangle.shiftFunctor C 0 :=
          Functor.isoWhiskerLeft _ (Triangle.shiftFunctorZero C).symm
    _ ≅ invRotate C ⋙ Triangle.shiftFunctor C 1 ⋙ Triangle.shiftFunctor C (-1) :=
          Functor.isoWhiskerLeft _ (Triangle.shiftFunctorAdd' C 1 (-1) 0 (add_neg_cancel 1))
    _ ≅ invRotate C ⋙ (rotate C ⋙ rotate C ⋙ rotate C) ⋙ Triangle.shiftFunctor C (-1) :=
          Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (rotateRotateRotateIso C).symm _)
    _ ≅ (invRotate C ⋙ rotate C) ⋙ rotate C ⋙ rotate C ⋙ Triangle.shiftFunctor C (-1) :=
          Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft _ (Functor.associator _ _ _)) ≪≫ (Functor.associator _ _ _).symm
    _ ≅ 𝟭 _ ⋙ rotate C ⋙ rotate C ⋙ Triangle.shiftFunctor C (-1) :=
          Functor.isoWhiskerRight (triangleRotation C).counitIso _
    _ ≅ _ := Functor.leftUnitor _

namespace Triangle

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasShift (Triangle C) Int
  body: hasShiftMk (Triangle C) Int
    { F := Triangle.shiftFunctor C
      zero := Triangle.shiftFunctorZero C
      add := fun a b => Triangle.shiftFunctorAdd' C a b _ rfl
      assoc_hom_app := fun a b c T => by
        ext
        all_goals
          dsimp
          rw [← shiftFunctorAdd'_assoc_hom_app

中文:
实例 :
  签名: HasShift (Triangle C) 整数
  定义体: hasShiftMk (Triangle C) Int
    { F := Triangle.shiftFunctor C
      zero := Triangle.shiftFunctorZero C
      add := fun a b => Triangle.shiftFunctorAdd' C a b _ rfl
      assoc_hom_app := fun a b c T => by
        ext
        all_goals
          dsimp
          rw [← shiftFunctorAdd'_assoc_hom_app

Depends on / 依赖: CategoryTheory, CategoryTheory.shiftFunctorAdd, Triangle, Triangle.shiftFunctor, Triangle.shiftFunctorAdd, Triangle.shiftFunctorZero, _assoc_hom_app, add_assoc, all_goals, assoc_hom_app, hasShiftMk, shiftFunctor, shiftFunctorAdd, shiftFunctorZero
-/
noncomputable instance : HasShift (Triangle C) Int :=
  hasShiftMk (Triangle C) Int
    { F := Triangle.shiftFunctor C
      zero := Triangle.shiftFunctorZero C
      add := fun a b => Triangle.shiftFunctorAdd' C a b _ rfl
      assoc_hom_app := fun a b c T => by
        ext
        all_goals
          dsimp
          rw [← shiftFunctorAdd'_assoc_hom_app a b c _ _ _ rfl rfl (add_assoc a b c)]
          dsimp only [CategoryTheory.shiftFunctorAdd']
          simp }

@[simp]
/--
lemma `shiftFunctor_eq` / 引理 `shiftFunctor_eq`

English:
lemma shiftFunctor_eq
  given: (n : Int)
  proof: rfl

@[simp]

中文:
引理 shiftFunctor_eq
  条件: (n : 整数)
  证明: rfl

@[simp]
-/
lemma shiftFunctor_eq (n : Int) :
    CategoryTheory.shiftFunctor (Triangle C) n = Triangle.shiftFunctor C n := rfl

@[simp]
/--
lemma `shiftFunctorZero_eq` / 引理 `shiftFunctorZero_eq`

English:
lemma shiftFunctorZero_eq
  proof: ShiftMkCore.shiftFunctorZero_eq _

@[simp]

中文:
引理 shiftFunctorZero_eq
  证明: ShiftMkCore.shiftFunctorZero_eq _

@[simp]

Depends on / 依赖: ShiftMkCore, ShiftMkCore.shiftFunctorZero_eq, shiftFunctorZero_eq
-/
lemma shiftFunctorZero_eq :
    CategoryTheory.shiftFunctorZero (Triangle C) Int = Triangle.shiftFunctorZero C :=
  ShiftMkCore.shiftFunctorZero_eq _

@[simp]
/--
lemma `shiftFunctorAdd_eq` / 引理 `shiftFunctorAdd_eq`

English:
lemma shiftFunctorAdd_eq
  given: (a b : Int)
  proof: ShiftMkCore.shiftFunctorAdd_eq _ _ _

@[simp]

中文:
引理 shiftFunctorAdd_eq
  条件: (a b : 整数)
  证明: ShiftMkCore.shiftFunctorAdd_eq _ _ _

@[simp]

Depends on / 依赖: ShiftMkCore, ShiftMkCore.shiftFunctorAdd_eq, shiftFunctorAdd_eq
-/
lemma shiftFunctorAdd_eq (a b : Int) :
    CategoryTheory.shiftFunctorAdd (Triangle C) a b =
      Triangle.shiftFunctorAdd' C a b _ rfl :=
  ShiftMkCore.shiftFunctorAdd_eq _ _ _

@[simp]
/--
lemma `shiftFunctorAdd'_eq` / 引理 `shiftFunctorAdd'_eq`

English:
lemma shiftFunctorAdd'_eq
  given: (a b c : Int) (h : a + b = c)
  proof: by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd]
  apply shiftFunctorAdd_eq

中文:
引理 shiftFunctorAdd'_eq
  条件: (a b c : 整数) (h : a + b = c)
  证明: by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd]
  apply shiftFunctorAdd_eq

Depends on / 依赖: _eq_shiftFunctorAdd, shiftFunctorAdd, shiftFunctorAdd_eq
-/
lemma shiftFunctorAdd'_eq (a b c : Int) (h : a + b = c) :
    CategoryTheory.shiftFunctorAdd' (Triangle C) a b c h =
      Triangle.shiftFunctorAdd' C a b c h := by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd]
  apply shiftFunctorAdd_eq

end Triangle

end Pretriangulated

end CategoryTheory
