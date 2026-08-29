/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Center.Basic
public import Mathlib.CategoryTheory.Shift.CommShift

/-!
# Twisting a shift

Given a category `C` equipped with a shift by a monoid `A`, we introduce
a structure `t : TwistShiftData C A` which consists of a collection of
invertible elements in the center of the category `C` (typically, `C` will
be preadditive, and these will be signs), which allow to introduce a type
synonym category `t.Category` with identical shift functors as `C` but where
the isomorphisms `shiftFunctorAdd` have been modified.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] (A : Type w) [AddMonoid A] [HasShift C A]

/--
Definition of `TwistShiftData` / `TwistShiftData` 的定义

English:
structure TwistShiftData
  parameters: where
  axioms and operations (4):
    - z((a b : A)) : (CatCenter C)ˣ
    - z_zero_zero : z 0 0 = 1  [default: by cat_disch]
    - assoc((a b c : A)) : z (a + b) c * z a b = z a (b + c) * z b c  [default: by cat_disch]
    - commShift((a b : A)) : NatTrans.CommShift (z a b).val A  [default: by infer_instance]

中文:
结构 TwistShiftData
  参数: where
  公理与运算 (4 个):
    - z((a b : A)) : (CatCenter C)ˣ
    - z_zero_zero : z 0 0 = 1  [默认: by cat_disch]
    - assoc((a b c : A)) : z (a + b) c * z a b = z a (b + c) * z b c  [默认: by cat_disch]
    - commShift((a b : A)) : 自然变换.交换Shift (z a b).val A  [默认: by infer_instance]

Depends on / 依赖: CommShift, NatTrans, NatTrans.CommShift, cat_disch, commShift, infer_instance
-/
structure TwistShiftData where
  /-- The invertible elements in the center of `C` which are used to
  modify the `shiftFunctorAdd` isomorphisms. -/
  z (a b : A) : (CatCenter C)ˣ
  z_zero_zero : z 0 0 = 1 := by cat_disch
  assoc (a b c : A) : z (a + b) c * z a b = z a (b + c) * z b c := by cat_disch
  commShift (a b : A) : NatTrans.CommShift (z a b).val A := by infer_instance

namespace TwistShiftData

variable {C A} (t : TwistShiftData C A)

attribute [local simp] z_zero_zero

@[simp]
/--
lemma `z_zero_right` / 引理 `z_zero_right`

English:
lemma z_zero_right
  given: (a : A)
  statement: t.z a 0 = 1
  proof: by simpa using t.assoc a 0 0

@[simp]

中文:
引理 z_zero_right
  条件: (a : A)
  结论: t.z a 0 = 1
  证明: by simpa using t.assoc a 0 0

@[simp]

Depends on / 依赖: t.assoc
-/
lemma z_zero_right (a : A) : t.z a 0 = 1 := by simpa using t.assoc a 0 0

@[simp]
/--
lemma `z_zero_left` / 引理 `z_zero_left`

English:
lemma z_zero_left
  given: (b : A)
  statement: t.z 0 b = 1
  proof: by simpa using t.assoc 0 0 b

中文:
引理 z_zero_left
  条件: (b : A)
  结论: t.z 0 b = 1
  证明: by simpa using t.assoc 0 0 b

Depends on / 依赖: t.assoc
-/
lemma z_zero_left (b : A) : t.z 0 b = 1 := by simpa using t.assoc 0 0 b

attribute [instance] commShift

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `shift_z_app` / 引理 `shift_z_app`

English:
lemma shift_z_app
  given: (a b c : A) (X : C)
  proof: by
  simpa using NatTrans.shift_app_comm (t.z a b).val c X

中文:
引理 shift_z_app
  条件: (a b c : A) (X : C)
  证明: by
  simpa using NatTrans.shift_app_comm (t.z a b).val c X

Depends on / 依赖: NatTrans, NatTrans.shift_app_comm, shift_app_comm
-/
lemma shift_z_app (a b c : A) (X : C) :
    ((t.z a b).val.app X)⟦c⟧' = (t.z a b).val.app (X⟦c⟧) := by
  simpa using NatTrans.shift_app_comm (t.z a b).val c X

/-- Given `t : TwistShiftData C A`, this is a type synonym for the category `C`,
which the same shift functors as `C` but where the `shiftFunctorAdd` isomorphisms
have been modified using `t`. -/
@[nolint unusedArguments]
/--
Definition of `Category` / `Category` 的定义

English:
definition Category
  signature: (_ : TwistShiftData C A)
  body: C

中文:
定义 范畴
  签名: (_ : TwistShiftData C A)
  定义体: C
-/
protected def Category (_ : TwistShiftData C A) : Type u := C

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category t.Category
  body: inferInstanceAs (Category C)

中文:
实例 :
  签名: 范畴 t.范畴
  定义体: inferInstanceAs (Category C)

Depends on / 依赖: Category
-/
instance : Category t.Category := inferInstanceAs (Category C)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `shiftMkCore` / `shiftMkCore` 的定义

English:
definition shiftMkCore
  signature: : ShiftMkCore t.Category A where
  body: shiftFunctor C a
  zero := shiftFunctorZero C A
  add a b := NatIso.ofComponents (fun X => t.z a b • (shiftFunctorAdd C a b).app X) (by
    simp [CatCenter.naturality_assoc, CatCenter.naturality, CatCenter.smul_iso_hom_eq])
  add_zero_hom_app := by simp [shiftFunctorAdd_add_zero_hom_app, CatCenter.smul_iso_hom_eq]
  zero_add_hom_app := by simp [shiftFunctorAdd_zero_add_hom_app, CatCenter.smul_iso_hom_eq]
  assoc_hom_app a b c X := by
    dsimp
    simp only [Functor.map_comp, Category.assoc, CatCenter.smul_iso_hom_eq]
    rw [CatCenter.naturality]; rw [CatCenter.naturality_assoc]; rw [CatCenter.naturality_assoc]; rw [CatCenter.naturality_assoc]; rw [CatCenter.naturality_assoc]; rw [CatCenter.naturality_assoc]; rw [t.shift_z_app]; rw [CatCenter.naturality]; rw [CatCenter.naturality_assoc]; rw [← CatCenter.mul_app_assoc]; rw [← CatCenter.mul_app_assoc]; rw [← Units.val_mul]; rw [← Units.val_mul]; rw [t.assoc a b c]
    simp [shiftFunctorAdd_assoc_hom_app (C := C) a b c X, shiftFunctorAdd']

中文:
定义 shiftMkCore
  签名: : ShiftMkCore t.范畴 A where
  定义体: shiftFunctor C a
  zero := shiftFunctorZero C A
  add a b := NatIso.ofComponents (fun X => t.z a b • (shiftFunctorAdd C a b).app X) (by
    simp [CatCenter.naturality_assoc, CatCenter.naturality, CatCenter.smul_iso_hom_eq])
  add_zero_hom_app := by simp [shiftFunctorAdd_add_zero_hom_app, CatCenter.smul_iso_hom_eq]
  zero_add_hom_app := by simp [shiftFunctorAdd_zero_add_hom_app, CatCenter.smul_iso_hom_eq]
  assoc_hom_app a b c X := by
    dsimp
    simp only [Functor.map_comp, Category.assoc, CatCenter.smul_iso_hom_eq]
    rw [CatCenter.naturality]; rw [CatCenter.naturality_assoc]; rw [CatCenter.naturality_assoc]; rw [CatCenter.naturality_assoc]; rw [CatCenter.naturality_assoc]; rw [CatCenter.naturality_assoc]; rw [t.shift_z_app]; rw [CatCenter.naturality]; rw [CatCenter.naturality_assoc]; rw [← CatCenter.mul_app_assoc]; rw [← CatCenter.mul_app_assoc]; rw [← Units.val_mul]; rw [← Units.val_mul]; rw [t.assoc a b c]
    simp [shiftFunctorAdd_assoc_hom_app (C := C) a b c X, shiftFunctorAdd']

Depends on / 依赖: shiftFunctor
-/
def shiftMkCore : ShiftMkCore t.Category A where
  F a := shiftFunctor C a
  zero := shiftFunctorZero C A
  add a b := NatIso.ofComponents (fun X => t.z a b • (shiftFunctorAdd C a b).app X) (by
    simp [CatCenter.naturality_assoc, CatCenter.naturality, CatCenter.smul_iso_hom_eq])
  add_zero_hom_app := by simp [shiftFunctorAdd_add_zero_hom_app, CatCenter.smul_iso_hom_eq]
  zero_add_hom_app := by simp [shiftFunctorAdd_zero_add_hom_app, CatCenter.smul_iso_hom_eq]
  assoc_hom_app a b c X := by
    dsimp
    simp only [Functor.map_comp, Category.assoc, CatCenter.smul_iso_hom_eq]
    rw [CatCenter.naturality]; rw [CatCenter.naturality_assoc]; rw [CatCenter.naturality_assoc]; rw [CatCenter.naturality_assoc]; rw [CatCenter.naturality_assoc]; rw [CatCenter.naturality_assoc]; rw [t.shift_z_app]; rw [CatCenter.naturality]; rw [CatCenter.naturality_assoc]; rw [← CatCenter.mul_app_assoc]; rw [← CatCenter.mul_app_assoc]; rw [← Units.val_mul]; rw [← Units.val_mul]; rw [t.assoc a b c]
    simp [shiftFunctorAdd_assoc_hom_app (C := C) a b c X, shiftFunctorAdd']

/--
Instance `hasShift` / 实例 `hasShift`

English:
instance hasShift
  signature: : HasShift t.Category A
  body: hasShiftMk _ _ (shiftMkCore t)

中文:
实例 hasShift
  签名: : 有Shift t.范畴 A
  定义体: hasShiftMk _ _ (shiftMkCore t)

Depends on / 依赖: hasShiftMk, shiftMkCore
-/
instance hasShift : HasShift t.Category A := hasShiftMk _ _ (shiftMkCore t)

/--
Definition of `shiftIso` / `shiftIso` 的定义

English:
definition shiftIso
  signature: (m : A)
  body: Iso.refl _

中文:
定义 shiftIso
  签名: (m : A)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
noncomputable def shiftIso (m : A) : shiftFunctor t.Category m ≅ shiftFunctor C m :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/--
lemma `shiftFunctor_map` / 引理 `shiftFunctor_map`

English:
lemma shiftFunctor_map
  given: {X Y : t.Category} (f : X ⟶ Y) (m : A)
  proof: by
  simp

中文:
引理 shiftFunctor_map
  条件: {X Y : t.范畴} (f : X ⟶ Y) (m : A)
  证明: by
  simp
-/
lemma shiftFunctor_map {X Y : t.Category} (f : X ⟶ Y) (m : A) :
    (shiftFunctor t.Category m).map f =
      (t.shiftIso m).hom.app X ≫ (shiftFunctor C m).map f ≫ (t.shiftIso m).inv.app Y := by
  simp

/--
lemma `shiftFunctorZero_hom_app` / 引理 `shiftFunctorZero_hom_app`

English:
lemma shiftFunctorZero_hom_app
  given: (X : t.Category)
  proof: (Category.id_comp _).symm

中文:
引理 shiftFunctorZero_hom_app
  条件: (X : t.范畴)
  证明: (Category.id_comp _).symm

Depends on / 依赖: Category, Category.id_comp, id_comp
-/
lemma shiftFunctorZero_hom_app (X : t.Category) :
    (shiftFunctorZero t.Category A).hom.app X =
      (shiftIso t (0 : A)).hom.app X ≫ (shiftFunctorZero C A).hom.app X :=
  (Category.id_comp _).symm

/--
lemma `shiftFunctorZero_inv_app` / 引理 `shiftFunctorZero_inv_app`

English:
lemma shiftFunctorZero_inv_app
  given: (X : t.Category)
  proof: (Category.comp_id _).symm

中文:
引理 shiftFunctorZero_inv_app
  条件: (X : t.范畴)
  证明: (Category.comp_id _).symm

Depends on / 依赖: Category, Category.comp_id, comp_id
-/
lemma shiftFunctorZero_inv_app (X : t.Category) :
    (shiftFunctorZero t.Category A).inv.app X =
      (shiftFunctorZero C A).inv.app X ≫ (shiftIso t (0 : A)).inv.app X :=
  (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `shiftFunctorAdd'_hom_app` / 引理 `shiftFunctorAdd'_hom_app`

English:
lemma shiftFunctorAdd'_hom_app
  given: (i j k : A) (h : i + j = k) (X : t.Category)
  proof: by
  have : (shiftFunctorAdd' t.Category i j k h).hom.app X =
      (t.z i j).val • (shiftFunctorAdd' C i j k h).hom.app X := by
    dsimp [shiftFunctorAdd']
    cat_disch
  rw [this]
  congr
  change _ = 𝟙 _ ≫ _ ≫ (shiftFunctor C j).map (𝟙 _) ≫ 𝟙 _
  simp

中文:
引理 shiftFunctorAdd'_hom_app
  条件: (i j k : A) (h : i + j = k) (X : t.范畴)
  证明: by
  have : (shiftFunctorAdd' t.Category i j k h).hom.app X =
      (t.z i j).val • (shiftFunctorAdd' C i j k h).hom.app X := by
    dsimp [shiftFunctorAdd']
    cat_disch
  rw [this]
  congr
  change _ = 𝟙 _ ≫ _ ≫ (shiftFunctor C j).map (𝟙 _) ≫ 𝟙 _
  simp

Depends on / 依赖: Category, cat_disch, hom.app, shiftFunctor, shiftFunctorAdd, t.Category
-/
lemma shiftFunctorAdd'_hom_app (i j k : A) (h : i + j = k) (X : t.Category) :
    (shiftFunctorAdd' t.Category i j k h).hom.app X =
      (t.z i j).val • (t.shiftIso k).hom.app X ≫
        (shiftFunctorAdd' C i j k h).hom.app X ≫
        (shiftFunctor C j).map ((t.shiftIso i).inv.app X) ≫ (t.shiftIso j).inv.app _ := by
  have : (shiftFunctorAdd' t.Category i j k h).hom.app X =
      (t.z i j).val • (shiftFunctorAdd' C i j k h).hom.app X := by
    dsimp [shiftFunctorAdd']
    cat_disch
  rw [this]
  congr
  change _ = 𝟙 _ ≫ _ ≫ (shiftFunctor C j).map (𝟙 _) ≫ 𝟙 _
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `shiftFunctorAdd'_inv_app` / 引理 `shiftFunctorAdd'_inv_app`

English:
lemma shiftFunctorAdd'_inv_app
  given: (i j k : A) (h : i + j = k) (X : t.Category)
  proof: by
  have : (shiftFunctorAdd' t.Category i j k h).inv.app X =
      ((t.z i j)⁻¹).val • (shiftFunctorAdd' C i j k h).inv.app X := by
    dsimp [shiftFunctorAdd']
    cat_disch
  rw [this]
  congr
  change _ = 𝟙 _ ≫ (shiftFunctor C j).map (𝟙 _) ≫ _ ≫ 𝟙 _
  simp

中文:
引理 shiftFunctorAdd'_inv_app
  条件: (i j k : A) (h : i + j = k) (X : t.范畴)
  证明: by
  have : (shiftFunctorAdd' t.Category i j k h).inv.app X =
      ((t.z i j)⁻¹).val • (shiftFunctorAdd' C i j k h).inv.app X := by
    dsimp [shiftFunctorAdd']
    cat_disch
  rw [this]
  congr
  change _ = 𝟙 _ ≫ (shiftFunctor C j).map (𝟙 _) ≫ _ ≫ 𝟙 _
  simp

Depends on / 依赖: M.ground_nonempty.elim, ground_nonempty, isNonloop_of_loopless, rankPos
-/
lemma shiftFunctorAdd'_inv_app (i j k : A) (h : i + j = k) (X : t.Category) :
    (shiftFunctorAdd' t.Category i j k h).inv.app X =
      ((t.z i j)⁻¹).val • (t.shiftIso j).hom.app _ ≫
        (shiftFunctor C j).map ((t.shiftIso i).hom.app X) ≫
        (shiftFunctorAdd' C i j k h).inv.app X ≫
        (t.shiftIso k).inv.app X := by
  have : (shiftFunctorAdd' t.Category i j k h).inv.app X =
      ((t.z i j)⁻¹).val • (shiftFunctorAdd' C i j k h).inv.app X := by
    dsimp [shiftFunctorAdd']
    cat_disch
  rw [this]
  congr
  change _ = 𝟙 _ ≫ (shiftFunctor C j).map (𝟙 _) ≫ _ ≫ 𝟙 _
  simp

end TwistShiftData

end CategoryTheory
