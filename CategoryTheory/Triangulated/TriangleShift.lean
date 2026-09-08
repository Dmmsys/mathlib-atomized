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

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasShift C ℤ]
  [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive]

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
/-
**CategoryTheory.Pretriangulated.Triangle.shiftFunctor** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Pretriangulated.Triangle`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] →     [Category
Theory.Preadditive C] →       [inst_2 : CategoryTheory.HasShift C ℤ] →         ℤ
 →           CategoryTheory.Functor (CategoryTheory.Pretriangulated.Triangle C) 
(CategoryTheory.Pretriangulated.Triangle C)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The shift functor `Triangle C ⥤ Triangle C` by `n : ℤ` sends a triangle
to the triangle obtained by shifting the objects by `n` in `C` and by
multiplying the three morphisms by `(-1)^n`.
-/
noncomputable def Triangle.shiftFunctor (n : ℤ) : Triangle C ⥤ Triangle C where
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
        rw [Linear.units_smul_comp, Linear.comp_units_smul, ← Functor.map_comp_assoc, ← f.comm₃,
          Functor.map_comp, assoc, assoc, dsimp% (shiftFunctorComm C 1 n).hom.naturality] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism `Triangle.shiftFunctor C 0 ≅ 𝟭 (Triangle C)`. -/
@[simps!]
/-
**CategoryTheory.Pretriangulated.Triangle.shiftFunctorZero** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Pretriangulated.Triangle`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Preadditive C] →       [inst_2 : CategoryTheory.HasShift C ℤ] → 
        CategoryTheory.Pretriangulated.Triangle.shiftFunctor C 0 ≅           Cat
egoryTheory.Functor.id (CategoryTheory.Pretriangulated.Triangle C)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `Triangle.shiftFunctor C 0 ≅ 𝟭 (Triangle C)`.
-/
noncomputable def Triangle.shiftFunctorZero : Triangle.shiftFunctor C 0 ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ ((CategoryTheory.shiftFunctorZero C ℤ).app _)
      ((CategoryTheory.shiftFunctorZero C ℤ).app _) ((CategoryTheory.shiftFunctorZero C ℤ).app _)
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
/-
**CategoryTheory.Pretriangulated.Triangle.shiftFunctorAdd'** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Pretriangulated.Triangle`。
形式化陈述：shiftFunctorAdd'_eq (a b c : Int) (h : a + b = c) : CategoryTheory.shiftFu
nctorAdd' (Triangle C) a b c h = Triangle.shiftFunctorAdd' C a b c h
参数：a b c : Int；h : a + b = c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism
`Triangle.shiftFunctor C n ≅ Triangle.shiftFunctor C a ⋙ Triangle.shiftFunctor C
 b`
when `a + b = n`.
-/
noncomputable def Triangle.shiftFunctorAdd' (a b n : ℤ) (h : a + b = n) :
    Triangle.shiftFunctor C n ≅ Triangle.shiftFunctor C a ⋙ Triangle.shiftFunctor C b :=
  NatIso.ofComponents
    (fun T => Triangle.isoMk _ _
      ((CategoryTheory.shiftFunctorAdd' C a b n h).app _)
      ((CategoryTheory.shiftFunctorAdd' C a b n h).app _)
      ((CategoryTheory.shiftFunctorAdd' C a b n h).app _)
      (by
        subst h
        dsimp
        rw [Linear.units_smul_comp, NatTrans.naturality, Linear.comp_units_smul, Functor.comp_map,
          Functor.map_units_smul, Linear.comp_units_smul, smul_smul, Int.negOnePow_add, mul_comm])
      (by
        subst h
        dsimp
        rw [Linear.units_smul_comp, NatTrans.naturality, Linear.comp_units_smul, Functor.comp_map,
          Functor.map_units_smul, Linear.comp_units_smul, smul_smul, Int.negOnePow_add, mul_comm])
      (by
        subst h
        dsimp
        rw [Linear.units_smul_comp, Linear.comp_units_smul, Functor.map_units_smul,
          Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, assoc, Functor.map_comp, assoc,
          ← dsimp% (CategoryTheory.shiftFunctorAdd' C a b (a + b) rfl).hom.naturality_assoc]
        simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, Int.negOnePow_add,
          shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd_hom_app, add_comm a]))
    (by intros; ext <;> simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Rotating triangles three times identifies with the shift by `1`. -/
/-
**CategoryTheory.Pretriangulated.rotateRotateRotateIso** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Pretriangulated`。
形式化陈述：rotateRotateRotateIso : rotate C ⋙ rotate C ⋙ rotate C ≅ Triangle.shiftFun
ctor C 1
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Rotating triangles three times identifies with the shift by `1`.
-/
noncomputable def rotateRotateRotateIso :
    rotate C ⋙ rotate C ⋙ rotate C ≅ Triangle.shiftFunctor C 1 :=
  NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp))
    (by cat_disch)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Rotating triangles three times backwards identifies with the shift by `-1`. -/
/-
**CategoryTheory.Pretriangulated.invRotateInvRotateInvRotateIso** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：invRotateInvRotateInvRotateIso : invRotate C ⋙ invRotate C ⋙ invRotate C ≅
 Triangle.shiftFunctor C (-1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Rotating triangles three times backwards identifies with the shift by `-1`.
-/
noncomputable def invRotateInvRotateInvRotateIso :
    invRotate C ⋙ invRotate C ⋙ invRotate C ≅ Triangle.shiftFunctor C (-1) :=
  NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp)
      (by simp)
      (by
        dsimp [shiftFunctorCompIsoId]
        simp [shiftFunctorComm_eq C _ _ _ (add_neg_cancel (1 : ℤ))]))
    (by cat_disch)

/-- The inverse of the rotation of triangles can be expressed using a double
rotation and the shift by `-1`. -/
/-
**CategoryTheory.Pretriangulated.invRotateIsoRotateRotateShiftFunctorNegOne** 是 
Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：invRotateIsoRotateRotateShiftFunctorNegOne : invRotate C ≅ rotate C ⋙ rota
te C ⋙ Triangle.shiftFunctor C (-1)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Pretriangulated.Triangle.shiftFunctorAdd'`：shiftFunctorAd
d'_eq (a b c : Int) (h : a + b = c) : CategoryTheory.shiftFunctorAdd' (Triangle 
C) a b c h = Triangle.shiftFunctorAdd' C a b c…

--- 原说明 ---
The inverse of the rotation of triangles can be expressed using a double
rotation and the shift by `-1`.
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
/-
**CategoryTheory.Pretriangulated.Triangle.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Pretriangulated.Triangle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : HasShift (Triangle C) ℤ :=
  hasShiftMk (Triangle C) ℤ
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
/-
**CategoryTheory.Pretriangulated.Triangle.shiftFunctor_eq** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Pretriangulated.Triangle`。
形式化陈述：shiftFunctor_eq (n : Int) : CategoryTheory.shiftFunctor (Triangle C) n = T
riangle.shiftFunctor C n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma shiftFunctor_eq (n : ℤ) :
    CategoryTheory.shiftFunctor (Triangle C) n = Triangle.shiftFunctor C n := rfl

@[simp]
/-
**CategoryTheory.Pretriangulated.Triangle.shiftFunctorZero_eq** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Pretriangulated.Triangle`。
形式化陈述：shiftFunctorZero_eq : CategoryTheory.shiftFunctorZero (Triangle C) Int = T
riangle.shiftFunctorZero C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShiftMkCore.shiftFunctorZero_eq`：∀ {C : Type u} {A : Type
 u_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddMonoid A]   (h : Ca
tegoryTheory.ShiftMkCore C A), Categ…
· 使用引理 `CategoryTheory.Pretriangulated.Triangle.shiftFunctorAdd'`：shiftFunctorAd
d'_eq (a b c : Int) (h : a + b = c) : CategoryTheory.shiftFunctorAdd' (Triangle 
C) a b c h = Triangle.shiftFunctorAdd' C a b c…
-/
lemma shiftFunctorZero_eq :
    CategoryTheory.shiftFunctorZero (Triangle C) ℤ = Triangle.shiftFunctorZero C :=
  ShiftMkCore.shiftFunctorZero_eq _

@[simp]
/-
**CategoryTheory.Pretriangulated.Triangle.shiftFunctorAdd_eq** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Pretriangulated.Triangle`。
形式化陈述：shiftFunctorAdd_eq (a b : Int) : CategoryTheory.shiftFunctorAdd (Triangle 
C) a b = Triangle.shiftFunctorAdd' C a b _ rfl
参数：a b : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShiftMkCore.shiftFunctorAdd_eq`：∀ {C : Type u} {A : Type 
u_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddMonoid A]   (h : Cat
egoryTheory.ShiftMkCore C A) (a b :…
· 使用引理 `CategoryTheory.Pretriangulated.Triangle.shiftFunctorAdd'`：shiftFunctorAd
d'_eq (a b c : Int) (h : a + b = c) : CategoryTheory.shiftFunctorAdd' (Triangle 
C) a b c h = Triangle.shiftFunctorAdd' C a b c…
-/
lemma shiftFunctorAdd_eq (a b : ℤ) :
    CategoryTheory.shiftFunctorAdd (Triangle C) a b =
      Triangle.shiftFunctorAdd' C a b _ rfl :=
  ShiftMkCore.shiftFunctorAdd_eq _ _ _

@[simp]
/-
**CategoryTheory.Pretriangulated.Triangle.shiftFunctorAdd'_eq** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Pretriangulated.Triangle`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   [inst_2 : CategoryTheory.HasShift C ℤ] [inst_3 : ∀ (n :
 ℤ), (CategoryTheory.shiftFunctor C n).Additive] (a b c : ℤ)   (h : a + b = c), 
  CategoryTheory.shiftFunctorAdd' (CategoryTheory.Pretriangulated.Triangle C) a 
b c h =     CategoryTheory.Pretriangulated.Triangle.shiftFunctorAdd' C a b c h
参数：C : Type u；n : ℤ；CategoryTheory.shiftFunctor C n；a b c : ℤ；h : a + b = c；Cate
goryTheory.Pretriangulated.Triangle C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Pretriangulated.Triangle.shiftFunctorAdd'`：shiftFunctorAd
d'_eq (a b c : Int) (h : a + b = c) : CategoryTheory.shiftFunctorAdd' (Triangle 
C) a b c h = Triangle.shiftFunctorAdd' C a b c…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.shiftFunctorAdd'_eq_shiftFunctorAdd`：∀ (C : Type u) {A : 
Type u_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddMonoid A]   [in
st_2 : CategoryTheory.HasShift C A] (i j…
· 使用引理 `CategoryTheory.Pretriangulated.Triangle.shiftFunctorAdd_eq`：shiftFunctor
Add_eq (a b : Int) : CategoryTheory.shiftFunctorAdd (Triangle C) a b = Triangle.
shiftFunctorAdd' C a b _ rfl
-/
lemma shiftFunctorAdd'_eq (a b c : ℤ) (h : a + b = c) :
    CategoryTheory.shiftFunctorAdd' (Triangle C) a b c h =
      Triangle.shiftFunctorAdd' C a b c h := by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd]
  apply shiftFunctorAdd_eq

end Triangle

end Pretriangulated

end CategoryTheory

