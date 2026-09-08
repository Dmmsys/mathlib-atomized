/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Commutative group objects in additive categories.

We construct an inverse of the forgetful functor `CommGrp C ⥤ C` if `C` is an additive category.

This looks slightly strange because the additive structure of `C` maps to the multiplicative
structure of the commutative group objects.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Preadditive

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [CartesianMonoidalCategory C]

@[simps]
/-
**CategoryTheory.Preadditive.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Preaddit
ive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : GrpObj X where
  one := 0
  mul := fst _ _ + snd _ _
  inv := -𝟙 X
  one_mul := by simp [← leftUnitor_hom]
  mul_one := by simp [← rightUnitor_hom]
  mul_assoc := by simp [add_assoc]

variable [BraidedCategory C]
/-
**CategoryTheory.Preadditive.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Preaddit
ive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : IsCommMonObj X where
  mul_comm := by simp [add_comm]

variable (C) in
/-- The canonical functor from an additive category into its commutative group objects. This is
always an equivalence, see `commGrpEquivalence`. -/
@[simps]
/-
**CategoryTheory.Preadditive.toCommGrp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Preadditive`。
形式化陈述：toCommGrp : C ⥤ CommGrp C where obj X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Preadditive.instIsCommMonObj`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   [inst_2 
: CategoryTheory.CartesianMonoida…

--- 原说明 ---
The canonical functor from an additive category into its commutative group objec
ts. This is
always an equivalence, see `commGrpEquivalence`.
-/
def toCommGrp : C ⥤ CommGrp C where
  obj X := ⟨X⟩
  map {X Y} f := InducedCategory.homMk (Grp.homMk'' f)

-- PROJECT: develop `ChosenFiniteCoproducts`, and construct `ChosenFiniteCoproducts` from
-- `CartesianMonoidalCategory` in preadditive categories, to give this lemma a proper home.
set_option backward.privateInPublic true in
omit [BraidedCategory C] in
/-
**CategoryTheory.Preadditive.monoidal_hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Preadditive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem monoidal_hom_ext {X Y Z : C} {f g : X ⊗ Y ⟶ Z}
    (h₁ : lift (𝟙 X) 0 ≫ f = lift (𝟙 X) 0 ≫ g) (h₂ : lift 0 (𝟙 Y) ≫ f = lift 0 (𝟙 Y) ≫ g) :
    f = g :=
  BinaryCofan.IsColimit.hom_ext
    (binaryBiconeIsBilimitOfLimitConeOfIsLimit (tensorProductIsBinaryProduct X Y)).isColimit h₁ h₂

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Auxiliary definition for `commGrpEquivalence`. -/
@[simps!]
/-
**CategoryTheory.Preadditive.commGrpEquivalenceAux** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Preadditive`。
形式化陈述：commGrpEquivalenceAux : CommGrp.forget C ⋙ toCommGrp C ≅ 𝟭 (CommGrp C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `commGrpEquivalence`.
-/
def commGrpEquivalenceAux : CommGrp.forget C ⋙ toCommGrp C ≅
      𝟭 (CommGrp C) := by
  refine NatIso.ofComponents (fun _ => CommGrp.mkIso (Iso.refl _) ?_ ?_) ?_
  · exact ((IsZero.iff_id_eq_zero _).2 (Subsingleton.elim _ _)).eq_of_src _ _
  · simp only [Functor.id_obj,
      mul_def, Iso.refl_hom, Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp]
    apply monoidal_hom_ext
    · simp only [comp_add, lift_fst, lift_snd, add_zero]
      convert! (MonObj.lift_comp_one_right _ 0).symm
      · simp
      · infer_instance
    · simp only [comp_add, lift_fst, lift_snd, zero_add]
      convert! (MonObj.lift_comp_one_left 0 _).symm
      · simp
      · infer_instance
  · cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An additive category is equivalent to its category of commutative group objects. -/
@[simps!]
/-
**CategoryTheory.Preadditive.commGrpEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Preadditive`。
形式化陈述：commGrpEquivalence : C ≌ CommGrp C where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive category is equivalent to its category of commutative group objects.
-/
def commGrpEquivalence : C ≌ CommGrp C where
  functor := toCommGrp C
  inverse := CommGrp.forget C
  unitIso := Iso.refl _
  counitIso := commGrpEquivalenceAux

end CategoryTheory.Preadditive

