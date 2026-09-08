/-
Copyright (c) 2026 Leopold Mayer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leopold Mayer
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Biproducts in functor categories

We show that if `C` has binary biproducts, then the functor category `D ⥤ C` also
has binary biproducts
(`CategoryTheory.Limits.BinaryBiproduct.functorCategoryHasBinaryBiproducts`).
-/

@[expose] public noncomputable section

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

variable {D : Type*} [Category* D]

variable (F G : D ⥤ C)

/-- The binary bicone associated to the biproduct of functors `F` and `G` -/
@[simps]
/-
**CategoryTheory.Limits.pointwiseBinaryBicone** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：pointwiseBinaryBicone : BinaryBicone F G where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The binary bicone associated to the biproduct of functors `F` and `G`
-/
def pointwiseBinaryBicone : BinaryBicone F G where
  pt :=
    { obj P := F.obj P ⊞ G.obj P
      map f := biprod.map (F.map f) (G.map f) }
  fst := { app X := biprod.fst }
  snd := { app X := biprod.snd }
  inl := { app X := biprod.inl }
  inr := { app X := biprod.inr }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The bicone associated with `F` and `G` is a bilimit bicone. -/
@[simps]
/-
**CategoryTheory.Limits.pointwiseBinaryBicone.isBilimit** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits.pointwiseBinaryBicone`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       [inst_2 : CategoryTheor
y.Limits.HasBinaryBiproducts C] →         {D : Type u_2} →           [inst_3 : C
ategoryTheory.Category.{v_2, u_2} D] →             (F G : CategoryTheory.Functor
 D C) → (CategoryTheory.Limits.pointwiseBinaryBicone F G).IsBilimit
参数：F G : CategoryTheory.Functor D C；CategoryTheory.Limits.pointwiseBinaryBicone 
F G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bicone associated with `F` and `G` is a bilimit bicone.
-/
def pointwiseBinaryBicone.isBilimit : (pointwiseBinaryBicone F G).IsBilimit where
  isLimit := evaluationJointlyReflectsLimits _ fun d => by
    refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ (BinaryBiproduct.isLimit (F.obj d) (G.obj d))
    · exact (pairComp F G ((evaluation D C).obj d)).symm
    · exact Cone.ext (Iso.refl _) <| by rintro (_ | _ | _) <;> cat_disch
  isColimit := evaluationJointlyReflectsColimits _ fun d => by
    refine IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_ (BinaryBiproduct.isColimit (F.obj d) (G.obj d))
    · exact (pairComp F G ((evaluation D C).obj d)).symm
    · exact Cocone.ext (Iso.refl _) <| by rintro (_ | _ | _) <;> cat_disch

/-- Construction of the binary biproduct data for functors `F` and `G` -/
@[simps]
/-
**CategoryTheory.Limits.pointwiseBinaryBiproductData** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：pointwiseBinaryBiproductData : BinaryBiproductData F G where bicone
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construction of the binary biproduct data for functors `F` and `G`
-/
def pointwiseBinaryBiproductData : BinaryBiproductData F G where
  bicone := pointwiseBinaryBicone F G
  isBilimit := pointwiseBinaryBicone.isBilimit F G

/-- If `C` has binary biproducts, then the functor category `D ⥤ C` does too. -/
/-
**CategoryTheory.Limits.functorCategoryHasBinaryBiproducts** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：functorCategoryHasBinaryBiproducts : HasBinaryBiproducts (D ⥤ C) where has
_binary_biproduct F G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` has binary biproducts, then the functor category `D ⥤ C` does too.
-/
instance functorCategoryHasBinaryBiproducts : HasBinaryBiproducts (D ⥤ C) where
  has_binary_biproduct F G := ⟨⟨pointwiseBinaryBiproductData F G⟩⟩

end CategoryTheory.Limits

