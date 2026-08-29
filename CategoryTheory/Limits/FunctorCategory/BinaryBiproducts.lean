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
/--
Definition of `pointwiseBinaryBicone` / `pointwiseBinaryBicone` 的定义

English:
definition pointwiseBinaryBicone
  signature: : BinaryBicone F G where
  body: { obj P := F.obj P ⊞ G.obj P
      map f := biprod.map (F.map f) (G.map f) }
  fst := { app X := biprod.fst }
  snd := { app X := biprod.snd }
  inl := { app X := biprod.inl }
  inr := { app X := biprod.inr }

中文:
定义 pointwiseBinaryBicone
  签名: : BinaryBicone F G where
  定义体: { obj P := F.obj P ⊞ G.obj P
      map f := biprod.map (F.map f) (G.map f) }
  fst := { app X := biprod.fst }
  snd := { app X := biprod.snd }
  inl := { app X := biprod.inl }
  inr := { app X := biprod.inr }

Depends on / 依赖: F.map, F.obj, G.map, G.obj, biprod, biprod.fst, biprod.inl, biprod.inr, biprod.map, biprod.snd
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
/--
Definition of `pointwiseBinaryBicone.isBilimit` / `pointwiseBinaryBicone.isBilimit` 的定义

English:
definition pointwiseBinaryBicone.isBilimit
  signature: : (pointwiseBinaryBicone F G).IsBilimit where
  body: evaluationJointlyReflectsLimits _ fun d => by
    refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ (BinaryBiproduct.isLimit (F.obj d) (G.obj d))
    · exact (pairComp F G ((evaluation D C).obj d)).symm
· exact Cone.ext (Iso.refl _) by rintro (_ | _ | _) <;> cat_disch
  isColimit := evaluationJointlyReflectsColimits _ fun d => by
    refine IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_ (BinaryBiproduct.isColimit (F.obj d) (G.obj d))
    · exact (pairComp F G ((evaluation D C).obj d)).symm
· exact Cocone.ext (Iso.refl _) by rintro (_ | _ | _) <;> cat_disch

中文:
定义 pointwiseBinaryBicone.isBilimit
  签名: : (pointwiseBinaryBicone F G).是Bilimit where
  定义体: evaluationJointlyReflectsLimits _ fun d => by
    refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ (BinaryBiproduct.isLimit (F.obj d) (G.obj d))
    · exact (pairComp F G ((evaluation D C).obj d)).symm
· exact Cone.ext (Iso.refl _) by rintro (_ | _ | _) <;> cat_disch
  isColimit := evaluationJointlyReflectsColimits _ fun d => by
    refine IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_ (BinaryBiproduct.isColimit (F.obj d) (G.obj d))
    · exact (pairComp F G ((evaluation D C).obj d)).symm
· exact Cocone.ext (Iso.refl _) by rintro (_ | _ | _) <;> cat_disch

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isColimit, BinaryBiproduct.isLimit, Cocone, Cocone.ext, Cone.ext, F.obj, G.obj, IsColimit, IsColimit.equivOfNatIsoOfIso, IsLimit, IsLimit.equivOfNatIsoOfIso, Iso.refl, cat_disch, equivOfNatIsoOfIso, evaluation, evaluationJointlyReflectsColimits, evaluationJointlyReflectsLimits, isColimit, isLimit
-/
def pointwiseBinaryBicone.isBilimit : (pointwiseBinaryBicone F G).IsBilimit where
  isLimit := evaluationJointlyReflectsLimits _ fun d => by
    refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ (BinaryBiproduct.isLimit (F.obj d) (G.obj d))
    · exact (pairComp F G ((evaluation D C).obj d)).symm
· exact Cone.ext (Iso.refl _) by rintro (_ | _ | _) <;> cat_disch
  isColimit := evaluationJointlyReflectsColimits _ fun d => by
    refine IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_ (BinaryBiproduct.isColimit (F.obj d) (G.obj d))
    · exact (pairComp F G ((evaluation D C).obj d)).symm
· exact Cocone.ext (Iso.refl _) by rintro (_ | _ | _) <;> cat_disch

/-- Construction of the binary biproduct data for functors `F` and `G` -/
@[simps]
/--
Definition of `pointwiseBinaryBiproductData` / `pointwiseBinaryBiproductData` 的定义

English:
definition pointwiseBinaryBiproductData
  signature: : BinaryBiproductData F G where
  body: pointwiseBinaryBicone F G
  isBilimit := pointwiseBinaryBicone.isBilimit F G

中文:
定义 pointwiseBinaryBiproductData
  签名: : BinaryBiproductData F G where
  定义体: pointwiseBinaryBicone F G
  isBilimit := pointwiseBinaryBicone.isBilimit F G

Depends on / 依赖: pointwiseBinaryBicone
-/
def pointwiseBinaryBiproductData : BinaryBiproductData F G where
  bicone := pointwiseBinaryBicone F G
  isBilimit := pointwiseBinaryBicone.isBilimit F G

/--
Instance `functorCategoryHasBinaryBiproducts` / 实例 `functorCategoryHasBinaryBiproducts`

English:
instance functorCategoryHasBinaryBiproducts
  signature: : HasBinaryBiproducts (D ⥤ C) where
  body: ⟨⟨pointwiseBinaryBiproductData F G⟩⟩

中文:
实例 functorCategoryHasBinaryBiproducts
  签名: : 有BinaryBiproducts (D ⥤ C) where
  定义体: ⟨⟨pointwiseBinaryBiproductData F G⟩⟩

Depends on / 依赖: pointwiseBinaryBiproductData
-/
instance functorCategoryHasBinaryBiproducts : HasBinaryBiproducts (D ⥤ C) where
  has_binary_biproduct F G := ⟨⟨pointwiseBinaryBiproductData F G⟩⟩

end CategoryTheory.Limits
