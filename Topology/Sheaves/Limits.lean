/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Presheaves in `C` have limits and colimits when `C` does.
-/

public section


noncomputable section

universe v u w t

open CategoryTheory

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {J : Type w} [Category* J]

namespace TopCat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimitsOfShape
  signature: J C] (X
  body: functorCategoryHasLimitsOfShape

中文:
实例 [HasLimitsOfShape
  签名: J C] (X
  定义体: functorCategoryHasLimitsOfShape

Depends on / 依赖: functorCategoryHasLimitsOfShape
-/
instance [HasLimitsOfShape J C] (X : TopCat.{t}) : HasLimitsOfShape J (Presheaf C X) :=
  functorCategoryHasLimitsOfShape

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimits
  signature: C] (X

中文:
实例 [HasLimits
  签名: C] (X
-/
instance [HasLimits C] (X : TopCat.{v}) : HasLimits.{v} (Presheaf C X) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimitsOfShape
  signature: J C] (X
  body: functorCategoryHasColimitsOfShape

中文:
实例 [HasColimitsOfShape
  签名: J C] (X
  定义体: functorCategoryHasColimitsOfShape

Depends on / 依赖: functorCategoryHasColimitsOfShape
-/
instance [HasColimitsOfShape J C] (X : TopCat) : HasColimitsOfShape J (Presheaf C X) :=
  functorCategoryHasColimitsOfShape

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimits.{v,
  signature: u} C] (X : TopCat.{t}) : HasColimitsOfSize.{v, v} (Presheaf C X) where

中文:
实例 [HasColimits.{v,
  签名: u} C] (X : TopCat.{t}) : HasColimitsOfSize.{v, v} (Presheaf C X) where
-/
instance [HasColimits.{v, u} C] (X : TopCat.{t}) : HasColimitsOfSize.{v, v} (Presheaf C X) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimitsOfShape
  signature: J C] (X
  body: inferInstanceAs CreatesLimitsOfShape J (sheafToPresheaf _ _)

中文:
实例 [HasLimitsOfShape
  签名: J C] (X
  定义体: inferInstanceAs CreatesLimitsOfShape J (sheafToPresheaf _ _)

Depends on / 依赖: CreatesLimitsOfShape, sheafToPresheaf
-/
instance [HasLimitsOfShape J C] (X : TopCat.{t}) : CreatesLimitsOfShape J (Sheaf.forget C X) :=
inferInstanceAs CreatesLimitsOfShape J (sheafToPresheaf _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimitsOfShape
  signature: J C] (X
  body: hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (Sheaf.forget C X)

中文:
实例 [HasLimitsOfShape
  签名: J C] (X
  定义体: hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (Sheaf.forget C X)

Depends on / 依赖: Sheaf.forget, forget, hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
-/
instance [HasLimitsOfShape J C] (X : TopCat.{t}) : HasLimitsOfShape J (Sheaf C X) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (Sheaf.forget C X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimits
  signature: C] (X

中文:
实例 [HasLimits
  签名: C] (X
-/
instance [HasLimits C] (X : TopCat) : CreatesLimits.{v, v} (Sheaf.forget C X) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimits
  signature: C] (X

中文:
实例 [HasLimits
  签名: C] (X
-/
instance [HasLimits C] (X : TopCat.{v}) : HasLimitsOfSize.{v, v} (Sheaf.{v} C X) where

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isSheaf_of_isLimit` / 定理 `isSheaf_of_isLimit`

English:
theorem isSheaf_of_isLimit
  statement: [HasLimitsOfShape J C] {X : TopCat.{v}} (F : J ⥤ Presheaf.{v} C X)
  proof: by
  let F' : J ⥤ Sheaf C X :=
    { obj := fun j => ⟨F.obj j, H j⟩
      map := fun f => ⟨F.map f⟩ }
  let e : F' ⋙ Sheaf.forget C X ≅ F := NatIso.ofComponents fun _ => Iso.refl _
  exact Presheaf.isSheaf_of_iso
    ((isLimitOfPreserves (Sheaf.forget C X) (limit.isLimit F')).conePointsIsoOfNatIso h

中文:
定理 isSheaf_of_isLimit
  结论: [HasLimitsOfShape J C] {X : TopCat.{v}} (F : J ⥤ Presheaf.{v} C X)
  证明: by
  let F' : J ⥤ Sheaf C X :=
    { obj := fun j => ⟨F.obj j, H j⟩
      map := fun f => ⟨F.map f⟩ }
  let e : F' ⋙ Sheaf.forget C X ≅ F := NatIso.ofComponents fun _ => Iso.refl _
  exact Presheaf.isSheaf_of_iso
    ((isLimitOfPreserves (Sheaf.forget C X) (limit.isLimit F')).conePointsIsoOfNatIso h

Depends on / 依赖: F.map, F.obj, Iso.refl, NatIso, NatIso.ofComponents, Presheaf, Presheaf.isSheaf_of_iso, Sheaf.forget, conePointsIsoOfNatIso, forget, isLimit, isLimitOfPreserves, isSheaf_of_iso, limit.isLimit, ofComponents
-/
theorem isSheaf_of_isLimit [HasLimitsOfShape J C] {X : TopCat.{v}} (F : J ⥤ Presheaf.{v} C X)
    (H : forall j, (F.obj j).IsSheaf) {c : Cone F} (hc : IsLimit c) : c.pt.IsSheaf := by
  let F' : J ⥤ Sheaf C X :=
    { obj := fun j => ⟨F.obj j, H j⟩
      map := fun f => ⟨F.map f⟩ }
  let e : F' ⋙ Sheaf.forget C X ≅ F := NatIso.ofComponents fun _ => Iso.refl _
  exact Presheaf.isSheaf_of_iso
    ((isLimitOfPreserves (Sheaf.forget C X) (limit.isLimit F')).conePointsIsoOfNatIso hc e)
    (limit F').2

/--
theorem `limit_isSheaf` / 定理 `limit_isSheaf`

English:
theorem limit_isSheaf
  statement: [HasLimitsOfShape J C] {X : TopCat.{v}} (F : J ⥤ Presheaf.{v} C X)
  proof: isSheaf_of_isLimit F H (limit.isLimit F)

中文:
定理 limit_isSheaf
  结论: [HasLimitsOfShape J C] {X : TopCat.{v}} (F : J ⥤ Presheaf.{v} C X)
  证明: isSheaf_of_isLimit F H (limit.isLimit F)

Depends on / 依赖: isLimit, isSheaf_of_isLimit, limit.isLimit
-/
theorem limit_isSheaf [HasLimitsOfShape J C] {X : TopCat.{v}} (F : J ⥤ Presheaf.{v} C X)
    (H : forall j, (F.obj j).IsSheaf) : (limit F).IsSheaf :=
  isSheaf_of_isLimit F H (limit.isLimit F)

end TopCat
