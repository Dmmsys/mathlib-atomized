/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape

/-!
# Limits in full subcategories

If a property of objects `P` is closed under taking limits,
then limits in `FullSubcategory P` can be constructed from limits in `C`.
More precisely, the inclusion creates such limits.

-/

@[expose] public section


noncomputable section

universe w' w v v₁ v₂ u u₁ u₂

open CategoryTheory

namespace CategoryTheory

namespace Limits

variable {J : Type w} [Category.{w'} J] {C : Type u} [Category.{v} C] {P : ObjectProperty C}

/-- If a `J`-shaped diagram in `FullSubcategory P` has a limit cone in `C` whose cone point lives
    in the full subcategory, then this defines a limit in the full subcategory. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitFullSubcategoryInclusion'** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：createsLimitFullSubcategoryInclusion' (F : J ⥤ P.FullSubcategory) {c : Con
e (F ⋙ P.ι)} (hc : IsLimit c) (h : P c.pt) : CreatesLimit F P.ι
参数：F : J ⥤ P.FullSubcategory；F ⋙ P.ι；hc : IsLimit c；h : P c.pt。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a `J`-shaped diagram in `FullSubcategory P` has a limit cone in `C` whose con
e point lives
    in the full subcategory, then this defines a limit in the full subcategory.
-/
def createsLimitFullSubcategoryInclusion' (F : J ⥤ P.FullSubcategory)
    {c : Cone (F ⋙ P.ι)} (hc : IsLimit c) (h : P c.pt) :
    CreatesLimit F P.ι :=
  createsLimitOfFullyFaithfulOfIso' hc ⟨_, h⟩ (Iso.refl _)

/-- If a `J`-shaped diagram in `FullSubcategory P` has a limit in `C` whose cone point lives in the
    full subcategory, then this defines a limit in the full subcategory. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitFullSubcategoryInclusion** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：createsLimitFullSubcategoryInclusion (F : J ⥤ P.FullSubcategory) [HasLimit
 (F ⋙ P.ι)] (h : P (limit (F ⋙ P.ι))) : CreatesLimit F P.ι
参数：F : J ⥤ P.FullSubcategory；F ⋙ P.ι；h : P (limit (F ⋙ P.ι))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a `J`-shaped diagram in `FullSubcategory P` has a limit in `C` whose cone poi
nt lives in the
    full subcategory, then this defines a limit in the full subcategory.
-/
def createsLimitFullSubcategoryInclusion (F : J ⥤ P.FullSubcategory)
    [HasLimit (F ⋙ P.ι)] (h : P (limit (F ⋙ P.ι))) :
    CreatesLimit F P.ι :=
  createsLimitFullSubcategoryInclusion' F (limit.isLimit _) h

/-- If a `J`-shaped diagram in `FullSubcategory P` has a colimit cocone in `C` whose cocone point
    lives in the full subcategory, then this defines a colimit in the full subcategory. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitFullSubcategoryInclusion'** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：createsColimitFullSubcategoryInclusion' (F : J ⥤ P.FullSubcategory) {c : C
ocone (F ⋙ P.ι)} (hc : IsColimit c) (h : P c.pt) : CreatesColimit F P.ι
参数：F : J ⥤ P.FullSubcategory；F ⋙ P.ι；hc : IsColimit c；h : P c.pt。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a `J`-shaped diagram in `FullSubcategory P` has a colimit cocone in `C` whose
 cocone point
    lives in the full subcategory, then this defines a colimit in the full subca
tegory.
-/
def createsColimitFullSubcategoryInclusion' (F : J ⥤ P.FullSubcategory)
    {c : Cocone (F ⋙ P.ι)} (hc : IsColimit c) (h : P c.pt) :
    CreatesColimit F P.ι :=
  createsColimitOfFullyFaithfulOfIso' hc ⟨_, h⟩ (Iso.refl _)

/-- If a `J`-shaped diagram in `FullSubcategory P` has a colimit in `C` whose cocone point lives in
    the full subcategory, then this defines a colimit in the full subcategory. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitFullSubcategoryInclusion** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：createsColimitFullSubcategoryInclusion (F : J ⥤ P.FullSubcategory) [HasCol
imit (F ⋙ P.ι)] (h : P (colimit (F ⋙ P.ι))) : CreatesColimit F P.ι
参数：F : J ⥤ P.FullSubcategory；F ⋙ P.ι；h : P (colimit (F ⋙ P.ι))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a `J`-shaped diagram in `FullSubcategory P` has a colimit in `C` whose cocone
 point lives in
    the full subcategory, then this defines a colimit in the full subcategory.
-/
def createsColimitFullSubcategoryInclusion (F : J ⥤ P.FullSubcategory)
    [HasColimit (F ⋙ P.ι)]
    (h : P (colimit (F ⋙ P.ι))) :
    CreatesColimit F P.ι :=
  createsColimitFullSubcategoryInclusion' F (colimit.isColimit _) h

variable (P J)

/-- If `P` is closed under limits of shape `J`, then the inclusion creates such limits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitFullSubcategoryInclusionOfClosed** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：createsLimitFullSubcategoryInclusionOfClosed [P.IsClosedUnderLimitsOfShape
 J] (F : J ⥤ P.FullSubcategory) [HasLimit (F ⋙ P.ι)] : CreatesLimit F P.ι
参数：F : J ⥤ P.FullSubcategory；F ⋙ P.ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` is closed under limits of shape `J`, then the inclusion creates such limi
ts.
-/
def createsLimitFullSubcategoryInclusionOfClosed [P.IsClosedUnderLimitsOfShape J]
    (F : J ⥤ P.FullSubcategory) [HasLimit (F ⋙ P.ι)] :
    CreatesLimit F P.ι :=
  createsLimitFullSubcategoryInclusion F (P.prop_limit _ fun j => (F.obj j).property)

/-- If `P` is closed under limits of shape `J`, then the inclusion creates such limits. -/
/-
**CategoryTheory.Limits.createsLimitsOfShapeFullSubcategoryInclusion** 是 Mathlib
 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：createsLimitsOfShapeFullSubcategoryInclusion [P.IsClosedUnderLimitsOfShape
 J] [HasLimitsOfShape J C] : CreatesLimitsOfShape J P.ι where CreatesLimit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` is closed under limits of shape `J`, then the inclusion creates such limi
ts.
-/
instance createsLimitsOfShapeFullSubcategoryInclusion [P.IsClosedUnderLimitsOfShape J]
    [HasLimitsOfShape J C] : CreatesLimitsOfShape J P.ι where
  CreatesLimit := @fun F => createsLimitFullSubcategoryInclusionOfClosed J P F
/-
**CategoryTheory.Limits.hasLimit_of_closedUnderLimits** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：hasLimit_of_closedUnderLimits [P.IsClosedUnderLimitsOfShape J] (F : J ⥤ P.
FullSubcategory) [HasLimit (F ⋙ P.ι)] : HasLimit F
参数：F : J ⥤ P.FullSubcategory；F ⋙ P.ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimit_of_created`：hasLimit_of_created (K : J ⥤ C) (F :
 C ⥤ D) [HasLimit (K ⋙ F)] [CreatesLimit K F] : HasLimit K
-/
theorem hasLimit_of_closedUnderLimits [P.IsClosedUnderLimitsOfShape J]
    (F : J ⥤ P.FullSubcategory) [HasLimit (F ⋙ P.ι)] : HasLimit F :=
  have : CreatesLimit F P.ι :=
    createsLimitFullSubcategoryInclusionOfClosed J P F
  hasLimit_of_created F P.ι
/-
**CategoryTheory.Limits.hasLimitsOfShape_of_closedUnderLimits** 是 Mathlib 中的一个实例
，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasLimitsOfShape_of_closedUnderLimits [P.IsClosedUnderLimitsOfShape J] [Ha
sLimitsOfShape J C] : HasLimitsOfShape J P.FullSubcategory
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimit_of_closedUnderLimits`：hasLimit_of_closedU
nderLimits [P.IsClosedUnderLimitsOfShape J] (F : J ⥤ P.FullSubcategory) [HasLimi
t (F ⋙ P.ι)] : HasLimit F
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance hasLimitsOfShape_of_closedUnderLimits [P.IsClosedUnderLimitsOfShape J]
    [HasLimitsOfShape J C] : HasLimitsOfShape J P.FullSubcategory :=
  { has_limit := fun F => hasLimit_of_closedUnderLimits J P F }

/-- If `P` is closed under colimits of shape `J`, then the inclusion creates such colimits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitFullSubcategoryInclusionOfClosed** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：createsColimitFullSubcategoryInclusionOfClosed [P.IsClosedUnderColimitsOfS
hape J] (F : J ⥤ P.FullSubcategory) [HasColimit (F ⋙ P.ι)] : CreatesColimit F P.
ι
参数：F : J ⥤ P.FullSubcategory；F ⋙ P.ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` is closed under colimits of shape `J`, then the inclusion creates such co
limits.
-/
def createsColimitFullSubcategoryInclusionOfClosed [P.IsClosedUnderColimitsOfShape J]
    (F : J ⥤ P.FullSubcategory) [HasColimit (F ⋙ P.ι)] :
    CreatesColimit F P.ι :=
  createsColimitFullSubcategoryInclusion F (P.prop_colimit _ fun j => (F.obj j).property)

/-- If `P` is closed under colimits of shape `J`, then the inclusion creates such colimits. -/
/-
**CategoryTheory.Limits.createsColimitsOfShapeFullSubcategoryInclusion** 是 Mathl
ib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：createsColimitsOfShapeFullSubcategoryInclusion [P.IsClosedUnderColimitsOfS
hape J] [HasColimitsOfShape J C] : CreatesColimitsOfShape J P.ι where CreatesCol
imit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` is closed under colimits of shape `J`, then the inclusion creates such co
limits.
-/
instance createsColimitsOfShapeFullSubcategoryInclusion [P.IsClosedUnderColimitsOfShape J]
    [HasColimitsOfShape J C] : CreatesColimitsOfShape J P.ι where
  CreatesColimit := @fun F => createsColimitFullSubcategoryInclusionOfClosed J P F
/-
**CategoryTheory.Limits.hasColimit_of_closedUnderColimits** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：hasColimit_of_closedUnderColimits [P.IsClosedUnderColimitsOfShape J] (F : 
J ⥤ P.FullSubcategory) [HasColimit (F ⋙ P.ι)] : HasColimit F
参数：F : J ⥤ P.FullSubcategory；F ⋙ P.ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasColimit_of_created`：hasColimit_of_created (K : J ⥤ C) 
(F : C ⥤ D) [HasColimit (K ⋙ F)] [CreatesColimit K F] : HasColimit K
-/
theorem hasColimit_of_closedUnderColimits [P.IsClosedUnderColimitsOfShape J]
    (F : J ⥤ P.FullSubcategory) [HasColimit (F ⋙ P.ι)] : HasColimit F :=
  have : CreatesColimit F P.ι :=
    createsColimitFullSubcategoryInclusionOfClosed J P F
  hasColimit_of_created F P.ι
/-
**CategoryTheory.Limits.hasColimitsOfShape_of_closedUnderColimits** 是 Mathlib 中的
一个实例，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasColimitsOfShape_of_closedUnderColimits [P.IsClosedUnderColimitsOfShape 
J] [HasColimitsOfShape J C] : HasColimitsOfShape J P.FullSubcategory
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimit_of_closedUnderColimits`：hasColimit_of_c
losedUnderColimits [P.IsClosedUnderColimitsOfShape J] (F : J ⥤ P.FullSubcategory
) [HasColimit (F ⋙ P.ι)] : HasColimit F
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance hasColimitsOfShape_of_closedUnderColimits [P.IsClosedUnderColimitsOfShape J]
    [HasColimitsOfShape J C] : HasColimitsOfShape J P.FullSubcategory :=
  { has_colimit := fun F => hasColimit_of_closedUnderColimits J P F }

end Limits

namespace ObjectProperty

open Limits

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C) (J : Type w) [Category.{w'} J]

/-
**CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_of_preservesColimit
sOfShape_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι
    [HasColimitsOfShape J P.FullSubcategory] [P.IsClosedUnderIsomorphisms]
    [PreservesColimitsOfShape J P.ι] :
    P.IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    exact P.prop_of_iso (IsColimit.coconePointUniqueUpToIso
      (isColimitOfPreserves P.ι (colimit.isColimit (P.lift p.diag p.prop_diag_obj)))
        p.isColimit) (colimit (P.lift p.diag p.prop_diag_obj)).property
/-
**CategoryTheory.ObjectProperty.isClosedUnderLimitsOfShape_of_preservesLimitsOfS
hape_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι
    [HasLimitsOfShape J P.FullSubcategory] [P.IsClosedUnderIsomorphisms]
    [PreservesLimitsOfShape J P.ι] :
    P.IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    exact P.prop_of_iso (IsLimit.conePointUniqueUpToIso
      (isLimitOfPreserves P.ι (limit.isLimit (P.lift p.diag p.prop_diag_obj)))
        p.isLimit) (limit (P.lift p.diag p.prop_diag_obj)).property

end ObjectProperty

variable {J : Type w} [Category.{w'} J]
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (F : C ⥤ D)

namespace Limits

/-- The essential image of a functor is closed under the limits it preserves. -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The essential image of a functor is closed under the limits it preserves.
-/
instance [HasLimitsOfShape J C] [PreservesLimitsOfShape J F] [F.Full] [F.Faithful] :
    F.essImage.IsClosedUnderLimitsOfShape J :=
  .mk' (by
    rintro _ ⟨G, hG⟩
    exact ⟨limit (Functor.essImage.liftFunctor G F hG),
      ⟨IsLimit.conePointsIsoOfNatIso
        (isLimitOfPreserves F (limit.isLimit _)) (limit.isLimit _)
        (Functor.essImage.liftFunctorCompIso _ _ _)⟩⟩)

/-- The essential image of a functor is closed under the colimits it preserves. -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The essential image of a functor is closed under the colimits it preserves.
-/
instance [HasColimitsOfShape J C] [PreservesColimitsOfShape J F] [F.Full] [F.Faithful] :
    F.essImage.IsClosedUnderColimitsOfShape J :=
  .mk' (by
    rintro _ ⟨G, hG⟩
    exact ⟨colimit (Functor.essImage.liftFunctor G F hG),
      ⟨IsColimit.coconePointsIsoOfNatIso
        (isColimitOfPreserves F (colimit.isColimit _)) (colimit.isColimit _)
        (Functor.essImage.liftFunctorCompIso _ _ _)⟩⟩)

end CategoryTheory.Limits

