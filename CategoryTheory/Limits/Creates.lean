/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Creating (co)limits

We say that `F` creates limits of `K` if, given any limit cone `c` for `K ⋙ F`
(i.e. below), we can lift it to a cone "above", and further that `F` reflects
limits for `K`.
-/

@[expose] public section


open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

noncomputable section

namespace CategoryTheory

universe w' w'₁ w w₁ v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]

section Creates

variable {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J] {K : J ⥤ C}

/-- Define the lift of a cone: For a cone `c` for `K ⋙ F`, give a cone for `K`
which is a lift of `c`, i.e. the image of it under `F` is (iso) to `c`.

We will then use this as part of the definition of creation of limits:
every limit cone has a lift.

Note this definition is really only useful when `c` is a limit already.
-/
/-
**CategoryTheory.LiftableCone** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {J : Typ
e w} →           [inst_2 : CategoryTheory.Category.{w', w} J] →             (K :
 CategoryTheory.Functor J C) →               (F : CategoryTheory.Functor C D) → 
                CategoryTheory.Limits.Cone (K.comp F) → Type (max (max (max u₁ v
₁) v₂) w)
参数：K : CategoryTheory.Functor J C；F : CategoryTheory.Functor C D；K.comp F；max (m
ax (max u₁ v₁) v₂) w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define the lift of a cone: For a cone `c` for `K ⋙ F`, give a cone for `K`
which is a lift of `c`, i.e. the image of it under `F` is (iso) to `c`.

We will then use this as part of the definition of creation of limits:
every limit cone has a lift.

Note this definition is really only useful when `c` is a limit already.
-/
structure LiftableCone (K : J ⥤ C) (F : C ⥤ D) (c : Cone (K ⋙ F)) where
  /-- a cone in the source category of the functor -/
  liftedCone : Cone K
  /-- the isomorphism expressing that `liftedCone` lifts the given cone -/
  validLift : F.mapCone liftedCone ≅ c

/-- Define the lift of a cocone: For a cocone `c` for `K ⋙ F`, give a cocone for
`K` which is a lift of `c`, i.e. the image of it under `F` is (iso) to `c`.

We will then use this as part of the definition of creation of colimits:
every limit cocone has a lift.

Note this definition is really only useful when `c` is a colimit already.
-/
/-
**CategoryTheory.LiftableCocone** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {J : Typ
e w} →           [inst_2 : CategoryTheory.Category.{w', w} J] →             (K :
 CategoryTheory.Functor J C) →               (F : CategoryTheory.Functor C D) → 
                CategoryTheory.Limits.Cocone (K.comp F) → Type (max (max (max u₁
 v₁) v₂) w)
参数：K : CategoryTheory.Functor J C；F : CategoryTheory.Functor C D；K.comp F；max (m
ax (max u₁ v₁) v₂) w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define the lift of a cocone: For a cocone `c` for `K ⋙ F`, give a cocone for
`K` which is a lift of `c`, i.e. the image of it under `F` is (iso) to `c`.

We will then use this as part of the definition of creation of colimits:
every limit cocone has a lift.

Note this definition is really only useful when `c` is a colimit already.
-/
structure LiftableCocone (K : J ⥤ C) (F : C ⥤ D) (c : Cocone (K ⋙ F)) where
  /-- a cocone in the source category of the functor -/
  liftedCocone : Cocone K
  /-- the isomorphism expressing that `liftedCocone` lifts the given cocone -/
  validLift : F.mapCocone liftedCocone ≅ c

/-- Definition 3.3.1 of [Riehl].
We say that `F` creates limits of `K` if, given any limit cone `c` for `K ⋙ F`
(i.e. below) we can lift it to a cone "above", and further that `F` reflects
limits for `K`.

If `F` reflects isomorphisms, it suffices to show only that the lifted cone is
a limit - see `createsLimitOfReflectsIso`.
-/
/-
**CategoryTheory.CreatesLimit** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {J : Typ
e w} →           [inst_2 : CategoryTheory.Category.{w', w} J] →             Cate
goryTheory.Functor J C → CategoryTheory.Functor C D → Type (max (max (max (max u
₁ u₂) v₁) v₂) w)
参数：max (max (max (max u₁ u₂) v₁) v₂) w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Definition 3.3.1 of [Riehl].
We say that `F` creates limits of `K` if, given any limit cone `c` for `K ⋙ F`
(i.e. below) we can lift it to a cone "above", and further that `F` reflects
limits for `K`.

If `F` reflects isomorphisms, it suffices to show only that the lifted cone is
a limit - see `createsLimitOfReflectsIso`.
-/
class CreatesLimit (K : J ⥤ C) (F : C ⥤ D) extends ReflectsLimit K F where
  /-- any limit cone can be lifted to a cone above -/
  lifts : ∀ c, IsLimit c → LiftableCone K F c

/-- `F` creates limits of shape `J` if `F` creates the limit of any diagram
`K : J ⥤ C`.
-/
/-
**CategoryTheory.CreatesLimitsOfShape** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：CreatesLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where Crea
tesLimit : forall {K : J ⥤ C}, CreatesLimit K F
参数：J : Type w；F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F` creates limits of shape `J` if `F` creates the limit of any diagram
`K : J ⥤ C`.
-/
class CreatesLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  CreatesLimit : ∀ {K : J ⥤ C}, CreatesLimit K F := by infer_instance

-- This should be used with explicit universe variables.
set_option linter.checkUnivs false in
/-- `F` creates limits if it creates limits of shape `J` for any `J`. -/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the shape universes in
-- `CreatesLimitsOfSize` and `CreatesColimitsOfSize` would default to universe output parameters.
-- See Note [universe output parameters and typeclass caching].
@[univ_out_params, pp_with_univ]
/-
**CategoryTheory.CreatesLimitsOfSize** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：CreatesLimitsOfSize (F : C ⥤ D) where CreatesLimitsOfShape : forall {J : T
ype w} [Category.{w'} J], CreatesLimitsOfShape J F
参数：F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class CreatesLimitsOfSize (F : C ⥤ D) where
  CreatesLimitsOfShape : ∀ {J : Type w} [Category.{w'} J], CreatesLimitsOfShape J F := by
    infer_instance

/-- `F` creates small limits if it creates limits of shape `J` for any small `J`. -/
/-
**CategoryTheory.CreatesLimits** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：CreatesLimits (F : C ⥤ D)
参数：F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F` creates small limits if it creates limits of shape `J` for any small `J`.
-/
abbrev CreatesLimits (F : C ⥤ D) :=
  CreatesLimitsOfSize.{v₂, v₂} F

/-- Dual of definition 3.3.1 of [Riehl].
We say that `F` creates colimits of `K` if, given any limit cocone `c` for
`K ⋙ F` (i.e. below) we can lift it to a cocone "above", and further that `F`
reflects limits for `K`.

If `F` reflects isomorphisms, it suffices to show only that the lifted cocone is
a limit - see `createsColimitOfReflectsIso`.
-/
/-
**CategoryTheory.CreatesColimit** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {J : Typ
e w} →           [inst_2 : CategoryTheory.Category.{w', w} J] →             Cate
goryTheory.Functor J C → CategoryTheory.Functor C D → Type (max (max (max (max u
₁ u₂) v₁) v₂) w)
参数：max (max (max (max u₁ u₂) v₁) v₂) w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dual of definition 3.3.1 of [Riehl].
We say that `F` creates colimits of `K` if, given any limit cocone `c` for
`K ⋙ F` (i.e. below) we can lift it to a cocone "above", and further that `F`
reflects limits for `K`.

If `F` reflects isomorphisms, it suffices to show only that the lifted cocone is
a limit - see `createsColimitOfReflectsIso`.
-/
class CreatesColimit (K : J ⥤ C) (F : C ⥤ D) extends ReflectsColimit K F where
  /-- any limit cocone can be lifted to a cocone above -/
  lifts : ∀ c, IsColimit c → LiftableCocone K F c

/-- `F` creates colimits of shape `J` if `F` creates the colimit of any diagram
`K : J ⥤ C`.
-/
/-
**CategoryTheory.CreatesColimitsOfShape** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory
`。
形式化陈述：CreatesColimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where Cr
eatesColimit : forall {K : J ⥤ C}, CreatesColimit K F
参数：J : Type w；F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F` creates colimits of shape `J` if `F` creates the colimit of any diagram
`K : J ⥤ C`.
-/
class CreatesColimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  CreatesColimit : ∀ {K : J ⥤ C}, CreatesColimit K F := by infer_instance

-- This should be used with explicit universe variables.
set_option linter.checkUnivs false in
/-- `F` creates colimits if it creates colimits of shape `J` for any small `J`. -/
@[univ_out_params, pp_with_univ]
/-
**CategoryTheory.CreatesColimitsOfSize** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`
。
形式化陈述：CreatesColimitsOfSize (F : C ⥤ D) where CreatesColimitsOfShape : forall {J
 : Type w} [Category.{w'} J], CreatesColimitsOfShape J F
参数：F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F` creates colimits if it creates colimits of shape `J` for any small `J`.
-/
class CreatesColimitsOfSize (F : C ⥤ D) where
  CreatesColimitsOfShape : ∀ {J : Type w} [Category.{w'} J], CreatesColimitsOfShape J F := by
    infer_instance

/-- `F` creates small colimits if it creates colimits of shape `J` for any small `J`. -/
/-
**CategoryTheory.CreatesColimits** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：CreatesColimits (F : C ⥤ D)
参数：F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F` creates small colimits if it creates colimits of shape `J` for any small `J`
.
-/
abbrev CreatesColimits (F : C ⥤ D) :=
  CreatesColimitsOfSize.{v₂, v₂} F

-- see Note [lower instance priority]
attribute [instance_reducible, instance 100]
  CreatesLimitsOfShape.CreatesLimit CreatesLimitsOfSize.CreatesLimitsOfShape
  CreatesColimitsOfShape.CreatesColimit CreatesColimitsOfSize.CreatesColimitsOfShape

-- see Note [lower instance priority]
-- Interface to the `CreatesLimit` class.
/-- `liftLimit t` is the cone for `K` given by lifting the limit `t` for `K ⋙ F`. -/
/-
**CategoryTheory.liftLimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：liftLimit {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)} (t
 : IsLimit c) : Cone K
参数：K ⋙ F；t : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`liftLimit t` is the cone for `K` given by lifting the limit `t` for `K ⋙ F`.
-/
def liftLimit {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)} (t : IsLimit c) :
    Cone K :=
  (CreatesLimit.lifts c t).liftedCone

/-- The lifted cone has an image isomorphic to the original cone. -/
/-
**CategoryTheory.liftedLimitMapsToOriginal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory`。
形式化陈述：liftedLimitMapsToOriginal {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : 
Cone (K ⋙ F)} (t : IsLimit c) : F.mapCone (liftLimit t) ≅ c
参数：K ⋙ F；t : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lifted cone has an image isomorphic to the original cone.
-/
def liftedLimitMapsToOriginal {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)}
    (t : IsLimit c) : F.mapCone (liftLimit t) ≅ c :=
  (CreatesLimit.lifts c t).validLift

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.liftedLimitMapsToOriginal_inv_map_** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma liftedLimitMapsToOriginal_inv_map_π
    {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)} (t : IsLimit c) (j : J) :
      (liftedLimitMapsToOriginal t).inv.hom ≫ F.map ((liftLimit t).π.app j) = c.π.app j := by
  rw [show F.map ((liftLimit t).π.app j) = (liftedLimitMapsToOriginal t).hom.hom ≫ c.π.app j
    from (by simp), ← Category.assoc, ← Cone.category_comp_hom]
  simp

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.liftedLimitMapsToOriginal_hom_** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma liftedLimitMapsToOriginal_hom_π
    {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)} (t : IsLimit c) (j : J) :
      (liftedLimitMapsToOriginal t).hom.hom ≫ c.π.app j = F.map ((liftLimit t).π.app j) := by
  rw [← liftedLimitMapsToOriginal_inv_map_π (t := t)]
  simp only [← Category.assoc, ← Cone.category_comp_hom,
    Iso.hom_inv_id, Cone.category_id_hom, Category.id_comp]

/-- The lifted cone is a limit. -/
/-
**CategoryTheory.liftedLimitIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：liftedLimitIsLimit {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K
 ⋙ F)} (t : IsLimit c) : IsLimit (liftLimit t)
参数：K ⋙ F；t : IsLimit c。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CreatesLimit.toReflectsLimit`：∀ {C : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
The lifted cone is a limit.
-/
def liftedLimitIsLimit {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)}
    (t : IsLimit c) : IsLimit (liftLimit t) :=
  isLimitOfReflects _ (IsLimit.ofIsoLimit t (liftedLimitMapsToOriginal t).symm)

/-- If `F` creates the limit of `K` and `K ⋙ F` has a limit, then `K` has a limit. -/
/-
**CategoryTheory.hasLimit_of_created** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：hasLimit_of_created (K : J ⥤ C) (F : C ⥤ D) [HasLimit (K ⋙ F)] [CreatesLim
it K F] : HasLimit K
参数：K : J ⥤ C；F : C ⥤ D；K ⋙ F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…

--- 原说明 ---
If `F` creates the limit of `K` and `K ⋙ F` has a limit, then `K` has a limit.
-/
theorem hasLimit_of_created (K : J ⥤ C) (F : C ⥤ D) [HasLimit (K ⋙ F)] [CreatesLimit K F] :
    HasLimit K :=
  HasLimit.mk
    { cone := liftLimit (limit.isLimit (K ⋙ F))
      isLimit := liftedLimitIsLimit _ }

/-- If `F` creates limits of shape `J`, and `D` has limits of shape `J`, then
`C` has limits of shape `J`.
-/
/-
**CategoryTheory.hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (F : C ⥤ D) [Has
LimitsOfShape J D] [CreatesLimitsOfShape J F] : HasLimitsOfShape J C
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimit_of_created`：hasLimit_of_created (K : J ⥤ C) (F :
 C ⥤ D) [HasLimit (K ⋙ F)] [CreatesLimit K F] : HasLimit K
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
If `F` creates limits of shape `J`, and `D` has limits of shape `J`, then
`C` has limits of shape `J`.
-/
theorem hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (F : C ⥤ D) [HasLimitsOfShape J D]
    [CreatesLimitsOfShape J F] : HasLimitsOfShape J C :=
  ⟨fun G => hasLimit_of_created G F⟩

/-- If `F` creates limits, and `D` has all limits, then `C` has all limits. -/
/-
**CategoryTheory.hasLimits_of_hasLimits_createsLimits** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory`。
形式化陈述：hasLimits_of_hasLimits_createsLimits (F : C ⥤ D) [HasLimitsOfSize.{w, w'} 
D] [CreatesLimitsOfSize.{w, w'} F] : HasLimitsOfSize.{w, w'} C
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
`：hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (F : C ⥤ D) [HasLimi
tsOfShape J D] [CreatesLimitsOfShape J F] : HasLimitsOfShape J…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
If `F` creates limits, and `D` has all limits, then `C` has all limits.
-/
theorem hasLimits_of_hasLimits_createsLimits (F : C ⥤ D) [HasLimitsOfSize.{w, w'} D]
    [CreatesLimitsOfSize.{w, w'} F] : HasLimitsOfSize.{w, w'} C :=
  ⟨fun _ _ => hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape F⟩

-- Interface to the `CreatesColimit` class.
/-- `liftColimit t` is the cocone for `K` given by lifting the colimit `t` for `K ⋙ F`. -/
/-
**CategoryTheory.liftColimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：liftColimit {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : Cocone (K ⋙ 
F)} (t : IsColimit c) : Cocone K
参数：K ⋙ F；t : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`liftColimit t` is the cocone for `K` given by lifting the colimit `t` for `K ⋙ 
F`.
-/
def liftColimit {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : Cocone (K ⋙ F)}
    (t : IsColimit c) : Cocone K :=
  (CreatesColimit.lifts c t).liftedCocone

/-- The lifted cocone has an image isomorphic to the original cocone. -/
/-
**CategoryTheory.liftedColimitMapsToOriginal** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory`。
形式化陈述：liftedColimitMapsToOriginal {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {
c : Cocone (K ⋙ F)} (t : IsColimit c) : F.mapCocone (liftColimit t) ≅ c
参数：K ⋙ F；t : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lifted cocone has an image isomorphic to the original cocone.
-/
def liftedColimitMapsToOriginal {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : Cocone (K ⋙ F)}
    (t : IsColimit c) : F.mapCocone (liftColimit t) ≅ c :=
  (CreatesColimit.lifts c t).validLift

/-- The lifted cocone is a colimit. -/
/-
**CategoryTheory.liftedColimitIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y`。
形式化陈述：liftedColimitIsColimit {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : C
ocone (K ⋙ F)} (t : IsColimit c) : IsColimit (liftColimit t)
参数：K ⋙ F；t : IsColimit c。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CreatesColimit.toReflectsColimit`：∀ {C : Type u₁} {inst :
 CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
The lifted cocone is a colimit.
-/
def liftedColimitIsColimit {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : Cocone (K ⋙ F)}
    (t : IsColimit c) : IsColimit (liftColimit t) :=
  isColimitOfReflects _ (IsColimit.ofIsoColimit t (liftedColimitMapsToOriginal t).symm)

/-- If `F` creates the limit of `K` and `K ⋙ F` has a limit, then `K` has a limit. -/
/-
**CategoryTheory.hasColimit_of_created** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
`。
形式化陈述：hasColimit_of_created (K : J ⥤ C) (F : C ⥤ D) [HasColimit (K ⋙ F)] [Create
sColimit K F] : HasColimit K
参数：K : J ⥤ C；F : C ⥤ D；K ⋙ F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…

--- 原说明 ---
If `F` creates the limit of `K` and `K ⋙ F` has a limit, then `K` has a limit.
-/
theorem hasColimit_of_created (K : J ⥤ C) (F : C ⥤ D) [HasColimit (K ⋙ F)] [CreatesColimit K F] :
    HasColimit K :=
  HasColimit.mk
    { cocone := liftColimit (colimit.isColimit (K ⋙ F))
      isColimit := liftedColimitIsColimit _ }

/-- If `F` creates colimits of shape `J`, and `D` has colimits of shape `J`, then
`C` has colimits of shape `J`.
-/
/-
**CategoryTheory.hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (F : C ⥤ D
) [HasColimitsOfShape J D] [CreatesColimitsOfShape J F] : HasColimitsOfShape J C
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasColimit_of_created`：hasColimit_of_created (K : J ⥤ C) 
(F : C ⥤ D) [HasColimit (K ⋙ F)] [CreatesColimit K F] : HasColimit K
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
If `F` creates colimits of shape `J`, and `D` has colimits of shape `J`, then
`C` has colimits of shape `J`.
-/
theorem hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (F : C ⥤ D)
    [HasColimitsOfShape J D] [CreatesColimitsOfShape J F] : HasColimitsOfShape J C :=
  ⟨fun G => hasColimit_of_created G F⟩

/-- If `F` creates colimits, and `D` has all colimits, then `C` has all colimits. -/
/-
**CategoryTheory.hasColimits_of_hasColimits_createsColimits** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory`。
形式化陈述：hasColimits_of_hasColimits_createsColimits (F : C ⥤ D) [HasColimitsOfSize.
{w, w'} D] [CreatesColimitsOfSize.{w, w'} F] : HasColimitsOfSize.{w, w'} C
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsO
fShape`：hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (F : C ⥤
 D) [HasColimitsOfShape J D] [CreatesColimitsOfShape J F] : HasColim…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
If `F` creates colimits, and `D` has all colimits, then `C` has all colimits.
-/
theorem hasColimits_of_hasColimits_createsColimits (F : C ⥤ D) [HasColimitsOfSize.{w, w'} D]
    [CreatesColimitsOfSize.{w, w'} F] : HasColimitsOfSize.{w, w'} C :=
  ⟨fun _ _ => hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape F⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 10) reflectsLimitsOfShapeOfCreatesLimitsOfShape (F : C ⥤ D)
    [CreatesLimitsOfShape J F] : ReflectsLimitsOfShape J F where
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 10) reflectsLimitsOfCreatesLimits (F : C ⥤ D)
    [CreatesLimitsOfSize.{w, w'} F] : ReflectsLimitsOfSize.{w, w'} F where
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 10) reflectsColimitsOfShapeOfCreatesColimitsOfShape (F : C ⥤ D)
    [CreatesColimitsOfShape J F] : ReflectsColimitsOfShape J F where
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 10) reflectsColimitsOfCreatesColimits (F : C ⥤ D)
    [CreatesColimitsOfSize.{w, w'} F] : ReflectsColimitsOfSize.{w, w'} F where

/-- A helper to show a functor creates limits. In particular, if we can show
that for any limit cone `c` for `K ⋙ F`, there is a lift of it which is
a limit and `F` reflects isomorphisms, then `F` creates limits.
Usually, `F` creating limits says that _any_ lift of `c` is a limit, but
here we only need to show that our particular lift of `c` is a limit.
-/
/-
**CategoryTheory.LiftsToLimit** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {J : Typ
e w} →           [inst_2 : CategoryTheory.Category.{w', w} J] →             (K :
 CategoryTheory.Functor J C) →               (F : CategoryTheory.Functor C D) → 
                (c : CategoryTheory.Limits.Cone (K.comp F)) →                   
CategoryTheory.Limits.IsLimit c → Type (max (max (max u₁ v₁) v₂) w)
参数：K : CategoryTheory.Functor J C；F : CategoryTheory.Functor C D；c : CategoryThe
ory.Limits.Cone (K.comp F)；max (max (max u₁ v₁) v₂) w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A helper to show a functor creates limits. In particular, if we can show
that for any limit cone `c` for `K ⋙ F`, there is a lift of it which is
a limit and `F` reflects isomorphisms, then `F` creates limits.
Usually, `F` creating limits says that _any_ lift of `c` is a limit, but
here we only need to show that our particular lift of `c` is a limit.
-/
structure LiftsToLimit (K : J ⥤ C) (F : C ⥤ D) (c : Cone (K ⋙ F)) (t : IsLimit c) extends
  LiftableCone K F c where
  /-- the lifted cone is limit -/
  makesLimit : IsLimit liftedCone

/-- A helper to show a functor creates colimits. In particular, if we can show
that for any limit cocone `c` for `K ⋙ F`, there is a lift of it which is
a limit and `F` reflects isomorphisms, then `F` creates colimits.
Usually, `F` creating colimits says that _any_ lift of `c` is a colimit, but
here we only need to show that our particular lift of `c` is a colimit.
-/
/-
**CategoryTheory.LiftsToColimit** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {J : Typ
e w} →           [inst_2 : CategoryTheory.Category.{w', w} J] →             (K :
 CategoryTheory.Functor J C) →               (F : CategoryTheory.Functor C D) → 
                (c : CategoryTheory.Limits.Cocone (K.comp F)) →                 
  CategoryTheory.Limits.IsColimit c → Type (max (max (max u₁ v₁) v₂) w)
参数：K : CategoryTheory.Functor J C；F : CategoryTheory.Functor C D；c : CategoryThe
ory.Limits.Cocone (K.comp F)；max (max (max u₁ v₁) v₂) w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A helper to show a functor creates colimits. In particular, if we can show
that for any limit cocone `c` for `K ⋙ F`, there is a lift of it which is
a limit and `F` reflects isomorphisms, then `F` creates colimits.
Usually, `F` creating colimits says that _any_ lift of `c` is a colimit, but
here we only need to show that our particular lift of `c` is a colimit.
-/
structure LiftsToColimit (K : J ⥤ C) (F : C ⥤ D) (c : Cocone (K ⋙ F)) (t : IsColimit c) extends
  LiftableCocone K F c where
  /-- the lifted cocone is colimit -/
  makesColimit : IsColimit liftedCocone

set_option backward.isDefEq.respectTransparency.types false in
/-- If `F` reflects isomorphisms and we can lift any limit cone to a limit cone,
then `F` creates limits.
In particular here we don't need to assume that F reflects limits.
-/
@[instance_reducible]
/-
**CategoryTheory.createsLimitOfReflectsIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory`。
形式化陈述：createsLimitOfReflectsIso {K : J ⥤ C} {F : C ⥤ D} [F.ReflectsIsomorphisms]
 (h : forall c t, LiftsToLimit K F c t) : CreatesLimit K F where lifts c t
参数：h : forall c t, LiftsToLimit K F c t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` reflects isomorphisms and we can lift any limit cone to a limit cone,
then `F` creates limits.
In particular here we don't need to assume that F reflects limits.
-/
def createsLimitOfReflectsIso {K : J ⥤ C} {F : C ⥤ D} [F.ReflectsIsomorphisms]
    (h : ∀ c t, LiftsToLimit K F c t) : CreatesLimit K F where
  lifts c t := (h c t).toLiftableCone
  toReflectsLimit :=
    { reflects := fun {d} hd => ⟨by
        let d' : Cone K := (h (F.mapCone d) hd).toLiftableCone.liftedCone
        let i : F.mapCone d' ≅ F.mapCone d :=
          (h (F.mapCone d) hd).toLiftableCone.validLift
        let hd' : IsLimit d' := (h (F.mapCone d) hd).makesLimit
        let f : d ⟶ d' := hd'.liftConeMorphism d
        have : (Cone.functoriality K F).map f = i.inv :=
          (hd.ofIsoLimit i.symm).uniq_cone_morphism
        haveI : IsIso ((Cone.functoriality K F).map f) := by
          rw [this]
          infer_instance
        haveI : IsIso f := isIso_of_reflects_iso f (Cone.functoriality K F)
        exact IsLimit.ofIsoLimit hd' (asIso f).symm⟩ }

/-- If `F` reflects isomorphisms and we can lift a single limit cone to a limit cone, then `F`
creates limits. Note that unlike `createsLimitOfReflectsIso`, to apply this result it is
necessary to know that `K ⋙ F` actually has a limit. -/
@[instance_reducible]
/-
**CategoryTheory.createsLimitOfReflectsIso'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory`。
形式化陈述：createsLimitOfReflectsIso' {K : J ⥤ C} {F : C ⥤ D} [F.ReflectsIsomorphisms
] {c : Cone (K ⋙ F)} (hc : IsLimit c) (h : LiftsToLimit K F c hc) : CreatesLimit
 K F
参数：K ⋙ F；hc : IsLimit c；h : LiftsToLimit K F c hc。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` reflects isomorphisms and we can lift a single limit cone to a limit cone
, then `F`
creates limits. Note that unlike `createsLimitOfReflectsIso`, to apply this resu
lt it is
necessary to know that `K ⋙ F` actually has a limit.
-/
def createsLimitOfReflectsIso' {K : J ⥤ C} {F : C ⥤ D} [F.ReflectsIsomorphisms]
    {c : Cone (K ⋙ F)} (hc : IsLimit c) (h : LiftsToLimit K F c hc) : CreatesLimit K F :=
  createsLimitOfReflectsIso fun _ t =>
    { liftedCone := h.liftedCone
      validLift := h.validLift ≪≫ IsLimit.uniqueUpToIso hc t
      makesLimit := h.makesLimit }

/-- If `F` reflects isomorphisms, and we already know that the limit exists in the source and `F`
preserves it, then `F` creates that limit. -/
@[instance_reducible]
/-
**CategoryTheory.createsLimitOfReflectsIsomorphismsOfPreserves** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory`。
形式化陈述：createsLimitOfReflectsIsomorphismsOfPreserves {K : J ⥤ C} {F : C ⥤ D} [F.R
eflectsIsomorphisms] [HasLimit K] [PreservesLimit K F] : CreatesLimit K F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` reflects isomorphisms, and we already know that the limit exists in the s
ource and `F`
preserves it, then `F` creates that limit.
-/
def createsLimitOfReflectsIsomorphismsOfPreserves {K : J ⥤ C} {F : C ⥤ D} [F.ReflectsIsomorphisms]
    [HasLimit K] [PreservesLimit K F] : CreatesLimit K F :=
  createsLimitOfReflectsIso' (isLimitOfPreserves F (limit.isLimit _))
    ⟨⟨_, Iso.refl _⟩, limit.isLimit _⟩

-- Notice however that even if the isomorphism is `Iso.refl _`,
-- this construction will insert additional identity morphisms in the cone maps,
-- so the constructed limits may not be ideal, definitionally.
/--
When `F` is fully faithful, to show that `F` creates the limit for `K` it suffices to exhibit a lift
of a limit cone for `K ⋙ F`.
-/
@[instance_reducible]
/-
**CategoryTheory.createsLimitOfFullyFaithfulOfLift'** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory`。
形式化陈述：createsLimitOfFullyFaithfulOfLift' {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Fai
thful] {l : Cone (K ⋙ F)} (hl : IsLimit l) (c : Cone K) (i : F.mapCone c ≅ l) : 
CreatesLimit K F
参数：K ⋙ F；hl : IsLimit l；c : Cone K；i : F.mapCone c ≅ l。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…

--- 原说明 ---
When `F` is fully faithful, to show that `F` creates the limit for `K` it suffic
es to exhibit a lift
of a limit cone for `K ⋙ F`.
-/
def createsLimitOfFullyFaithfulOfLift' {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    {l : Cone (K ⋙ F)} (hl : IsLimit l) (c : Cone K) (i : F.mapCone c ≅ l) :
    CreatesLimit K F :=
  createsLimitOfReflectsIso' hl ⟨⟨c, i⟩, isLimitOfReflects F (IsLimit.ofIsoLimit hl i.symm)⟩

-- Notice however that even if the isomorphism is `Iso.refl _`,
-- this construction will insert additional identity morphisms in the cone maps,
-- so the constructed limits may not be ideal, definitionally.
/-- When `F` is fully faithful, and `HasLimit (K ⋙ F)`, to show that `F` creates the limit for `K`
it suffices to exhibit a lift of the chosen limit cone for `K ⋙ F`.
-/
@[instance_reducible]
/-
**CategoryTheory.createsLimitOfFullyFaithfulOfLift** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：createsLimitOfFullyFaithfulOfLift {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Fait
hful] [HasLimit (K ⋙ F)] (c : Cone K) (i : F.mapCone c ≅ limit.cone (K ⋙ F)) : C
reatesLimit K F
参数：K ⋙ F；c : Cone K；i : F.mapCone c ≅ limit.cone (K ⋙ F)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `F` is fully faithful, and `HasLimit (K ⋙ F)`, to show that `F` creates the
 limit for `K`
it suffices to exhibit a lift of the chosen limit cone for `K ⋙ F`.
-/
def createsLimitOfFullyFaithfulOfLift {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    [HasLimit (K ⋙ F)] (c : Cone K) (i : F.mapCone c ≅ limit.cone (K ⋙ F)) :
    CreatesLimit K F :=
  createsLimitOfFullyFaithfulOfLift' (limit.isLimit _) c i

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- Notice however that even if the isomorphism is `Iso.refl _`,
-- this construction will insert additional identity morphisms in the cone maps,
-- so the constructed limits may not be ideal, definitionally.
/--
When `F` is fully faithful, to show that `F` creates the limit for `K` it suffices to show that a
limit point is in the essential image of `F`.
-/
@[instance_reducible]
/-
**CategoryTheory.createsLimitOfFullyFaithfulOfIso'** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：createsLimitOfFullyFaithfulOfIso' {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Fait
hful] {l : Cone (K ⋙ F)} (hl : IsLimit l) (X : C) (i : F.obj X ≅ l.pt) : Creates
Limit K F
参数：K ⋙ F；hl : IsLimit l；X : C；i : F.obj X ≅ l.pt。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `F` is fully faithful, to show that `F` creates the limit for `K` it suffic
es to show that a
limit point is in the essential image of `F`.
-/
def createsLimitOfFullyFaithfulOfIso' {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    {l : Cone (K ⋙ F)} (hl : IsLimit l) (X : C) (i : F.obj X ≅ l.pt) : CreatesLimit K F :=
  createsLimitOfFullyFaithfulOfLift' hl
    { pt := X
      π :=
        { app := fun j => F.preimage (i.hom ≫ l.π.app j)
          naturality := fun Y Z f =>
            F.map_injective <| by
              simpa using (l.w f).symm } }
    (Cone.ext i fun j => by simp only [Functor.map_preimage, Functor.mapCone_π_app])

-- Notice however that even if the isomorphism is `Iso.refl _`,
-- this construction will insert additional identity morphisms in the cone maps,
-- so the constructed limits may not be ideal, definitionally.
/-- When `F` is fully faithful, and `HasLimit (K ⋙ F)`, to show that `F` creates the limit for `K`
it suffices to show that the chosen limit point is in the essential image of `F`.
-/
@[instance_reducible]
/-
**CategoryTheory.createsLimitOfFullyFaithfulOfIso** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory`。
形式化陈述：createsLimitOfFullyFaithfulOfIso {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faith
ful] [HasLimit (K ⋙ F)] (X : C) (i : F.obj X ≅ limit (K ⋙ F)) : CreatesLimit K F
参数：K ⋙ F；X : C；i : F.obj X ≅ limit (K ⋙ F)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `F` is fully faithful, and `HasLimit (K ⋙ F)`, to show that `F` creates the
 limit for `K`
it suffices to show that the chosen limit point is in the essential image of `F`
.
-/
def createsLimitOfFullyFaithfulOfIso {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    [HasLimit (K ⋙ F)] (X : C) (i : F.obj X ≅ limit (K ⋙ F)) : CreatesLimit K F :=
  createsLimitOfFullyFaithfulOfIso' (limit.isLimit _) X i

/-- A fully faithful functor that preserves a limit that exists also creates the limit. -/
@[instance_reducible]
/-
**CategoryTheory.createsLimitOfFullyFaithfulOfPreserves** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory`。
形式化陈述：createsLimitOfFullyFaithfulOfPreserves {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F
.Faithful] [HasLimit K] [PreservesLimit K F] : CreatesLimit K F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A fully faithful functor that preserves a limit that exists also creates the lim
it.
-/
def createsLimitOfFullyFaithfulOfPreserves {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    [HasLimit K] [PreservesLimit K F] : CreatesLimit K F :=
  createsLimitOfFullyFaithfulOfLift' (isLimitOfPreserves _ (limit.isLimit K)) _ (Iso.refl _)

-- see Note [lower instance priority]
/-- `F` preserves the limit of `K` if it creates the limit and `K ⋙ F` has the limit. -/
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F` preserves the limit of `K` if it creates the limit and `K ⋙ F` has the limit
.
-/
instance (priority := 100) preservesLimit_of_createsLimit_and_hasLimit (K : J ⥤ C) (F : C ⥤ D)
    [CreatesLimit K F] [HasLimit (K ⋙ F)] : PreservesLimit K F where
  preserves t := ⟨IsLimit.ofIsoLimit (limit.isLimit _)
    ((liftedLimitMapsToOriginal (limit.isLimit _)).symm ≪≫
      (Cone.functoriality K F).mapIso ((liftedLimitIsLimit (limit.isLimit _)).uniqueUpToIso t))⟩

-- see Note [lower instance priority]
/-- `F` preserves the limit of shape `J` if it creates these limits and `D` has them. -/
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F` preserves the limit of shape `J` if it creates these limits and `D` has them
.
-/
instance (priority := 100) preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape
    (F : C ⥤ D) [CreatesLimitsOfShape J F] [HasLimitsOfShape J D] : PreservesLimitsOfShape J F where

-- see Note [lower instance priority]
/-- `F` preserves limits if it creates limits and `D` has limits. -/
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F` preserves limits if it creates limits and `D` has limits.
-/
instance (priority := 100) preservesLimits_of_createsLimits_and_hasLimits (F : C ⥤ D)
    [CreatesLimitsOfSize.{w, w'} F] [HasLimitsOfSize.{w, w'} D] :
    PreservesLimitsOfSize.{w, w'} F where

set_option backward.isDefEq.respectTransparency.types false in
/-- If `F` reflects isomorphisms and we can lift any colimit cocone to a colimit cocone,
then `F` creates colimits.
In particular here we don't need to assume that F reflects colimits.
-/
@[instance_reducible]
/-
**CategoryTheory.createsColimitOfReflectsIso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory`。
形式化陈述：createsColimitOfReflectsIso {K : J ⥤ C} {F : C ⥤ D} [F.ReflectsIsomorphism
s] (h : forall c t, LiftsToColimit K F c t) : CreatesColimit K F where lifts c t
参数：h : forall c t, LiftsToColimit K F c t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` reflects isomorphisms and we can lift any colimit cocone to a colimit coc
one,
then `F` creates colimits.
In particular here we don't need to assume that F reflects colimits.
-/
def createsColimitOfReflectsIso {K : J ⥤ C} {F : C ⥤ D} [F.ReflectsIsomorphisms]
    (h : ∀ c t, LiftsToColimit K F c t) : CreatesColimit K F where
  lifts c t := (h c t).toLiftableCocone
  toReflectsColimit :=
    { reflects := fun {d} hd => ⟨by
        let d' : Cocone K := (h (F.mapCocone d) hd).toLiftableCocone.liftedCocone
        let i : F.mapCocone d' ≅ F.mapCocone d :=
          (h (F.mapCocone d) hd).toLiftableCocone.validLift
        let hd' : IsColimit d' := (h (F.mapCocone d) hd).makesColimit
        let f : d' ⟶ d := hd'.descCoconeMorphism d
        have : (Cocone.functoriality K F).map f = i.hom :=
          (hd.ofIsoColimit i.symm).uniq_cocone_morphism
        haveI : IsIso ((Cocone.functoriality K F).map f) := by
          rw [this]
          infer_instance
        haveI := isIso_of_reflects_iso f (Cocone.functoriality K F)
        exact IsColimit.ofIsoColimit hd' (asIso f)⟩ }

/-- If `F` reflects isomorphisms and we can lift a single colimit cocone to a colimit cocone, then
`F` creates limits. Note that unlike `createsColimitOfReflectsIso`, to apply this result it is
necessary to know that `K ⋙ F` actually has a colimit. -/
@[instance_reducible]
/-
**CategoryTheory.createsColimitOfReflectsIso'** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory`。
形式化陈述：createsColimitOfReflectsIso' {K : J ⥤ C} {F : C ⥤ D} [F.ReflectsIsomorphis
ms] {c : Cocone (K ⋙ F)} (hc : IsColimit c) (h : LiftsToColimit K F c hc) : Crea
tesColimit K F
参数：K ⋙ F；hc : IsColimit c；h : LiftsToColimit K F c hc。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` reflects isomorphisms and we can lift a single colimit cocone to a colimi
t cocone, then
`F` creates limits. Note that unlike `createsColimitOfReflectsIso`, to apply thi
s result it is
necessary to know that `K ⋙ F` actually has a colimit.
-/
def createsColimitOfReflectsIso' {K : J ⥤ C} {F : C ⥤ D} [F.ReflectsIsomorphisms]
    {c : Cocone (K ⋙ F)} (hc : IsColimit c) (h : LiftsToColimit K F c hc) : CreatesColimit K F :=
  createsColimitOfReflectsIso fun _ t =>
    { liftedCocone := h.liftedCocone
      validLift := h.validLift ≪≫ IsColimit.uniqueUpToIso hc t
      makesColimit := h.makesColimit }

/-- If `F` reflects isomorphisms, and we already know that the colimit exists in the source and `F`
preserves it, then `F` creates that colimit. -/
@[instance_reducible]
/-
**CategoryTheory.createsColimitOfReflectsIsomorphismsOfPreserves** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory`。
形式化陈述：createsColimitOfReflectsIsomorphismsOfPreserves {K : J ⥤ C} {F : C ⥤ D} [F
.ReflectsIsomorphisms] [HasColimit K] [PreservesColimit K F] : CreatesColimit K 
F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` reflects isomorphisms, and we already know that the colimit exists in the
 source and `F`
preserves it, then `F` creates that colimit.
-/
def createsColimitOfReflectsIsomorphismsOfPreserves {K : J ⥤ C} {F : C ⥤ D}
    [F.ReflectsIsomorphisms] [HasColimit K] [PreservesColimit K F] : CreatesColimit K F :=
  createsColimitOfReflectsIso' (isColimitOfPreserves F (colimit.isColimit _))
    ⟨⟨_, Iso.refl _⟩, colimit.isColimit _⟩

-- Notice however that even if the isomorphism is `Iso.refl _`,
-- this construction will insert additional identity morphisms in the cocone maps,
-- so the constructed colimits may not be ideal, definitionally.
/--
When `F` is fully faithful, to show that `F` creates the colimit for `K` it suffices to exhibit a
lift of a colimit cocone for `K ⋙ F`.
-/
@[instance_reducible]
/-
**CategoryTheory.createsColimitOfFullyFaithfulOfLift'** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory`。
形式化陈述：createsColimitOfFullyFaithfulOfLift' {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.F
aithful] {l : Cocone (K ⋙ F)} (hl : IsColimit l) (c : Cocone K) (i : F.mapCocone
 c ≅ l) : CreatesColimit K F
参数：K ⋙ F；hl : IsColimit l；c : Cocone K；i : F.mapCocone c ≅ l。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…

--- 原说明 ---
When `F` is fully faithful, to show that `F` creates the colimit for `K` it suff
ices to exhibit a
lift of a colimit cocone for `K ⋙ F`.
-/
def createsColimitOfFullyFaithfulOfLift' {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    {l : Cocone (K ⋙ F)} (hl : IsColimit l) (c : Cocone K) (i : F.mapCocone c ≅ l) :
    CreatesColimit K F :=
  createsColimitOfReflectsIso' hl ⟨⟨c, i⟩, isColimitOfReflects F (IsColimit.ofIsoColimit hl i.symm)⟩

-- Notice however that even if the isomorphism is `Iso.refl _`,
-- this construction will insert additional identity morphisms in the cocone maps,
-- so the constructed colimits may not be ideal, definitionally.
/--
When `F` is fully faithful, and `HasColimit (K ⋙ F)`, to show that `F` creates the colimit for `K`
it suffices to exhibit a lift of the chosen colimit cocone for `K ⋙ F`.
-/
@[instance_reducible]
/-
**CategoryTheory.createsColimitOfFullyFaithfulOfLift** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory`。
形式化陈述：createsColimitOfFullyFaithfulOfLift {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Fa
ithful] [HasColimit (K ⋙ F)] (c : Cocone K) (i : F.mapCocone c ≅ colimit.cocone 
(K ⋙ F)) : CreatesColimit K F
参数：K ⋙ F；c : Cocone K；i : F.mapCocone c ≅ colimit.cocone (K ⋙ F)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `F` is fully faithful, and `HasColimit (K ⋙ F)`, to show that `F` creates t
he colimit for `K`
it suffices to exhibit a lift of the chosen colimit cocone for `K ⋙ F`.
-/
def createsColimitOfFullyFaithfulOfLift {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    [HasColimit (K ⋙ F)] (c : Cocone K) (i : F.mapCocone c ≅ colimit.cocone (K ⋙ F)) :
    CreatesColimit K F :=
  createsColimitOfFullyFaithfulOfLift' (colimit.isColimit _) c i

set_option backward.defeqAttrib.useBackward true in
-- Notice however that even if the isomorphism is `Iso.refl _`,
-- this construction will insert additional identity morphisms in the cocone maps,
-- so the constructed colimits may not be ideal, definitionally.
/--
When `F` is fully faithful, to show that `F` creates the colimit for `K` it suffices to show that
a colimit point is in the essential image of `F`.
-/
@[instance_reducible]
/-
**CategoryTheory.createsColimitOfFullyFaithfulOfIso'** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory`。
形式化陈述：createsColimitOfFullyFaithfulOfIso' {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Fa
ithful] {l : Cocone (K ⋙ F)} (hl : IsColimit l) (X : C) (i : F.obj X ≅ l.pt) : C
reatesColimit K F
参数：K ⋙ F；hl : IsColimit l；X : C；i : F.obj X ≅ l.pt。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `F` is fully faithful, to show that `F` creates the colimit for `K` it suff
ices to show that
a colimit point is in the essential image of `F`.
-/
def createsColimitOfFullyFaithfulOfIso' {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    {l : Cocone (K ⋙ F)} (hl : IsColimit l) (X : C) (i : F.obj X ≅ l.pt) : CreatesColimit K F :=
  createsColimitOfFullyFaithfulOfLift' hl
    { pt := X
      ι :=
        { app := fun j => F.preimage (l.ι.app j ≫ i.inv)
          naturality := fun Y Z f =>
            F.map_injective <| by
              simpa [← cancel_mono i.hom] using l.w f } }
    (Cocone.ext i fun j => by simp)

-- Notice however that even if the isomorphism is `Iso.refl _`,
-- this construction will insert additional identity morphisms in the cocone maps,
-- so the constructed colimits may not be ideal, definitionally.
/--
When `F` is fully faithful, and `HasColimit (K ⋙ F)`, to show that `F` creates the colimit for `K`
it suffices to show that the chosen colimit point is in the essential image of `F`.
-/
@[instance_reducible]
/-
**CategoryTheory.createsColimitOfFullyFaithfulOfIso** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory`。
形式化陈述：createsColimitOfFullyFaithfulOfIso {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Fai
thful] [HasColimit (K ⋙ F)] (X : C) (i : F.obj X ≅ colimit (K ⋙ F)) : CreatesCol
imit K F
参数：K ⋙ F；X : C；i : F.obj X ≅ colimit (K ⋙ F)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `F` is fully faithful, and `HasColimit (K ⋙ F)`, to show that `F` creates t
he colimit for `K`
it suffices to show that the chosen colimit point is in the essential image of `
F`.
-/
def createsColimitOfFullyFaithfulOfIso {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    [HasColimit (K ⋙ F)] (X : C) (i : F.obj X ≅ colimit (K ⋙ F)) : CreatesColimit K F :=
  createsColimitOfFullyFaithfulOfIso' (colimit.isColimit _) X i

-- see Note [lower instance priority]
/-- `F` preserves the colimit of `K` if it creates the colimit and `K ⋙ F` has the colimit. -/
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F` preserves the colimit of `K` if it creates the colimit and `K ⋙ F` has the c
olimit.
-/
instance (priority := 100) preservesColimit_of_createsColimit_and_hasColimit (K : J ⥤ C) (F : C ⥤ D)
    [CreatesColimit K F] [HasColimit (K ⋙ F)] : PreservesColimit K F where
  preserves t :=
    ⟨IsColimit.ofIsoColimit (colimit.isColimit _)
      ((liftedColimitMapsToOriginal (colimit.isColimit _)).symm ≪≫
        (Cocone.functoriality K F).mapIso
          ((liftedColimitIsColimit (colimit.isColimit _)).uniqueUpToIso t))⟩

-- see Note [lower instance priority]
/-- `F` preserves the colimit of shape `J` if it creates these colimits and `D` has them. -/
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F` preserves the colimit of shape `J` if it creates these colimits and `D` has 
them.
-/
instance (priority := 100) preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape
    (F : C ⥤ D) [CreatesColimitsOfShape J F] [HasColimitsOfShape J D] :
    PreservesColimitsOfShape J F where

-- see Note [lower instance priority]
/-- `F` preserves limits if it creates limits and `D` has limits. -/
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F` preserves limits if it creates limits and `D` has limits.
-/
instance (priority := 100) preservesColimits_of_createsColimits_and_hasColimits (F : C ⥤ D)
    [CreatesColimitsOfSize.{w, w'} F] [HasColimitsOfSize.{w, w'} D] :
    PreservesColimitsOfSize.{w, w'} F where

set_option backward.defeqAttrib.useBackward true in
/-- Transfer creation of limits along a natural isomorphism in the diagram. -/
@[instance_reducible]
/-
**CategoryTheory.createsLimitOfIsoDiagram** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory`。
形式化陈述：createsLimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [Create
sLimit K₁ F] : CreatesLimit K₂ F
参数：F : C ⥤ D；h : K₁ ≅ K₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Transfer creation of limits along a natural isomorphism in the diagram.
-/
def createsLimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [CreatesLimit K₁ F] :
    CreatesLimit K₂ F :=
  { reflectsLimit_of_iso_diagram F h with
    lifts := fun c t =>
      let t' := (IsLimit.postcomposeInvEquiv (isoWhiskerRight h F :) c).symm t
      { liftedCone := (Cone.postcompose h.hom).obj (liftLimit t')
        validLift :=
          Functor.mapConePostcompose F ≪≫
            (Cone.postcompose (isoWhiskerRight h F).hom).mapIso (liftedLimitMapsToOriginal t') ≪≫
              Cone.ext (Iso.refl _) fun j => by
                dsimp
                rw [Category.assoc, ← F.map_comp]
                simp } }

/-- If `F` creates the limit of `K` and `F ≅ G`, then `G` creates the limit of `K`. -/
@[instance_reducible]
/-
**CategoryTheory.createsLimitOfNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`
。
形式化陈述：createsLimitOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesLimit K F] : Create
sLimit K G where lifts c t
参数：h : F ≅ G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `F` creates the limit of `K` and `F ≅ G`, then `G` creates the limit of `K`.
-/
def createsLimitOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesLimit K F] : CreatesLimit K G where
  lifts c t :=
    { liftedCone := liftLimit ((IsLimit.postcomposeInvEquiv (isoWhiskerLeft K h :) c).symm t)
      validLift := by
        refine (IsLimit.mapConeEquiv h ?_).uniqueUpToIso t
        apply IsLimit.ofIsoLimit _ (liftedLimitMapsToOriginal _).symm
        apply (IsLimit.postcomposeInvEquiv _ _).symm t }
  toReflectsLimit := reflectsLimit_of_natIso _ h

/-- If `F` creates limits of shape `J` and `F ≅ G`, then `G` creates limits of shape `J`. -/
@[instance_reducible]
/-
**CategoryTheory.createsLimitsOfShapeOfNatIso** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory`。
形式化陈述：createsLimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesLimitsOfSha
pe J F] : CreatesLimitsOfShape J G where CreatesLimit
参数：h : F ≅ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` creates limits of shape `J` and `F ≅ G`, then `G` creates limits of shape
 `J`.
-/
def createsLimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesLimitsOfShape J F] :
    CreatesLimitsOfShape J G where CreatesLimit := createsLimitOfNatIso h

/-- If `F` creates limits and `F ≅ G`, then `G` creates limits. -/
@[instance_reducible]
/-
**CategoryTheory.createsLimitsOfNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
`。
形式化陈述：createsLimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesLimitsOfSize.{w, w
'} F] : CreatesLimitsOfSize.{w, w'} G where CreatesLimitsOfShape
参数：h : F ≅ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` creates limits and `F ≅ G`, then `G` creates limits.
-/
def createsLimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesLimitsOfSize.{w, w'} F] :
    CreatesLimitsOfSize.{w, w'} G where
  CreatesLimitsOfShape := createsLimitsOfShapeOfNatIso h

set_option backward.defeqAttrib.useBackward true in
/-- If `F` creates limits of shape `J` and `J ≌ J'`, then `F` creates limits of shape `J'`. -/
@[instance_reducible]
/-
**CategoryTheory.createsLimitsOfShapeOfEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory`。
形式化陈述：createsLimitsOfShapeOfEquiv {J' : Type w₁} [Category.{w'₁} J'] (e : J ≌ J'
) (F : C ⥤ D) [CreatesLimitsOfShape J F] : CreatesLimitsOfShape J' F where Creat
esLimit {K}
参数：e : J ≌ J'；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` creates limits of shape `J` and `J ≌ J'`, then `F` creates limits of shap
e `J'`.
-/
def createsLimitsOfShapeOfEquiv {J' : Type w₁} [Category.{w'₁} J'] (e : J ≌ J') (F : C ⥤ D)
    [CreatesLimitsOfShape J F] : CreatesLimitsOfShape J' F where
  CreatesLimit {K} :=
    { lifts c hc := by
        refine ⟨(Cone.whiskeringEquivalence e).inverse.obj
          (liftLimit (hc.whiskerEquivalence e)), ?_⟩
        letI inner := (Cone.whiskeringEquivalence (F := K ⋙ F) e).inverse.mapIso
          (liftedLimitMapsToOriginal (K := e.functor ⋙ K) (hc.whiskerEquivalence e))
        refine ?_ ≪≫ inner ≪≫ ((Cone.whiskeringEquivalence e).unitIso.app c).symm
        exact Cone.ext (Iso.refl _)
      toReflectsLimit := have := reflectsLimitsOfShape_of_equiv e F; inferInstance }

set_option backward.defeqAttrib.useBackward true in
/-- Transfer creation of colimits along a natural isomorphism in the diagram. -/
@[instance_reducible]
/-
**CategoryTheory.createsColimitOfIsoDiagram** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory`。
形式化陈述：createsColimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [Crea
tesColimit K₁ F] : CreatesColimit K₂ F
参数：F : C ⥤ D；h : K₁ ≅ K₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Transfer creation of colimits along a natural isomorphism in the diagram.
-/
def createsColimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [CreatesColimit K₁ F] :
    CreatesColimit K₂ F :=
  { reflectsColimit_of_iso_diagram F h with
    lifts := fun c t =>
      let t' := (IsColimit.precomposeHomEquiv (isoWhiskerRight h F :) c).symm t
      { liftedCocone := (Cocone.precompose h.inv).obj (liftColimit t')
        validLift :=
          Functor.mapCoconePrecompose F ≪≫
            (Cocone.precompose (isoWhiskerRight h F).inv).mapIso
                (liftedColimitMapsToOriginal t') ≪≫
              Cocone.ext (Iso.refl _) fun j => by
                dsimp
                rw [← F.map_comp_assoc]
                simp } }

/-- If `F` creates the colimit of `K` and `F ≅ G`, then `G` creates the colimit of `K`. -/
@[instance_reducible]
/-
**CategoryTheory.createsColimitOfNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y`。
形式化陈述：createsColimitOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesColimit K F] : Cr
eatesColimit K G where lifts c t
参数：h : F ≅ G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `F` creates the colimit of `K` and `F ≅ G`, then `G` creates the colimit of `
K`.
-/
def createsColimitOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesColimit K F] : CreatesColimit K G where
  lifts c t :=
    { liftedCocone := liftColimit ((IsColimit.precomposeHomEquiv (isoWhiskerLeft K h :) c).symm t)
      validLift := by
        refine (IsColimit.mapCoconeEquiv h ?_).uniqueUpToIso t
        apply IsColimit.ofIsoColimit _ (liftedColimitMapsToOriginal _).symm
        apply (IsColimit.precomposeHomEquiv _ _).symm t }
  toReflectsColimit := reflectsColimit_of_natIso _ h

/-- If `F` creates colimits of shape `J` and `F ≅ G`, then `G` creates colimits of shape `J`. -/
@[instance_reducible]
/-
**CategoryTheory.createsColimitsOfShapeOfNatIso** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory`。
形式化陈述：createsColimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesColimitsO
fShape J F] : CreatesColimitsOfShape J G where CreatesColimit
参数：h : F ≅ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` creates colimits of shape `J` and `F ≅ G`, then `G` creates colimits of s
hape `J`.
-/
def createsColimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesColimitsOfShape J F] :
    CreatesColimitsOfShape J G where CreatesColimit := createsColimitOfNatIso h

/-- If `F` creates colimits and `F ≅ G`, then `G` creates colimits. -/
@[instance_reducible]
/-
**CategoryTheory.createsColimitsOfNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry`。
形式化陈述：createsColimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesColimitsOfSize.{
w, w'} F] : CreatesColimitsOfSize.{w, w'} G where CreatesColimitsOfShape
参数：h : F ≅ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` creates colimits and `F ≅ G`, then `G` creates colimits.
-/
def createsColimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesColimitsOfSize.{w, w'} F] :
    CreatesColimitsOfSize.{w, w'} G where
  CreatesColimitsOfShape := createsColimitsOfShapeOfNatIso h

set_option backward.defeqAttrib.useBackward true in
/-- If `F` creates colimits of shape `J` and `J ≌ J'`, then `F` creates colimits of shape `J'`. -/
@[instance_reducible]
/-
**CategoryTheory.createsColimitsOfShapeOfEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory`。
形式化陈述：createsColimitsOfShapeOfEquiv {J' : Type w₁} [Category.{w'₁} J'] (e : J ≌ 
J') (F : C ⥤ D) [CreatesColimitsOfShape J F] : CreatesColimitsOfShape J' F where
 CreatesColimit {K}
参数：e : J ≌ J'；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` creates colimits of shape `J` and `J ≌ J'`, then `F` creates colimits of 
shape `J'`.
-/
def createsColimitsOfShapeOfEquiv {J' : Type w₁} [Category.{w'₁} J'] (e : J ≌ J') (F : C ⥤ D)
    [CreatesColimitsOfShape J F] : CreatesColimitsOfShape J' F where
  CreatesColimit {K} :=
    { lifts c hc := by
        refine ⟨(Cocone.whiskeringEquivalence e).inverse.obj
          (liftColimit (hc.whiskerEquivalence e)), ?_⟩
        letI inner := (Cocone.whiskeringEquivalence (F := K ⋙ F) e).inverse.mapIso
          (liftedColimitMapsToOriginal (K := e.functor ⋙ K) (hc.whiskerEquivalence e))
        refine ?_ ≪≫ inner ≪≫ ((Cocone.whiskeringEquivalence e).unitIso.app c).symm
        exact Cocone.ext (Iso.refl _)
      toReflectsColimit := have := reflectsColimitsOfShape_of_equiv e F; inferInstance }

-- For the inhabited linter later.
/-- If F creates the limit of K, any cone lifts to a limit. -/
/-
**CategoryTheory.liftsToLimitOfCreates** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
`。
形式化陈述：liftsToLimitOfCreates (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K F] (c : Cone
 (K ⋙ F)) (t : IsLimit c) : LiftsToLimit K F c t where liftedCone
参数：K : J ⥤ C；F : C ⥤ D；c : Cone (K ⋙ F)；t : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If F creates the limit of K, any cone lifts to a limit.
-/
def liftsToLimitOfCreates (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K F] (c : Cone (K ⋙ F))
    (t : IsLimit c) : LiftsToLimit K F c t where
  liftedCone := liftLimit t
  validLift := liftedLimitMapsToOriginal t
  makesLimit := liftedLimitIsLimit t

-- For the inhabited linter later.
/-- If F creates the colimit of K, any cocone lifts to a colimit. -/
/-
**CategoryTheory.liftsToColimitOfCreates** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry`。
形式化陈述：liftsToColimitOfCreates (K : J ⥤ C) (F : C ⥤ D) [CreatesColimit K F] (c : 
Cocone (K ⋙ F)) (t : IsColimit c) : LiftsToColimit K F c t where liftedCocone
参数：K : J ⥤ C；F : C ⥤ D；c : Cocone (K ⋙ F)；t : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If F creates the colimit of K, any cocone lifts to a colimit.
-/
def liftsToColimitOfCreates (K : J ⥤ C) (F : C ⥤ D) [CreatesColimit K F] (c : Cocone (K ⋙ F))
    (t : IsColimit c) : LiftsToColimit K F c t where
  liftedCocone := liftColimit t
  validLift := liftedColimitMapsToOriginal t
  makesColimit := liftedColimitIsColimit t

set_option backward.defeqAttrib.useBackward true in
/-- Any cone lifts through the identity functor. -/
/-
**CategoryTheory.idLiftsCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：idLiftsCone (c : Cone (K ⋙ 𝟭 C)) : LiftableCone K (𝟭 C) c where liftedCone
参数：c : Cone (K ⋙ 𝟭 C)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any cone lifts through the identity functor.
-/
def idLiftsCone (c : Cone (K ⋙ 𝟭 C)) : LiftableCone K (𝟭 C) c where
  liftedCone :=
    { pt := c.pt
      π := c.π ≫ K.rightUnitor.hom }
  validLift := Cone.ext (Iso.refl _)

/-- The identity functor creates all limits. -/
/-
**CategoryTheory.idCreatesLimits** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：idCreatesLimits : CreatesLimitsOfSize.{w, w'} (𝟭 C) where CreatesLimitsOfS
hape
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity functor creates all limits.
-/
instance idCreatesLimits : CreatesLimitsOfSize.{w, w'} (𝟭 C) where
  CreatesLimitsOfShape :=
    { CreatesLimit := { lifts := fun c _ => idLiftsCone c } }

set_option backward.defeqAttrib.useBackward true in
/-- Any cocone lifts through the identity functor. -/
/-
**CategoryTheory.idLiftsCocone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：idLiftsCocone (c : Cocone (K ⋙ 𝟭 C)) : LiftableCocone K (𝟭 C) c where lift
edCocone
参数：c : Cocone (K ⋙ 𝟭 C)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any cocone lifts through the identity functor.
-/
def idLiftsCocone (c : Cocone (K ⋙ 𝟭 C)) : LiftableCocone K (𝟭 C) c where
  liftedCocone :=
    { pt := c.pt
      ι := K.rightUnitor.inv ≫ c.ι }
  validLift := Cocone.ext (Iso.refl _)

/-- The identity functor creates all colimits. -/
/-
**CategoryTheory.idCreatesColimits** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：idCreatesColimits : CreatesColimitsOfSize.{w, w'} (𝟭 C) where CreatesColim
itsOfShape
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity functor creates all colimits.
-/
instance idCreatesColimits : CreatesColimitsOfSize.{w, w'} (𝟭 C) where
  CreatesColimitsOfShape :=
    { CreatesColimit := { lifts := fun c _ => idLiftsCocone c } }

/-- Satisfy the inhabited linter -/
/-
**CategoryTheory.inhabitedLiftableCone** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
`。
形式化陈述：inhabitedLiftableCone (c : Cone (K ⋙ 𝟭 C)) : Inhabited (LiftableCone K (𝟭 
C) c)
参数：c : Cone (K ⋙ 𝟭 C)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Satisfy the inhabited linter
-/
instance inhabitedLiftableCone (c : Cone (K ⋙ 𝟭 C)) : Inhabited (LiftableCone K (𝟭 C) c) :=
  ⟨idLiftsCone c⟩
/-
**CategoryTheory.inhabitedLiftableCocone** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry`。
形式化陈述：inhabitedLiftableCocone (c : Cocone (K ⋙ 𝟭 C)) : Inhabited (LiftableCocone
 K (𝟭 C) c)
参数：c : Cocone (K ⋙ 𝟭 C)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedLiftableCocone (c : Cocone (K ⋙ 𝟭 C)) : Inhabited (LiftableCocone K (𝟭 C) c) :=
  ⟨idLiftsCocone c⟩

/-- Satisfy the inhabited linter -/
/-
**CategoryTheory.inhabitedLiftsToLimit** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
`。
形式化陈述：inhabitedLiftsToLimit (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K F] (c : Cone
 (K ⋙ F)) (t : IsLimit c) : Inhabited (LiftsToLimit _ _ _ t)
参数：K : J ⥤ C；F : C ⥤ D；c : Cone (K ⋙ F)；t : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Satisfy the inhabited linter
-/
instance inhabitedLiftsToLimit (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K F] (c : Cone (K ⋙ F))
    (t : IsLimit c) : Inhabited (LiftsToLimit _ _ _ t) :=
  ⟨liftsToLimitOfCreates K F c t⟩
/-
**CategoryTheory.inhabitedLiftsToColimit** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry`。
形式化陈述：inhabitedLiftsToColimit (K : J ⥤ C) (F : C ⥤ D) [CreatesColimit K F] (c : 
Cocone (K ⋙ F)) (t : IsColimit c) : Inhabited (LiftsToColimit _ _ _ t)
参数：K : J ⥤ C；F : C ⥤ D；c : Cocone (K ⋙ F)；t : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedLiftsToColimit (K : J ⥤ C) (F : C ⥤ D) [CreatesColimit K F] (c : Cocone (K ⋙ F))
    (t : IsColimit c) : Inhabited (LiftsToColimit _ _ _ t) :=
  ⟨liftsToColimitOfCreates K F c t⟩

section Comp

variable {E : Type u₃} [ℰ : Category.{v₃} E]
variable (F : C ⥤ D) (G : D ⥤ E)

/-
**CategoryTheory.compCreatesLimit** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：compCreatesLimit [CreatesLimit K F] [CreatesLimit (K ⋙ F) G] : CreatesLimi
t K (F ⋙ G) where lifts c t
参数：K ⋙ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance compCreatesLimit [CreatesLimit K F] [CreatesLimit (K ⋙ F) G] :
    CreatesLimit K (F ⋙ G) where
  lifts c t := by
    let c' : Cone ((K ⋙ F) ⋙ G) := c
    let t' : IsLimit c' := t
    exact
      { liftedCone := liftLimit (liftedLimitIsLimit t')
        validLift := (Cone.functoriality (K ⋙ F) G).mapIso
            (liftedLimitMapsToOriginal (liftedLimitIsLimit t')) ≪≫
          liftedLimitMapsToOriginal t' }
/-
**CategoryTheory.compCreatesLimitsOfShape** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory`。
形式化陈述：compCreatesLimitsOfShape [CreatesLimitsOfShape J F] [CreatesLimitsOfShape 
J G] : CreatesLimitsOfShape J (F ⋙ G) where CreatesLimit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance compCreatesLimitsOfShape [CreatesLimitsOfShape J F] [CreatesLimitsOfShape J G] :
    CreatesLimitsOfShape J (F ⋙ G) where CreatesLimit := inferInstance
/-
**CategoryTheory.compCreatesLimits** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：compCreatesLimits [CreatesLimitsOfSize.{w, w'} F] [CreatesLimitsOfSize.{w,
 w'} G] : CreatesLimitsOfSize.{w, w'} (F ⋙ G) where CreatesLimitsOfShape
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance compCreatesLimits [CreatesLimitsOfSize.{w, w'} F] [CreatesLimitsOfSize.{w, w'} G] :
    CreatesLimitsOfSize.{w, w'} (F ⋙ G) where CreatesLimitsOfShape := inferInstance
/-
**CategoryTheory.preservesLimit_comp_of_createsLimit** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory`。
形式化陈述：preservesLimit_comp_of_createsLimit [CreatesLimit K F] [PreservesLimit K (
F ⋙ G)] : PreservesLimit (K ⋙ F) G where preserves hc
参数：F ⋙ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preservesLimit_comp_of_createsLimit [CreatesLimit K F] [PreservesLimit K (F ⋙ G)] :
    PreservesLimit (K ⋙ F) G where
  preserves hc := ⟨IsLimit.ofIsoLimit (isLimitOfPreserves (F ⋙ G) (liftedLimitIsLimit hc))
    ((Functor.mapConeMapCone (liftLimit hc)).symm ≪≫
      (Cone.functoriality _ _).mapIso (liftedLimitMapsToOriginal hc))⟩
/-
**CategoryTheory.compCreatesColimit** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：compCreatesColimit [CreatesColimit K F] [CreatesColimit (K ⋙ F) G] : Creat
esColimit K (F ⋙ G) where lifts c t
参数：K ⋙ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance compCreatesColimit [CreatesColimit K F] [CreatesColimit (K ⋙ F) G] :
    CreatesColimit K (F ⋙ G) where
  lifts c t :=
    let c' : Cocone ((K ⋙ F) ⋙ G) := c
    let t' : IsColimit c' := t
    { liftedCocone := liftColimit (liftedColimitIsColimit t')
      validLift :=
        (Cocone.functoriality (K ⋙ F) G).mapIso
            (liftedColimitMapsToOriginal (liftedColimitIsColimit t')) ≪≫
          liftedColimitMapsToOriginal t' }
/-
**CategoryTheory.compCreatesColimitsOfShape** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory`。
形式化陈述：compCreatesColimitsOfShape [CreatesColimitsOfShape J F] [CreatesColimitsOf
Shape J G] : CreatesColimitsOfShape J (F ⋙ G) where CreatesColimit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance compCreatesColimitsOfShape [CreatesColimitsOfShape J F] [CreatesColimitsOfShape J G] :
    CreatesColimitsOfShape J (F ⋙ G) where CreatesColimit := inferInstance
/-
**CategoryTheory.compCreatesColimits** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：compCreatesColimits [CreatesColimitsOfSize.{w, w'} F] [CreatesColimitsOfSi
ze.{w, w'} G] : CreatesColimitsOfSize.{w, w'} (F ⋙ G) where CreatesColimitsOfSha
pe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance compCreatesColimits [CreatesColimitsOfSize.{w, w'} F] [CreatesColimitsOfSize.{w, w'} G] :
    CreatesColimitsOfSize.{w, w'} (F ⋙ G) where CreatesColimitsOfShape := inferInstance
/-
**CategoryTheory.preservesColimit_comp_of_createsColimit** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory`。
形式化陈述：preservesColimit_comp_of_createsColimit [CreatesColimit K F] [PreservesCol
imit K (F ⋙ G)] : PreservesColimit (K ⋙ F) G where preserves hc
参数：F ⋙ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preservesColimit_comp_of_createsColimit [CreatesColimit K F] [PreservesColimit K (F ⋙ G)] :
    PreservesColimit (K ⋙ F) G where
  preserves hc := ⟨IsColimit.ofIsoColimit (isColimitOfPreserves (F ⋙ G) (liftedColimitIsColimit hc))
    ((Functor.mapCoconeMapCocone (liftColimit hc)).symm ≪≫
      (Cocone.functoriality _ _).mapIso (liftedColimitMapsToOriginal hc))⟩

end Comp

end Creates

end CategoryTheory

