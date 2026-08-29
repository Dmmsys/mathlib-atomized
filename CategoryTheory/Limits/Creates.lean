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

/--
Definition of `LiftableCone` / `LiftableCone` 的定义

English:
structure LiftableCone
  parameters: (K : J ⥤ C) (F : C ⥤ D) (c : Cone (K ⋙ F))
  axioms and operations (2):
    - liftedCone : Cone K
    - validLift : F.mapCone liftedCone ≅ c

中文:
结构 LiftableCone
  参数: (K : J ⥤ C) (F : C ⥤ D) (c : 锥 (K ⋙ F))
  公理与运算 (2 个):
    - liftedCone : 锥 K
    - validLift : F.mapCone liftedCone ≅ c
-/
structure LiftableCone (K : J ⥤ C) (F : C ⥤ D) (c : Cone (K ⋙ F)) where
  /-- a cone in the source category of the functor -/
  liftedCone : Cone K
  /-- the isomorphism expressing that `liftedCone` lifts the given cone -/
  validLift : F.mapCone liftedCone ≅ c

/--
Definition of `LiftableCocone` / `LiftableCocone` 的定义

English:
structure LiftableCocone
  parameters: (K : J ⥤ C) (F : C ⥤ D) (c : Cocone (K ⋙ F))
  axioms and operations (2):
    - liftedCocone : Cocone K
    - validLift : F.mapCocone liftedCocone ≅ c

中文:
结构 LiftableCocone
  参数: (K : J ⥤ C) (F : C ⥤ D) (c : 余锥 (K ⋙ F))
  公理与运算 (2 个):
    - liftedCocone : 余锥 K
    - validLift : F.mapCocone liftedCocone ≅ c
-/
structure LiftableCocone (K : J ⥤ C) (F : C ⥤ D) (c : Cocone (K ⋙ F)) where
  /-- a cocone in the source category of the functor -/
  liftedCocone : Cocone K
  /-- the isomorphism expressing that `liftedCocone` lifts the given cocone -/
  validLift : F.mapCocone liftedCocone ≅ c

/--
Definition of `CreatesLimit` / `CreatesLimit` 的定义

English:
class CreatesLimit
  parameters: (K : J ⥤ C) (F : C ⥤ D)
  extends: ReflectsLimit K F
  axioms and operations (1):
    - lifts : forall c, IsLimit c -> LiftableCone K F c

中文:
类 创造极限
  参数: (K : J ⥤ C) (F : C ⥤ D)
  继承: 反映极限 K F
  公理与运算 (1 个):
    - lifts : 对任意 c, 是极限 c -> LiftableCone K F c
-/
class CreatesLimit (K : J ⥤ C) (F : C ⥤ D) extends ReflectsLimit K F where
  /-- any limit cone can be lifted to a cone above -/
  lifts : forall c, IsLimit c -> LiftableCone K F c

/--
Definition of `CreatesLimitsOfShape` / `CreatesLimitsOfShape` 的定义

English:
class CreatesLimitsOfShape
  parameters: (J : Type w) [Category.{w'} J] (F : C ⥤ D)
  axioms and operations (1):
    - CreatesLimit : forall {K : J ⥤ C}, CreatesLimit K F  [default: by infer_instance]

中文:
类 创造形状极限
  参数: (J : 类型 w) [范畴.{w'} J] (F : C ⥤ D)
  公理与运算 (1 个):
    - CreatesLimit : 对任意 {K : J ⥤ C}, 创造极限 K F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class CreatesLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  CreatesLimit : forall {K : J ⥤ C}, CreatesLimit K F := by infer_instance

-- This should be used with explicit universe variables.
set_option linter.checkUnivs false in
/-- `F` creates limits if it creates limits of shape `J` for any `J`. -/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the shape universes in
-- `CreatesLimitsOfSize` and `CreatesColimitsOfSize` would default to universe output parameters.
-- See Note [universe output parameters and typeclass caching].
@[univ_out_params, pp_with_univ]
/--
Definition of `CreatesLimitsOfSize` / `CreatesLimitsOfSize` 的定义

English:
class CreatesLimitsOfSize
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - CreatesLimitsOfShape : forall {J : Type w} [Category.{w'} J], CreatesLimitsOfShape J F  [default: by infer_instance]

中文:
类 CreatesLimitsOfSize
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - CreatesLimitsOfShape : 对任意 {J : 类型 w} [范畴.{w'} J], 创造形状极限 J F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class CreatesLimitsOfSize (F : C ⥤ D) where
  CreatesLimitsOfShape : forall {J : Type w} [Category.{w'} J], CreatesLimitsOfShape J F := by
    infer_instance

/--
Definition of `CreatesLimits` / `CreatesLimits` 的定义

English:
abbreviation CreatesLimits
  signature: (F : C ⥤ D)
  body: CreatesLimitsOfSize.{v₂, v₂} F

中文:
缩写 CreatesLimits
  签名: (F : C ⥤ D)
  定义体: CreatesLimitsOfSize.{v₂, v₂} F

Depends on / 依赖: CreatesLimitsOfSize
-/
abbrev CreatesLimits (F : C ⥤ D) :=
  CreatesLimitsOfSize.{v₂, v₂} F

/--
Definition of `CreatesColimit` / `CreatesColimit` 的定义

English:
class CreatesColimit
  parameters: (K : J ⥤ C) (F : C ⥤ D)
  extends: ReflectsColimit K F
  axioms and operations (1):
    - lifts : forall c, IsColimit c -> LiftableCocone K F c

中文:
类 创造余极限
  参数: (K : J ⥤ C) (F : C ⥤ D)
  继承: 反映余极限 K F
  公理与运算 (1 个):
    - lifts : 对任意 c, 是余极限 c -> LiftableCocone K F c
-/
class CreatesColimit (K : J ⥤ C) (F : C ⥤ D) extends ReflectsColimit K F where
  /-- any limit cocone can be lifted to a cocone above -/
  lifts : forall c, IsColimit c -> LiftableCocone K F c

/--
Definition of `CreatesColimitsOfShape` / `CreatesColimitsOfShape` 的定义

English:
class CreatesColimitsOfShape
  parameters: (J : Type w) [Category.{w'} J] (F : C ⥤ D)
  axioms and operations (1):
    - CreatesColimit : forall {K : J ⥤ C}, CreatesColimit K F  [default: by infer_instance]

中文:
类 创造形状余极限
  参数: (J : 类型 w) [范畴.{w'} J] (F : C ⥤ D)
  公理与运算 (1 个):
    - CreatesColimit : 对任意 {K : J ⥤ C}, 创造余极限 K F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class CreatesColimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  CreatesColimit : forall {K : J ⥤ C}, CreatesColimit K F := by infer_instance

-- This should be used with explicit universe variables.
set_option linter.checkUnivs false in
/-- `F` creates colimits if it creates colimits of shape `J` for any small `J`. -/
@[univ_out_params, pp_with_univ]
/--
Definition of `CreatesColimitsOfSize` / `CreatesColimitsOfSize` 的定义

English:
class CreatesColimitsOfSize
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - CreatesColimitsOfShape : forall {J : Type w} [Category.{w'} J], CreatesColimitsOfShape J F  [default: by infer_instance]

中文:
类 CreatesColimitsOfSize
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - CreatesColimitsOfShape : 对任意 {J : 类型 w} [范畴.{w'} J], 创造形状余极限 J F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class CreatesColimitsOfSize (F : C ⥤ D) where
  CreatesColimitsOfShape : forall {J : Type w} [Category.{w'} J], CreatesColimitsOfShape J F := by
    infer_instance

/--
Definition of `CreatesColimits` / `CreatesColimits` 的定义

English:
abbreviation CreatesColimits
  signature: (F : C ⥤ D)
  body: CreatesColimitsOfSize.{v₂, v₂} F

中文:
缩写 CreatesColimits
  签名: (F : C ⥤ D)
  定义体: CreatesColimitsOfSize.{v₂, v₂} F

Depends on / 依赖: CreatesColimitsOfSize
-/
abbrev CreatesColimits (F : C ⥤ D) :=
  CreatesColimitsOfSize.{v₂, v₂} F

-- see Note [lower instance priority]
attribute [instance_reducible, instance 100]
  CreatesLimitsOfShape.CreatesLimit CreatesLimitsOfSize.CreatesLimitsOfShape
  CreatesColimitsOfShape.CreatesColimit CreatesColimitsOfSize.CreatesColimitsOfShape

-- see Note [lower instance priority]
-- Interface to the `CreatesLimit` class.
/--
Definition of `liftLimit` / `liftLimit` 的定义

English:
definition liftLimit
  signature: {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)} (t : IsLimit c)
  body: (CreatesLimit.lifts c t).liftedCone

中文:
定义 liftLimit
  签名: {K : J ⥤ C} {F : C ⥤ D} [创造极限 K F] {c : 锥 (K ⋙ F)} (t : 是极限 c)
  定义体: (CreatesLimit.lifts c t).liftedCone

Depends on / 依赖: CreatesLimit, CreatesLimit.lifts, liftedCone
-/
def liftLimit {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)} (t : IsLimit c) :
    Cone K :=
  (CreatesLimit.lifts c t).liftedCone

/--
Definition of `liftedLimitMapsToOriginal` / `liftedLimitMapsToOriginal` 的定义

English:
definition liftedLimitMapsToOriginal
  signature: {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)}
  body: (CreatesLimit.lifts c t).validLift

中文:
定义 liftedLimitMapsToOriginal
  签名: {K : J ⥤ C} {F : C ⥤ D} [创造极限 K F] {c : 锥 (K ⋙ F)}
  定义体: (CreatesLimit.lifts c t).validLift

Depends on / 依赖: CreatesLimit, CreatesLimit.lifts, validLift
-/
def liftedLimitMapsToOriginal {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)}
    (t : IsLimit c) : F.mapCone (liftLimit t) ≅ c :=
  (CreatesLimit.lifts c t).validLift

set_option backward.isDefEq.respectTransparency false in
/--
lemma `liftedLimitMapsToOriginal_inv_map_π` / 引理 `liftedLimitMapsToOriginal_inv_map_π`

English:
lemma liftedLimitMapsToOriginal_inv_map_π
  proof: by
  rw [show F.map ((liftLimit t).π.app j) = (liftedLimitMapsToOriginal t).hom.hom ≫ c.π.app j
    from (by simp)]; rw [← Category.assoc]; rw [← Cone.category_comp_hom]
  simp

中文:
引理 liftedLimitMapsToOriginal_inv_map_π
  证明: by
  rw [show F.map ((liftLimit t).π.app j) = (liftedLimitMapsToOriginal t).hom.hom ≫ c.π.app j
    from (by simp)]; rw [← Category.assoc]; rw [← Cone.category_comp_hom]
  simp

Depends on / 依赖: Category, Category.assoc, Cone.category_comp_hom, F.map, category_comp_hom, hom.hom, liftLimit, liftedLimitMapsToOriginal
-/
lemma liftedLimitMapsToOriginal_inv_map_π
    {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)} (t : IsLimit c) (j : J) :
      (liftedLimitMapsToOriginal t).inv.hom ≫ F.map ((liftLimit t).π.app j) = c.π.app j := by
  rw [show F.map ((liftLimit t).π.app j) = (liftedLimitMapsToOriginal t).hom.hom ≫ c.π.app j
    from (by simp)]; rw [← Category.assoc]; rw [← Cone.category_comp_hom]
  simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `liftedLimitMapsToOriginal_hom_π` / 引理 `liftedLimitMapsToOriginal_hom_π`

English:
lemma liftedLimitMapsToOriginal_hom_π
  proof: by
  rw [← liftedLimitMapsToOriginal_inv_map_π (t := t)]
  simp only [← Category.assoc, ← Cone.category_comp_hom,
    Iso.hom_inv_id, Cone.category_id_hom, Category.id_comp]

中文:
引理 liftedLimitMapsToOriginal_hom_π
  证明: by
  rw [← liftedLimitMapsToOriginal_inv_map_π (t := t)]
  simp only [← Category.assoc, ← Cone.category_comp_hom,
    Iso.hom_inv_id, Cone.category_id_hom, Category.id_comp]

Depends on / 依赖: Category, Category.assoc, Category.id_comp, Cone.category_comp_hom, Cone.category_id_hom, Iso.hom_inv_id, Quot.mk, category_comp_hom, category_id_hom, hom_inv_id, id_comp
-/
lemma liftedLimitMapsToOriginal_hom_π
    {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)} (t : IsLimit c) (j : J) :
      (liftedLimitMapsToOriginal t).hom.hom ≫ c.π.app j = F.map ((liftLimit t).π.app j) := by
  rw [← liftedLimitMapsToOriginal_inv_map_π (t := t)]
  simp only [← Category.assoc, ← Cone.category_comp_hom,
    Iso.hom_inv_id, Cone.category_id_hom, Category.id_comp]

/--
Definition of `liftedLimitIsLimit` / `liftedLimitIsLimit` 的定义

English:
definition liftedLimitIsLimit
  signature: {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)}
  body: isLimitOfReflects _ (IsLimit.ofIsoLimit t (liftedLimitMapsToOriginal t).symm)

中文:
定义 liftedLimitIsLimit
  签名: {K : J ⥤ C} {F : C ⥤ D} [创造极限 K F] {c : 锥 (K ⋙ F)}
  定义体: isLimitOfReflects _ (IsLimit.ofIsoLimit t (liftedLimitMapsToOriginal t).symm)

Depends on / 依赖: IsLimit, IsLimit.ofIsoLimit, Quot.sound, coendRel, coendRel.mk, isLimitOfReflects, liftedLimitMapsToOriginal, ofIsoLimit
-/
def liftedLimitIsLimit {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)}
    (t : IsLimit c) : IsLimit (liftLimit t) :=
  isLimitOfReflects _ (IsLimit.ofIsoLimit t (liftedLimitMapsToOriginal t).symm)

/--
theorem `hasLimit_of_created` / 定理 `hasLimit_of_created`

English:
theorem hasLimit_of_created
  given: (K : J ⥤ C) (F : C ⥤ D) [HasLimit (K ⋙ F)] [CreatesLimit K F]
  proof: HasLimit.mk
    { cone := liftLimit (limit.isLimit (K ⋙ F))
      isLimit := liftedLimitIsLimit _ }

中文:
定理 hasLimit_of_created
  条件: (K : J ⥤ C) (F : C ⥤ D) [有极限 (K ⋙ F)] [创造极限 K F]
  证明: HasLimit.mk
    { cone := liftLimit (limit.isLimit (K ⋙ F))
      isLimit := liftedLimitIsLimit _ }

Depends on / 依赖: HasLimit, HasLimit.mk, isLimit, liftLimit, liftedLimitIsLimit, limit.isLimit
-/
theorem hasLimit_of_created (K : J ⥤ C) (F : C ⥤ D) [HasLimit (K ⋙ F)] [CreatesLimit K F] :
    HasLimit K :=
  HasLimit.mk
    { cone := liftLimit (limit.isLimit (K ⋙ F))
      isLimit := liftedLimitIsLimit _ }

/--
theorem `hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape` / 定理 `hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape`

English:
theorem hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
  statement: (F : C ⥤ D) [HasLimitsOfShape J D]
  proof: ⟨fun G => hasLimit_of_created G F⟩

中文:
定理 hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
  结论: (F : C ⥤ D) [有形状极限 J D]
  证明: ⟨fun G => hasLimit_of_created G F⟩

Depends on / 依赖: hasLimit_of_created
-/
theorem hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (F : C ⥤ D) [HasLimitsOfShape J D]
    [CreatesLimitsOfShape J F] : HasLimitsOfShape J C :=
  ⟨fun G => hasLimit_of_created G F⟩

/--
theorem `hasLimits_of_hasLimits_createsLimits` / 定理 `hasLimits_of_hasLimits_createsLimits`

English:
theorem hasLimits_of_hasLimits_createsLimits
  statement: (F : C ⥤ D) [HasLimitsOfSize.{w, w'} D]
  proof: ⟨fun _ _ => hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape F⟩

中文:
定理 hasLimits_of_hasLimits_createsLimits
  结论: (F : C ⥤ D) [有LimitsOfSize.{w, w'} D]
  证明: ⟨fun _ _ => hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape F⟩

Depends on / 依赖: hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
-/
theorem hasLimits_of_hasLimits_createsLimits (F : C ⥤ D) [HasLimitsOfSize.{w, w'} D]
    [CreatesLimitsOfSize.{w, w'} F] : HasLimitsOfSize.{w, w'} C :=
  ⟨fun _ _ => hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape F⟩

-- Interface to the `CreatesColimit` class.
/--
Definition of `liftColimit` / `liftColimit` 的定义

English:
definition liftColimit
  signature: {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : Cocone (K ⋙ F)}
  body: (CreatesColimit.lifts c t).liftedCocone

中文:
定义 liftColimit
  签名: {K : J ⥤ C} {F : C ⥤ D} [创造余极限 K F] {c : 余锥 (K ⋙ F)}
  定义体: (CreatesColimit.lifts c t).liftedCocone

Depends on / 依赖: CreatesColimit, CreatesColimit.lifts, liftedCocone
-/
def liftColimit {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : Cocone (K ⋙ F)}
    (t : IsColimit c) : Cocone K :=
  (CreatesColimit.lifts c t).liftedCocone

/--
Definition of `liftedColimitMapsToOriginal` / `liftedColimitMapsToOriginal` 的定义

English:
definition liftedColimitMapsToOriginal
  signature: {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : Cocone (K ⋙ F)}
  body: (CreatesColimit.lifts c t).validLift

中文:
定义 liftedColimitMapsToOriginal
  签名: {K : J ⥤ C} {F : C ⥤ D} [创造余极限 K F] {c : 余锥 (K ⋙ F)}
  定义体: (CreatesColimit.lifts c t).validLift

Depends on / 依赖: CreatesColimit, CreatesColimit.lifts, validLift
-/
def liftedColimitMapsToOriginal {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : Cocone (K ⋙ F)}
    (t : IsColimit c) : F.mapCocone (liftColimit t) ≅ c :=
  (CreatesColimit.lifts c t).validLift

/--
Definition of `liftedColimitIsColimit` / `liftedColimitIsColimit` 的定义

English:
definition liftedColimitIsColimit
  signature: {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : Cocone (K ⋙ F)}
  body: isColimitOfReflects _ (IsColimit.ofIsoColimit t (liftedColimitMapsToOriginal t).symm)

中文:
定义 liftedColimitIsColimit
  签名: {K : J ⥤ C} {F : C ⥤ D} [创造余极限 K F] {c : 余锥 (K ⋙ F)}
  定义体: isColimitOfReflects _ (IsColimit.ofIsoColimit t (liftedColimitMapsToOriginal t).symm)

Depends on / 依赖: IsColimit, IsColimit.ofIsoColimit, isColimitOfReflects, liftedColimitMapsToOriginal, ofIsoColimit
-/
def liftedColimitIsColimit {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : Cocone (K ⋙ F)}
    (t : IsColimit c) : IsColimit (liftColimit t) :=
  isColimitOfReflects _ (IsColimit.ofIsoColimit t (liftedColimitMapsToOriginal t).symm)

/--
theorem `hasColimit_of_created` / 定理 `hasColimit_of_created`

English:
theorem hasColimit_of_created
  given: (K : J ⥤ C) (F : C ⥤ D) [HasColimit (K ⋙ F)] [CreatesColimit K F]
  proof: HasColimit.mk
    { cocone := liftColimit (colimit.isColimit (K ⋙ F))
      isColimit := liftedColimitIsColimit _ }

中文:
定理 hasColimit_of_created
  条件: (K : J ⥤ C) (F : C ⥤ D) [有余极限 (K ⋙ F)] [创造余极限 K F]
  证明: HasColimit.mk
    { cocone := liftColimit (colimit.isColimit (K ⋙ F))
      isColimit := liftedColimitIsColimit _ }

Depends on / 依赖: HasColimit, HasColimit.mk, cocone, colimit, colimit.isColimit, isColimit, liftColimit, liftedColimitIsColimit
-/
theorem hasColimit_of_created (K : J ⥤ C) (F : C ⥤ D) [HasColimit (K ⋙ F)] [CreatesColimit K F] :
    HasColimit K :=
  HasColimit.mk
    { cocone := liftColimit (colimit.isColimit (K ⋙ F))
      isColimit := liftedColimitIsColimit _ }

/--
theorem `hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape` / 定理 `hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape`

English:
theorem hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
  statement: (F : C ⥤ D)
  proof: ⟨fun G => hasColimit_of_created G F⟩

中文:
定理 hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
  结论: (F : C ⥤ D)
  证明: ⟨fun G => hasColimit_of_created G F⟩

Depends on / 依赖: hasColimit_of_created
-/
theorem hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (F : C ⥤ D)
    [HasColimitsOfShape J D] [CreatesColimitsOfShape J F] : HasColimitsOfShape J C :=
  ⟨fun G => hasColimit_of_created G F⟩

/--
theorem `hasColimits_of_hasColimits_createsColimits` / 定理 `hasColimits_of_hasColimits_createsColimits`

English:
theorem hasColimits_of_hasColimits_createsColimits
  statement: (F : C ⥤ D) [HasColimitsOfSize.{w, w'} D]
  proof: ⟨fun _ _ => hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape F⟩

中文:
定理 hasColimits_of_hasColimits_createsColimits
  结论: (F : C ⥤ D) [有余limitsOfSize.{w, w'} D]
  证明: ⟨fun _ _ => hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape F⟩

Depends on / 依赖: hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
-/
theorem hasColimits_of_hasColimits_createsColimits (F : C ⥤ D) [HasColimitsOfSize.{w, w'} D]
    [CreatesColimitsOfSize.{w, w'} F] : HasColimitsOfSize.{w, w'} C :=
  ⟨fun _ _ => hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape F⟩

instance (priority := 10) reflectsLimitsOfShapeOfCreatesLimitsOfShape (F : C ⥤ D)
    [CreatesLimitsOfShape J F] : ReflectsLimitsOfShape J F where

instance (priority := 10) reflectsLimitsOfCreatesLimits (F : C ⥤ D)
    [CreatesLimitsOfSize.{w, w'} F] : ReflectsLimitsOfSize.{w, w'} F where

instance (priority := 10) reflectsColimitsOfShapeOfCreatesColimitsOfShape (F : C ⥤ D)
    [CreatesColimitsOfShape J F] : ReflectsColimitsOfShape J F where

instance (priority := 10) reflectsColimitsOfCreatesColimits (F : C ⥤ D)
    [CreatesColimitsOfSize.{w, w'} F] : ReflectsColimitsOfSize.{w, w'} F where

/--
Definition of `LiftsToLimit` / `LiftsToLimit` 的定义

English:
structure LiftsToLimit
  parameters: (K : J ⥤ C) (F : C ⥤ D) (c : Cone (K ⋙ F)) (t : IsLimit c)
  axioms and operations (1):
    - makesLimit : IsLimit liftedCone

中文:
结构 LiftsToLimit
  参数: (K : J ⥤ C) (F : C ⥤ D) (c : 锥 (K ⋙ F)) (t : 是极限 c)
  公理与运算 (1 个):
    - makesLimit : 是极限 liftedCone
-/
structure LiftsToLimit (K : J ⥤ C) (F : C ⥤ D) (c : Cone (K ⋙ F)) (t : IsLimit c) extends
  LiftableCone K F c where
  /-- the lifted cone is limit -/
  makesLimit : IsLimit liftedCone

/--
Definition of `LiftsToColimit` / `LiftsToColimit` 的定义

English:
structure LiftsToColimit
  parameters: (K : J ⥤ C) (F : C ⥤ D) (c : Cocone (K ⋙ F)) (t : IsColimit c)
  axioms and operations (1):
    - makesColimit : IsColimit liftedCocone

中文:
结构 LiftsToColimit
  参数: (K : J ⥤ C) (F : C ⥤ D) (c : 余锥 (K ⋙ F)) (t : 是余极限 c)
  公理与运算 (1 个):
    - makesColimit : 是余极限 liftedCocone
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
/--
Definition of `createsLimitOfReflectsIso` / `createsLimitOfReflectsIso` 的定义

English:
definition createsLimitOfReflectsIso
  signature: {K : J ⥤ C} {F : C ⥤ D} [F.ReflectsIsomorphisms]
  body: (h c t).toLiftableCone
  toReflectsLimit :=
    { reflects := fun {d} hd => ⟨by
        let d' : Cone K := (h (F.mapCone d) hd).toLiftableCone.liftedCone
        let i : F.mapCone d' ≅ F.mapCone d :=
          (h (F.mapCone d) hd).toLiftableCone.validLift
        let hd' : IsLimit d' := (h (F.mapCon

中文:
定义 createsLimitOfReflectsIso
  签名: {K : J ⥤ C} {F : C ⥤ D} [F.反映同构]
  定义体: (h c t).toLiftableCone
  toReflectsLimit :=
    { reflects := fun {d} hd => ⟨by
        let d' : Cone K := (h (F.mapCone d) hd).toLiftableCone.liftedCone
        let i : F.mapCone d' ≅ F.mapCone d :=
          (h (F.mapCone d) hd).toLiftableCone.validLift
        let hd' : IsLimit d' := (h (F.mapCon

Depends on / 依赖: toLiftableCone
-/
def createsLimitOfReflectsIso {K : J ⥤ C} {F : C ⥤ D} [F.ReflectsIsomorphisms]
    (h : forall c t, LiftsToLimit K F c t) : CreatesLimit K F where
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
/--
Definition of `createsLimitOfReflectsIso'` / `createsLimitOfReflectsIso'` 的定义

English:
definition createsLimitOfReflectsIso'
  signature: {K : J ⥤ C} {F : C ⥤ D} [F.ReflectsIsomorphisms]
  body: createsLimitOfReflectsIso fun _ t =>
    { liftedCone := h.liftedCone
      validLift := h.validLift ≪≫ IsLimit.uniqueUpToIso hc t
      makesLimit := h.makesLimit }

中文:
定义 createsLimitOfReflectsIso'
  签名: {K : J ⥤ C} {F : C ⥤ D} [F.反映同构]
  定义体: createsLimitOfReflectsIso fun _ t =>
    { liftedCone := h.liftedCone
      validLift := h.validLift ≪≫ IsLimit.uniqueUpToIso hc t
      makesLimit := h.makesLimit }

Depends on / 依赖: IsLimit, IsLimit.uniqueUpToIso, createsLimitOfReflectsIso, h.liftedCone, h.makesLimit, h.validLift, liftedCone, makesLimit, uniqueUpToIso, validLift
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
/--
Definition of `createsLimitOfReflectsIsomorphismsOfPreserves` / `createsLimitOfReflectsIsomorphismsOfPreserves` 的定义

English:
definition createsLimitOfReflectsIsomorphismsOfPreserves
  signature: {K : J ⥤ C} {F : C ⥤ D} [F.ReflectsIsomorphisms]
  body: createsLimitOfReflectsIso' (isLimitOfPreserves F (limit.isLimit _))
    ⟨⟨_, Iso.refl _⟩, limit.isLimit _⟩

中文:
定义 createsLimitOfReflectsIsomorphismsOfPreserves
  签名: {K : J ⥤ C} {F : C ⥤ D} [F.反映同构]
  定义体: createsLimitOfReflectsIso' (isLimitOfPreserves F (limit.isLimit _))
    ⟨⟨_, Iso.refl _⟩, limit.isLimit _⟩

Depends on / 依赖: Iso.refl, createsLimitOfReflectsIso, isLimit, isLimitOfPreserves, limit.isLimit
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
/--
Definition of `createsLimitOfFullyFaithfulOfLift'` / `createsLimitOfFullyFaithfulOfLift'` 的定义

English:
definition createsLimitOfFullyFaithfulOfLift'
  signature: {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
  body: createsLimitOfReflectsIso' hl ⟨⟨c, i⟩, isLimitOfReflects F (IsLimit.ofIsoLimit hl i.symm)⟩

中文:
定义 createsLimitOfFullyFaithfulOfLift'
  签名: {K : J ⥤ C} {F : C ⥤ D} [F.满] [F.忠实]
  定义体: createsLimitOfReflectsIso' hl ⟨⟨c, i⟩, isLimitOfReflects F (IsLimit.ofIsoLimit hl i.symm)⟩

Depends on / 依赖: IsLimit, IsLimit.ofIsoLimit, createsLimitOfReflectsIso, i.symm, isLimitOfReflects, ofIsoLimit
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
/--
Definition of `createsLimitOfFullyFaithfulOfLift` / `createsLimitOfFullyFaithfulOfLift` 的定义

English:
definition createsLimitOfFullyFaithfulOfLift
  signature: {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
  body: createsLimitOfFullyFaithfulOfLift' (limit.isLimit _) c i

中文:
定义 createsLimitOfFullyFaithfulOfLift
  签名: {K : J ⥤ C} {F : C ⥤ D} [F.满] [F.忠实]
  定义体: createsLimitOfFullyFaithfulOfLift' (limit.isLimit _) c i

Depends on / 依赖: createsLimitOfFullyFaithfulOfLift, isLimit, limit.isLimit
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
/--
Definition of `createsLimitOfFullyFaithfulOfIso'` / `createsLimitOfFullyFaithfulOfIso'` 的定义

English:
definition createsLimitOfFullyFaithfulOfIso'
  signature: {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
  body: createsLimitOfFullyFaithfulOfLift' hl
    { pt := X
      π :=
        { app := fun j => F.preimage (i.hom ≫ l.π.app j)
          naturality := fun Y Z f =>
F.map_injective by
              simpa using (l.w f).symm } }
    (Cone.ext i fun j => by simp only [Functor.map_preimage, Functor.mapCone_π_ap

中文:
定义 createsLimitOfFullyFaithfulOfIso'
  签名: {K : J ⥤ C} {F : C ⥤ D} [F.满] [F.忠实]
  定义体: createsLimitOfFullyFaithfulOfLift' hl
    { pt := X
      π :=
        { app := fun j => F.preimage (i.hom ≫ l.π.app j)
          naturality := fun Y Z f =>
F.map_injective by
              simpa using (l.w f).symm } }
    (Cone.ext i fun j => by simp only [Functor.map_preimage, Functor.mapCone_π_ap

Depends on / 依赖: Cone.ext, F.map_injective, F.preimage, Functor, Functor.mapCone_, Functor.map_preimage, createsLimitOfFullyFaithfulOfLift, i.hom, map_injective, map_preimage, naturality, preimage
-/
def createsLimitOfFullyFaithfulOfIso' {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    {l : Cone (K ⋙ F)} (hl : IsLimit l) (X : C) (i : F.obj X ≅ l.pt) : CreatesLimit K F :=
  createsLimitOfFullyFaithfulOfLift' hl
    { pt := X
      π :=
        { app := fun j => F.preimage (i.hom ≫ l.π.app j)
          naturality := fun Y Z f =>
F.map_injective by
              simpa using (l.w f).symm } }
    (Cone.ext i fun j => by simp only [Functor.map_preimage, Functor.mapCone_π_app])

-- Notice however that even if the isomorphism is `Iso.refl _`,
-- this construction will insert additional identity morphisms in the cone maps,
-- so the constructed limits may not be ideal, definitionally.
/-- When `F` is fully faithful, and `HasLimit (K ⋙ F)`, to show that `F` creates the limit for `K`
it suffices to show that the chosen limit point is in the essential image of `F`.
-/
@[instance_reducible]
/--
Definition of `createsLimitOfFullyFaithfulOfIso` / `createsLimitOfFullyFaithfulOfIso` 的定义

English:
definition createsLimitOfFullyFaithfulOfIso
  signature: {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
  body: createsLimitOfFullyFaithfulOfIso' (limit.isLimit _) X i

中文:
定义 createsLimitOfFullyFaithfulOfIso
  签名: {K : J ⥤ C} {F : C ⥤ D} [F.满] [F.忠实]
  定义体: createsLimitOfFullyFaithfulOfIso' (limit.isLimit _) X i

Depends on / 依赖: createsLimitOfFullyFaithfulOfIso, isLimit, limit.isLimit
-/
def createsLimitOfFullyFaithfulOfIso {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    [HasLimit (K ⋙ F)] (X : C) (i : F.obj X ≅ limit (K ⋙ F)) : CreatesLimit K F :=
  createsLimitOfFullyFaithfulOfIso' (limit.isLimit _) X i

/-- A fully faithful functor that preserves a limit that exists also creates the limit. -/
@[instance_reducible]
/--
Definition of `createsLimitOfFullyFaithfulOfPreserves` / `createsLimitOfFullyFaithfulOfPreserves` 的定义

English:
definition createsLimitOfFullyFaithfulOfPreserves
  signature: {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
  body: createsLimitOfFullyFaithfulOfLift' (isLimitOfPreserves _ (limit.isLimit K)) _ (Iso.refl _)

中文:
定义 createsLimitOfFullyFaithfulOfPreserves
  签名: {K : J ⥤ C} {F : C ⥤ D} [F.满] [F.忠实]
  定义体: createsLimitOfFullyFaithfulOfLift' (isLimitOfPreserves _ (limit.isLimit K)) _ (Iso.refl _)

Depends on / 依赖: Iso.refl, createsLimitOfFullyFaithfulOfLift, isLimit, isLimitOfPreserves, limit.isLimit
-/
def createsLimitOfFullyFaithfulOfPreserves {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    [HasLimit K] [PreservesLimit K F] : CreatesLimit K F :=
  createsLimitOfFullyFaithfulOfLift' (isLimitOfPreserves _ (limit.isLimit K)) _ (Iso.refl _)

-- see Note [lower instance priority]
/-- `F` preserves the limit of `K` if it creates the limit and `K ⋙ F` has the limit. -/
instance (priority := 100) preservesLimit_of_createsLimit_and_hasLimit (K : J ⥤ C) (F : C ⥤ D)
    [CreatesLimit K F] [HasLimit (K ⋙ F)] : PreservesLimit K F where
  preserves t := ⟨IsLimit.ofIsoLimit (limit.isLimit _)
    ((liftedLimitMapsToOriginal (limit.isLimit _)).symm ≪≫
      (Cone.functoriality K F).mapIso ((liftedLimitIsLimit (limit.isLimit _)).uniqueUpToIso t))⟩

-- see Note [lower instance priority]
/-- `F` preserves the limit of shape `J` if it creates these limits and `D` has them. -/
instance (priority := 100) preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape
    (F : C ⥤ D) [CreatesLimitsOfShape J F] [HasLimitsOfShape J D] : PreservesLimitsOfShape J F where

-- see Note [lower instance priority]
/-- `F` preserves limits if it creates limits and `D` has limits. -/
instance (priority := 100) preservesLimits_of_createsLimits_and_hasLimits (F : C ⥤ D)
    [CreatesLimitsOfSize.{w, w'} F] [HasLimitsOfSize.{w, w'} D] :
    PreservesLimitsOfSize.{w, w'} F where

set_option backward.isDefEq.respectTransparency.types false in
/-- If `F` reflects isomorphisms and we can lift any colimit cocone to a colimit cocone,
then `F` creates colimits.
In particular here we don't need to assume that F reflects colimits.
-/
@[instance_reducible]
/--
Definition of `createsColimitOfReflectsIso` / `createsColimitOfReflectsIso` 的定义

English:
definition createsColimitOfReflectsIso
  signature: {K : J ⥤ C} {F : C ⥤ D} [F.ReflectsIsomorphisms]
  body: (h c t).toLiftableCocone
  toReflectsColimit :=
    { reflects := fun {d} hd => ⟨by
        let d' : Cocone K := (h (F.mapCocone d) hd).toLiftableCocone.liftedCocone
        let i : F.mapCocone d' ≅ F.mapCocone d :=
          (h (F.mapCocone d) hd).toLiftableCocone.validLift
        let hd' : IsColi

中文:
定义 createsColimitOfReflectsIso
  签名: {K : J ⥤ C} {F : C ⥤ D} [F.反映同构]
  定义体: (h c t).toLiftableCocone
  toReflectsColimit :=
    { reflects := fun {d} hd => ⟨by
        let d' : Cocone K := (h (F.mapCocone d) hd).toLiftableCocone.liftedCocone
        let i : F.mapCocone d' ≅ F.mapCocone d :=
          (h (F.mapCocone d) hd).toLiftableCocone.validLift
        let hd' : IsColi

Depends on / 依赖: toLiftableCocone
-/
def createsColimitOfReflectsIso {K : J ⥤ C} {F : C ⥤ D} [F.ReflectsIsomorphisms]
    (h : forall c t, LiftsToColimit K F c t) : CreatesColimit K F where
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
/--
Definition of `createsColimitOfReflectsIso'` / `createsColimitOfReflectsIso'` 的定义

English:
definition createsColimitOfReflectsIso'
  signature: {K : J ⥤ C} {F : C ⥤ D} [F.ReflectsIsomorphisms]
  body: createsColimitOfReflectsIso fun _ t =>
    { liftedCocone := h.liftedCocone
      validLift := h.validLift ≪≫ IsColimit.uniqueUpToIso hc t
      makesColimit := h.makesColimit }

中文:
定义 createsColimitOfReflectsIso'
  签名: {K : J ⥤ C} {F : C ⥤ D} [F.反映同构]
  定义体: createsColimitOfReflectsIso fun _ t =>
    { liftedCocone := h.liftedCocone
      validLift := h.validLift ≪≫ IsColimit.uniqueUpToIso hc t
      makesColimit := h.makesColimit }

Depends on / 依赖: IsColimit, IsColimit.uniqueUpToIso, createsColimitOfReflectsIso, h.liftedCocone, h.makesColimit, h.validLift, liftedCocone, makesColimit, uniqueUpToIso, validLift
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
/--
Definition of `createsColimitOfReflectsIsomorphismsOfPreserves` / `createsColimitOfReflectsIsomorphismsOfPreserves` 的定义

English:
definition createsColimitOfReflectsIsomorphismsOfPreserves
  signature: {K : J ⥤ C} {F : C ⥤ D}
  body: createsColimitOfReflectsIso' (isColimitOfPreserves F (colimit.isColimit _))
    ⟨⟨_, Iso.refl _⟩, colimit.isColimit _⟩

中文:
定义 createsColimitOfReflectsIsomorphismsOfPreserves
  签名: {K : J ⥤ C} {F : C ⥤ D}
  定义体: createsColimitOfReflectsIso' (isColimitOfPreserves F (colimit.isColimit _))
    ⟨⟨_, Iso.refl _⟩, colimit.isColimit _⟩

Depends on / 依赖: Iso.refl, colimit, colimit.isColimit, createsColimitOfReflectsIso, isColimit, isColimitOfPreserves
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
/--
Definition of `createsColimitOfFullyFaithfulOfLift'` / `createsColimitOfFullyFaithfulOfLift'` 的定义

English:
definition createsColimitOfFullyFaithfulOfLift'
  signature: {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
  body: createsColimitOfReflectsIso' hl ⟨⟨c, i⟩, isColimitOfReflects F (IsColimit.ofIsoColimit hl i.symm)⟩

中文:
定义 createsColimitOfFullyFaithfulOfLift'
  签名: {K : J ⥤ C} {F : C ⥤ D} [F.满] [F.忠实]
  定义体: createsColimitOfReflectsIso' hl ⟨⟨c, i⟩, isColimitOfReflects F (IsColimit.ofIsoColimit hl i.symm)⟩

Depends on / 依赖: IsColimit, IsColimit.ofIsoColimit, createsColimitOfReflectsIso, i.symm, isColimitOfReflects, ofIsoColimit
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
/--
Definition of `createsColimitOfFullyFaithfulOfLift` / `createsColimitOfFullyFaithfulOfLift` 的定义

English:
definition createsColimitOfFullyFaithfulOfLift
  signature: {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
  body: createsColimitOfFullyFaithfulOfLift' (colimit.isColimit _) c i

中文:
定义 createsColimitOfFullyFaithfulOfLift
  签名: {K : J ⥤ C} {F : C ⥤ D} [F.满] [F.忠实]
  定义体: createsColimitOfFullyFaithfulOfLift' (colimit.isColimit _) c i

Depends on / 依赖: colimit, colimit.isColimit, createsColimitOfFullyFaithfulOfLift, isColimit
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
/--
Definition of `createsColimitOfFullyFaithfulOfIso'` / `createsColimitOfFullyFaithfulOfIso'` 的定义

English:
definition createsColimitOfFullyFaithfulOfIso'
  signature: {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
  body: createsColimitOfFullyFaithfulOfLift' hl
    { pt := X
      ι :=
        { app := fun j => F.preimage (l.ι.app j ≫ i.inv)
          naturality := fun Y Z f =>
F.map_injective by
              simpa [← cancel_mono i.hom] using l.w f } }
    (Cocone.ext i fun j => by simp)

中文:
定义 createsColimitOfFullyFaithfulOfIso'
  签名: {K : J ⥤ C} {F : C ⥤ D} [F.满] [F.忠实]
  定义体: createsColimitOfFullyFaithfulOfLift' hl
    { pt := X
      ι :=
        { app := fun j => F.preimage (l.ι.app j ≫ i.inv)
          naturality := fun Y Z f =>
F.map_injective by
              simpa [← cancel_mono i.hom] using l.w f } }
    (Cocone.ext i fun j => by simp)

Depends on / 依赖: Cocone, Cocone.ext, F.map_injective, F.preimage, cancel_mono, createsColimitOfFullyFaithfulOfLift, i.hom, i.inv, map_injective, naturality, preimage
-/
def createsColimitOfFullyFaithfulOfIso' {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    {l : Cocone (K ⋙ F)} (hl : IsColimit l) (X : C) (i : F.obj X ≅ l.pt) : CreatesColimit K F :=
  createsColimitOfFullyFaithfulOfLift' hl
    { pt := X
      ι :=
        { app := fun j => F.preimage (l.ι.app j ≫ i.inv)
          naturality := fun Y Z f =>
F.map_injective by
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
/--
Definition of `createsColimitOfFullyFaithfulOfIso` / `createsColimitOfFullyFaithfulOfIso` 的定义

English:
definition createsColimitOfFullyFaithfulOfIso
  signature: {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
  body: createsColimitOfFullyFaithfulOfIso' (colimit.isColimit _) X i

中文:
定义 createsColimitOfFullyFaithfulOfIso
  签名: {K : J ⥤ C} {F : C ⥤ D} [F.满] [F.忠实]
  定义体: createsColimitOfFullyFaithfulOfIso' (colimit.isColimit _) X i

Depends on / 依赖: colimit, colimit.isColimit, createsColimitOfFullyFaithfulOfIso, isColimit
-/
def createsColimitOfFullyFaithfulOfIso {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    [HasColimit (K ⋙ F)] (X : C) (i : F.obj X ≅ colimit (K ⋙ F)) : CreatesColimit K F :=
  createsColimitOfFullyFaithfulOfIso' (colimit.isColimit _) X i

-- see Note [lower instance priority]
/-- `F` preserves the colimit of `K` if it creates the colimit and `K ⋙ F` has the colimit. -/
instance (priority := 100) preservesColimit_of_createsColimit_and_hasColimit (K : J ⥤ C) (F : C ⥤ D)
    [CreatesColimit K F] [HasColimit (K ⋙ F)] : PreservesColimit K F where
  preserves t :=
    ⟨IsColimit.ofIsoColimit (colimit.isColimit _)
      ((liftedColimitMapsToOriginal (colimit.isColimit _)).symm ≪≫
        (Cocone.functoriality K F).mapIso
          ((liftedColimitIsColimit (colimit.isColimit _)).uniqueUpToIso t))⟩

-- see Note [lower instance priority]
/-- `F` preserves the colimit of shape `J` if it creates these colimits and `D` has them. -/
instance (priority := 100) preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape
    (F : C ⥤ D) [CreatesColimitsOfShape J F] [HasColimitsOfShape J D] :
    PreservesColimitsOfShape J F where

-- see Note [lower instance priority]
/-- `F` preserves limits if it creates limits and `D` has limits. -/
instance (priority := 100) preservesColimits_of_createsColimits_and_hasColimits (F : C ⥤ D)
    [CreatesColimitsOfSize.{w, w'} F] [HasColimitsOfSize.{w, w'} D] :
    PreservesColimitsOfSize.{w, w'} F where

set_option backward.defeqAttrib.useBackward true in
/-- Transfer creation of limits along a natural isomorphism in the diagram. -/
@[instance_reducible]
/--
Definition of `createsLimitOfIsoDiagram` / `createsLimitOfIsoDiagram` 的定义

English:
definition createsLimitOfIsoDiagram
  signature: {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [CreatesLimit K₁ F]
  body: { reflectsLimit_of_iso_diagram F h with
    lifts := fun c t =>
      let t' := (IsLimit.postcomposeInvEquiv (isoWhiskerRight h F :) c).symm t
      { liftedCone := (Cone.postcompose h.hom).obj (liftLimit t')
        validLift :=
          Functor.mapConePostcompose F ≪≫
            (Cone.postcompos

中文:
定义 createsLimitOfIsoDiagram
  签名: {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [创造极限 K₁ F]
  定义体: { reflectsLimit_of_iso_diagram F h with
    lifts := fun c t =>
      let t' := (IsLimit.postcomposeInvEquiv (isoWhiskerRight h F :) c).symm t
      { liftedCone := (Cone.postcompose h.hom).obj (liftLimit t')
        validLift :=
          Functor.mapConePostcompose F ≪≫
            (Cone.postcompos

Depends on / 依赖: Category, Category.assoc, Cone.ext, Cone.postcompose, F.map_comp, Functor, Functor.mapConePostcompose, IsLimit, IsLimit.postcomposeInvEquiv, Iso.refl, h.hom, isoWhiskerRight, liftLimit, liftedCone, liftedLimitMapsToOriginal, mapConePostcompose, mapIso, map_comp, postcompose, postcomposeInvEquiv
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
                rw [Category.assoc]; rw [← F.map_comp]
                simp } }

/-- If `F` creates the limit of `K` and `F ≅ G`, then `G` creates the limit of `K`. -/
@[instance_reducible]
/--
Definition of `createsLimitOfNatIso` / `createsLimitOfNatIso` 的定义

English:
definition createsLimitOfNatIso
  signature: {F G : C ⥤ D} (h : F ≅ G) [CreatesLimit K F]
  body: { liftedCone := liftLimit ((IsLimit.postcomposeInvEquiv (isoWhiskerLeft K h :) c).symm t)
      validLift := by
        refine (IsLimit.mapConeEquiv h ?_).uniqueUpToIso t
        apply IsLimit.ofIsoLimit _ (liftedLimitMapsToOriginal _).symm
        apply (IsLimit.postcomposeInvEquiv _ _).symm t }
  

中文:
定义 createsLimitOf自然数Iso
  签名: {F G : C ⥤ D} (h : F ≅ G) [创造极限 K F]
  定义体: { liftedCone := liftLimit ((IsLimit.postcomposeInvEquiv (isoWhiskerLeft K h :) c).symm t)
      validLift := by
        refine (IsLimit.mapConeEquiv h ?_).uniqueUpToIso t
        apply IsLimit.ofIsoLimit _ (liftedLimitMapsToOriginal _).symm
        apply (IsLimit.postcomposeInvEquiv _ _).symm t }
  

Depends on / 依赖: IsLimit, IsLimit.mapConeEquiv, IsLimit.ofIsoLimit, IsLimit.postcomposeInvEquiv, isoWhiskerLeft, liftLimit, liftedCone, liftedLimitMapsToOriginal, mapConeEquiv, ofIsoLimit, postcomposeInvEquiv, reflectsLimit_of_natIso, toReflectsLimit, uniqueUpToIso, validLift
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
/--
Definition of `createsLimitsOfShapeOfNatIso` / `createsLimitsOfShapeOfNatIso` 的定义

English:
definition createsLimitsOfShapeOfNatIso
  signature: {F G : C ⥤ D} (h : F ≅ G) [CreatesLimitsOfShape J F]
  body: createsLimitOfNatIso h

中文:
定义 createsLimitsOfShapeOf自然数Iso
  签名: {F G : C ⥤ D} (h : F ≅ G) [创造形状极限 J F]
  定义体: createsLimitOfNatIso h

Depends on / 依赖: createsLimitOfNatIso
-/
def createsLimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesLimitsOfShape J F] :
    CreatesLimitsOfShape J G where CreatesLimit := createsLimitOfNatIso h

/-- If `F` creates limits and `F ≅ G`, then `G` creates limits. -/
@[instance_reducible]
/--
Definition of `createsLimitsOfNatIso` / `createsLimitsOfNatIso` 的定义

English:
definition createsLimitsOfNatIso
  signature: {F G : C ⥤ D} (h : F ≅ G) [CreatesLimitsOfSize.{w, w'} F]
  body: createsLimitsOfShapeOfNatIso h

中文:
定义 createsLimitsOf自然数Iso
  签名: {F G : C ⥤ D} (h : F ≅ G) [CreatesLimitsOfSize.{w, w'} F]
  定义体: createsLimitsOfShapeOfNatIso h

Depends on / 依赖: createsLimitsOfShapeOfNatIso
-/
def createsLimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesLimitsOfSize.{w, w'} F] :
    CreatesLimitsOfSize.{w, w'} G where
  CreatesLimitsOfShape := createsLimitsOfShapeOfNatIso h

set_option backward.defeqAttrib.useBackward true in
/-- If `F` creates limits of shape `J` and `J ≌ J'`, then `F` creates limits of shape `J'`. -/
@[instance_reducible]
/--
Definition of `createsLimitsOfShapeOfEquiv` / `createsLimitsOfShapeOfEquiv` 的定义

English:
definition createsLimitsOfShapeOfEquiv
  signature: {J' : Type w₁} [Category.{w'₁} J'] (e : J ≌ J') (F : C ⥤ D)
  body: { lifts c hc := by
        refine ⟨(Cone.whiskeringEquivalence e).inverse.obj
          (liftLimit (hc.whiskerEquivalence e)), ?_⟩
        letI inner := (Cone.whiskeringEquivalence (F := K ⋙ F) e).inverse.mapIso
          (liftedLimitMapsToOriginal (K := e.functor ⋙ K) (hc.whiskerEquivalence e))
   

中文:
定义 createsLimitsOfShapeOfEquiv
  签名: {J' : 类型 w₁} [范畴.{w'₁} J'] (e : J ≌ J') (F : C ⥤ D)
  定义体: { lifts c hc := by
        refine ⟨(Cone.whiskeringEquivalence e).inverse.obj
          (liftLimit (hc.whiskerEquivalence e)), ?_⟩
        letI inner := (Cone.whiskeringEquivalence (F := K ⋙ F) e).inverse.mapIso
          (liftedLimitMapsToOriginal (K := e.functor ⋙ K) (hc.whiskerEquivalence e))
   

Depends on / 依赖: Cone.ext, Cone.whiskeringEquivalence, Iso.refl, e.functor, functor, hc.whiskerEquivalence, inverse, inverse.mapIso, inverse.obj, liftLimit, liftedLimitMapsToOriginal, mapIso, reflectsLimitsOfShape_of_equiv, toReflectsLimit, unitIso, unitIso.app, whiskerEquivalence, whiskeringEquivalence
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
/--
Definition of `createsColimitOfIsoDiagram` / `createsColimitOfIsoDiagram` 的定义

English:
definition createsColimitOfIsoDiagram
  signature: {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [CreatesColimit K₁ F]
  body: { reflectsColimit_of_iso_diagram F h with
    lifts := fun c t =>
      let t' := (IsColimit.precomposeHomEquiv (isoWhiskerRight h F :) c).symm t
      { liftedCocone := (Cocone.precompose h.inv).obj (liftColimit t')
        validLift :=
          Functor.mapCoconePrecompose F ≪≫
            (Cocone

中文:
定义 createsColimitOfIsoDiagram
  签名: {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [创造余极限 K₁ F]
  定义体: { reflectsColimit_of_iso_diagram F h with
    lifts := fun c t =>
      let t' := (IsColimit.precomposeHomEquiv (isoWhiskerRight h F :) c).symm t
      { liftedCocone := (Cocone.precompose h.inv).obj (liftColimit t')
        validLift :=
          Functor.mapCoconePrecompose F ≪≫
            (Cocone

Depends on / 依赖: Cocone, Cocone.ext, Cocone.precompose, F.map_comp_assoc, Functor, Functor.mapCoconePrecompose, IsColimit, IsColimit.precomposeHomEquiv, Iso.refl, h.inv, isoWhiskerRight, liftColimit, liftedCocone, liftedColimitMapsToOriginal, mapCoconePrecompose, mapIso, map_comp_assoc, precompose, precomposeHomEquiv, reflectsColimit_of_iso_diagram
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
/--
Definition of `createsColimitOfNatIso` / `createsColimitOfNatIso` 的定义

English:
definition createsColimitOfNatIso
  signature: {F G : C ⥤ D} (h : F ≅ G) [CreatesColimit K F]
  body: { liftedCocone := liftColimit ((IsColimit.precomposeHomEquiv (isoWhiskerLeft K h :) c).symm t)
      validLift := by
        refine (IsColimit.mapCoconeEquiv h ?_).uniqueUpToIso t
        apply IsColimit.ofIsoColimit _ (liftedColimitMapsToOriginal _).symm
        apply (IsColimit.precomposeHomEquiv 

中文:
定义 createsColimitOf自然数Iso
  签名: {F G : C ⥤ D} (h : F ≅ G) [创造余极限 K F]
  定义体: { liftedCocone := liftColimit ((IsColimit.precomposeHomEquiv (isoWhiskerLeft K h :) c).symm t)
      validLift := by
        refine (IsColimit.mapCoconeEquiv h ?_).uniqueUpToIso t
        apply IsColimit.ofIsoColimit _ (liftedColimitMapsToOriginal _).symm
        apply (IsColimit.precomposeHomEquiv 

Depends on / 依赖: IsColimit, IsColimit.mapCoconeEquiv, IsColimit.ofIsoColimit, IsColimit.precomposeHomEquiv, isoWhiskerLeft, liftColimit, liftedCocone, liftedColimitMapsToOriginal, mapCoconeEquiv, ofIsoColimit, precomposeHomEquiv, reflectsColimit_of_natIso, toReflectsColimit, uniqueUpToIso, validLift
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
/--
Definition of `createsColimitsOfShapeOfNatIso` / `createsColimitsOfShapeOfNatIso` 的定义

English:
definition createsColimitsOfShapeOfNatIso
  signature: {F G : C ⥤ D} (h : F ≅ G) [CreatesColimitsOfShape J F]
  body: createsColimitOfNatIso h

中文:
定义 createsColimitsOfShapeOf自然数Iso
  签名: {F G : C ⥤ D} (h : F ≅ G) [创造形状余极限 J F]
  定义体: createsColimitOfNatIso h

Depends on / 依赖: createsColimitOfNatIso
-/
def createsColimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesColimitsOfShape J F] :
    CreatesColimitsOfShape J G where CreatesColimit := createsColimitOfNatIso h

/-- If `F` creates colimits and `F ≅ G`, then `G` creates colimits. -/
@[instance_reducible]
/--
Definition of `createsColimitsOfNatIso` / `createsColimitsOfNatIso` 的定义

English:
definition createsColimitsOfNatIso
  signature: {F G : C ⥤ D} (h : F ≅ G) [CreatesColimitsOfSize.{w, w'} F]
  body: createsColimitsOfShapeOfNatIso h

中文:
定义 createsColimitsOf自然数Iso
  签名: {F G : C ⥤ D} (h : F ≅ G) [CreatesColimitsOfSize.{w, w'} F]
  定义体: createsColimitsOfShapeOfNatIso h

Depends on / 依赖: createsColimitsOfShapeOfNatIso
-/
def createsColimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesColimitsOfSize.{w, w'} F] :
    CreatesColimitsOfSize.{w, w'} G where
  CreatesColimitsOfShape := createsColimitsOfShapeOfNatIso h

set_option backward.defeqAttrib.useBackward true in
/-- If `F` creates colimits of shape `J` and `J ≌ J'`, then `F` creates colimits of shape `J'`. -/
@[instance_reducible]
/--
Definition of `createsColimitsOfShapeOfEquiv` / `createsColimitsOfShapeOfEquiv` 的定义

English:
definition createsColimitsOfShapeOfEquiv
  signature: {J' : Type w₁} [Category.{w'₁} J'] (e : J ≌ J') (F : C ⥤ D)
  body: { lifts c hc := by
        refine ⟨(Cocone.whiskeringEquivalence e).inverse.obj
          (liftColimit (hc.whiskerEquivalence e)), ?_⟩
        letI inner := (Cocone.whiskeringEquivalence (F := K ⋙ F) e).inverse.mapIso
          (liftedColimitMapsToOriginal (K := e.functor ⋙ K) (hc.whiskerEquivalence

中文:
定义 createsColimitsOfShapeOfEquiv
  签名: {J' : 类型 w₁} [范畴.{w'₁} J'] (e : J ≌ J') (F : C ⥤ D)
  定义体: { lifts c hc := by
        refine ⟨(Cocone.whiskeringEquivalence e).inverse.obj
          (liftColimit (hc.whiskerEquivalence e)), ?_⟩
        letI inner := (Cocone.whiskeringEquivalence (F := K ⋙ F) e).inverse.mapIso
          (liftedColimitMapsToOriginal (K := e.functor ⋙ K) (hc.whiskerEquivalence

Depends on / 依赖: Cocone, Cocone.ext, Cocone.whiskeringEquivalence, Iso.refl, e.functor, functor, hc.whiskerEquivalence, inverse, inverse.mapIso, inverse.obj, liftColimit, liftedColimitMapsToOriginal, mapIso, reflectsColimitsOfShape_of_equiv, toReflectsColimit, unitIso, unitIso.app, whiskerEquivalence, whiskeringEquivalence
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
/--
Definition of `liftsToLimitOfCreates` / `liftsToLimitOfCreates` 的定义

English:
definition liftsToLimitOfCreates
  signature: (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K F] (c : Cone (K ⋙ F))
  body: liftLimit t
  validLift := liftedLimitMapsToOriginal t
  makesLimit := liftedLimitIsLimit t

中文:
定义 liftsToLimitOfCreates
  签名: (K : J ⥤ C) (F : C ⥤ D) [创造极限 K F] (c : 锥 (K ⋙ F))
  定义体: liftLimit t
  validLift := liftedLimitMapsToOriginal t
  makesLimit := liftedLimitIsLimit t

Depends on / 依赖: liftLimit
-/
def liftsToLimitOfCreates (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K F] (c : Cone (K ⋙ F))
    (t : IsLimit c) : LiftsToLimit K F c t where
  liftedCone := liftLimit t
  validLift := liftedLimitMapsToOriginal t
  makesLimit := liftedLimitIsLimit t

-- For the inhabited linter later.
/--
Definition of `liftsToColimitOfCreates` / `liftsToColimitOfCreates` 的定义

English:
definition liftsToColimitOfCreates
  signature: (K : J ⥤ C) (F : C ⥤ D) [CreatesColimit K F] (c : Cocone (K ⋙ F))
  body: liftColimit t
  validLift := liftedColimitMapsToOriginal t
  makesColimit := liftedColimitIsColimit t

中文:
定义 liftsToColimitOfCreates
  签名: (K : J ⥤ C) (F : C ⥤ D) [创造余极限 K F] (c : 余锥 (K ⋙ F))
  定义体: liftColimit t
  validLift := liftedColimitMapsToOriginal t
  makesColimit := liftedColimitIsColimit t

Depends on / 依赖: liftColimit
-/
def liftsToColimitOfCreates (K : J ⥤ C) (F : C ⥤ D) [CreatesColimit K F] (c : Cocone (K ⋙ F))
    (t : IsColimit c) : LiftsToColimit K F c t where
  liftedCocone := liftColimit t
  validLift := liftedColimitMapsToOriginal t
  makesColimit := liftedColimitIsColimit t

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `idLiftsCone` / `idLiftsCone` 的定义

English:
definition idLiftsCone
  signature: (c : Cone (K ⋙ 𝟭 C))
  body: { pt := c.pt
      π := c.π ≫ K.rightUnitor.hom }
  validLift := Cone.ext (Iso.refl _)

中文:
定义 idLiftsCone
  签名: (c : 锥 (K ⋙ 𝟭 C))
  定义体: { pt := c.pt
      π := c.π ≫ K.rightUnitor.hom }
  validLift := Cone.ext (Iso.refl _)

Depends on / 依赖: Cone.ext, Iso.refl, K.rightUnitor.hom, c.pt, rightUnitor, validLift
-/
def idLiftsCone (c : Cone (K ⋙ 𝟭 C)) : LiftableCone K (𝟭 C) c where
  liftedCone :=
    { pt := c.pt
      π := c.π ≫ K.rightUnitor.hom }
  validLift := Cone.ext (Iso.refl _)

/--
Instance `idCreatesLimits` / 实例 `idCreatesLimits`

English:
instance idCreatesLimits
  signature: : CreatesLimitsOfSize.{w, w'} (𝟭 C) where
  body: { CreatesLimit := { lifts := fun c _ => idLiftsCone c } }

中文:
实例 idCreatesLimits
  签名: : CreatesLimitsOfSize.{w, w'} (𝟭 C) where
  定义体: { CreatesLimit := { lifts := fun c _ => idLiftsCone c } }

Depends on / 依赖: CreatesLimit, idLiftsCone
-/
instance idCreatesLimits : CreatesLimitsOfSize.{w, w'} (𝟭 C) where
  CreatesLimitsOfShape :=
    { CreatesLimit := { lifts := fun c _ => idLiftsCone c } }

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `idLiftsCocone` / `idLiftsCocone` 的定义

English:
definition idLiftsCocone
  signature: (c : Cocone (K ⋙ 𝟭 C))
  body: { pt := c.pt
      ι := K.rightUnitor.inv ≫ c.ι }
  validLift := Cocone.ext (Iso.refl _)

中文:
定义 idLiftsCocone
  签名: (c : 余锥 (K ⋙ 𝟭 C))
  定义体: { pt := c.pt
      ι := K.rightUnitor.inv ≫ c.ι }
  validLift := Cocone.ext (Iso.refl _)

Depends on / 依赖: Cocone, Cocone.ext, Iso.refl, K.rightUnitor.inv, c.pt, rightUnitor, validLift
-/
def idLiftsCocone (c : Cocone (K ⋙ 𝟭 C)) : LiftableCocone K (𝟭 C) c where
  liftedCocone :=
    { pt := c.pt
      ι := K.rightUnitor.inv ≫ c.ι }
  validLift := Cocone.ext (Iso.refl _)

/--
Instance `idCreatesColimits` / 实例 `idCreatesColimits`

English:
instance idCreatesColimits
  signature: : CreatesColimitsOfSize.{w, w'} (𝟭 C) where
  body: { CreatesColimit := { lifts := fun c _ => idLiftsCocone c } }

中文:
实例 idCreatesColimits
  签名: : CreatesColimitsOfSize.{w, w'} (𝟭 C) where
  定义体: { CreatesColimit := { lifts := fun c _ => idLiftsCocone c } }

Depends on / 依赖: CreatesColimit, idLiftsCocone
-/
instance idCreatesColimits : CreatesColimitsOfSize.{w, w'} (𝟭 C) where
  CreatesColimitsOfShape :=
    { CreatesColimit := { lifts := fun c _ => idLiftsCocone c } }

/--
Instance `inhabitedLiftableCone` / 实例 `inhabitedLiftableCone`

English:
instance inhabitedLiftableCone
  signature: (c : Cone (K ⋙ 𝟭 C))
  body: ⟨idLiftsCone c⟩

中文:
实例 inhabitedLiftableCone
  签名: (c : 锥 (K ⋙ 𝟭 C))
  定义体: ⟨idLiftsCone c⟩

Depends on / 依赖: idLiftsCone
-/
instance inhabitedLiftableCone (c : Cone (K ⋙ 𝟭 C)) : Inhabited (LiftableCone K (𝟭 C) c) :=
  ⟨idLiftsCone c⟩

/--
Instance `inhabitedLiftableCocone` / 实例 `inhabitedLiftableCocone`

English:
instance inhabitedLiftableCocone
  signature: (c : Cocone (K ⋙ 𝟭 C))
  body: ⟨idLiftsCocone c⟩

中文:
实例 inhabitedLiftableCocone
  签名: (c : 余锥 (K ⋙ 𝟭 C))
  定义体: ⟨idLiftsCocone c⟩

Depends on / 依赖: idLiftsCocone
-/
instance inhabitedLiftableCocone (c : Cocone (K ⋙ 𝟭 C)) : Inhabited (LiftableCocone K (𝟭 C) c) :=
  ⟨idLiftsCocone c⟩

/--
Instance `inhabitedLiftsToLimit` / 实例 `inhabitedLiftsToLimit`

English:
instance inhabitedLiftsToLimit
  signature: (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K F] (c : Cone (K ⋙ F))
  body: ⟨liftsToLimitOfCreates K F c t⟩

中文:
实例 inhabitedLiftsToLimit
  签名: (K : J ⥤ C) (F : C ⥤ D) [创造极限 K F] (c : 锥 (K ⋙ F))
  定义体: ⟨liftsToLimitOfCreates K F c t⟩

Depends on / 依赖: liftsToLimitOfCreates
-/
instance inhabitedLiftsToLimit (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K F] (c : Cone (K ⋙ F))
    (t : IsLimit c) : Inhabited (LiftsToLimit _ _ _ t) :=
  ⟨liftsToLimitOfCreates K F c t⟩

/--
Instance `inhabitedLiftsToColimit` / 实例 `inhabitedLiftsToColimit`

English:
instance inhabitedLiftsToColimit
  signature: (K : J ⥤ C) (F : C ⥤ D) [CreatesColimit K F] (c : Cocone (K ⋙ F))
  body: ⟨liftsToColimitOfCreates K F c t⟩

中文:
实例 inhabitedLiftsToColimit
  签名: (K : J ⥤ C) (F : C ⥤ D) [创造余极限 K F] (c : 余锥 (K ⋙ F))
  定义体: ⟨liftsToColimitOfCreates K F c t⟩

Depends on / 依赖: liftsToColimitOfCreates
-/
instance inhabitedLiftsToColimit (K : J ⥤ C) (F : C ⥤ D) [CreatesColimit K F] (c : Cocone (K ⋙ F))
    (t : IsColimit c) : Inhabited (LiftsToColimit _ _ _ t) :=
  ⟨liftsToColimitOfCreates K F c t⟩

section Comp

variable {E : Type u₃} [ℰ : Category.{v₃} E]
variable (F : C ⥤ D) (G : D ⥤ E)

/--
Instance `compCreatesLimit` / 实例 `compCreatesLimit`

English:
instance compCreatesLimit
  signature: [CreatesLimit K F] [CreatesLimit (K ⋙ F) G]
  body: by
    let c' : Cone ((K ⋙ F) ⋙ G) := c
    let t' : IsLimit c' := t
    exact
      { liftedCone := liftLimit (liftedLimitIsLimit t')
        validLift := (Cone.functoriality (K ⋙ F) G).mapIso
            (liftedLimitMapsToOriginal (liftedLimitIsLimit t')) ≪≫
          liftedLimitMapsToOriginal t' 

中文:
实例 compCreatesLimit
  签名: [创造极限 K F] [创造极限 (K ⋙ F) G]
  定义体: by
    let c' : Cone ((K ⋙ F) ⋙ G) := c
    let t' : IsLimit c' := t
    exact
      { liftedCone := liftLimit (liftedLimitIsLimit t')
        validLift := (Cone.functoriality (K ⋙ F) G).mapIso
            (liftedLimitMapsToOriginal (liftedLimitIsLimit t')) ≪≫
          liftedLimitMapsToOriginal t' 

Depends on / 依赖: Cone.functoriality, IsLimit, functoriality, liftLimit, liftedCone, liftedLimitIsLimit, liftedLimitMapsToOriginal, mapIso, validLift
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

/--
Instance `compCreatesLimitsOfShape` / 实例 `compCreatesLimitsOfShape`

English:
instance compCreatesLimitsOfShape
  signature: [CreatesLimitsOfShape J F] [CreatesLimitsOfShape J G]
  body: inferInstance

中文:
实例 compCreatesLimitsOfShape
  签名: [创造形状极限 J F] [创造形状极限 J G]
  定义体: inferInstance
-/
instance compCreatesLimitsOfShape [CreatesLimitsOfShape J F] [CreatesLimitsOfShape J G] :
    CreatesLimitsOfShape J (F ⋙ G) where CreatesLimit := inferInstance

/--
Instance `compCreatesLimits` / 实例 `compCreatesLimits`

English:
instance compCreatesLimits
  signature: [CreatesLimitsOfSize.{w, w'} F] [CreatesLimitsOfSize.{w, w'} G]
  body: inferInstance

中文:
实例 compCreatesLimits
  签名: [CreatesLimitsOfSize.{w, w'} F] [CreatesLimitsOfSize.{w, w'} G]
  定义体: inferInstance
-/
instance compCreatesLimits [CreatesLimitsOfSize.{w, w'} F] [CreatesLimitsOfSize.{w, w'} G] :
    CreatesLimitsOfSize.{w, w'} (F ⋙ G) where CreatesLimitsOfShape := inferInstance

/--
Instance `preservesLimit_comp_of_createsLimit` / 实例 `preservesLimit_comp_of_createsLimit`

English:
instance preservesLimit_comp_of_createsLimit
  signature: [CreatesLimit K F] [PreservesLimit K (F ⋙ G)]
  body: ⟨IsLimit.ofIsoLimit (isLimitOfPreserves (F ⋙ G) (liftedLimitIsLimit hc))
    ((Functor.mapConeMapCone (liftLimit hc)).symm ≪≫
      (Cone.functoriality _ _).mapIso (liftedLimitMapsToOriginal hc))⟩

中文:
实例 preservesLimit_comp_of_createsLimit
  签名: [创造极限 K F] [保持极限 K (F ⋙ G)]
  定义体: ⟨IsLimit.ofIsoLimit (isLimitOfPreserves (F ⋙ G) (liftedLimitIsLimit hc))
    ((Functor.mapConeMapCone (liftLimit hc)).symm ≪≫
      (Cone.functoriality _ _).mapIso (liftedLimitMapsToOriginal hc))⟩

Depends on / 依赖: IsLimit, IsLimit.ofIsoLimit, isLimitOfPreserves, liftedLimitIsLimit, ofIsoLimit
-/
instance preservesLimit_comp_of_createsLimit [CreatesLimit K F] [PreservesLimit K (F ⋙ G)] :
    PreservesLimit (K ⋙ F) G where
  preserves hc := ⟨IsLimit.ofIsoLimit (isLimitOfPreserves (F ⋙ G) (liftedLimitIsLimit hc))
    ((Functor.mapConeMapCone (liftLimit hc)).symm ≪≫
      (Cone.functoriality _ _).mapIso (liftedLimitMapsToOriginal hc))⟩

/--
Instance `compCreatesColimit` / 实例 `compCreatesColimit`

English:
instance compCreatesColimit
  signature: [CreatesColimit K F] [CreatesColimit (K ⋙ F) G]
  body: let c' : Cocone ((K ⋙ F) ⋙ G) := c
    let t' : IsColimit c' := t
    { liftedCocone := liftColimit (liftedColimitIsColimit t')
      validLift :=
        (Cocone.functoriality (K ⋙ F) G).mapIso
            (liftedColimitMapsToOriginal (liftedColimitIsColimit t')) ≪≫
          liftedColimitMapsToOri

中文:
实例 compCreatesColimit
  签名: [创造余极限 K F] [创造余极限 (K ⋙ F) G]
  定义体: let c' : Cocone ((K ⋙ F) ⋙ G) := c
    let t' : IsColimit c' := t
    { liftedCocone := liftColimit (liftedColimitIsColimit t')
      validLift :=
        (Cocone.functoriality (K ⋙ F) G).mapIso
            (liftedColimitMapsToOriginal (liftedColimitIsColimit t')) ≪≫
          liftedColimitMapsToOri

Depends on / 依赖: Cocone, Cocone.functoriality, IsColimit, functoriality, liftColimit, liftedCocone, liftedColimitIsColimit, liftedColimitMapsToOriginal, mapIso, validLift
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

/--
Instance `compCreatesColimitsOfShape` / 实例 `compCreatesColimitsOfShape`

English:
instance compCreatesColimitsOfShape
  signature: [CreatesColimitsOfShape J F] [CreatesColimitsOfShape J G]
  body: inferInstance

中文:
实例 compCreatesColimitsOfShape
  签名: [创造形状余极限 J F] [创造形状余极限 J G]
  定义体: inferInstance
-/
instance compCreatesColimitsOfShape [CreatesColimitsOfShape J F] [CreatesColimitsOfShape J G] :
    CreatesColimitsOfShape J (F ⋙ G) where CreatesColimit := inferInstance

/--
Instance `compCreatesColimits` / 实例 `compCreatesColimits`

English:
instance compCreatesColimits
  signature: [CreatesColimitsOfSize.{w, w'} F] [CreatesColimitsOfSize.{w, w'} G]
  body: inferInstance

中文:
实例 compCreatesColimits
  签名: [CreatesColimitsOfSize.{w, w'} F] [CreatesColimitsOfSize.{w, w'} G]
  定义体: inferInstance
-/
instance compCreatesColimits [CreatesColimitsOfSize.{w, w'} F] [CreatesColimitsOfSize.{w, w'} G] :
    CreatesColimitsOfSize.{w, w'} (F ⋙ G) where CreatesColimitsOfShape := inferInstance

/--
Instance `preservesColimit_comp_of_createsColimit` / 实例 `preservesColimit_comp_of_createsColimit`

English:
instance preservesColimit_comp_of_createsColimit
  signature: [CreatesColimit K F] [PreservesColimit K (F ⋙ G)]
  body: ⟨IsColimit.ofIsoColimit (isColimitOfPreserves (F ⋙ G) (liftedColimitIsColimit hc))
    ((Functor.mapCoconeMapCocone (liftColimit hc)).symm ≪≫
      (Cocone.functoriality _ _).mapIso (liftedColimitMapsToOriginal hc))⟩

中文:
实例 preservesColimit_comp_of_createsColimit
  签名: [创造余极限 K F] [保持余极限 K (F ⋙ G)]
  定义体: ⟨IsColimit.ofIsoColimit (isColimitOfPreserves (F ⋙ G) (liftedColimitIsColimit hc))
    ((Functor.mapCoconeMapCocone (liftColimit hc)).symm ≪≫
      (Cocone.functoriality _ _).mapIso (liftedColimitMapsToOriginal hc))⟩

Depends on / 依赖: IsColimit, IsColimit.ofIsoColimit, isColimitOfPreserves, liftedColimitIsColimit, ofIsoColimit
-/
instance preservesColimit_comp_of_createsColimit [CreatesColimit K F] [PreservesColimit K (F ⋙ G)] :
    PreservesColimit (K ⋙ F) G where
  preserves hc := ⟨IsColimit.ofIsoColimit (isColimitOfPreserves (F ⋙ G) (liftedColimitIsColimit hc))
    ((Functor.mapCoconeMapCocone (liftColimit hc)).symm ≪≫
      (Cocone.functoriality _ _).mapIso (liftedColimitMapsToOriginal hc))⟩

end Comp

end Creates

end CategoryTheory
