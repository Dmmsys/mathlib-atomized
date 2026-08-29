/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Comon_
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Limits of monoid objects.

If `C` has limits (of a given shape), so does `Mon C`,
and the forgetful functor preserves these limits.

(This could potentially replace many individual constructions for concrete categories,
in particular `MonCat`, `SemiRingCat`, `RingCat`, and `AlgCat R`.)
-/

@[expose] public section


open CategoryTheory Limits MonoidalCategory

universe v u w

noncomputable section

namespace CategoryTheory
namespace Mon

variable {J : Type w} [Category* J]
variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

open MonObj

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
We construct the limit object of a functor `F : J ⥤ Mon C` given a limit cone `c` of
`F ⋙ forget C`.
-/
@[simps!]
/--
Definition of `limit` / `limit` 的定义

English:
definition limit
  signature: (F : J ⥤ Mon C) (c : Cone (F ⋙ Mon.forget C)) (hc : IsLimit c)
  body: c.pt
  mon.one := hc.lift
    { pt := _
      π.app X := η[(F.obj X).X] }
  mon.mul := hc.lift
    { pt := _
      π.app X := (c.π.app X otimesₘ c.π.app X) ≫ μ[(F.obj X).X]
      π.naturality i j f := by have := c.π.naturality f; simp_all }
mon.one_mul := hc.hom_ext by simp [whiskerRight_comp_tensorHom_assoc]
mon.mul_one := hc.hom_ext by simp [whiskerLeft_comp_tensorHom_assoc]
  mon.mul_assoc := by
    apply hc.hom_ext
    simp only [Functor.comp_obj, forget_obj, Functor.const_obj_obj, IsLimit.fac,
      mon_tauto, implies_true]

中文:
定义 limit
  签名: (F : J ⥤ 幺半群 C) (c : 锥 (F ⋙ 幺半群.forget C)) (hc : 是极限 c)
  定义体: c.pt
  mon.one := hc.lift
    { pt := _
      π.app X := η[(F.obj X).X] }
  mon.mul := hc.lift
    { pt := _
      π.app X := (c.π.app X otimesₘ c.π.app X) ≫ μ[(F.obj X).X]
      π.naturality i j f := by have := c.π.naturality f; simp_all }
mon.one_mul := hc.hom_ext by simp [whiskerRight_comp_tensorHom_assoc]
mon.mul_one := hc.hom_ext by simp [whiskerLeft_comp_tensorHom_assoc]
  mon.mul_assoc := by
    apply hc.hom_ext
    simp only [Functor.comp_obj, forget_obj, Functor.const_obj_obj, IsLimit.fac,
      mon_tauto, implies_true]

Depends on / 依赖: c.pt
-/
def limit (F : J ⥤ Mon C) (c : Cone (F ⋙ Mon.forget C)) (hc : IsLimit c) :
    Mon C where
  X := c.pt
  mon.one := hc.lift
    { pt := _
      π.app X := η[(F.obj X).X] }
  mon.mul := hc.lift
    { pt := _
      π.app X := (c.π.app X otimesₘ c.π.app X) ≫ μ[(F.obj X).X]
      π.naturality i j f := by have := c.π.naturality f; simp_all }
mon.one_mul := hc.hom_ext by simp [whiskerRight_comp_tensorHom_assoc]
mon.mul_one := hc.hom_ext by simp [whiskerLeft_comp_tensorHom_assoc]
  mon.mul_assoc := by
    apply hc.hom_ext
    simp only [Functor.comp_obj, forget_obj, Functor.const_obj_obj, IsLimit.fac,
      mon_tauto, implies_true]

set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `Mon.hasLimits`: a limiting cone over a functor `F : J ⥤ Mon C`.
-/
@[simps]
/--
Definition of `limitCone` / `limitCone` 的定义

English:
definition limitCone
  signature: (F : J ⥤ Mon C) (c : Cone (F ⋙ Mon.forget C)) (hc : IsLimit c)
  body: limit F c hc
  π.app j := .mk' (c.π.app j)
  π.naturality j j' f := Hom.ext' (c.π.naturality f)

中文:
定义 limitCone
  签名: (F : J ⥤ 幺半群 C) (c : 锥 (F ⋙ 幺半群.forget C)) (hc : 是极限 c)
  定义体: limit F c hc
  π.app j := .mk' (c.π.app j)
  π.naturality j j' f := Hom.ext' (c.π.naturality f)
-/
def limitCone (F : J ⥤ Mon C) (c : Cone (F ⋙ Mon.forget C)) (hc : IsLimit c) : Cone F where
  pt := limit F c hc
  π.app j := .mk' (c.π.app j)
  π.naturality j j' f := Hom.ext' (c.π.naturality f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The image of the proposed limit cone for `F : J ⥤ Mon C` under the forgetful functor
`forget C : Mon C ⥤ C` is isomorphic to the limit cone of `F ⋙ forget C`.
-/
@[simps!]
/--
Definition of `forgetMapConeLimitConeIso` / `forgetMapConeLimitConeIso` 的定义

English:
definition forgetMapConeLimitConeIso
  signature: (F : J ⥤ Mon C) (c : Cone (F ⋙ Mon.forget C)) (hc : IsLimit c)
  body: Cone.ext (Iso.refl _) (by simp)

中文:
定义 forgetMapConeLimitConeIso
  签名: (F : J ⥤ 幺半群 C) (c : 锥 (F ⋙ 幺半群.forget C)) (hc : 是极限 c)
  定义体: Cone.ext (Iso.refl _) (by simp)

Depends on / 依赖: Cone.ext, Iso.refl
-/
def forgetMapConeLimitConeIso (F : J ⥤ Mon C) (c : Cone (F ⋙ Mon.forget C)) (hc : IsLimit c) :
    (forget C).mapCone (limitCone F c hc) ≅ c :=
  Cone.ext (Iso.refl _) (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `Mon.hasLimitsOfShape`:
the proposed cone over a functor `F : J ⥤ Mon C` is a limit cone.
-/
@[simps]
/--
Definition of `limitConeIsLimit` / `limitConeIsLimit` 的定义

English:
definition limitConeIsLimit
  signature: (F : J ⥤ Mon C) (c : Cone (F ⋙ Mon.forget C)) (hc : IsLimit c)
  body: { hom := hc.lift ((Mon.forget C).mapCone s)
isMonHom_hom.mul_hom := hc.hom_ext by simp
isMonHom_hom.one_hom := hc.hom_ext by simp }
  fac s h := by ext; simp
uniq s m w := Hom.ext' hc.hom_ext fun j => by simpa using congr($(w j).hom)

中文:
定义 limitConeIsLimit
  签名: (F : J ⥤ 幺半群 C) (c : 锥 (F ⋙ 幺半群.forget C)) (hc : 是极限 c)
  定义体: { hom := hc.lift ((Mon.forget C).mapCone s)
isMonHom_hom.mul_hom := hc.hom_ext by simp
isMonHom_hom.one_hom := hc.hom_ext by simp }
  fac s h := by ext; simp
uniq s m w := Hom.ext' hc.hom_ext fun j => by simpa using congr($(w j).hom)

Depends on / 依赖: Hom.ext, Mon.forget, forget, hc.hom_ext, hc.lift, hom_ext, isMonHom_hom, isMonHom_hom.mul_hom, isMonHom_hom.one_hom, mapCone, mul_hom, one_hom
-/
def limitConeIsLimit (F : J ⥤ Mon C) (c : Cone (F ⋙ Mon.forget C)) (hc : IsLimit c) :
    IsLimit (limitCone F c hc) where
  lift s :=
    { hom := hc.lift ((Mon.forget C).mapCone s)
isMonHom_hom.mul_hom := hc.hom_ext by simp
isMonHom_hom.one_hom := hc.hom_ext by simp }
  fac s h := by ext; simp
uniq s m w := Hom.ext' hc.hom_ext fun j => by simpa using congr($(w j).hom)

/--
Definition of `limitConeLiftsToLimit` / `limitConeLiftsToLimit` 的定义

English:
definition limitConeLiftsToLimit
  signature: (F : J ⥤ Mon C) (c : Cone (F ⋙ Mon.forget C)) (hc : IsLimit c)
  body: limitCone F c hc
  validLift := forgetMapConeLimitConeIso _ _ _
  makesLimit := limitConeIsLimit _ _ _

中文:
定义 limitConeLiftsToLimit
  签名: (F : J ⥤ 幺半群 C) (c : 锥 (F ⋙ 幺半群.forget C)) (hc : 是极限 c)
  定义体: limitCone F c hc
  validLift := forgetMapConeLimitConeIso _ _ _
  makesLimit := limitConeIsLimit _ _ _

Depends on / 依赖: limitCone
-/
def limitConeLiftsToLimit (F : J ⥤ Mon C) (c : Cone (F ⋙ Mon.forget C)) (hc : IsLimit c) :
    LiftsToLimit F (forget C) c hc where
  liftedCone := limitCone F c hc
  validLift := forgetMapConeLimitConeIso _ _ _
  makesLimit := limitConeIsLimit _ _ _

instance (F : J ⥤ Mon C) : CreatesLimit F (forget C) :=
  createsLimitOfReflectsIso (limitConeLiftsToLimit _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CreatesLimitsOfShape J (forget C)
  body: ⟨inferInstance⟩

中文:
实例 :
  签名: 创造形状极限 J (forget C)
  定义体: ⟨inferInstance⟩
-/
instance : CreatesLimitsOfShape J (forget C) := ⟨inferInstance⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CreatesLimitsOfSize.{w} (forget C)
  body: ⟨inferInstance⟩

中文:
实例 :
  签名: CreatesLimitsOfSize.{w} (forget C)
  定义体: ⟨inferInstance⟩
-/
instance : CreatesLimitsOfSize.{w} (forget C) := ⟨inferInstance⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CreatesLimits (forget C)
  body: ⟨inferInstance⟩

中文:
实例 :
  签名: CreatesLimits (forget C)
  定义体: ⟨inferInstance⟩

Depends on / 依赖: isConservative_pointsBot
-/
instance : CreatesLimits (forget C) := ⟨inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimitsOfShape
  signature: J C] : HasLimitsOfShape J (Mon C)
  body: hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (forget C)

中文:
实例 [有形状极限
  签名: J C] : 有形状极限 J (幺半群 C)
  定义体: hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (forget C)

Depends on / 依赖: forget, hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
-/
instance [HasLimitsOfShape J C] : HasLimitsOfShape J (Mon C) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (forget C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimitsOfShape
  signature: J C] :
  body: CategoryTheory.preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape _

中文:
实例 [有形状极限
  签名: J C] :
  定义体: CategoryTheory.preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape _

Depends on / 依赖: CategoryTheory, CategoryTheory.preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape, preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape
-/
instance [HasLimitsOfShape J C] :
    PreservesLimitsOfShape J (Mon.forget C) :=
  CategoryTheory.preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape _

end Mon
end CategoryTheory
