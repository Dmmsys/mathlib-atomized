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
/-
**CategoryTheory.Mon.limit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mon`。
形式化陈述：limit (F : J ⥤ Mon C) (c : Cone (F ⋙ Mon.forget C)) (hc : IsLimit c) : Mon
 C where X
参数：F : J ⥤ Mon C；c : Cone (F ⋙ Mon.forget C)；hc : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We construct the limit object of a functor `F : J ⥤ Mon C` given a limit cone `c
` of
`F ⋙ forget C`.
-/
def limit (F : J ⥤ Mon C) (c : Cone (F ⋙ Mon.forget C)) (hc : IsLimit c) :
    Mon C where
  X := c.pt
  mon.one := hc.lift
    { pt := _
      π.app X := η[(F.obj X).X] }
  mon.mul := hc.lift
    { pt := _
      π.app X := (c.π.app X ⊗ₘ c.π.app X) ≫ μ[(F.obj X).X]
      π.naturality i j f := by have := c.π.naturality f; simp_all }
  mon.one_mul := hc.hom_ext <| by simp [whiskerRight_comp_tensorHom_assoc]
  mon.mul_one := hc.hom_ext <| by simp [whiskerLeft_comp_tensorHom_assoc]
  mon.mul_assoc := by
    apply hc.hom_ext
    simp only [Functor.comp_obj, forget_obj, Functor.const_obj_obj, IsLimit.fac,
      mon_tauto, implies_true]

set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `Mon.hasLimits`: a limiting cone over a functor `F : J ⥤ Mon C`.
-/
@[simps]
/-
**CategoryTheory.Mon.limitCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mon`。
形式化陈述：limitCone (F : J ⥤ Mon C) (c : Cone (F ⋙ Mon.forget C)) (hc : IsLimit c) :
 Cone F where pt
参数：F : J ⥤ Mon C；c : Cone (F ⋙ Mon.forget C)；hc : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation of `Mon.hasLimits`: a limiting cone over a functor `F : J ⥤ Mon C
`.
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
/-
**CategoryTheory.Mon.forgetMapConeLimitConeIso** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Mon`。
形式化陈述：forgetMapConeLimitConeIso (F : J ⥤ Mon C) (c : Cone (F ⋙ Mon.forget C)) (h
c : IsLimit c) : (forget C).mapCone (limitCone F c hc) ≅ c
参数：F : J ⥤ Mon C；c : Cone (F ⋙ Mon.forget C)；hc : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of the proposed limit cone for `F : J ⥤ Mon C` under the forgetful fun
ctor
`forget C : Mon C ⥤ C` is isomorphic to the limit cone of `F ⋙ forget C`.
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
/-
**CategoryTheory.Mon.limitConeIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Mon`。
形式化陈述：limitConeIsLimit (F : J ⥤ Mon C) (c : Cone (F ⋙ Mon.forget C)) (hc : IsLim
it c) : IsLimit (limitCone F c hc) where lift s
参数：F : J ⥤ Mon C；c : Cone (F ⋙ Mon.forget C)；hc : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation of `Mon.hasLimitsOfShape`:
the proposed cone over a functor `F : J ⥤ Mon C` is a limit cone.
-/
def limitConeIsLimit (F : J ⥤ Mon C) (c : Cone (F ⋙ Mon.forget C)) (hc : IsLimit c) :
    IsLimit (limitCone F c hc) where
  lift s :=
    { hom := hc.lift ((Mon.forget C).mapCone s)
      isMonHom_hom.mul_hom := hc.hom_ext <| by simp
      isMonHom_hom.one_hom := hc.hom_ext <| by simp }
  fac s h := by ext; simp
  uniq s m w := Hom.ext' <| hc.hom_ext fun j ↦ by simpa using congr($(w j).hom)

/--
A helper definition to show that the forgetful functor `forget C : Mon C ⥤ C` creates limits:
given a limit cone `c` of `F ⋙ forget C`, we can lift it to a limit cone of `F`.
-/
/-
**CategoryTheory.Mon.limitConeLiftsToLimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Mon`。
形式化陈述：limitConeLiftsToLimit (F : J ⥤ Mon C) (c : Cone (F ⋙ Mon.forget C)) (hc : 
IsLimit c) : LiftsToLimit F (forget C) c hc where liftedCone
参数：F : J ⥤ Mon C；c : Cone (F ⋙ Mon.forget C)；hc : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A helper definition to show that the forgetful functor `forget C : Mon C ⥤ C` cr
eates limits:
given a limit cone `c` of `F ⋙ forget C`, we can lift it to a limit cone of `F`.
-/
def limitConeLiftsToLimit (F : J ⥤ Mon C) (c : Cone (F ⋙ Mon.forget C)) (hc : IsLimit c) :
    LiftsToLimit F (forget C) c hc where
  liftedCone := limitCone F c hc
  validLift := forgetMapConeLimitConeIso _ _ _
  makesLimit := limitConeIsLimit _ _ _
/-
**CategoryTheory.Mon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : J ⥤ Mon C) : CreatesLimit F (forget C) :=
  createsLimitOfReflectsIso (limitConeLiftsToLimit _)
/-
**CategoryTheory.Mon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CreatesLimitsOfShape J (forget C) := ⟨inferInstance⟩
/-
**CategoryTheory.Mon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CreatesLimitsOfSize.{w} (forget C) := ⟨inferInstance⟩
/-
**CategoryTheory.Mon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CreatesLimits (forget C) := ⟨inferInstance⟩
/-
**CategoryTheory.Mon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasLimitsOfShape J C] : HasLimitsOfShape J (Mon C) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (forget C)
/-
**CategoryTheory.Mon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasLimitsOfShape J C] :
    PreservesLimitsOfShape J (Mon.forget C) :=
  CategoryTheory.preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape _

end Mon
end CategoryTheory

