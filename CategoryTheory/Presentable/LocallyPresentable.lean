/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.CardinalFilteredPresentation

/-!
# Locally presentable and accessible categories

In this file, we define the notion of locally presentable and accessible
categories. We first define these notions for a category `C` relative to a
fixed regular cardinal `κ` (typeclasses `IsCardinalLocallyPresentable C κ`
and `IsCardinalAccessibleCategory C κ`). The existence of such a regular
cardinal `κ` is asserted in the typeclasses `IsLocallyPresentable` and
`IsAccessibleCategory`. We show that in a locally presentable or
accessible category, any object is presentable.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

public section

universe w v u

namespace CategoryTheory

open Limits

section

variable (C : Type u) [Category.{v} C] (κ : Cardinal.{w}) [Fact κ.IsRegular]

/--
Definition of `IsCardinalLocallyPresentable` / `IsCardinalLocallyPresentable` 的定义

English:
class IsCardinalLocallyPresentable
  parameters: : Prop
  extends: HasCardinalFilteredGenerator C κ, HasColimitsOfSize.{w, w} C
  axioms and operations (1):
    - example((κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalLocallyPresentable C κ]) : ObjectProperty.EssentiallySmall.{w} (isCardinalPresentable C κ)  [default: inferInstance]

中文:
类 IsCardinalLocallyPresentable
  参数: : 命题
  继承: HasCardinalFilteredGenerator C κ, HasColimitsOfSize.{w, w} C
  公理与运算 (1 个):
    - example((κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalLocallyPresentable C κ]) : Object命题erty.EssentiallySmall.{w} (isCardinalPresentable C κ)  [默认: inferInstance]
-/
class IsCardinalLocallyPresentable : Prop
  extends HasCardinalFilteredGenerator C κ, HasColimitsOfSize.{w, w} C where

example (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalLocallyPresentable C κ] :
    ObjectProperty.EssentiallySmall.{w} (isCardinalPresentable C κ) := inferInstance

/--
Definition of `IsCardinalAccessibleCategory` / `IsCardinalAccessibleCategory` 的定义

English:
class IsCardinalAccessibleCategory
  parameters: : Prop
  extends: HasCardinalFilteredGenerator C κ, HasCardinalFilteredColimits.{w} C κ
  (no additional axioms)

中文:
类 IsCardinalAccessibleCategory
  参数: : 命题
  继承: HasCardinalFilteredGenerator C κ, HasCardinalFilteredColimits.{w} C κ
  (无附加公理)
-/
class IsCardinalAccessibleCategory : Prop
  extends HasCardinalFilteredGenerator C κ, HasCardinalFilteredColimits.{w} C κ where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCardinalLocallyPresentable
  signature: C κ] : IsCardinalAccessibleCategory C κ where
  body: inferInstance

中文:
实例 [IsCardinalLocallyPresentable
  签名: C κ] : IsCardinalAccessibleCategory C κ where
  定义体: inferInstance
-/
instance [IsCardinalLocallyPresentable C κ] : IsCardinalAccessibleCategory C κ where

example (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalAccessibleCategory C κ] :
    ObjectProperty.EssentiallySmall.{w} (isCardinalPresentable C κ) := inferInstance

section Finite

open Cardinal
attribute [local instance] fact_isRegular_aleph0

/--
Definition of `IsLocallyFinitelyPresentable` / `IsLocallyFinitelyPresentable` 的定义

English:
abbreviation IsLocallyFinitelyPresentable
  body: IsCardinalLocallyPresentable.{w} C ℵ₀

中文:
缩写 IsLocallyFinitelyPresentable
  定义体: IsCardinalLocallyPresentable.{w} C ℵ₀

Depends on / 依赖: IsCardinalLocallyPresentable
-/
abbrev IsLocallyFinitelyPresentable :=
  IsCardinalLocallyPresentable.{w} C ℵ₀

/--
Definition of `IsFinitelyAccessibleCategory` / `IsFinitelyAccessibleCategory` 的定义

English:
abbreviation IsFinitelyAccessibleCategory
  body: IsCardinalAccessibleCategory.{w} C ℵ₀

中文:
缩写 IsFinitelyAccessibleCategory
  定义体: IsCardinalAccessibleCategory.{w} C ℵ₀

Depends on / 依赖: IsCardinalAccessibleCategory
-/
abbrev IsFinitelyAccessibleCategory :=
  IsCardinalAccessibleCategory.{w} C ℵ₀

end Finite

end

section

/-- A category `C` is locally presentable if it is `κ`-locally presentable
for some regular cardinal `κ`. -/
@[pp_with_univ]
/--
Definition of `IsLocallyPresentable` / `IsLocallyPresentable` 的定义

English:
class IsLocallyPresentable
  parameters: (C : Type u) [hC : Category.{v} C]
  axioms and operations (1):
    - exists_cardinal((C) [hC]) : exists (κ : Cardinal.{w}) (_ : Fact κ.IsRegular), IsCardinalLocallyPresentable C κ

中文:
类 IsLocallyPresentable
  参数: (C : 类型u) [hC : Category.{v} C]
  公理与运算 (1 个):
    - exists_cardinal((C) [hC]) : 存在 (κ : Cardinal.{w}) (_ : Fact κ.IsRegular), IsCardinalLocallyPresentable C κ
-/
class IsLocallyPresentable (C : Type u) [hC : Category.{v} C] : Prop where
  exists_cardinal (C) [hC] : exists (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
    IsCardinalLocallyPresentable C κ

/-- A category `C` is accessible if it is `κ`-accessible
for some regular cardinal `κ`. -/
@[pp_with_univ]
/--
Definition of `IsAccessibleCategory` / `IsAccessibleCategory` 的定义

English:
class IsAccessibleCategory
  parameters: (C : Type u) [hC : Category.{v} C]
  axioms and operations (1):
    - exists_cardinal((C) [hC]) : exists (κ : Cardinal.{w}) (_ : Fact κ.IsRegular), IsCardinalAccessibleCategory C κ

中文:
类 IsAccessibleCategory
  参数: (C : 类型u) [hC : Category.{v} C]
  公理与运算 (1 个):
    - exists_cardinal((C) [hC]) : 存在 (κ : Cardinal.{w}) (_ : Fact κ.IsRegular), IsCardinalAccessibleCategory C κ
-/
class IsAccessibleCategory (C : Type u) [hC : Category.{v} C] : Prop where
  exists_cardinal (C) [hC] : exists (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
    IsCardinalAccessibleCategory C κ

variable (C : Type u) [hC : Category.{v} C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsLocallyPresentable.{w}
  signature: C] : IsAccessibleCategory.{w} C where
  body: by
    obtain ⟨κ, hκ, h'⟩ := IsLocallyPresentable.exists_cardinal C
    exact ⟨κ, hκ, inferInstance⟩

中文:
实例 [IsLocallyPresentable.{w}
  签名: C] : IsAccessibleCategory.{w} C where
  定义体: by
    obtain ⟨κ, hκ, h'⟩ := IsLocallyPresentable.exists_cardinal C
    exact ⟨κ, hκ, inferInstance⟩

Depends on / 依赖: IsLocallyPresentable, IsLocallyPresentable.exists_cardinal, exists_cardinal
-/
instance [IsLocallyPresentable.{w} C] : IsAccessibleCategory.{w} C where
  exists_cardinal := by
    obtain ⟨κ, hκ, h'⟩ := IsLocallyPresentable.exists_cardinal C
    exact ⟨κ, hκ, inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsAccessibleCategory.{w}
  signature: C] (X
  body: by
  obtain ⟨κ, _, _⟩ := IsAccessibleCategory.exists_cardinal C
  obtain ⟨_, _, h⟩ := HasCardinalFilteredGenerator.exists_generator C κ
  apply h.presentable

example [IsLocallyPresentable.{w} C] (X : C) : IsPresentable.{w} X := inferInstance

中文:
实例 [IsAccessibleCategory.{w}
  签名: C] (X
  定义体: by
  obtain ⟨κ, _, _⟩ := IsAccessibleCategory.exists_cardinal C
  obtain ⟨_, _, h⟩ := HasCardinalFilteredGenerator.exists_generator C κ
  apply h.presentable

example [IsLocallyPresentable.{w} C] (X : C) : IsPresentable.{w} X := inferInstance

Depends on / 依赖: HasCardinalFilteredGenerator, HasCardinalFilteredGenerator.exists_generator, IsAccessibleCategory, IsAccessibleCategory.exists_cardinal, exists_cardinal, exists_generator, h.presentable, presentable
-/
instance [IsAccessibleCategory.{w} C] (X : C) : IsPresentable.{w} X := by
  obtain ⟨κ, _, _⟩ := IsAccessibleCategory.exists_cardinal C
  obtain ⟨_, _, h⟩ := HasCardinalFilteredGenerator.exists_generator C κ
  apply h.presentable

example [IsLocallyPresentable.{w} C] (X : C) : IsPresentable.{w} X := inferInstance

end

end CategoryTheory
