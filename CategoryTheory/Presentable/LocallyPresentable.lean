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

/-- Given a regular cardinal `κ`, a category `C` is `κ`-locally presentable
if it is cocomplete and admits a (small) family `G : ι → C` of `κ`-presentable
objects such that any object identifies as a `κ`-filtered colimit of these objects. -/
/-
**CategoryTheory.IsCardinalLocallyPresentable** 是 Mathlib 中的一个类，位于命名空间 `Category
Theory`。
形式化陈述：IsCardinalLocallyPresentable : Prop extends HasCardinalFilteredGenerator C
 κ, HasColimitsOfSize.{w, w} C where  example (κ : Cardinal.{w}) [Fact κ.IsRegul
ar] [IsCardinalLocallyPresentable C κ] : ObjectProperty.EssentiallySmall.{w} (is
CardinalPresentable C κ)
继承自：HasCardinalFilteredGenerator C κ, HasColimitsOfSize.{w, w} C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a regular cardinal `κ`, a category `C` is `κ`-locally presentable
if it is cocomplete and admits a (small) family `G : ι → C` of `κ`-presentable
objects such that any object identifies as a `κ`-filtered colimit of these objec
ts.
-/
class IsCardinalLocallyPresentable : Prop
  extends HasCardinalFilteredGenerator C κ, HasColimitsOfSize.{w, w} C where
/-
**CategoryTheory.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalLocallyPresentable C κ] :
    ObjectProperty.EssentiallySmall.{w} (isCardinalPresentable C κ) := inferInstance

/-- Given a regular cardinal `κ`, a category `C` is `κ`-accessible
if it has `κ`-filtered colimits and admits a (small) family `G : ι → C` of `κ`-presentable
objects such that any object identifies as a `κ`-filtered colimit of these objects. -/
/-
**CategoryTheory.IsCardinalAccessibleCategory** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categ
oryTheory`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → (κ : Cardinal.{w}) → [
Fact κ.IsRegular] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a regular cardinal `κ`, a category `C` is `κ`-accessible
if it has `κ`-filtered colimits and admits a (small) family `G : ι → C` of `κ`-p
resentable
objects such that any object identifies as a `κ`-filtered colimit of these objec
ts.
-/
class IsCardinalAccessibleCategory : Prop
  extends HasCardinalFilteredGenerator C κ, HasCardinalFilteredColimits.{w} C κ where
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCardinalLocallyPresentable C κ] : IsCardinalAccessibleCategory C κ where
/-
**CategoryTheory.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalAccessibleCategory C κ] :
    ObjectProperty.EssentiallySmall.{w} (isCardinalPresentable C κ) := inferInstance

section Finite

open Cardinal
attribute [local instance] fact_isRegular_aleph0

/-- A category is locally finitely presentable if it is locally `ℵ₀`-presentable. -/
/-
**CategoryTheory.IsLocallyFinitelyPresentable** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory`。
形式化陈述：IsLocallyFinitelyPresentable
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.fact_isRegular_aleph0`：fact_isRegular_aleph0 : Fact (IsRegular 
ℵ₀) where out

--- 原说明 ---
A category is locally finitely presentable if it is locally `ℵ₀`-presentable.
-/
abbrev IsLocallyFinitelyPresentable :=
  IsCardinalLocallyPresentable.{w} C ℵ₀

/-- A category is finitely accessible if it is `ℵ₀`-accessible. -/
/-
**CategoryTheory.IsFinitelyAccessibleCategory** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory`。
形式化陈述：IsFinitelyAccessibleCategory
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.fact_isRegular_aleph0`：fact_isRegular_aleph0 : Fact (IsRegular 
ℵ₀) where out

--- 原说明 ---
A category is finitely accessible if it is `ℵ₀`-accessible.
-/
abbrev IsFinitelyAccessibleCategory :=
  IsCardinalAccessibleCategory.{w} C ℵ₀

end Finite

end

section

/-- A category `C` is locally presentable if it is `κ`-locally presentable
for some regular cardinal `κ`. -/
@[pp_with_univ]
/-
**CategoryTheory.IsLocallyPresentable** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheor
y`。
形式化陈述：(C : Type u) → [hC : CategoryTheory.Category.{v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `C` is locally presentable if it is `κ`-locally presentable
for some regular cardinal `κ`.
-/
class IsLocallyPresentable (C : Type u) [hC : Category.{v} C] : Prop where
  exists_cardinal (C) [hC] : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
    IsCardinalLocallyPresentable C κ

/-- A category `C` is accessible if it is `κ`-accessible
for some regular cardinal `κ`. -/
@[pp_with_univ]
/-
**CategoryTheory.IsAccessibleCategory** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheor
y`。
形式化陈述：(C : Type u) → [hC : CategoryTheory.Category.{v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `C` is accessible if it is `κ`-accessible
for some regular cardinal `κ`.
-/
class IsAccessibleCategory (C : Type u) [hC : Category.{v} C] : Prop where
  exists_cardinal (C) [hC] : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
    IsCardinalAccessibleCategory C κ

variable (C : Type u) [hC : Category.{v} C]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsLocallyPresentable.{w} C] : IsAccessibleCategory.{w} C where
  exists_cardinal := by
    obtain ⟨κ, hκ, h'⟩ := IsLocallyPresentable.exists_cardinal C
    exact ⟨κ, hκ, inferInstance⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsAccessibleCategory.{w} C] (X : C) : IsPresentable.{w} X := by
  obtain ⟨κ, _, _⟩ := IsAccessibleCategory.exists_cardinal C
  obtain ⟨_, _, h⟩ := HasCardinalFilteredGenerator.exists_generator C κ
  apply h.presentable
/-
**CategoryTheory.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [IsLocallyPresentable.{w} C] (X : C) : IsPresentable.{w} X := inferInstance

end

end CategoryTheory

