/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Serre classes

For any abelian category `C`, we introduce a type class `IsSerreClass C` for
Serre classes in `C` (also known as "Serre subcategories"). A Serre class is
a property `P : ObjectProperty C` of objects in `C` which holds for a zero object,
and is closed under subobjects, quotients and extensions.

## Future work

* Show that the localization of `C` with respect to a Serre class is an abelian category.

## References

* [Jean-Pierre Serre, *Groupes d'homotopie et classes de groupes abéliens*][serre1958]

-/

public section

universe v v' u u'

namespace CategoryTheory

open Limits ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C] (P : ObjectProperty C)
  {D : Type u'} [Category.{v'} D] [Abelian D]

namespace ObjectProperty

/-- A Serre class in an abelian category consists of a predicate which
holds for the zero object and is closed under subobjects, quotients, extensions. -/
/-
**CategoryTheory.ObjectProperty.IsSerreClass** 是 Mathlib 中的一个类，位于命名空间 `CategoryT
heory.ObjectProperty`。
形式化陈述：IsSerreClass : Prop extends P.ContainsZero, P.IsClosedUnderSubobjects, P.I
sClosedUnderQuotients, P.IsClosedUnderExtensions where  variable [P.IsSerreClass
]  example : P.IsClosedUnderIsomorphisms
继承自：P.ContainsZero, P.IsClosedUnderSubobjects, P.IsClosedUnderQuotients, P.IsClo
sedUnderExtensions。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Serre class in an abelian category consists of a predicate which
holds for the zero object and is closed under subobjects, quotients, extensions.
-/
class IsSerreClass : Prop extends P.ContainsZero,
    P.IsClosedUnderSubobjects, P.IsClosedUnderQuotients,
    P.IsClosedUnderExtensions where

variable [P.IsSerreClass]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : P.IsClosedUnderIsomorphisms := inferInstance
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (⊤ : ObjectProperty C).IsSerreClass where
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSerreClass (IsZero (C := C)) where
/-
**CategoryTheory.ObjectProperty.prop_iff_of_shortExact** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ObjectProperty`。
形式化陈述：prop_iff_of_shortExact {S : ShortComplex C} (hS : S.ShortExact) : P S.X₂ ↔
 P S.X₁ ∧ P S.X₃
参数：hS : S.ShortExact。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_X₁_of_shortExact`：prop_X₁_of_shortExa
ct [HasZeroMorphisms C] {S : ShortComplex C} (hS : S.ShortExact) (h₂ : P S.X₂) :
 P S.X₁
· 使用定理 `CategoryTheory.ObjectProperty.IsSerreClass.toIsClosedUnderSubobjects`：∀ 
{C : Type u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.
Abelian C}   {P : CategoryTheory.ObjectProperty C} [self :…
· 使用引理 `CategoryTheory.ObjectProperty.prop_X₃_of_shortExact`：prop_X₃_of_shortExa
ct [HasZeroMorphisms C] {S : ShortComplex C} (hS : S.ShortExact) (h₂ : P S.X₂) :
 P S.X₃
· 使用定理 `CategoryTheory.ObjectProperty.IsSerreClass.toIsClosedUnderQuotients`：∀ {
C : Type u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.A
belian C}   {P : CategoryTheory.ObjectProperty C} [self :…
· 使用引理 `CategoryTheory.ObjectProperty.prop_X₂_of_shortExact`：prop_X₂_of_shortExa
ct [P.IsClosedUnderExtensions] {S : ShortComplex C} (hS : S.ShortExact) (h₁ : P 
S.X₁) (h₃ : P S.X₃) : P S.X₂
· 使用定理 `CategoryTheory.ObjectProperty.IsSerreClass.toIsClosedUnderExtensions`：∀ 
{C : Type u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.
Abelian C}   {P : CategoryTheory.ObjectProperty C} [self :…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma prop_iff_of_shortExact {S : ShortComplex C} (hS : S.ShortExact) :
    P S.X₂ ↔ P S.X₁ ∧ P S.X₃ :=
  ⟨fun h ↦ ⟨P.prop_X₁_of_shortExact hS h, P.prop_X₃_of_shortExact hS h⟩,
    fun h ↦ P.prop_X₂_of_shortExact hS h.1 h.2⟩
/-
**CategoryTheory.ObjectProperty.prop_X** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.ObjectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prop_X₂_of_exact {S : ShortComplex C} (hS : S.Exact)
    (h₁ : P S.X₁) (h₃ : P S.X₃) : P S.X₂ := by
  let d := S.homologyData
  have := hS.epi_f' d.left
  have := hS.mono_g' d.right
  exact (P.prop_X₂_of_shortExact (hS.shortExact d)
    (P.prop_of_epi d.left.f' h₁) (P.prop_of_mono d.right.g' h₃) :)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : D ⥤ C) [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] :
    (P.inverseImage F).IsSerreClass where

end ObjectProperty

end CategoryTheory

