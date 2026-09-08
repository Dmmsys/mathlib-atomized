/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Properties of objects that are closed under subobjects and quotients

Given a category `C` and `P : ObjectProperty C`, we define type classes
`P.IsClosedUnderSubobjects` and `P.IsClosedUnderQuotients` expressing
that `P` is closed under subobjects (resp. quotients).

-/

public section

universe v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace ObjectProperty

variable (P : ObjectProperty C)

/-- Given `P : ObjectProperty C`, we say that `P` is closed under subobjects,
if for any monomorphism `X ⟶ Y`, `P Y` implies `P X`. -/
/-
**CategoryTheory.ObjectProperty.IsClosedUnderSubobjects** 是 Mathlib 中的一个归纳类型，位于命
名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
ObjectProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `P : ObjectProperty C`, we say that `P` is closed under subobjects,
if for any monomorphism `X ⟶ Y`, `P Y` implies `P X`.
-/
class IsClosedUnderSubobjects : Prop where
  prop_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (hY : P Y) : P X

section

variable [P.IsClosedUnderSubobjects]

/-
**CategoryTheory.ObjectProperty.prop_of_mono** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ObjectProperty`。
形式化陈述：prop_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (hY : P Y) : P X
参数：f : X ⟶ Y；hY : P Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsClosedUnderSubobjects.prop_of_mono`：∀ {C
 : Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.ObjectP
roperty C}   [self : P.IsClosedUnderSubobjects] {X Y : C…
-/
lemma prop_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (hY : P Y) : P X :=
  IsClosedUnderSubobjects.prop_of_mono f hY
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.IsClosedUnderIsomorphisms where
  of_iso e := P.prop_of_mono e.inv
/-
**CategoryTheory.ObjectProperty.prop_X** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.ObjectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prop_X₁_of_shortExact [HasZeroMorphisms C] {S : ShortComplex C} (hS : S.ShortExact)
    (h₂ : P S.X₂) : P S.X₁ := by
  have := hS.mono_f
  exact P.prop_of_mono S.f h₂
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : D ⥤ C) [F.PreservesMonomorphisms] :
    (P.inverseImage F).IsClosedUnderSubobjects where
  prop_of_mono f _ h := P.prop_of_mono (F.map f) h

end

section

/-- Given `P : ObjectProperty C`, we say that `P` is closed under quotients,
if for any epimorphism `X ⟶ Y`, `P X` implies `P Y`. -/
/-
**CategoryTheory.ObjectProperty.IsClosedUnderQuotients** 是 Mathlib 中的一个归纳类型，位于命名
空间 `CategoryTheory.ObjectProperty`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
ObjectProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `P : ObjectProperty C`, we say that `P` is closed under quotients,
if for any epimorphism `X ⟶ Y`, `P X` implies `P Y`.
-/
class IsClosedUnderQuotients : Prop where
  prop_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (hX : P X) : P Y

variable [P.IsClosedUnderQuotients]
/-
**CategoryTheory.ObjectProperty.prop_of_epi** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ObjectProperty`。
形式化陈述：prop_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (hX : P X) : P Y
参数：f : X ⟶ Y；hX : P X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsClosedUnderQuotients.prop_of_epi`：∀ {C :
 Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.ObjectPro
perty C}   [self : P.IsClosedUnderQuotients] {X Y : C}…
-/
lemma prop_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (hX : P X) : P Y :=
  IsClosedUnderQuotients.prop_of_epi f hX
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.IsClosedUnderIsomorphisms where
  of_iso e := P.prop_of_epi e.hom
/-
**CategoryTheory.ObjectProperty.prop_X** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.ObjectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prop_X₃_of_shortExact [HasZeroMorphisms C] {S : ShortComplex C} (hS : S.ShortExact)
    (h₂ : P S.X₂) : P S.X₃ := by
  have := hS.epi_g
  exact P.prop_of_epi S.g h₂
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : D ⥤ C) [F.PreservesEpimorphisms] :
    (P.inverseImage F).IsClosedUnderQuotients where
  prop_of_epi f _ h := P.prop_of_epi (F.map f) h

end

/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (⊤ : ObjectProperty C).IsClosedUnderSubobjects where
  prop_of_mono := by simp
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (⊤ : ObjectProperty C).IsClosedUnderQuotients where
  prop_of_epi := by simp
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroMorphisms C] : IsClosedUnderSubobjects (IsZero (C := C)) where
  prop_of_mono f _ hX := IsZero.of_mono f hX
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroMorphisms C] : IsClosedUnderQuotients (IsZero (C := C)) where
  prop_of_epi f _ hX := IsZero.of_epi f hX

end ObjectProperty

end CategoryTheory

