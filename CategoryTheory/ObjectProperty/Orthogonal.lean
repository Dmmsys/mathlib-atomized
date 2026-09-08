/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

/-!
# Orthogonal of a property of objects

Let `P` be a property of objects in a category with zero morphisms.
We define `P.rightOrthogonal` as the property of objects `Y` such that
any map `f : X ⟶ Y` vanishes when `P X` holds. Similarly, we define
`P.leftOrthogonal` as the property of objects `X` such that
any map `f : X ⟶ Y` vanishes when `P Y` holds.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits ZeroObject

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

namespace ObjectProperty

variable (P : ObjectProperty C)

/-- In a category with zero morphisms, the right orthogonal of a property of objects `P`
is the property of objects `Y` such that any map `X ⟶ Y` vanishes when `P X` holds. -/
@[stacks 0FXB]
/-
**CategoryTheory.ObjectProperty.rightOrthogonal** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.ObjectProperty`。
形式化陈述：rightOrthogonal : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a category with zero morphisms, the right orthogonal of a property of objects
 `P`
is the property of objects `Y` such that any map `X ⟶ Y` vanishes when `P X` hol
ds.
-/
def rightOrthogonal : ObjectProperty C :=
  fun Y ↦ ∀ ⦃X : C⦄ (f : X ⟶ Y), P X → f = 0
/-
**CategoryTheory.ObjectProperty.rightOrthogonal_iff** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ObjectProperty`。
形式化陈述：rightOrthogonal_iff (Y : C) : P.rightOrthogonal Y ↔ forall ⦃X : C⦄ (f : X 
⟶ Y), P X -> f = 0
参数：Y : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma rightOrthogonal_iff (Y : C) :
    P.rightOrthogonal Y ↔ ∀ ⦃X : C⦄ (f : X ⟶ Y), P X → f = 0 := Iff.rfl

/-- In a category with zero morphisms, the left orthogonal of a property of objects `P`
is the property of objects `X` such that any map `X ⟶ Y` vanishes when `P Y` holds. -/
@[stacks 0FXB]
/-
**CategoryTheory.ObjectProperty.leftOrthogonal** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.ObjectProperty`。
形式化陈述：leftOrthogonal : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a category with zero morphisms, the left orthogonal of a property of objects 
`P`
is the property of objects `X` such that any map `X ⟶ Y` vanishes when `P Y` hol
ds.
-/
def leftOrthogonal : ObjectProperty C :=
  fun X ↦ ∀ ⦃Y : C⦄ (f : X ⟶ Y), P Y → f = 0
/-
**CategoryTheory.ObjectProperty.leftOrthogonal_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ObjectProperty`。
形式化陈述：leftOrthogonal_iff (X : C) : P.leftOrthogonal X ↔ forall ⦃Y : C⦄ (f : X ⟶ 
Y), P Y -> f = 0
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma leftOrthogonal_iff (X : C) :
    P.leftOrthogonal X ↔ ∀ ⦃Y : C⦄ (f : X ⟶ Y), P Y → f = 0 := Iff.rfl
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.rightOrthogonal.IsClosedUnderIsomorphisms where
  of_iso e h X f hX := by
    rw [← cancel_mono e.inv, zero_comp]
    exact h _ hX
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.leftOrthogonal.IsClosedUnderIsomorphisms where
  of_iso e h Y f hY := by
    rw [← cancel_epi e.hom, comp_zero]
    exact h _ hY
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroObject C] : P.rightOrthogonal.ContainsZero where
  exists_zero := ⟨0, isZero_zero _, fun _ _ _ ↦ by ext⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroObject C] : P.leftOrthogonal.ContainsZero where
  exists_zero := ⟨0, isZero_zero _, fun _ _ _ ↦ by ext⟩

end ObjectProperty

end CategoryTheory

