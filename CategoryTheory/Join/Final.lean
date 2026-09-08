/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Join.Basic
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.IsConnected

/-!
# (Co)Finality of the inclusions in joins of categories

This file records the fact that `inclLeft C D : C ⥤ C ⋆ D` is initial if `C` is connected.
Dually, `inclRight : C ⥤ C ⋆ D` is final if `D` is connected.

-/

@[expose] public section

namespace CategoryTheory.Join

variable (C D : Type*) [Category* C] [Category* D]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The category of `Join.inclLeft C D`-costructured arrows with target `right d` is equivalent to
`C`. -/
/-
**CategoryTheory.Join.costructuredArrowEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Join`。
形式化陈述：costructuredArrowEquiv (d : D) : CostructuredArrow (inclLeft C D) (right d
) ≌ C where functor
参数：d : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of `Join.inclLeft C D`-costructured arrows with target `right d` is
 equivalent to
`C`.
-/
def costructuredArrowEquiv (d : D) : CostructuredArrow (inclLeft C D) (right d) ≌ C where
  functor := CostructuredArrow.proj (inclLeft C D) (right d)
  inverse :=
    { obj c := .mk (edge c d)
      map f := CostructuredArrow.homMk f }
  unitIso := NatIso.ofComponents (fun _ ↦ CostructuredArrow.isoMk (Iso.refl _))
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The category of `Join.inclRight C D`-structured arrows with source `left c` is equivalent to
`D`. -/
/-
**CategoryTheory.Join.structuredArrowEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Join`。
形式化陈述：structuredArrowEquiv (c : C) : StructuredArrow (left c) (inclRight C D) ≌ 
D where functor
参数：c : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of `Join.inclRight C D`-structured arrows with source `left c` is e
quivalent to
`D`.
-/
def structuredArrowEquiv (c : C) : StructuredArrow (left c) (inclRight C D) ≌ D where
  functor := StructuredArrow.proj (left c) (inclRight C D)
  inverse :=
    { obj d := .mk (edge c d)
      map f := StructuredArrow.homMk f }
  unitIso := NatIso.ofComponents (fun _ ↦ StructuredArrow.isoMk (Iso.refl _))
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
/-
**CategoryTheory.Join.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Join`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsConnected C] : (inclLeft C D).Initial where
  out x := match x with
    | .left _ => isConnected_of_isTerminal _ CostructuredArrow.mkIdTerminal
    | .right d => isConnected_of_equivalent (costructuredArrowEquiv C D d).symm
/-
**CategoryTheory.Join.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Join`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsConnected D] : (inclRight C D).Final where
  out x := match x with
    | .left c => isConnected_of_equivalent (structuredArrowEquiv C D c).symm
    | .right _ => isConnected_of_isInitial _ (StructuredArrow.mkIdInitial (T := inclRight C D))

end CategoryTheory.Join

