/-
Copyright (c) 2024 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Compactness.DeltaGeneratedSpace
public import Mathlib.Topology.Convenient.Category

/-!
# Delta-generated topological spaces

This file defines the category `DeltaGenerated` of delta-generated spaces.
This is a particular case of the construction in the file
`Mathlib/Topology/Convenient/Category.Lean`: this is the category of
`X`-generated spaces where `X` is the family of spaces `Fin n → ℝ`
for all `n : ℕ`.

## TODO
* `DeltaGenerated` is Cartesian closed (@joelriou).

## References
* https://ncatlab.org/nlab/show/Delta-generated+topological+space

-/

@[expose] public section

universe u

open CategoryTheory

/-- The category of delta-generated topological spaces. -/
/-
**DeltaGenerated** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：DeltaGenerated
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of delta-generated topological spaces.
-/
abbrev DeltaGenerated := GeneratedByTopCat.{u} (fun n ↦ Fin n → ℝ)

/-- The faithful (but not full) functor taking each topological space to its delta-generated
  coreflection. -/
/-
**TopCat.toDeltaGenerated** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：TopCat.toDeltaGenerated : TopCat.{u} ⥤ DeltaGenerated.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The faithful (but not full) functor taking each topological space to its delta-g
enerated
  coreflection.
-/
abbrev TopCat.toDeltaGenerated : TopCat.{u} ⥤ DeltaGenerated.{u} :=
  TopCat.toGeneratedByTopCat

namespace DeltaGenerated

/-- Constructor for objects of the category `DeltaGenerated` -/
/-
**DeltaGenerated.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `DeltaGenerated`。
形式化陈述：of (X : Type u) [TopologicalSpace X] [DeltaGeneratedSpace X] : DeltaGenera
ted.{u}
参数：X : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for objects of the category `DeltaGenerated`
-/
abbrev of (X : Type u) [TopologicalSpace X] [DeltaGeneratedSpace X] : DeltaGenerated.{u} :=
  GeneratedByTopCat.of X

/-- The forgetful functor `DeltaGenerated ⥤ TopCat` -/
/-
**DeltaGenerated.deltaGeneratedToTop** 是 Mathlib 中的一个缩写定义，位于命名空间 `DeltaGenerated
`。
形式化陈述：deltaGeneratedToTop : DeltaGenerated.{u} ⥤ TopCat.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor `DeltaGenerated ⥤ TopCat`
-/
abbrev deltaGeneratedToTop : DeltaGenerated.{u} ⥤ TopCat.{u} :=
  GeneratedByTopCat.toTopCat

/-- `deltaGeneratedToTop` is fully faithful. -/
/-
**DeltaGenerated.fullyFaithfulDeltaGeneratedToTop** 是 Mathlib 中的一个缩写定义，位于命名空间 `D
eltaGenerated`。
形式化陈述：fullyFaithfulDeltaGeneratedToTop : deltaGeneratedToTop.{u}.FullyFaithful
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`deltaGeneratedToTop` is fully faithful.
-/
abbrev fullyFaithfulDeltaGeneratedToTop : deltaGeneratedToTop.{u}.FullyFaithful :=
  GeneratedByTopCat.fullyFaithfulToTopCat _

@[deprecated (since := "2026-04-23")] alias topToDeltaGenerated := TopCat.toDeltaGenerated

/-- The adjunction between the forgetful functor `DeltaGenerated ⥤ TopCat` and its coreflector. -/
/-
**DeltaGenerated.coreflectorAdjunction** 是 Mathlib 中的一个缩写定义，位于命名空间 `DeltaGenerat
ed`。
形式化陈述：coreflectorAdjunction : deltaGeneratedToTop ⊣ TopCat.toDeltaGenerated
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction between the forgetful functor `DeltaGenerated ⥤ TopCat` and its c
oreflector.
-/
abbrev coreflectorAdjunction : deltaGeneratedToTop ⊣ TopCat.toDeltaGenerated :=
  GeneratedByTopCat.adj

end DeltaGenerated

