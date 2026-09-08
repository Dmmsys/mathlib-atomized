/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-!
# Simplicial categories

A simplicial category is a category `C` that is enriched over the
category of simplicial sets in such a way that morphisms in
`C` identify to the `0`-simplices of the enriched hom.

## TODO

* construct a simplicial category structure on simplicial objects, so
  that it applies in particular to simplicial sets
* obtain the adjunction property `(K ⊗ X ⟶ Y) ≃ (K ⟶ sHom X Y)` when `K`, `X`, and `Y`
  are simplicial sets
* develop the notion of "simplicial tensor" `K ⊗ₛ X : C` with `K : SSet` and `X : C`
  an object in a simplicial category `C`
* define the notion of path between `0`-simplices of simplicial sets
* deduce the notion of homotopy between morphisms in a simplicial category
* obtain that homotopies in simplicial categories can be interpreted as given
  by morphisms `Δ[1] ⊗ X ⟶ Y`.

## References
* [Daniel G. Quillen, *Homotopical algebra*, II §1][quillen-1967]

-/

@[expose] public section

universe v u

open CategoryTheory Category Simplicial MonoidalCategory

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- A simplicial category is a category `C` that is enriched over the
category of simplicial sets in such a way that morphisms in
`C` identify to the `0`-simplices of the enriched hom. -/
/-
**CategoryTheory.SimplicialCategory** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`
。
形式化陈述：SimplicialCategory
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simplicial category is a category `C` that is enriched over the
category of simplicial sets in such a way that morphisms in
`C` identify to the `0`-simplices of the enriched hom.
-/
abbrev SimplicialCategory := EnrichedOrdinaryCategory SSet.{v} C

namespace SimplicialCategory

variable [SimplicialCategory C]

variable {C}

/-- Abbreviation for the enriched hom of a simplicial category. -/
/-
**CategoryTheory.SimplicialCategory.sHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.SimplicialCategory`。
形式化陈述：sHom (K L : C) : SSet.{v}
参数：K L : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Abbreviation for the enriched hom of a simplicial category.
-/
abbrev sHom (K L : C) : SSet.{v} := K ⟶[SSet] L

/-- Abbreviation for the enriched composition in a simplicial category. -/
/-
**CategoryTheory.SimplicialCategory.sHomComp** 是 Mathlib 中的一个缩写定义，位于命名空间 `Catego
ryTheory.SimplicialCategory`。
形式化陈述：sHomComp (K L M : C) : sHom K L otimes sHom L M ⟶ sHom K M
参数：K L M : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Abbreviation for the enriched composition in a simplicial category.
-/
abbrev sHomComp (K L M : C) : sHom K L ⊗ sHom L M ⟶ sHom K M := eComp SSet K L M

/-- The bijection `(K ⟶ L) ≃ sHom K L _⦋0⦌` for all objects `K` and `L`
in a simplicial category. -/
/-
**CategoryTheory.SimplicialCategory.homEquiv'** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.SimplicialCategory`。
形式化陈述：homEquiv' (K L : C) : (K ⟶ L) ≃ sHom K L _⦋0⦌
参数：K L : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The bijection `(K ⟶ L) ≃ sHom K L _⦋0⦌` for all objects `K` and `L`
in a simplicial category.
-/
def homEquiv' (K L : C) : (K ⟶ L) ≃ sHom K L _⦋0⦌ :=
  (eHomEquiv SSet).trans (sHom K L).unitHomEquiv

variable (C) in
/-- The bifunctor `Cᵒᵖ ⥤ C ⥤ SSet.{v}` which sends `K : Cᵒᵖ` and `L : C` to `sHom K.unop L`. -/
/-
**CategoryTheory.SimplicialCategory.sHomFunctor** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cat
egoryTheory.SimplicialCategory`。
形式化陈述：sHomFunctor : Cᵒᵖ ⥤ C ⥤ SSet.{v}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bifunctor `Cᵒᵖ ⥤ C ⥤ SSet.{v}` which sends `K : Cᵒᵖ` and `L : C` to `sHom K.
unop L`.
-/
noncomputable abbrev sHomFunctor : Cᵒᵖ ⥤ C ⥤ SSet.{v} := eHomFunctor _ _

end SimplicialCategory

end CategoryTheory

