/-
Copyright (c) 2025 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl
-/
module

public import Mathlib.CategoryTheory.Bicategory.CatEnriched
public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialCategory.SimplicialObject
public import Mathlib.AlgebraicTopology.SimplicialSet.HoFunctorMonoidal

/-!
# The strict bicategory of quasicategories

In this file we define a strict bicategory `QCat.strictBicategory` whose objects
are quasicategories.

This strict category is defined from `QCat.catEnrichedOrdinaryCategory` which is
the `Cat`-enriched ordinary category of quasicategories whose hom-categories are the
homotopy categories of the simplicial internal homs, defined by
applying `hoFunctor : SSet ⥤ Cat`.

As an enriched ordinary category, there is an equivalence `QCat.forgetEnrichment.equiv`
between the underlying category and the full subcategory of quasicategories. Thus the
`1`-morphisms of `QCat.strictBicategory` are maps of simplicial sets.

Future work will use the fact that quasicategories define a cartesian closed subcategory
of simplicial sets to identify the `2`-morphisms of `QCat.strictBicategory` with
homotopy classes of homotopies between them, defined using the simplicial interval `Δ[1]`.

This strict bicategory serves as a setting to develop the formal category theory of quasicategories.

## References

* [Emily Riehl and Dominic Verity, Elements of ∞-Category Theory][RiehlVerity2022]
* [Emily Riehl and Dominic Verity, The 2-category theory of quasi-categories][RiehlVerity2015]

-/

@[expose] public section

universe u

namespace SSet

open CategoryTheory Simplicial

/-- `QCat` is the category of quasi-categories defined as the full subcategory of the category
`SSet` of simplicial sets. -/
/-
**SSet.QCat** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet`。
形式化陈述：QCat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`QCat` is the category of quasi-categories defined as the full subcategory of th
e category
`SSet` of simplicial sets.
-/
abbrev QCat := ObjectProperty.FullSubcategory Quasicategory

/-- `QCat` obtains a `Cat`-enriched ordinary category structure by applying `hoFunctor` to the
hom objects in its `SSet`-enriched ordinary structure. -/
/-
**SSet.QCat.catEnrichedOrdinaryCategory** 是 Mathlib 中的一个定义，位于命名空间 `SSet.QCat`。
形式化陈述：CategoryTheory.EnrichedOrdinaryCategory CategoryTheory.Cat SSet.QCat
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
`QCat` obtains a `Cat`-enriched ordinary category structure by applying `hoFunct
or` to the
hom objects in its `SSet`-enriched ordinary structure.
-/
instance QCat.catEnrichedOrdinaryCategory : EnrichedOrdinaryCategory Cat QCat :=
  TransportEnrichment.enrichedOrdinaryCategory QCat hoFunctor.{u}
    (hoFunctor.unitHomEquiv · |>.trans <| Functor.equivCatHom _ _)
      (congrArg (Functor.toCatHom) <| hoFunctor.unitHomEquiv_eq · ·)

/-- The underlying category of the `Cat`-enriched ordinary category of quasicategories is
equivalent to `QCat`. -/
/-
**SSet.QCat.forgetEnrichment.equiv** 是 Mathlib 中的一个定义，位于命名空间 `SSet.QCat.forgetEn
richment`。
形式化陈述：CategoryTheory.ForgetEnrichment CategoryTheory.Cat SSet.QCat ≌ SSet.QCat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying category of the `Cat`-enriched ordinary category of quasicategori
es is
equivalent to `QCat`.
-/
def QCat.forgetEnrichment.equiv :
    ForgetEnrichment Cat QCat ≌ QCat := ForgetEnrichment.equiv Cat

/-- The bicategory of quasicategories extracted from `QCat.CatEnrichedOrdinaryCat`. -/
/-
**SSet.QCat.bicategory** 是 Mathlib 中的一个定义，位于命名空间 `SSet.QCat`。
形式化陈述：CategoryTheory.Bicategory SSet.QCat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bicategory of quasicategories extracted from `QCat.CatEnrichedOrdinaryCat`.
-/
instance QCat.bicategory : Bicategory QCat :=
  CatEnrichedOrdinary.instBicategory

/-- The strict bicategory of quasicategories extracted from `QCat.CatEnrichedOrdinaryCat`. -/
/-
**SSet.QCat.strictBicategory** 是 Mathlib 中的一个定理，位于命名空间 `SSet.QCat`。
形式化陈述：CategoryTheory.Bicategory.Strict SSet.QCat
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CatEnrichedOrdinary.instStrict`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.EnrichedOrdinaryCateg
ory CategoryTheory.Cat C],   Catego…

--- 原说明 ---
The strict bicategory of quasicategories extracted from `QCat.CatEnrichedOrdinar
yCat`.
-/
instance QCat.strictBicategory : Bicategory.Strict QCat :=
  CatEnrichedOrdinary.instStrict

end SSet

