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

/--
Definition of `QCat` / `QCat` 的定义

English:
abbreviation QCat
  body: ObjectProperty.FullSubcategory Quasicategory

中文:
缩写 QCat
  定义体: ObjectProperty.FullSubcategory Quasicategory

Depends on / 依赖: FullSubcategory, ObjectProperty, ObjectProperty.FullSubcategory, Quasicategory
-/
abbrev QCat := ObjectProperty.FullSubcategory Quasicategory

/--
Instance `QCat.catEnrichedOrdinaryCategory` / 实例 `QCat.catEnrichedOrdinaryCategory`

English:
instance QCat.catEnrichedOrdinaryCategory
  signature: : EnrichedOrdinaryCategory Cat QCat
  body: TransportEnrichment.enrichedOrdinaryCategory QCat hoFunctor.{u}
    (hoFunctor.unitHomEquiv · |>.trans <| Functor.equivCatHom _ _)
      (congrArg (Functor.toCatHom) <| hoFunctor.unitHomEquiv_eq · ·)

中文:
实例 QCat.catEnrichedOrdinaryCategory
  签名: : EnrichedOrdinaryCategory Cat QCat
  定义体: TransportEnrichment.enrichedOrdinaryCategory QCat hoFunctor.{u}
    (hoFunctor.unitHomEquiv · |>.trans <| Functor.equivCatHom _ _)
      (congrArg (Functor.toCatHom) <| hoFunctor.unitHomEquiv_eq · ·)

Depends on / 依赖: Functor, Functor.equivCatHom, Functor.toCatHom, TransportEnrichment, TransportEnrichment.enrichedOrdinaryCategory, enrichedOrdinaryCategory, equivCatHom, hoFunctor, hoFunctor.unitHomEquiv, hoFunctor.unitHomEquiv_eq, toCatHom, unitHomEquiv, unitHomEquiv_eq
-/
instance QCat.catEnrichedOrdinaryCategory : EnrichedOrdinaryCategory Cat QCat :=
  TransportEnrichment.enrichedOrdinaryCategory QCat hoFunctor.{u}
    (hoFunctor.unitHomEquiv · |>.trans <| Functor.equivCatHom _ _)
      (congrArg (Functor.toCatHom) <| hoFunctor.unitHomEquiv_eq · ·)

/--
Definition of `QCat.forgetEnrichment.equiv` / `QCat.forgetEnrichment.equiv` 的定义

English:
definition QCat.forgetEnrichment.equiv
  signature: :
  body: ForgetEnrichment.equiv Cat

中文:
定义 QCat.forgetEnrichment.equiv
  签名: :
  定义体: ForgetEnrichment.equiv Cat

Depends on / 依赖: ForgetEnrichment, ForgetEnrichment.equiv
-/
def QCat.forgetEnrichment.equiv :
    ForgetEnrichment Cat QCat ≌ QCat := ForgetEnrichment.equiv Cat

/--
Instance `QCat.bicategory` / 实例 `QCat.bicategory`

English:
instance QCat.bicategory
  signature: : Bicategory QCat
  body: CatEnrichedOrdinary.instBicategory

中文:
实例 QCat.bicategory
  签名: : Bicategory QCat
  定义体: CatEnrichedOrdinary.instBicategory

Depends on / 依赖: CatEnrichedOrdinary, CatEnrichedOrdinary.instBicategory, instBicategory
-/
instance QCat.bicategory : Bicategory QCat :=
  CatEnrichedOrdinary.instBicategory

/--
Instance `QCat.strictBicategory` / 实例 `QCat.strictBicategory`

English:
instance QCat.strictBicategory
  signature: : Bicategory.Strict QCat
  body: CatEnrichedOrdinary.instStrict

中文:
实例 QCat.strictBicategory
  签名: : Bicategory.Strict QCat
  定义体: CatEnrichedOrdinary.instStrict

Depends on / 依赖: CatEnrichedOrdinary, CatEnrichedOrdinary.instStrict, instStrict
-/
instance QCat.strictBicategory : Bicategory.Strict QCat :=
  CatEnrichedOrdinary.instStrict

end SSet
