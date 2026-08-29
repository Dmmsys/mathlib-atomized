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

/--
Definition of `SimplicialCategory` / `SimplicialCategory` 的定义

English:
abbreviation SimplicialCategory
  body: EnrichedOrdinaryCategory SSet.{v} C

中文:
缩写 SimplicialCategory
  定义体: EnrichedOrdinaryCategory SSet.{v} C

Depends on / 依赖: EnrichedOrdinaryCategory
-/
abbrev SimplicialCategory := EnrichedOrdinaryCategory SSet.{v} C

namespace SimplicialCategory

variable [SimplicialCategory C]

variable {C}

/--
Definition of `sHom` / `sHom` 的定义

English:
abbreviation sHom
  signature: (K L : C)
  body: K ⟶[SSet] L

中文:
缩写 sHom
  签名: (K L : C)
  定义体: K ⟶[SSet] L
-/
abbrev sHom (K L : C) : SSet.{v} := K ⟶[SSet] L

/--
Definition of `sHomComp` / `sHomComp` 的定义

English:
abbreviation sHomComp
  signature: (K L M : C)
  body: eComp SSet K L M

中文:
缩写 sHomComp
  签名: (K L M : C)
  定义体: eComp SSet K L M
-/
abbrev sHomComp (K L M : C) : sHom K L otimes sHom L M ⟶ sHom K M := eComp SSet K L M

/--
Definition of `homEquiv'` / `homEquiv'` 的定义

English:
definition homEquiv'
  signature: (K L : C)
  body: (eHomEquiv SSet).trans (sHom K L).unitHomEquiv

中文:
定义 homEquiv'
  签名: (K L : C)
  定义体: (eHomEquiv SSet).trans (sHom K L).unitHomEquiv

Depends on / 依赖: eHomEquiv, unitHomEquiv
-/
def homEquiv' (K L : C) : (K ⟶ L) ≃ sHom K L _⦋0⦌ :=
  (eHomEquiv SSet).trans (sHom K L).unitHomEquiv

variable (C) in
/--
Definition of `sHomFunctor` / `sHomFunctor` 的定义

English:
abbreviation sHomFunctor
  signature: : Cᵒᵖ ⥤ C ⥤ SSet.{v}
  body: eHomFunctor _ _

中文:
缩写 sHomFunctor
  签名: : Cᵒᵖ ⥤ C ⥤ SSet.{v}
  定义体: eHomFunctor _ _

Depends on / 依赖: eHomFunctor
-/
noncomputable abbrev sHomFunctor : Cᵒᵖ ⥤ C ⥤ SSet.{v} := eHomFunctor _ _

end SimplicialCategory

end CategoryTheory
