/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction
public import Mathlib.Topology.Convenient.Category

/-!
# The category of `X`-generated spaces, as a localization

Let `X i` be a family of topological spaces. In this file, we introduce
a property of morphisms `morphismPropertyWithGeneratedByTopologyEquiv X`
in the category `TopCat`: it consists of the morphisms corresponding to
the canonical continuous maps `WithGeneratedByTopology X Z → Z` for
all topological spaces `Z`. We show that the functor
`TopCat.toContinuousGeneratedByCat X : TopCat ⥤ ContinuousGeneratedByCat X`
makes `ContinuousGeneratedByCat X` the localized category of `TopCat` with
respect to this class of morphisms. Similarly,
`TopCat.toGeneratedByTopCat : TopCat ⥤ GeneratedByTopCat X` is also
a localization functor.

-/

@[expose] public section

universe v t u

open CategoryTheory MorphismProperty

namespace TopCat

variable {ι : Type t} (X : ι -> Type u) [forall i, TopologicalSpace (X i)]

/--
Definition of `morphismPropertyWithGeneratedByTopologyEquiv` / `morphismPropertyWithGeneratedByTopologyEquiv` 的定义

English:
definition morphismPropertyWithGeneratedByTopologyEquiv
  signature: : MorphismProperty TopCat.{v}
  body: MorphismProperty.ofHoms (GeneratedByTopCat.adjCounit (X := X)).app

中文:
定义 morphismPropertyWithGeneratedByTopologyEquiv
  签名: : Morphism命题erty TopCat.{v}
  定义体: MorphismProperty.ofHoms (GeneratedByTopCat.adjCounit (X := X)).app

Depends on / 依赖: GeneratedByTopCat, GeneratedByTopCat.adjCounit, MorphismProperty, MorphismProperty.ofHoms, adjCounit, ofHoms
-/
def morphismPropertyWithGeneratedByTopologyEquiv : MorphismProperty TopCat.{v} :=
  MorphismProperty.ofHoms (GeneratedByTopCat.adjCounit (X := X)).app

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (TopCat.toContinuousGeneratedByCat.{v} X).IsLocalization
  body: ContinuousGeneratedByCat.adj.isLocalization_rightAdjoint _
    (by rintro _ _ _ ⟨Z⟩; infer_instance)
    (fun _ => by constructor)

中文:
实例 :
  签名: (TopCat.toContinuousGeneratedByCat.{v} X).IsLocalization
  定义体: ContinuousGeneratedByCat.adj.isLocalization_rightAdjoint _
    (by rintro _ _ _ ⟨Z⟩; infer_instance)
    (fun _ => by constructor)

Depends on / 依赖: ContinuousGeneratedByCat, ContinuousGeneratedByCat.adj.isLocalization_rightAdjoint, infer_instance, isLocalization_rightAdjoint
-/
instance : (TopCat.toContinuousGeneratedByCat.{v} X).IsLocalization
    (TopCat.morphismPropertyWithGeneratedByTopologyEquiv X) :=
  ContinuousGeneratedByCat.adj.isLocalization_rightAdjoint _
    (by rintro _ _ _ ⟨Z⟩; infer_instance)
    (fun _ => by constructor)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (TopCat.toGeneratedByTopCat.{v} (X := X)).IsLocalization
  body: GeneratedByTopCat.adj.isLocalization_rightAdjoint _
    (by rintro _ _ _ ⟨Z⟩; infer_instance)
    (fun _ => by constructor)

中文:
实例 :
  签名: (TopCat.toGeneratedByTopCat.{v} (X := X)).IsLocalization
  定义体: GeneratedByTopCat.adj.isLocalization_rightAdjoint _
    (by rintro _ _ _ ⟨Z⟩; infer_instance)
    (fun _ => by constructor)

Depends on / 依赖: IsLocalization
-/
instance : (TopCat.toGeneratedByTopCat.{v} (X := X)).IsLocalization
    (TopCat.morphismPropertyWithGeneratedByTopologyEquiv X) :=
  GeneratedByTopCat.adj.isLocalization_rightAdjoint _
    (by rintro _ _ _ ⟨Z⟩; infer_instance)
    (fun _ => by constructor)

end TopCat
