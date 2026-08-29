/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveSheaves
public import Mathlib.CategoryTheory.Sites.Limits
/-!

# Colimits in categories of extensive sheaves

This file proves that `J`-shaped colimits of `A`-valued sheaves for the extensive topology are
computed objectwise if `colim : J ⥤ A ⥤ A` preserves finite products.

This holds for all shapes `J` if `A` is a preadditive category.

This can also easily be applied to filtered `J` in the case when `A` is a category of sets, and
eventually to sifted `J` once that API is developed.
-/

public section

namespace CategoryTheory

open Limits Sheaf GrothendieckTopology Opposite

section

variable {A C J : Type*} [Category* A] [Category* C] [Category* J]
  [FinitaryExtensive C] [HasColimitsOfShape J A]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isSheaf_pointwiseColimit` / 引理 `isSheaf_pointwiseColimit`

English:
lemma isSheaf_pointwiseColimit
  statement: [PreservesFiniteProducts (colim (J := J) (C := A))]
  proof: by
  rw [Presheaf.isSheaf_iff_preservesFiniteProducts]
  dsimp only [pointwiseCocone_pt]
  apply +allowSynthFailures comp_preservesFiniteProducts
  have : forall (i : J), PreservesFiniteProducts ((G ⋙ sheafToPresheaf _ A).obj i) := fun i => by
    rw [← Presheaf.isSheaf_iff_preservesFiniteProducts]


中文:
引理 isSheaf_pointwiseColimit
  结论: [PreservesFiniteProducts (colim (J := J) (C := A))]
  证明: by
  rw [Presheaf.isSheaf_iff_preservesFiniteProducts]
  dsimp only [pointwiseCocone_pt]
  apply +allowSynthFailures comp_preservesFiniteProducts
  have : forall (i : J), PreservesFiniteProducts ((G ⋙ sheafToPresheaf _ A).obj i) := fun i => by
    rw [← Presheaf.isSheaf_iff_preservesFiniteProducts]

-/
lemma isSheaf_pointwiseColimit [PreservesFiniteProducts (colim (J := J) (C := A))]
    (G : J ⥤ Sheaf (extensiveTopology C) A) :
    Presheaf.IsSheaf (extensiveTopology C) (pointwiseCocone (G ⋙ sheafToPresheaf _ A)).pt := by
  rw [Presheaf.isSheaf_iff_preservesFiniteProducts]
  dsimp only [pointwiseCocone_pt]
  apply +allowSynthFailures comp_preservesFiniteProducts
  have : forall (i : J), PreservesFiniteProducts ((G ⋙ sheafToPresheaf _ A).obj i) := fun i => by
    rw [← Presheaf.isSheaf_iff_preservesFiniteProducts]
    exact (G.obj i).property
  exact ⟨fun _ => preservesLimitsOfShape_of_evaluation _ _ fun d =>
    inferInstanceAs (PreservesLimitsOfShape _ ((G ⋙ sheafToPresheaf _ _).obj d))⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preadditive
  signature: A] : PreservesFiniteProducts (colim (J := J) (C := A)) where
  body: by
    apply +allowSynthFailures preservesProductsOfShape_of_preservesBiproductsOfShape
    apply preservesBiproductsOfShape_of_preservesCoproductsOfShape

中文:
实例 [Preadditive
  签名: A] : PreservesFiniteProducts (colim (J := J) (C := A)) where
  定义体: by
    apply +allowSynthFailures preservesProductsOfShape_of_preservesBiproductsOfShape
    apply preservesBiproductsOfShape_of_preservesCoproductsOfShape
-/
instance [Preadditive A] : PreservesFiniteProducts (colim (J := J) (C := A)) where
  preserves _ := by
    apply +allowSynthFailures preservesProductsOfShape_of_preservesBiproductsOfShape
    apply preservesBiproductsOfShape_of_preservesCoproductsOfShape

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PreservesFiniteProducts
  signature: (colim (J := J) (C := A))] :
  body: by
    suffices CreatesColimit G (sheafToPresheaf (extensiveTopology C) A) from inferInstance
    refine createsColimitOfIsSheaf _ (fun c hc => ?_)
    let i : c.pt ≅ (G ⋙ sheafToPresheaf _ _).flip ⋙ colim :=
      hc.coconePointUniqueUpToIso (pointwiseIsColimit _)
    rw [Presheaf.isSheaf_of_iso_if

中文:
实例 [PreservesFiniteProducts
  签名: (colim (J := J) (C := A))] :
  定义体: by
    suffices CreatesColimit G (sheafToPresheaf (extensiveTopology C) A) from inferInstance
    refine createsColimitOfIsSheaf _ (fun c hc => ?_)
    let i : c.pt ≅ (G ⋙ sheafToPresheaf _ _).flip ⋙ colim :=
      hc.coconePointUniqueUpToIso (pointwiseIsColimit _)
    rw [Presheaf.isSheaf_of_iso_if
-/
instance [PreservesFiniteProducts (colim (J := J) (C := A))] :
    PreservesColimitsOfShape J (sheafToPresheaf (extensiveTopology C) A) where
  preservesColimit {G} := by
    suffices CreatesColimit G (sheafToPresheaf (extensiveTopology C) A) from inferInstance
    refine createsColimitOfIsSheaf _ (fun c hc => ?_)
    let i : c.pt ≅ (G ⋙ sheafToPresheaf _ _).flip ⋙ colim :=
      hc.coconePointUniqueUpToIso (pointwiseIsColimit _)
    rw [Presheaf.isSheaf_of_iso_iff i]
    exact isSheaf_pointwiseColimit _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preadditive
  signature: A] [HasFiniteColimits A] :
  body: inferInstance

中文:
实例 [Preadditive
  签名: A] [HasFiniteColimits A] :
  定义体: inferInstance
-/
instance [Preadditive A] [HasFiniteColimits A] :
    PreservesFiniteColimits (sheafToPresheaf (extensiveTopology C) A) where
  preservesFiniteColimits _ := inferInstance

end

end CategoryTheory
