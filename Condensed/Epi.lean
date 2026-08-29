/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.Coherent.LocallySurjective
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Condensed.Equivalence
public import Mathlib.Condensed.Module
/-!

# Epimorphisms of condensed objects

This file characterises epimorphisms of condensed sets and condensed `R`-modules for any ring `R`,
as those morphisms which are objectwise surjective on `Stonean` (see
`CondensedSet.epi_iff_surjective_on_stonean` and `CondensedMod.epi_iff_surjective_on_stonean`).
-/

public section

universe v u w u' v'

open CategoryTheory Sheaf Opposite Limits Condensed ConcreteCategory

namespace Condensed

variable (A : Type u') [Category.{v'} A] {FA : A -> A -> Type*} {CA : A -> Type v'}
variable [forall X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{v'} A FA]
  [HasFunctorialSurjectiveInjectiveFactorization A]

variable {X Y : Condensed.{u} A} (f : X ⟶ Y)

set_option Elab.async false in -- TODO: universe levels from type are unified in proof
variable
  [(coherentTopology CompHaus).WEqualsLocallyBijective A]
  [HasSheafify (coherentTopology CompHaus) A]
  [(coherentTopology CompHaus.{u}).HasSheafCompose (CategoryTheory.forget A)]
  [Balanced (Sheaf (coherentTopology CompHaus) A)]
  [PreservesFiniteProducts (CategoryTheory.forget A)] in
/--
lemma `epi_iff_locallySurjective_on_compHaus` / 引理 `epi_iff_locallySurjective_on_compHaus`

English:
lemma epi_iff_locallySurjective_on_compHaus
  statement: Epi f ↔
  proof: by
  rw [← isLocallySurjective_iff_epi']; rw [coherentTopology.isLocallySurjective_iff]; rw [regularTopology.isLocallySurjective_iff]
  simp_rw [((CompHaus.effectiveEpi_tfae _).out 0 2 :)]

中文:
引理 epi_iff_locallySurjective_on_compHaus
  结论: Epi f ↔
  证明: by
  rw [← isLocallySurjective_iff_epi']; rw [coherentTopology.isLocallySurjective_iff]; rw [regularTopology.isLocallySurjective_iff]
  simp_rw [((CompHaus.effectiveEpi_tfae _).out 0 2 :)]

Depends on / 依赖: CompHaus, CompHaus.effectiveEpi_tfae, coherentTopology, coherentTopology.isLocallySurjective_iff, effectiveEpi_tfae, isLocallySurjective_iff, isLocallySurjective_iff_epi, regularTopology, regularTopology.isLocallySurjective_iff, simp_rw
-/
lemma epi_iff_locallySurjective_on_compHaus : Epi f ↔
    forall (S : CompHaus) (y : ToType (Y.obj.obj ⟨S⟩)),
      (exists (S' : CompHaus) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : ToType (X.obj.obj ⟨S'⟩)),
        f.hom.app ⟨S'⟩ x = Y.obj.map ⟨φ⟩ y) := by
  rw [← isLocallySurjective_iff_epi']; rw [coherentTopology.isLocallySurjective_iff]; rw [regularTopology.isLocallySurjective_iff]
  simp_rw [((CompHaus.effectiveEpi_tfae _).out 0 2 :)]

set_option Elab.async false in -- TODO: universe levels from type are unified in proof
variable
  [PreservesFiniteProducts (CategoryTheory.forget A)]
  [forall (X : CompHausᵒᵖ), HasLimitsOfShape (StructuredArrow X Stonean.toCompHaus.op) A]
  [(extensiveTopology Stonean).WEqualsLocallyBijective A]
  [HasSheafify (extensiveTopology Stonean) A]
  [(extensiveTopology Stonean.{u}).HasSheafCompose (CategoryTheory.forget A)]
  [Balanced (Sheaf (extensiveTopology Stonean) A)] in
/--
lemma `epi_iff_surjective_on_stonean` / 引理 `epi_iff_surjective_on_stonean`

English:
lemma epi_iff_surjective_on_stonean
  statement: Epi f ↔
  proof: by
  rw [← (StoneanCompHaus.equivalence A).inverse.epi_map_iff_epi]; rw [← Presheaf.coherentExtensiveEquivalence.functor.epi_map_iff_epi]; rw [← isLocallySurjective_iff_epi']
  exact extensiveTopology.isLocallySurjective_iff (D := A) _

中文:
引理 epi_iff_surjective_on_stonean
  结论: Epi f ↔
  证明: by
  rw [← (StoneanCompHaus.equivalence A).inverse.epi_map_iff_epi]; rw [← Presheaf.coherentExtensiveEquivalence.functor.epi_map_iff_epi]; rw [← isLocallySurjective_iff_epi']
  exact extensiveTopology.isLocallySurjective_iff (D := A) _

Depends on / 依赖: Presheaf, Presheaf.coherentExtensiveEquivalence.functor.epi_map_iff_epi, StoneanCompHaus, StoneanCompHaus.equivalence, coherentExtensiveEquivalence, epi_map_iff_epi, equivalence, extensiveTopology, extensiveTopology.isLocallySurjective_iff, functor, inverse, inverse.epi_map_iff_epi, isLocallySurjective_iff, isLocallySurjective_iff_epi
-/
lemma epi_iff_surjective_on_stonean : Epi f ↔
    forall (S : Stonean), Function.Surjective (f.hom.app (op S.compHaus)) := by
  rw [← (StoneanCompHaus.equivalence A).inverse.epi_map_iff_epi]; rw [← Presheaf.coherentExtensiveEquivalence.functor.epi_map_iff_epi]; rw [← isLocallySurjective_iff_epi']
  exact extensiveTopology.isLocallySurjective_iff (D := A) _

end Condensed

namespace CondensedSet

variable {X Y : CondensedSet.{u}} (f : X ⟶ Y)

/--
lemma `epi_iff_locallySurjective_on_compHaus` / 引理 `epi_iff_locallySurjective_on_compHaus`

English:
lemma epi_iff_locallySurjective_on_compHaus
  statement: Epi f ↔
  proof: Condensed.epi_iff_locallySurjective_on_compHaus _ f

中文:
引理 epi_iff_locallySurjective_on_compHaus
  结论: Epi f ↔
  证明: Condensed.epi_iff_locallySurjective_on_compHaus _ f

Depends on / 依赖: Condensed, Condensed.epi_iff_locallySurjective_on_compHaus, epi_iff_locallySurjective_on_compHaus
-/
lemma epi_iff_locallySurjective_on_compHaus : Epi f ↔
    forall (S : CompHaus) (y : Y.obj.obj ⟨S⟩),
      (exists (S' : CompHaus) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : X.obj.obj ⟨S'⟩),
        f.hom.app ⟨S'⟩ x = Y.obj.map ⟨φ⟩ y) :=
  Condensed.epi_iff_locallySurjective_on_compHaus _ f

/--
lemma `epi_iff_surjective_on_stonean` / 引理 `epi_iff_surjective_on_stonean`

English:
lemma epi_iff_surjective_on_stonean
  statement: Epi f ↔
  proof: Condensed.epi_iff_surjective_on_stonean _ f

中文:
引理 epi_iff_surjective_on_stonean
  结论: Epi f ↔
  证明: Condensed.epi_iff_surjective_on_stonean _ f

Depends on / 依赖: Condensed, Condensed.epi_iff_surjective_on_stonean, epi_iff_surjective_on_stonean
-/
lemma epi_iff_surjective_on_stonean : Epi f ↔
    forall (S : Stonean), Function.Surjective (f.hom.app (op S.compHaus)) :=
  Condensed.epi_iff_surjective_on_stonean _ f

end CondensedSet

namespace CondensedMod

variable (R : Type (u + 1)) [Ring R] {X Y : CondensedMod.{u} R} (f : X ⟶ Y)

/--
lemma `epi_iff_locallySurjective_on_compHaus` / 引理 `epi_iff_locallySurjective_on_compHaus`

English:
lemma epi_iff_locallySurjective_on_compHaus
  statement: Epi f ↔
  proof: Condensed.epi_iff_locallySurjective_on_compHaus _ f

中文:
引理 epi_iff_locallySurjective_on_compHaus
  结论: Epi f ↔
  证明: Condensed.epi_iff_locallySurjective_on_compHaus _ f

Depends on / 依赖: Condensed, Condensed.epi_iff_locallySurjective_on_compHaus, epi_iff_locallySurjective_on_compHaus
-/
lemma epi_iff_locallySurjective_on_compHaus : Epi f ↔
    forall (S : CompHaus) (y : Y.obj.obj ⟨S⟩),
      (exists (S' : CompHaus) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : X.obj.obj ⟨S'⟩),
        f.hom.app ⟨S'⟩ x = Y.obj.map ⟨φ⟩ y) :=
  Condensed.epi_iff_locallySurjective_on_compHaus _ f

/--
lemma `epi_iff_surjective_on_stonean` / 引理 `epi_iff_surjective_on_stonean`

English:
lemma epi_iff_surjective_on_stonean
  statement: Epi f ↔
  proof: have : HasLimitsOfSize.{u, u + 1} (ModuleCat R) :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
  Condensed.epi_iff_surjective_on_stonean _ f

中文:
引理 epi_iff_surjective_on_stonean
  结论: Epi f ↔
  证明: have : HasLimitsOfSize.{u, u + 1} (ModuleCat R) :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
  Condensed.epi_iff_surjective_on_stonean _ f

Depends on / 依赖: Condensed, Condensed.epi_iff_surjective_on_stonean, HasLimitsOfSize, ModuleCat, epi_iff_surjective_on_stonean, hasLimitsOfSizeShrink
-/
lemma epi_iff_surjective_on_stonean : Epi f ↔
    forall (S : Stonean), Function.Surjective (f.hom.app (op S.compHaus)) :=
  have : HasLimitsOfSize.{u, u + 1} (ModuleCat R) :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
  Condensed.epi_iff_surjective_on_stonean _ f

end CondensedMod
