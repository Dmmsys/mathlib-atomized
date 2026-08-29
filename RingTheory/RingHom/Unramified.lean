/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.RingTheory.LocalProperties.Basic

/-!

# The meta properties of unramified ring homomorphisms.

-/

@[expose] public section

namespace RingHom

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S]

/--
A ring homomorphism `R →+* A` is formally unramified if `Ω[A⁄R]` is trivial.
See `Algebra.FormallyUnramified`.
-/
@[algebraize Algebra.FormallyUnramified]
/--
Definition of `FormallyUnramified` / `FormallyUnramified` 的定义

English:
definition FormallyUnramified
  signature: (f : R ->+* S)
  body: letI := f.toAlgebra
  Algebra.FormallyUnramified R S

中文:
定义 形式非分歧
  签名: (f : R ->+* S)
  定义体: letI := f.toAlgebra
  Algebra.FormallyUnramified R S

Depends on / 依赖: Algebra, Algebra.FormallyUnramified, FormallyUnramified, f.toAlgebra, toAlgebra
-/
def FormallyUnramified (f : R ->+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.FormallyUnramified R S

/--
lemma `formallyUnramified_algebraMap` / 引理 `formallyUnramified_algebraMap`

English:
lemma formallyUnramified_algebraMap
  given: [Algebra R S]
  proof: by
  rw [FormallyUnramified]; rw [toAlgebra_algebraMap]

中文:
引理 formallyUnramified_algebraMap
  条件: [代数 R S]
  证明: by
  rw [FormallyUnramified]; rw [toAlgebra_algebraMap]

Depends on / 依赖: FormallyUnramified, toAlgebra_algebraMap
-/
lemma formallyUnramified_algebraMap [Algebra R S] :
    (algebraMap R S).FormallyUnramified ↔ Algebra.FormallyUnramified R S := by
  rw [FormallyUnramified]; rw [toAlgebra_algebraMap]

namespace FormallyUnramified

/--
lemma `of_surjective` / 引理 `of_surjective`

English:
lemma of_surjective
  given: {f : R ->+* S} (hf : Function.Surjective f)
  statement: f.FormallyUnramified
  proof: by
  algebraize [f]
  exact Algebra.FormallyUnramified.of_surjective (Algebra.ofId R S) hf

中文:
引理 of_surjective
  条件: {f : R ->+* S} (hf : 函数.满射 f)
  结论: f.形式非分歧
  证明: by
  algebraize [f]
  exact Algebra.FormallyUnramified.of_surjective (Algebra.ofId R S) hf

Depends on / 依赖: Algebra, Algebra.FormallyUnramified.of_surjective, Algebra.ofId, FormallyUnramified, algebraize, of_surjective
-/
lemma of_surjective {f : R ->+* S} (hf : Function.Surjective f) : f.FormallyUnramified := by
  algebraize [f]
  exact Algebra.FormallyUnramified.of_surjective (Algebra.ofId R S) hf

/--
lemma `of_comp` / 引理 `of_comp`

English:
lemma of_comp
  statement: {T : Type*} [CommRing T] {f : R ->+* S} {g : S ->+* T}
  proof: by
  algebraize [f, g, g.comp f]
  exact Algebra.FormallyUnramified.of_restrictScalars R _ _

中文:
引理 of_comp
  结论: {T : 类型} [交换环 T] {f : R ->+* S} {g : S ->+* T}
  证明: by
  algebraize [f, g, g.comp f]
  exact Algebra.FormallyUnramified.of_restrictScalars R _ _

Depends on / 依赖: Algebra, Algebra.FormallyUnramified.of_restrictScalars, FormallyUnramified, algebraize, g.comp, of_restrictScalars
-/
lemma of_comp {T : Type*} [CommRing T] {f : R ->+* S} {g : S ->+* T}
    (h : (g.comp f).FormallyUnramified) :
    g.FormallyUnramified := by
  algebraize [f, g, g.comp f]
  exact Algebra.FormallyUnramified.of_restrictScalars R _ _

/--
lemma `comp` / 引理 `comp`

English:
lemma comp
  statement: {T : Type*} [CommRing T] {f : R ->+* S} {g : S ->+* T} (hf : f.FormallyUnramified)
  proof: by
  algebraize [f, g, g.comp f]
  exact Algebra.FormallyUnramified.comp R S T

中文:
引理 comp
  结论: {T : 类型} [交换环 T] {f : R ->+* S} {g : S ->+* T} (hf : f.形式非分歧)
  证明: by
  algebraize [f, g, g.comp f]
  exact Algebra.FormallyUnramified.comp R S T

Depends on / 依赖: Algebra, Algebra.FormallyUnramified.comp, FormallyUnramified, algebraize, g.comp
-/
lemma comp {T : Type*} [CommRing T] {f : R ->+* S} {g : S ->+* T} (hf : f.FormallyUnramified)
    (hg : g.FormallyUnramified) :
    (g.comp f).FormallyUnramified := by
  algebraize [f, g, g.comp f]
  exact Algebra.FormallyUnramified.comp R S T

/--
lemma `stableUnderComposition` / 引理 `stableUnderComposition`

English:
lemma stableUnderComposition
  statement: StableUnderComposition FormallyUnramified
  proof: fun _ _ _ _ _ _ _ _ hf hg => .comp hf hg

中文:
引理 stableUnderComposition
  结论: StableUnderComposition 形式非分歧
  证明: fun _ _ _ _ _ _ _ _ hf hg => .comp hf hg
-/
lemma stableUnderComposition : StableUnderComposition FormallyUnramified :=
  fun _ _ _ _ _ _ _ _ hf hg => .comp hf hg

/--
lemma `respectsIso` / 引理 `respectsIso`

English:
lemma respectsIso
  proof: by
  refine stableUnderComposition.respectsIso ?_
  intro R S _ _ e
  exact .of_surjective e.surjective

中文:
引理 respectsIso
  证明: by
  refine stableUnderComposition.respectsIso ?_
  intro R S _ _ e
  exact .of_surjective e.surjective

Depends on / 依赖: e.surjective, of_surjective, respectsIso, stableUnderComposition, stableUnderComposition.respectsIso, surjective
-/
lemma respectsIso :
    RespectsIso FormallyUnramified := by
  refine stableUnderComposition.respectsIso ?_
  intro R S _ _ e
  exact .of_surjective e.surjective

/--
lemma `isStableUnderBaseChange` / 引理 `isStableUnderBaseChange`

English:
lemma isStableUnderBaseChange
  proof: by
  refine .mk respectsIso ?_
  introv H
  rw [formallyUnramified_algebraMap] at H ⊢
  infer_instance

中文:
引理 isStableUnderBaseChange
  证明: by
  refine .mk respectsIso ?_
  introv H
  rw [formallyUnramified_algebraMap] at H ⊢
  infer_instance

Depends on / 依赖: formallyUnramified_algebraMap, infer_instance, introv, respectsIso
-/
lemma isStableUnderBaseChange :
    IsStableUnderBaseChange FormallyUnramified := by
  refine .mk respectsIso ?_
  introv H
  rw [formallyUnramified_algebraMap] at H ⊢
  infer_instance

/--
lemma `holdsForLocalization` / 引理 `holdsForLocalization`

English:
lemma holdsForLocalization
  proof: by
  intro R S _ _ _ M _
  rw [formallyUnramified_algebraMap]
  exact .of_isLocalization M

中文:
引理 holdsForLocalization
  证明: by
  intro R S _ _ _ M _
  rw [formallyUnramified_algebraMap]
  exact .of_isLocalization M

Depends on / 依赖: formallyUnramified_algebraMap, of_isLocalization
-/
lemma holdsForLocalization :
    HoldsForLocalization FormallyUnramified := by
  intro R S _ _ _ M _
  rw [formallyUnramified_algebraMap]
  exact .of_isLocalization M

/--
lemma `holdsForLocalizationAway` / 引理 `holdsForLocalizationAway`

English:
lemma holdsForLocalizationAway
  proof: holdsForLocalization.holdsForLocalizationAway

中文:
引理 holdsForLocalizationAway
  证明: holdsForLocalization.holdsForLocalizationAway

Depends on / 依赖: holdsForLocalization, holdsForLocalization.holdsForLocalizationAway, holdsForLocalizationAway
-/
lemma holdsForLocalizationAway :
    HoldsForLocalizationAway FormallyUnramified :=
  holdsForLocalization.holdsForLocalizationAway

/--
lemma `ofLocalizationPrime` / 引理 `ofLocalizationPrime`

English:
lemma ofLocalizationPrime
  proof: by
  intro R S _ _ f H
  algebraize [f]
  rw [FormallyUnramified]; rw [Algebra.formallyUnramified_iff_forall]
  intro x
  let Rₓ := Localization.AtPrime (x.asIdeal.comap f)
  let Sₓ := Localization.AtPrime x.asIdeal
  let : Algebra Rₓ Sₓ := (Localization.localRingHom _ _ _ rfl).toAlgebra
  have : IsScalarTower R Rₓ Sₓ := .of_algebraMap_eq
    fun x => (Localization.localRingHom_to_map _ _ _ rfl x).symm
  have : Algebra.FormallyUnramified Rₓ Sₓ := H _ _
  exact Algebra.FormallyUnramified.comp R Rₓ Sₓ

中文:
引理 ofLocalizationPrime
  证明: by
  intro R S _ _ f H
  algebraize [f]
  rw [FormallyUnramified]; rw [Algebra.formallyUnramified_iff_forall]
  intro x
  let Rₓ := Localization.AtPrime (x.asIdeal.comap f)
  let Sₓ := Localization.AtPrime x.asIdeal
  let : Algebra Rₓ Sₓ := (Localization.localRingHom _ _ _ rfl).toAlgebra
  have : IsScalarTower R Rₓ Sₓ := .of_algebraMap_eq
    fun x => (Localization.localRingHom_to_map _ _ _ rfl x).symm
  have : Algebra.FormallyUnramified Rₓ Sₓ := H _ _
  exact Algebra.FormallyUnramified.comp R Rₓ Sₓ

Depends on / 依赖: Algebra, Algebra.FormallyUnramified, Algebra.FormallyUnramified.comp, Algebra.formallyUnramified_iff_forall, AtPrime, FormallyUnramified, IsScalarTower, Localization, Localization.AtPrime, Localization.localRingHom, Localization.localRingHom_to_map, algebraize, asIdeal, formallyUnramified_iff_forall, localRingHom, localRingHom_to_map, of_algebraMap_eq, toAlgebra, x.asIdeal, x.asIdeal.comap
-/
lemma ofLocalizationPrime :
    OfLocalizationPrime FormallyUnramified := by
  intro R S _ _ f H
  algebraize [f]
  rw [FormallyUnramified]; rw [Algebra.formallyUnramified_iff_forall]
  intro x
  let Rₓ := Localization.AtPrime (x.asIdeal.comap f)
  let Sₓ := Localization.AtPrime x.asIdeal
  let : Algebra Rₓ Sₓ := (Localization.localRingHom _ _ _ rfl).toAlgebra
  have : IsScalarTower R Rₓ Sₓ := .of_algebraMap_eq
    fun x => (Localization.localRingHom_to_map _ _ _ rfl x).symm
  have : Algebra.FormallyUnramified Rₓ Sₓ := H _ _
  exact Algebra.FormallyUnramified.comp R Rₓ Sₓ

/--
lemma `ofLocalizationSpanTarget` / 引理 `ofLocalizationSpanTarget`

English:
lemma ofLocalizationSpanTarget
  proof: by
  intro R S _ _ f s hs H
  algebraize [f]
  rw [FormallyUnramified]; rw [Algebra.formallyUnramified_iff_forall]
  intro x
  obtain ⟨r, hr, hrx⟩ : exists r in s, x in PrimeSpectrum.basicOpen r := by
    simpa using (PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr hs).ge
      (TopologicalSpace.Opens.mem_top x)
  refine Algebra.basicOpen_subset_unramifiedLocus_iff.mpr ?_ hrx
  convert! H ⟨r, hr⟩
  dsimp
  rw [← algebraMap_toAlgebra f]; rw [← IsScalarTower.algebraMap_eq]; rw [formallyUnramified_algebraMap]

中文:
引理 ofLocalizationSpanTarget
  证明: by
  intro R S _ _ f s hs H
  algebraize [f]
  rw [FormallyUnramified]; rw [Algebra.formallyUnramified_iff_forall]
  intro x
  obtain ⟨r, hr, hrx⟩ : exists r in s, x in PrimeSpectrum.basicOpen r := by
    simpa using (PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr hs).ge
      (TopologicalSpace.Opens.mem_top x)
  refine Algebra.basicOpen_subset_unramifiedLocus_iff.mpr ?_ hrx
  convert! H ⟨r, hr⟩
  dsimp
  rw [← algebraMap_toAlgebra f]; rw [← IsScalarTower.algebraMap_eq]; rw [formallyUnramified_algebraMap]

Depends on / 依赖: Algebra, Algebra.basicOpen_subset_unramifiedLocus_iff.mpr, Algebra.formallyUnramified_iff_forall, FormallyUnramified, IsScalarTower, IsScalarTower.algebraMap_eq, PrimeSpectrum, PrimeSpectrum.basicOpen, PrimeSpectrum.iSup_basicOpen_eq_top_iff, TopologicalSpace, TopologicalSpace.Opens.mem_top, algebraMap_eq, algebraMap_toAlgebra, algebraize, basicOpen, basicOpen_subset_unramifiedLocus_iff, convert, formallyUnramified_algebraMap, formallyUnramified_iff_forall, iSup_basicOpen_eq_top_iff
-/
lemma ofLocalizationSpanTarget :
    OfLocalizationSpanTarget FormallyUnramified := by
  intro R S _ _ f s hs H
  algebraize [f]
  rw [FormallyUnramified]; rw [Algebra.formallyUnramified_iff_forall]
  intro x
  obtain ⟨r, hr, hrx⟩ : exists r in s, x in PrimeSpectrum.basicOpen r := by
    simpa using (PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr hs).ge
      (TopologicalSpace.Opens.mem_top x)
  refine Algebra.basicOpen_subset_unramifiedLocus_iff.mpr ?_ hrx
  convert! H ⟨r, hr⟩
  dsimp
  rw [← algebraMap_toAlgebra f]; rw [← IsScalarTower.algebraMap_eq]; rw [formallyUnramified_algebraMap]

/--
lemma `propertyIsLocal` / 引理 `propertyIsLocal`

English:
lemma propertyIsLocal
  proof: by
  constructor
  · exact isStableUnderBaseChange.localizationPreserves.away
  · exact ofLocalizationSpanTarget
  · exact ofLocalizationSpanTarget.ofLocalizationSpan
      (stableUnderComposition.stableUnderCompositionWithLocalizationAway
          holdsForLocalizationAway).1
  · exact (stableUnderComposition.stableUnderCompositionWithLocalizationAway
        holdsForLocalizationAway).2

中文:
引理 propertyIsLocal
  证明: by
  constructor
  · exact isStableUnderBaseChange.localizationPreserves.away
  · exact ofLocalizationSpanTarget
  · exact ofLocalizationSpanTarget.ofLocalizationSpan
      (stableUnderComposition.stableUnderCompositionWithLocalizationAway
          holdsForLocalizationAway).1
  · exact (stableUnderComposition.stableUnderCompositionWithLocalizationAway
        holdsForLocalizationAway).2

Depends on / 依赖: holdsForLocalizationAway, isStableUnderBaseChange, isStableUnderBaseChange.localizationPreserves.away, localizationPreserves, ofLocalizationSpan, ofLocalizationSpanTarget, ofLocalizationSpanTarget.ofLocalizationSpan, stableUnderComposition, stableUnderComposition.stableUnderCompositionWithLocalizationAway, stableUnderCompositionWithLocalizationAway
-/
lemma propertyIsLocal :
    PropertyIsLocal FormallyUnramified := by
  constructor
  · exact isStableUnderBaseChange.localizationPreserves.away
  · exact ofLocalizationSpanTarget
  · exact ofLocalizationSpanTarget.ofLocalizationSpan
      (stableUnderComposition.stableUnderCompositionWithLocalizationAway
          holdsForLocalizationAway).1
  · exact (stableUnderComposition.stableUnderCompositionWithLocalizationAway
        holdsForLocalizationAway).2

end FormallyUnramified

/--
lemma `FormallyEtale.of_comp` / 引理 `FormallyEtale.of_comp`

English:
lemma FormallyEtale.of_comp
  statement: {T : Type*} [CommRing T] {f : R ->+* S} {g : S ->+* T}
  proof: by
  algebraize [f, g, g.comp f]
  exact Algebra.FormallyEtale.of_restrictScalars (R := R)

中文:
引理 形式平展.of_comp
  结论: {T : 类型} [交换环 T] {f : R ->+* S} {g : S ->+* T}
  证明: by
  algebraize [f, g, g.comp f]
  exact Algebra.FormallyEtale.of_restrictScalars (R := R)

Depends on / 依赖: Algebra, Algebra.FormallyEtale.of_restrictScalars, FormallyEtale, algebraize, g.comp, of_restrictScalars
-/
lemma FormallyEtale.of_comp {T : Type*} [CommRing T] {f : R ->+* S} {g : S ->+* T}
    (hf : f.FormallyUnramified) (h : (g.comp f).FormallyEtale) :
    g.FormallyEtale := by
  algebraize [f, g, g.comp f]
  exact Algebra.FormallyEtale.of_restrictScalars (R := R)

end RingHom
