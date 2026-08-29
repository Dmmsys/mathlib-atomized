/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalProperties.Basic

/-!
# Meta properties of essentially of finite type ring homomorphisms
-/

public section

namespace RingHom.EssFiniteType

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/--
lemma `comp` / 引理 `comp`

English:
lemma comp
  given: {f : R ->+* S} {g : S ->+* T} (hf : f.EssFiniteType) (hg : g.EssFiniteType)
  proof: by
  algebraize [f, g, g.comp f]
  exact Algebra.EssFiniteType.comp R S T

中文:
引理 comp
  条件: {f : R ->+* S} {g : S ->+* T} (hf : f.EssFiniteType) (hg : g.EssFiniteType)
  证明: by
  algebraize [f, g, g.comp f]
  exact Algebra.EssFiniteType.comp R S T

Depends on / 依赖: Algebra, Algebra.EssFiniteType.comp, EssFiniteType, algebraize, g.comp
-/
lemma comp {f : R ->+* S} {g : S ->+* T} (hf : f.EssFiniteType) (hg : g.EssFiniteType) :
    (g.comp f).EssFiniteType := by
  algebraize [f, g, g.comp f]
  exact Algebra.EssFiniteType.comp R S T

/--
lemma `comp_iff` / 引理 `comp_iff`

English:
lemma comp_iff
  given: {f : R ->+* S} {g : S ->+* T} (hf : f.EssFiniteType)
  proof: by
  algebraize [f, g, g.comp f]
  exact Algebra.EssFiniteType.comp_iff R S T

中文:
引理 comp_iff
  条件: {f : R ->+* S} {g : S ->+* T} (hf : f.EssFiniteType)
  证明: by
  algebraize [f, g, g.comp f]
  exact Algebra.EssFiniteType.comp_iff R S T

Depends on / 依赖: Algebra, Algebra.EssFiniteType.comp_iff, EssFiniteType, algebraize, comp_iff, g.comp
-/
lemma comp_iff {f : R ->+* S} {g : S ->+* T} (hf : f.EssFiniteType) :
    (g.comp f).EssFiniteType ↔ g.EssFiniteType := by
  algebraize [f, g, g.comp f]
  exact Algebra.EssFiniteType.comp_iff R S T

/--
lemma `of_comp` / 引理 `of_comp`

English:
lemma of_comp
  given: (f : R ->+* S) {g : S ->+* T} (h : (g.comp f).EssFiniteType)
  proof: by
  algebraize [f, g, g.comp f]
  exact Algebra.EssFiniteType.of_comp R S T

中文:
引理 of_comp
  条件: (f : R ->+* S) {g : S ->+* T} (h : (g.comp f).EssFiniteType)
  证明: by
  algebraize [f, g, g.comp f]
  exact Algebra.EssFiniteType.of_comp R S T

Depends on / 依赖: Algebra, Algebra.EssFiniteType.of_comp, EssFiniteType, algebraize, g.comp, of_comp
-/
lemma of_comp (f : R ->+* S) {g : S ->+* T} (h : (g.comp f).EssFiniteType) :
    g.EssFiniteType := by
  algebraize [f, g, g.comp f]
  exact Algebra.EssFiniteType.of_comp R S T

/--
lemma `stableUnderComposition` / 引理 `stableUnderComposition`

English:
lemma stableUnderComposition
  statement: StableUnderComposition EssFiniteType
  proof: fun _ _ _ _ _ _ _ _ hf hg => hf.comp hg

中文:
引理 stableUnderComposition
  结论: StableUnderComposition EssFiniteType
  证明: fun _ _ _ _ _ _ _ _ hf hg => hf.comp hg

Depends on / 依赖: hf.comp
-/
lemma stableUnderComposition : StableUnderComposition EssFiniteType :=
  fun _ _ _ _ _ _ _ _ hf hg => hf.comp hg

/--
lemma `respectsIso` / 引理 `respectsIso`

English:
lemma respectsIso
  statement: RespectsIso EssFiniteType
  proof: stableUnderComposition.respectsIso fun e => (FiniteType.of_surjective _ e.surjective).essFiniteType

中文:
引理 respectsIso
  结论: RespectsIso EssFiniteType
  证明: stableUnderComposition.respectsIso fun e => (FiniteType.of_surjective _ e.surjective).essFiniteType

Depends on / 依赖: FiniteType, FiniteType.of_surjective, e.surjective, essFiniteType, of_surjective, respectsIso, stableUnderComposition, stableUnderComposition.respectsIso, surjective
-/
lemma respectsIso : RespectsIso EssFiniteType :=
  stableUnderComposition.respectsIso fun e => (FiniteType.of_surjective _ e.surjective).essFiniteType

/--
lemma `isStableUnderBaseChange` / 引理 `isStableUnderBaseChange`

English:
lemma isStableUnderBaseChange
  statement: IsStableUnderBaseChange EssFiniteType
  proof: .mk respectsIso fun R S T _ _ _ _ _ h => by
    rw [essFiniteType_algebraMap] at h ⊢
    infer_instance

中文:
引理 isStableUnderBaseChange
  结论: IsStableUnderBaseChange EssFiniteType
  证明: .mk respectsIso fun R S T _ _ _ _ _ h => by
    rw [essFiniteType_algebraMap] at h ⊢
    infer_instance

Depends on / 依赖: essFiniteType_algebraMap, infer_instance, respectsIso
-/
lemma isStableUnderBaseChange : IsStableUnderBaseChange EssFiniteType :=
  .mk respectsIso fun R S T _ _ _ _ _ h => by
    rw [essFiniteType_algebraMap] at h ⊢
    infer_instance

/--
lemma `holdsForLocalization` / 引理 `holdsForLocalization`

English:
lemma holdsForLocalization
  statement: HoldsForLocalization EssFiniteType
  proof: by
  introv R _
  rw [essFiniteType_algebraMap]
  exact .of_isLocalization _ M

中文:
引理 holdsForLocalization
  结论: HoldsForLocalization EssFiniteType
  证明: by
  introv R _
  rw [essFiniteType_algebraMap]
  exact .of_isLocalization _ M

Depends on / 依赖: essFiniteType_algebraMap, introv, of_isLocalization
-/
lemma holdsForLocalization : HoldsForLocalization EssFiniteType := by
  introv R _
  rw [essFiniteType_algebraMap]
  exact .of_isLocalization _ M

/--
lemma `residueFieldMap` / 引理 `residueFieldMap`

English:
lemma residueFieldMap
  statement: {f : R ->+* S} [IsLocalRing R] [IsLocalRing S] [IsLocalHom f]
  proof: by
  refine .of_comp (IsLocalRing.residue R) ?_
  rw [IsLocalRing.ResidueField.map_comp_residue]
  exact .comp hf (FiniteType.of_surjective _ <| IsLocalRing.residue_surjective).essFiniteType

中文:
引理 residueFieldMap
  结论: {f : R ->+* S} [IsLocalRing R] [IsLocalRing S] [IsLocalHom f]
  证明: by
  refine .of_comp (IsLocalRing.residue R) ?_
  rw [IsLocalRing.ResidueField.map_comp_residue]
  exact .comp hf (FiniteType.of_surjective _ <| IsLocalRing.residue_surjective).essFiniteType

Depends on / 依赖: FiniteType, FiniteType.of_surjective, IsLocalRing, IsLocalRing.ResidueField.map_comp_residue, IsLocalRing.residue, IsLocalRing.residue_surjective, ResidueField, essFiniteType, map_comp_residue, of_comp, of_surjective, residue, residue_surjective
-/
lemma residueFieldMap {f : R ->+* S} [IsLocalRing R] [IsLocalRing S] [IsLocalHom f]
    (hf : f.EssFiniteType) :
    (IsLocalRing.ResidueField.map f).EssFiniteType := by
  refine .of_comp (IsLocalRing.residue R) ?_
  rw [IsLocalRing.ResidueField.map_comp_residue]
  exact .comp hf (FiniteType.of_surjective _ <| IsLocalRing.residue_surjective).essFiniteType

end RingHom.EssFiniteType
