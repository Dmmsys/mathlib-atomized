/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.Tactic.Algebraize

/-!
# Standard smooth ring homomorphisms

In this file we define standard smooth ring homomorphisms and show their
meta properties.

## Main definitions

- `RingHom.IsStandardSmooth`: A ring homomorphism `R →+* S` is standard smooth if `S` is standard
  smooth as `R`-algebra.
- `RingHom.IsStandardSmoothOfRelativeDimension n`: A ring homomorphism `R →+* S` is standard
  smooth of relative dimension `n` if `S` is standard smooth of relative dimension `n` as
  `R`-algebra.

## Notes

This contribution was created as part of the AIM workshop "Formalizing algebraic geometry"
in June 2024.

-/

@[expose] public section
universe t t' w w' u v

variable (n m : Nat)

open TensorProduct

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring homomorphism `R →+* S` is standard smooth if `S` is standard smooth as `R`-algebra. -/
@[algebraize RingHom.IsStandardSmooth.toAlgebra]
/--
Definition of `IsStandardSmooth` / `IsStandardSmooth` 的定义

English:
definition IsStandardSmooth
  signature: (f : R ->+* S)
  body: @Algebra.IsStandardSmooth _ _ _ _ f.toAlgebra

中文:
定义 是StandardSmooth
  签名: (f : R ->+* S)
  定义体: @Algebra.IsStandardSmooth _ _ _ _ f.toAlgebra

Depends on / 依赖: Algebra, Algebra.IsStandardSmooth, IsStandardSmooth, f.toAlgebra, toAlgebra
-/
def IsStandardSmooth (f : R ->+* S) : Prop :=
  @Algebra.IsStandardSmooth _ _ _ _ f.toAlgebra

/--
lemma `isStandardSmooth_algebraMap` / 引理 `isStandardSmooth_algebraMap`

English:
lemma isStandardSmooth_algebraMap
  given: [Algebra R S]
  proof: by
  rw [RingHom.IsStandardSmooth]; rw [toAlgebra_algebraMap]

中文:
引理 isStandardSmooth_algebraMap
  条件: [代数 R S]
  证明: by
  rw [RingHom.IsStandardSmooth]; rw [toAlgebra_algebraMap]

Depends on / 依赖: IsStandardSmooth, RingHom, RingHom.IsStandardSmooth, toAlgebra_algebraMap
-/
lemma isStandardSmooth_algebraMap [Algebra R S] :
    (algebraMap R S).IsStandardSmooth ↔ Algebra.IsStandardSmooth R S := by
  rw [RingHom.IsStandardSmooth]; rw [toAlgebra_algebraMap]

/--
lemma `IsStandardSmooth.toAlgebra` / 引理 `IsStandardSmooth.toAlgebra`

English:
lemma IsStandardSmooth.toAlgebra
  given: {f : R ->+* S} (hf : IsStandardSmooth f)
  proof: hf

中文:
引理 是StandardSmooth.toAlgebra
  条件: {f : R ->+* S} (hf : 是StandardSmooth f)
  证明: hf
-/
lemma IsStandardSmooth.toAlgebra {f : R ->+* S} (hf : IsStandardSmooth f) :
    @Algebra.IsStandardSmooth R S _ _ f.toAlgebra := hf

/-- A ring homomorphism `R →+* S` is standard smooth of relative dimension `n` if
`S` is standard smooth of relative dimension `n` as `R`-algebra. -/
@[algebraize RingHom.IsStandardSmoothOfRelativeDimension.toAlgebra]
/--
Definition of `IsStandardSmoothOfRelativeDimension` / `IsStandardSmoothOfRelativeDimension` 的定义

English:
definition IsStandardSmoothOfRelativeDimension
  signature: (f : R ->+* S)
  body: @Algebra.IsStandardSmoothOfRelativeDimension n _ _ _ _ f.toAlgebra

中文:
定义 是StandardSmoothOfRelativeDimension
  签名: (f : R ->+* S)
  定义体: @Algebra.IsStandardSmoothOfRelativeDimension n _ _ _ _ f.toAlgebra

Depends on / 依赖: Algebra, Algebra.IsStandardSmoothOfRelativeDimension, IsStandardSmoothOfRelativeDimension, f.toAlgebra, toAlgebra
-/
def IsStandardSmoothOfRelativeDimension (f : R ->+* S) : Prop :=
  @Algebra.IsStandardSmoothOfRelativeDimension n _ _ _ _ f.toAlgebra

/--
lemma `isStandardSmoothOfRelativeDimension_algebraMap` / 引理 `isStandardSmoothOfRelativeDimension_algebraMap`

English:
lemma isStandardSmoothOfRelativeDimension_algebraMap
  given: [Algebra R S]
  proof: by
  rw [RingHom.IsStandardSmoothOfRelativeDimension]; rw [toAlgebra_algebraMap]

中文:
引理 isStandardSmoothOfRelativeDimension_algebraMap
  条件: [代数 R S]
  证明: by
  rw [RingHom.IsStandardSmoothOfRelativeDimension]; rw [toAlgebra_algebraMap]

Depends on / 依赖: IsStandardSmoothOfRelativeDimension, RingHom, RingHom.IsStandardSmoothOfRelativeDimension, toAlgebra_algebraMap
-/
lemma isStandardSmoothOfRelativeDimension_algebraMap [Algebra R S] :
    (algebraMap R S).IsStandardSmoothOfRelativeDimension n ↔
      Algebra.IsStandardSmoothOfRelativeDimension n R S := by
  rw [RingHom.IsStandardSmoothOfRelativeDimension]; rw [toAlgebra_algebraMap]

/--
lemma `IsStandardSmoothOfRelativeDimension.toAlgebra` / 引理 `IsStandardSmoothOfRelativeDimension.toAlgebra`

English:
lemma IsStandardSmoothOfRelativeDimension.toAlgebra
  statement: {f : R ->+* S}
  proof: hf

中文:
引理 是StandardSmoothOfRelativeDimension.toAlgebra
  结论: {f : R ->+* S}
  证明: hf
-/
lemma IsStandardSmoothOfRelativeDimension.toAlgebra {f : R ->+* S}
    (hf : IsStandardSmoothOfRelativeDimension n f) :
    @Algebra.IsStandardSmoothOfRelativeDimension n R S _ _ f.toAlgebra := hf

/--
lemma `IsStandardSmoothOfRelativeDimension.isStandardSmooth` / 引理 `IsStandardSmoothOfRelativeDimension.isStandardSmooth`

English:
lemma IsStandardSmoothOfRelativeDimension.isStandardSmooth
  statement: (f : R ->+* S)
  proof: by
  algebraize [f]
  exact Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n

中文:
引理 是StandardSmoothOfRelativeDimension.isStandardSmooth
  结论: (f : R ->+* S)
  证明: by
  algebraize [f]
  exact Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n

Depends on / 依赖: Algebra, Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth, IsStandardSmoothOfRelativeDimension, algebraize, isStandardSmooth
-/
lemma IsStandardSmoothOfRelativeDimension.isStandardSmooth (f : R ->+* S)
    (hf : IsStandardSmoothOfRelativeDimension n f) :
    IsStandardSmooth f := by
  algebraize [f]
  exact Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n

variable {n m}

variable (R) in
/--
lemma `IsStandardSmoothOfRelativeDimension.id` / 引理 `IsStandardSmoothOfRelativeDimension.id`

English:
lemma IsStandardSmoothOfRelativeDimension.id
  proof: Algebra.IsStandardSmoothOfRelativeDimension.id R

中文:
引理 是StandardSmoothOfRelativeDimension.id
  证明: Algebra.IsStandardSmoothOfRelativeDimension.id R

Depends on / 依赖: Algebra, Algebra.IsStandardSmoothOfRelativeDimension.id, IsStandardSmoothOfRelativeDimension
-/
lemma IsStandardSmoothOfRelativeDimension.id :
    IsStandardSmoothOfRelativeDimension 0 (RingHom.id R) :=
  Algebra.IsStandardSmoothOfRelativeDimension.id R

/--
lemma `IsStandardSmoothOfRelativeDimension.equiv` / 引理 `IsStandardSmoothOfRelativeDimension.equiv`

English:
lemma IsStandardSmoothOfRelativeDimension.equiv
  given: (e : R ≃+* S)
  proof: by
  algebraize [e.toRingHom]
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective e.bijective

中文:
引理 是StandardSmoothOfRelativeDimension.equiv
  条件: (e : R ≃+* S)
  证明: by
  algebraize [e.toRingHom]
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective e.bijective

Depends on / 依赖: Algebra, Algebra.IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective, IsStandardSmoothOfRelativeDimension, algebraize, bijective, e.bijective, e.toRingHom, of_algebraMap_bijective, toRingHom
-/
lemma IsStandardSmoothOfRelativeDimension.equiv (e : R ≃+* S) :
    IsStandardSmoothOfRelativeDimension 0 (e : R ->+* S) := by
  algebraize [e.toRingHom]
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective e.bijective

variable {T : Type*} [CommRing T]

/--
lemma `IsStandardSmooth.comp` / 引理 `IsStandardSmooth.comp`

English:
lemma IsStandardSmooth.comp
  statement: {g : S ->+* T} {f : R ->+* S}
  proof: by
  rw [IsStandardSmooth]
  algebraize [f, g, (g.comp f)]
  exact Algebra.IsStandardSmooth.trans R S T

中文:
引理 是StandardSmooth.comp
  结论: {g : S ->+* T} {f : R ->+* S}
  证明: by
  rw [IsStandardSmooth]
  algebraize [f, g, (g.comp f)]
  exact Algebra.IsStandardSmooth.trans R S T

Depends on / 依赖: Algebra, Algebra.IsStandardSmooth.trans, IsStandardSmooth, algebraize, g.comp
-/
lemma IsStandardSmooth.comp {g : S ->+* T} {f : R ->+* S}
    (hg : IsStandardSmooth g) (hf : IsStandardSmooth f) :
    IsStandardSmooth (g.comp f) := by
  rw [IsStandardSmooth]
  algebraize [f, g, (g.comp f)]
  exact Algebra.IsStandardSmooth.trans R S T

/--
lemma `IsStandardSmoothOfRelativeDimension.comp` / 引理 `IsStandardSmoothOfRelativeDimension.comp`

English:
lemma IsStandardSmoothOfRelativeDimension.comp
  statement: {g : S ->+* T} {f : R ->+* S}
  proof: by
  rw [IsStandardSmoothOfRelativeDimension]
  algebraize [f, g, (g.comp f)]
  exact Algebra.IsStandardSmoothOfRelativeDimension.trans m n R S T

中文:
引理 是StandardSmoothOfRelativeDimension.comp
  结论: {g : S ->+* T} {f : R ->+* S}
  证明: by
  rw [IsStandardSmoothOfRelativeDimension]
  algebraize [f, g, (g.comp f)]
  exact Algebra.IsStandardSmoothOfRelativeDimension.trans m n R S T

Depends on / 依赖: Algebra, Algebra.IsStandardSmoothOfRelativeDimension.trans, IsStandardSmoothOfRelativeDimension, algebraize, g.comp
-/
lemma IsStandardSmoothOfRelativeDimension.comp {g : S ->+* T} {f : R ->+* S}
    (hg : IsStandardSmoothOfRelativeDimension n g)
    (hf : IsStandardSmoothOfRelativeDimension m f) :
    IsStandardSmoothOfRelativeDimension (n + m) (g.comp f) := by
  rw [IsStandardSmoothOfRelativeDimension]
  algebraize [f, g, (g.comp f)]
  exact Algebra.IsStandardSmoothOfRelativeDimension.trans m n R S T

/--
lemma `isStandardSmooth_stableUnderComposition` / 引理 `isStandardSmooth_stableUnderComposition`

English:
lemma isStandardSmooth_stableUnderComposition
  proof: fun _ _ _ _ _ _ _ _ hf hg => hg.comp hf

中文:
引理 isStandardSmooth_stableUnderComposition
  证明: fun _ _ _ _ _ _ _ _ hf hg => hg.comp hf

Depends on / 依赖: hg.comp
-/
lemma isStandardSmooth_stableUnderComposition :
    StableUnderComposition @IsStandardSmooth :=
  fun _ _ _ _ _ _ _ _ hf hg => hg.comp hf

/--
lemma `isStandardSmooth_respectsIso` / 引理 `isStandardSmooth_respectsIso`

English:
lemma isStandardSmooth_respectsIso
  statement: RespectsIso @IsStandardSmooth
  proof: by
  apply isStandardSmooth_stableUnderComposition.respectsIso
  introv
  exact (IsStandardSmoothOfRelativeDimension.equiv e).isStandardSmooth

中文:
引理 isStandardSmooth_respectsIso
  结论: RespectsIso @是StandardSmooth
  证明: by
  apply isStandardSmooth_stableUnderComposition.respectsIso
  introv
  exact (IsStandardSmoothOfRelativeDimension.equiv e).isStandardSmooth

Depends on / 依赖: IsStandardSmoothOfRelativeDimension, IsStandardSmoothOfRelativeDimension.equiv, introv, isStandardSmooth, isStandardSmooth_stableUnderComposition, isStandardSmooth_stableUnderComposition.respectsIso, respectsIso
-/
lemma isStandardSmooth_respectsIso : RespectsIso @IsStandardSmooth := by
  apply isStandardSmooth_stableUnderComposition.respectsIso
  introv
  exact (IsStandardSmoothOfRelativeDimension.equiv e).isStandardSmooth

/--
lemma `isStandardSmoothOfRelativeDimension_respectsIso` / 引理 `isStandardSmoothOfRelativeDimension_respectsIso`

English:
lemma isStandardSmoothOfRelativeDimension_respectsIso
  proof: by
    rw [← zero_add n]
    exact (IsStandardSmoothOfRelativeDimension.equiv e).comp hf
  right {R S T _ _ _} f e hf := by
    rw [← add_zero n]
    exact hf.comp (IsStandardSmoothOfRelativeDimension.equiv e)

中文:
引理 isStandardSmoothOfRelativeDimension_respectsIso
  证明: by
    rw [← zero_add n]
    exact (IsStandardSmoothOfRelativeDimension.equiv e).comp hf
  right {R S T _ _ _} f e hf := by
    rw [← add_zero n]
    exact hf.comp (IsStandardSmoothOfRelativeDimension.equiv e)

Depends on / 依赖: IsStandardSmoothOfRelativeDimension, IsStandardSmoothOfRelativeDimension.equiv, add_zero, hf.comp, zero_add
-/
lemma isStandardSmoothOfRelativeDimension_respectsIso :
    RespectsIso (@IsStandardSmoothOfRelativeDimension n) where
  left {R S T _ _ _} f e hf := by
    rw [← zero_add n]
    exact (IsStandardSmoothOfRelativeDimension.equiv e).comp hf
  right {R S T _ _ _} f e hf := by
    rw [← add_zero n]
    exact hf.comp (IsStandardSmoothOfRelativeDimension.equiv e)

/--
lemma `isStandardSmooth_isStableUnderBaseChange` / 引理 `isStandardSmooth_isStableUnderBaseChange`

English:
lemma isStandardSmooth_isStableUnderBaseChange
  proof: by
  apply IsStableUnderBaseChange.mk
  · exact isStandardSmooth_respectsIso
  · introv h
    replace h : Algebra.IsStandardSmooth R T := by
      rw [RingHom.IsStandardSmooth] at h; convert! h; ext; simp_rw [Algebra.smul_def]; rfl
    suffices Algebra.IsStandardSmooth S (S otimes[R] T) by
      rw 

中文:
引理 isStandardSmooth_isStableUnderBaseChange
  证明: by
  apply IsStableUnderBaseChange.mk
  · exact isStandardSmooth_respectsIso
  · introv h
    replace h : Algebra.IsStandardSmooth R T := by
      rw [RingHom.IsStandardSmooth] at h; convert! h; ext; simp_rw [Algebra.smul_def]; rfl
    suffices Algebra.IsStandardSmooth S (S otimes[R] T) by
      rw 

Depends on / 依赖: Algebra, Algebra.IsStandardSmooth, Algebra.smul_def, IsStableUnderBaseChange, IsStableUnderBaseChange.mk, IsStandardSmooth, RingHom, RingHom.IsStandardSmooth, convert, infer_instance, introv, isStandardSmooth_respectsIso, otimes, replace, simp_rw, smul_def
-/
lemma isStandardSmooth_isStableUnderBaseChange :
    IsStableUnderBaseChange @IsStandardSmooth := by
  apply IsStableUnderBaseChange.mk
  · exact isStandardSmooth_respectsIso
  · introv h
    replace h : Algebra.IsStandardSmooth R T := by
      rw [RingHom.IsStandardSmooth] at h; convert! h; ext; simp_rw [Algebra.smul_def]; rfl
    suffices Algebra.IsStandardSmooth S (S otimes[R] T) by
      rw [RingHom.IsStandardSmooth]; convert! this; ext; simp_rw [Algebra.smul_def]; rfl
    infer_instance

variable (n)

/--
lemma `isStandardSmoothOfRelativeDimension_isStableUnderBaseChange` / 引理 `isStandardSmoothOfRelativeDimension_isStableUnderBaseChange`

English:
lemma isStandardSmoothOfRelativeDimension_isStableUnderBaseChange
  proof: by
  apply IsStableUnderBaseChange.mk
  · exact isStandardSmoothOfRelativeDimension_respectsIso
  · introv h
    replace h : Algebra.IsStandardSmoothOfRelativeDimension n R T := by
      rw [RingHom.IsStandardSmoothOfRelativeDimension] at h
      convert! h; ext; simp_rw [Algebra.smul_def]; rfl
    

中文:
引理 isStandardSmoothOfRelativeDimension_isStableUnderBaseChange
  证明: by
  apply IsStableUnderBaseChange.mk
  · exact isStandardSmoothOfRelativeDimension_respectsIso
  · introv h
    replace h : Algebra.IsStandardSmoothOfRelativeDimension n R T := by
      rw [RingHom.IsStandardSmoothOfRelativeDimension] at h
      convert! h; ext; simp_rw [Algebra.smul_def]; rfl
    

Depends on / 依赖: Algebra, Algebra.IsStandardSmoothOfRelativeDimension, Algebra.smul_def, IsStableUnderBaseChange, IsStableUnderBaseChange.mk, IsStandardSmoothOfRelativeDimension, RingHom, RingHom.IsStandardSmoothOfRelativeDimension, convert, infer_instance, introv, isStandardSmoothOfRelativeDimension_respectsIso, otimes, replace, simp_rw, smul_def
-/
lemma isStandardSmoothOfRelativeDimension_isStableUnderBaseChange :
    IsStableUnderBaseChange (@IsStandardSmoothOfRelativeDimension n) := by
  apply IsStableUnderBaseChange.mk
  · exact isStandardSmoothOfRelativeDimension_respectsIso
  · introv h
    replace h : Algebra.IsStandardSmoothOfRelativeDimension n R T := by
      rw [RingHom.IsStandardSmoothOfRelativeDimension] at h
      convert! h; ext; simp_rw [Algebra.smul_def]; rfl
    suffices Algebra.IsStandardSmoothOfRelativeDimension n S (S otimes[R] T) by
      rw [RingHom.IsStandardSmoothOfRelativeDimension]
      convert! this; ext; simp_rw [Algebra.smul_def]; rfl
    infer_instance

/--
lemma `IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway` / 引理 `IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway`

English:
lemma IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway
  statement: {Rᵣ : Type*} [CommRing Rᵣ]
  proof: by
  have : (algebraMap R Rᵣ).toAlgebra = ‹Algebra R Rᵣ› := by
    ext
    rw [Algebra.smul_def]
    rfl
  rw [IsStandardSmoothOfRelativeDimension]; rw [this]
  exact Algebra.IsStandardSmoothOfRelativeDimension.localization_away r

中文:
引理 是StandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway
  结论: {Rᵣ : 类型} [交换环 Rᵣ]
  证明: by
  have : (algebraMap R Rᵣ).toAlgebra = ‹Algebra R Rᵣ› := by
    ext
    rw [Algebra.smul_def]
    rfl
  rw [IsStandardSmoothOfRelativeDimension]; rw [this]
  exact Algebra.IsStandardSmoothOfRelativeDimension.localization_away r

Depends on / 依赖: Algebra, Algebra.IsStandardSmoothOfRelativeDimension.localization_away, Algebra.smul_def, IsStandardSmoothOfRelativeDimension, algebraMap, localization_away, smul_def, toAlgebra
-/
lemma IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway {Rᵣ : Type*} [CommRing Rᵣ]
    [Algebra R Rᵣ] (r : R) [IsLocalization.Away r Rᵣ] :
    IsStandardSmoothOfRelativeDimension 0 (algebraMap R Rᵣ) := by
  have : (algebraMap R Rᵣ).toAlgebra = ‹Algebra R Rᵣ› := by
    ext
    rw [Algebra.smul_def]
    rfl
  rw [IsStandardSmoothOfRelativeDimension]; rw [this]
  exact Algebra.IsStandardSmoothOfRelativeDimension.localization_away r

/--
lemma `isStandardSmooth_localizationPreserves` / 引理 `isStandardSmooth_localizationPreserves`

English:
lemma isStandardSmooth_localizationPreserves
  statement: LocalizationPreserves IsStandardSmooth
  proof: isStandardSmooth_isStableUnderBaseChange.localizationPreserves

中文:
引理 isStandardSmooth_localizationPreserves
  结论: LocalizationPreserves 是StandardSmooth
  证明: isStandardSmooth_isStableUnderBaseChange.localizationPreserves

Depends on / 依赖: isStandardSmooth_isStableUnderBaseChange, isStandardSmooth_isStableUnderBaseChange.localizationPreserves, localizationPreserves
-/
lemma isStandardSmooth_localizationPreserves : LocalizationPreserves IsStandardSmooth :=
  isStandardSmooth_isStableUnderBaseChange.localizationPreserves

/--
lemma `isStandardSmoothOfRelativeDimension_localizationPreserves` / 引理 `isStandardSmoothOfRelativeDimension_localizationPreserves`

English:
lemma isStandardSmoothOfRelativeDimension_localizationPreserves
  proof: (isStandardSmoothOfRelativeDimension_isStableUnderBaseChange n).localizationPreserves

中文:
引理 isStandardSmoothOfRelativeDimension_localizationPreserves
  证明: (isStandardSmoothOfRelativeDimension_isStableUnderBaseChange n).localizationPreserves

Depends on / 依赖: isStandardSmoothOfRelativeDimension_isStableUnderBaseChange, localizationPreserves
-/
lemma isStandardSmoothOfRelativeDimension_localizationPreserves :
    LocalizationPreserves (IsStandardSmoothOfRelativeDimension n) :=
  (isStandardSmoothOfRelativeDimension_isStableUnderBaseChange n).localizationPreserves

/--
lemma `isStandardSmooth_holdsForLocalizationAway` / 引理 `isStandardSmooth_holdsForLocalizationAway`

English:
lemma isStandardSmooth_holdsForLocalizationAway
  proof: by
  introv R h
  exact (IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway r).isStandardSmooth

中文:
引理 isStandardSmooth_holdsForLocalizationAway
  证明: by
  introv R h
  exact (IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway r).isStandardSmooth

Depends on / 依赖: IsStandardSmoothOfRelativeDimension, IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway, algebraMap_isLocalizationAway, introv, isStandardSmooth
-/
lemma isStandardSmooth_holdsForLocalizationAway :
    HoldsForLocalizationAway IsStandardSmooth := by
  introv R h
  exact (IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway r).isStandardSmooth

/--
lemma `isStandardSmoothOfRelativeDimension_holdsForLocalizationAway` / 引理 `isStandardSmoothOfRelativeDimension_holdsForLocalizationAway`

English:
lemma isStandardSmoothOfRelativeDimension_holdsForLocalizationAway
  proof: by
  introv R h
  exact IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway r

中文:
引理 isStandardSmoothOfRelativeDimension_holdsForLocalizationAway
  证明: by
  introv R h
  exact IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway r

Depends on / 依赖: IsStandardSmoothOfRelativeDimension, IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway, NoncompactSpace, algebraMap_isLocalizationAway, introv, nhdsNE_neBot
-/
lemma isStandardSmoothOfRelativeDimension_holdsForLocalizationAway :
    HoldsForLocalizationAway (IsStandardSmoothOfRelativeDimension 0) := by
  introv R h
  exact IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway r

/--
lemma `isStandardSmooth_stableUnderCompositionWithLocalizationAway` / 引理 `isStandardSmooth_stableUnderCompositionWithLocalizationAway`

English:
lemma isStandardSmooth_stableUnderCompositionWithLocalizationAway
  proof: isStandardSmooth_stableUnderComposition.stableUnderCompositionWithLocalizationAway
    isStandardSmooth_holdsForLocalizationAway

中文:
引理 isStandardSmooth_stableUnderCompositionWithLocalizationAway
  证明: isStandardSmooth_stableUnderComposition.stableUnderCompositionWithLocalizationAway
    isStandardSmooth_holdsForLocalizationAway

Depends on / 依赖: isStandardSmooth_holdsForLocalizationAway, isStandardSmooth_stableUnderComposition, isStandardSmooth_stableUnderComposition.stableUnderCompositionWithLocalizationAway, stableUnderCompositionWithLocalizationAway
-/
lemma isStandardSmooth_stableUnderCompositionWithLocalizationAway :
    StableUnderCompositionWithLocalizationAway IsStandardSmooth :=
  isStandardSmooth_stableUnderComposition.stableUnderCompositionWithLocalizationAway
    isStandardSmooth_holdsForLocalizationAway

/--
lemma `isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway` / 引理 `isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway`

English:
lemma isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway
  proof: have : (algebraMap R S).IsStandardSmoothOfRelativeDimension 0 :=
      IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway r
    add_zero n ▸ IsStandardSmoothOfRelativeDimension.comp hf this
  right _ S T _ _ _ _ s _ _ hf :=
    have : (algebraMap S T).IsStandardSmoothOfRelativeDimensi

中文:
引理 isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway
  证明: have : (algebraMap R S).IsStandardSmoothOfRelativeDimension 0 :=
      IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway r
    add_zero n ▸ IsStandardSmoothOfRelativeDimension.comp hf this
  right _ S T _ _ _ _ s _ _ hf :=
    have : (algebraMap S T).IsStandardSmoothOfRelativeDimensi

Depends on / 依赖: IsStandardSmoothOfRelativeDimension, IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway, IsStandardSmoothOfRelativeDimension.comp, add_zero, algebraMap, algebraMap_isLocalizationAway, zero_add
-/
lemma isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway :
    StableUnderCompositionWithLocalizationAway (IsStandardSmoothOfRelativeDimension n) where
  left R S _ _ _ _ _ r _ _ hf :=
    have : (algebraMap R S).IsStandardSmoothOfRelativeDimension 0 :=
      IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway r
    add_zero n ▸ IsStandardSmoothOfRelativeDimension.comp hf this
  right _ S T _ _ _ _ s _ _ hf :=
    have : (algebraMap S T).IsStandardSmoothOfRelativeDimension 0 :=
      IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway s
    zero_add n ▸ IsStandardSmoothOfRelativeDimension.comp this hf

set_option backward.isDefEq.respectTransparency false in
variable (R S) in
/--
theorem `_root_.Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial` / 定理 `_root_.Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`

English:
theorem _root_.Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
  proof: by
  classical
  let := Fintype.ofFinite
  obtain ⟨ι, σ, _, _, P, e⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.out (R := R) (S := S) (n := n)
  let e₀ : σ oplus Fin n ≃ ι := ((Equiv.ofInjective _ P.map_inj).sumCongr
      (Finite.equivFinOfCardEq (by rw [Nat.card_coe_set_eq, Set.ncard_compl

中文:
定理 _root_.代数.是StandardSmoothOfRelativeDimension.存在_etale_mvPolynomial
  证明: by
  classical
  let := Fintype.ofFinite
  obtain ⟨ι, σ, _, _, P, e⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.out (R := R) (S := S) (n := n)
  let e₀ : σ oplus Fin n ≃ ι := ((Equiv.ofInjective _ P.map_inj).sumCongr
      (Finite.equivFinOfCardEq (by rw [Nat.card_coe_set_eq, Set.ncard_compl

Depends on / 依赖: Algebra, Algebra.IsStandardSmoothOfRelativeDimension.out, Algebra.Presentation.dimension, Equiv.Set.sumCompl, Equiv.ofInjective, Finite, Finite.equivFinOfCardEq, Fintype, Fintype.ofFinite, IsStandardSmoothOfRelativeDimension, MvPolynomial, MvPolynomial.sumAlgEquiv, Nat.card_coe_set_eq, P.Ring, P.map_inj, Presentation, Set.ncard_compl, Set.ncard_range_of_injective, card_coe_set_eq, classical
-/
theorem _root_.Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    [Algebra R S] [Algebra.IsStandardSmoothOfRelativeDimension n R S] :
    exists g : MvPolynomial (Fin n) R ->ₐ[R] S, g.Etale := by
  classical
  let := Fintype.ofFinite
  obtain ⟨ι, σ, _, _, P, e⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.out (R := R) (S := S) (n := n)
  let e₀ : σ oplus Fin n ≃ ι := ((Equiv.ofInjective _ P.map_inj).sumCongr
      (Finite.equivFinOfCardEq (by rw [Nat.card_coe_set_eq, Set.ncard_compl,
        Set.ncard_range_of_injective P.map_inj, ← e, Algebra.Presentation.dimension])).symm).trans
      (Equiv.Set.sumCompl _)
  let e : MvPolynomial σ (MvPolynomial (Fin n) R) ≃ₐ[R] P.Ring :=
    (MvPolynomial.sumAlgEquiv R _ _).symm.trans (MvPolynomial.renameEquiv _ e₀)
  let φ := e.toAlgHom.comp (IsScalarTower.toAlgHom _ (MvPolynomial (Fin n) R) _)
  algebraize [φ.toRingHom, (algebraMap P.Ring S).comp φ.toRingHom]
  have := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have : IsScalarTower R (MvPolynomial (Fin n) R) S := .to₁₂₄ _ _ P.Ring _
  refine ⟨IsScalarTower.toAlgHom _ _ _, ?_⟩
  have H : (MvPolynomial.aeval fun x => (algebraMap P.Ring S) (e (MvPolynomial.X x))).toRingHom =
      (algebraMap P.Ring S).comp e.toRingHom := by
    ext
    · simp [e, IsScalarTower.algebraMap_eq R (MvPolynomial (Fin n) R) S]
    · simp [e, @RingHom.algebraMap_toAlgebra (MvPolynomial (Fin n) R) S, φ]
    · simp [e]
  let P' : Algebra.PreSubmersivePresentation (MvPolynomial (Fin n) R) S σ σ :=
  { toGenerators := .ofSurjective (algebraMap _ _ <| e <| .X ·) <| by
      convert! P.algebraMap_surjective.comp e.surjective
      exact congr($H)
    relation := e.symm ∘ P.relation
    span_range_relation_eq_ker := by
      rw [Set.range_comp]; rw [← AlgEquiv.coe_ringEquiv e.symm]; rw [AlgEquiv.symm_toRingEquiv]; rw [← Ideal.map_span]; rw [P.span_range_relation_eq_ker]; rw [Ideal.map_symm]
      exact congr(RingHom.ker $H).symm
    map := _
    map_inj := Function.injective_id }
  let P' : Algebra.SubmersivePresentation (MvPolynomial (Fin n) R) S σ σ :=
  { __ := P'
    jacobian_isUnit := by
      convert! P.jacobian_isUnit using 1
      simp_rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, map_det]
      congr 1
      ext i j
      trans algebraMap P.Ring S (e ((e.symm (P.relation j)).pderiv i))
      · simpa [Algebra.PreSubmersivePresentation.jacobiMatrix_apply, P',
Algebra.Generators.ofSurjective] using congr( H _)
      suffices e ((e.symm (P.relation j)).pderiv i) = (P.relation j).pderiv (P.map i) by
        simp [Algebra.PreSubmersivePresentation.jacobiMatrix_apply, this]
      simp [e, ← MvPolynomial.pderiv_rename e₀.injective, show e₀ (Sum.inl i) = P.map i from rfl] }
  exact etale_algebraMap.mpr (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mpr
    ⟨_, _, _, inferInstance, P', by simp [Algebra.Presentation.dimension]⟩)

/--
theorem `IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial` / 定理 `IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`

English:
theorem IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
  proof: by
  algebraize [f]
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n R S
  exact ⟨_, g.comp_algebraMap, hg⟩

中文:
定理 是StandardSmoothOfRelativeDimension.存在_etale_mvPolynomial
  证明: by
  algebraize [f]
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n R S
  exact ⟨_, g.comp_algebraMap, hg⟩

Depends on / 依赖: Algebra, Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial, IsStandardSmoothOfRelativeDimension, algebraize, comp_algebraMap, exists_etale_mvPolynomial, g.comp_algebraMap
-/
theorem IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    {f : R ->+* S} {n : Nat} (hf : f.IsStandardSmoothOfRelativeDimension n) :
    exists g : MvPolynomial (Fin n) R ->+* S, g.comp MvPolynomial.C = f ∧ g.Etale := by
  algebraize [f]
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n R S
  exact ⟨_, g.comp_algebraMap, hg⟩

/--
theorem `IsStandardSmooth.exists_etale_mvPolynomial` / 定理 `IsStandardSmooth.exists_etale_mvPolynomial`

English:
theorem IsStandardSmooth.exists_etale_mvPolynomial
  proof: by
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := hf
  let := f.toAlgebra
  exact ⟨_, RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    ⟨_, _, _, ‹_›, P, rfl⟩⟩

中文:
定理 是StandardSmooth.存在_etale_mvPolynomial
  证明: by
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := hf
  let := f.toAlgebra
  exact ⟨_, RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    ⟨_, _, _, ‹_›, P, rfl⟩⟩

Depends on / 依赖: IsStandardSmoothOfRelativeDimension, RingHom, RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial, exists_etale_mvPolynomial, f.toAlgebra, toAlgebra
-/
theorem IsStandardSmooth.exists_etale_mvPolynomial
    {f : R ->+* S} (hf : f.IsStandardSmooth) :
    exists n, exists g : MvPolynomial (Fin n) R ->+* S, g.comp MvPolynomial.C = f ∧ g.Etale := by
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := hf
  let := f.toAlgebra
  exact ⟨_, RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    ⟨_, _, _, ‹_›, P, rfl⟩⟩

end RingHom
