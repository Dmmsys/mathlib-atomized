/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.Smooth.Locus

/-!
# Smooth ring homomorphisms

In this file we define smooth ring homomorphisms and show their meta properties.

-/

@[expose] public section

universe u

variable {R S : Type*} [CommRing R] [CommRing S]

open TensorProduct

namespace RingHom

/-- A ring homomorphism `f : R →+* S` is formally smooth
if `S` is formally smooth as an `R` algebra. -/
@[algebraize RingHom.FormallySmooth.toAlgebra]
/--
Definition of `FormallySmooth` / `FormallySmooth` 的定义

English:
definition FormallySmooth
  signature: (f : R ->+* S)
  body: letI := f.toAlgebra
  Algebra.FormallySmooth R S

中文:
定义 形式光滑
  签名: (f : R ->+* S)
  定义体: letI := f.toAlgebra
  Algebra.FormallySmooth R S

Depends on / 依赖: Algebra, Algebra.FormallySmooth, FormallySmooth, f.toAlgebra, toAlgebra
-/
def FormallySmooth (f : R ->+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.FormallySmooth R S

/--
lemma `FormallySmooth.toAlgebra` / 引理 `FormallySmooth.toAlgebra`

English:
lemma FormallySmooth.toAlgebra
  given: {f : R ->+* S} (hf : FormallySmooth f)
  proof: hf

中文:
引理 形式光滑.toAlgebra
  条件: {f : R ->+* S} (hf : 形式光滑 f)
  证明: hf
-/
lemma FormallySmooth.toAlgebra {f : R ->+* S} (hf : FormallySmooth f) :
    @Algebra.FormallySmooth R S _ _ f.toAlgebra := hf

/--
lemma `formallySmooth_algebraMap` / 引理 `formallySmooth_algebraMap`

English:
lemma formallySmooth_algebraMap
  given: [Algebra R S]
  proof: by
  rw [FormallySmooth]; rw [toAlgebra_algebraMap]

中文:
引理 formallySmooth_algebraMap
  条件: [代数 R S]
  证明: by
  rw [FormallySmooth]; rw [toAlgebra_algebraMap]

Depends on / 依赖: FormallySmooth, toAlgebra_algebraMap
-/
lemma formallySmooth_algebraMap [Algebra R S] :
    (algebraMap R S).FormallySmooth ↔ Algebra.FormallySmooth R S := by
  rw [FormallySmooth]; rw [toAlgebra_algebraMap]

/--
lemma `FormallySmooth.comp` / 引理 `FormallySmooth.comp`

English:
lemma FormallySmooth.comp
  statement: {T : Type*} [CommRing T] {f : R ->+* S} {g : S ->+* T}
  proof: by
  algebraize [f, g, g.comp f]
  exact Algebra.FormallySmooth.comp R S T

中文:
引理 形式光滑.comp
  结论: {T : 类型} [交换环 T] {f : R ->+* S} {g : S ->+* T}
  证明: by
  algebraize [f, g, g.comp f]
  exact Algebra.FormallySmooth.comp R S T

Depends on / 依赖: Algebra, Algebra.FormallySmooth.comp, FormallySmooth, algebraize, g.comp
-/
lemma FormallySmooth.comp {T : Type*} [CommRing T] {f : R ->+* S} {g : S ->+* T}
    (hf : f.FormallySmooth) (hg : g.FormallySmooth) : (g.comp f).FormallySmooth := by
  algebraize [f, g, g.comp f]
  exact Algebra.FormallySmooth.comp R S T

/--
lemma `FormallySmooth.of_bijective` / 引理 `FormallySmooth.of_bijective`

English:
lemma FormallySmooth.of_bijective
  given: {f : R ->+* S} (hf : Function.Bijective f)
  proof: by
  algebraize [f]
  exact Algebra.FormallySmooth.of_equiv (AlgEquiv.ofBijective (Algebra.ofId R S) hf)

中文:
引理 形式光滑.of_bijective
  条件: {f : R ->+* S} (hf : 函数.双射 f)
  证明: by
  algebraize [f]
  exact Algebra.FormallySmooth.of_equiv (AlgEquiv.ofBijective (Algebra.ofId R S) hf)

Depends on / 依赖: AlgEquiv, AlgEquiv.ofBijective, Algebra, Algebra.FormallySmooth.of_equiv, Algebra.ofId, FormallySmooth, algebraize, ofBijective, of_equiv
-/
lemma FormallySmooth.of_bijective {f : R ->+* S} (hf : Function.Bijective f) :
    f.FormallySmooth := by
  algebraize [f]
  exact Algebra.FormallySmooth.of_equiv (AlgEquiv.ofBijective (Algebra.ofId R S) hf)

/--
lemma `FormallySmooth.holdsForLocalizationAway` / 引理 `FormallySmooth.holdsForLocalizationAway`

English:
lemma FormallySmooth.holdsForLocalizationAway
  statement: HoldsForLocalizationAway @FormallySmooth
  proof: fun _ _ _ _ _ r _ => formallySmooth_algebraMap.mpr .of_isLocalization (.powers r)

中文:
引理 形式光滑.holdsForLocalizationAway
  结论: HoldsForLocalizationAway @形式光滑
  证明: fun _ _ _ _ _ r _ => formallySmooth_algebraMap.mpr .of_isLocalization (.powers r)

Depends on / 依赖: formallySmooth_algebraMap, formallySmooth_algebraMap.mpr, of_isLocalization, powers
-/
lemma FormallySmooth.holdsForLocalizationAway : HoldsForLocalizationAway @FormallySmooth :=
fun _ _ _ _ _ r _ => formallySmooth_algebraMap.mpr .of_isLocalization (.powers r)

/--
lemma `FormallySmooth.stableUnderComposition` / 引理 `FormallySmooth.stableUnderComposition`

English:
lemma FormallySmooth.stableUnderComposition
  statement: StableUnderComposition @FormallySmooth
  proof: fun _ _ _ _ _ _ _ _ hf hg => hf.comp hg

中文:
引理 形式光滑.stableUnderComposition
  结论: StableUnderComposition @形式光滑
  证明: fun _ _ _ _ _ _ _ _ hf hg => hf.comp hg

Depends on / 依赖: hf.comp
-/
lemma FormallySmooth.stableUnderComposition : StableUnderComposition @FormallySmooth :=
  fun _ _ _ _ _ _ _ _ hf hg => hf.comp hg

/--
lemma `FormallySmooth.respectsIso` / 引理 `FormallySmooth.respectsIso`

English:
lemma FormallySmooth.respectsIso
  statement: RespectsIso @FormallySmooth
  proof: stableUnderComposition.respectsIso fun e => holdsForLocalizationAway.of_bijective _ _ e.bijective

中文:
引理 形式光滑.respectsIso
  结论: RespectsIso @形式光滑
  证明: stableUnderComposition.respectsIso fun e => holdsForLocalizationAway.of_bijective _ _ e.bijective

Depends on / 依赖: bijective, e.bijective, holdsForLocalizationAway, holdsForLocalizationAway.of_bijective, of_bijective, respectsIso, stableUnderComposition, stableUnderComposition.respectsIso
-/
lemma FormallySmooth.respectsIso : RespectsIso @FormallySmooth :=
  stableUnderComposition.respectsIso fun e => holdsForLocalizationAway.of_bijective _ _ e.bijective

/--
lemma `FormallySmooth.isStableUnderBaseChange` / 引理 `FormallySmooth.isStableUnderBaseChange`

English:
lemma FormallySmooth.isStableUnderBaseChange
  statement: IsStableUnderBaseChange @FormallySmooth
  proof: by
  refine .mk respectsIso ?_
  introv H
  rw [formallySmooth_algebraMap] at H ⊢
  infer_instance

中文:
引理 形式光滑.isStableUnderBaseChange
  结论: 是StableUnderBaseChange @形式光滑
  证明: by
  refine .mk respectsIso ?_
  introv H
  rw [formallySmooth_algebraMap] at H ⊢
  infer_instance

Depends on / 依赖: formallySmooth_algebraMap, infer_instance, introv, respectsIso
-/
lemma FormallySmooth.isStableUnderBaseChange : IsStableUnderBaseChange @FormallySmooth := by
  refine .mk respectsIso ?_
  introv H
  rw [formallySmooth_algebraMap] at H ⊢
  infer_instance

/--
lemma `FormallySmooth.localizationPreserves` / 引理 `FormallySmooth.localizationPreserves`

English:
lemma FormallySmooth.localizationPreserves
  statement: LocalizationPreserves @FormallySmooth
  proof: isStableUnderBaseChange.localizationPreserves

中文:
引理 形式光滑.localizationPreserves
  结论: LocalizationPreserves @形式光滑
  证明: isStableUnderBaseChange.localizationPreserves

Depends on / 依赖: isStableUnderBaseChange, isStableUnderBaseChange.localizationPreserves, localizationPreserves
-/
lemma FormallySmooth.localizationPreserves : LocalizationPreserves @FormallySmooth :=
  isStableUnderBaseChange.localizationPreserves

/-- A ring homomorphism `f : R →+* S` is smooth if `S` is smooth as an `R` algebra. -/
@[algebraize RingHom.Smooth.toAlgebra]
/--
Definition of `Smooth` / `Smooth` 的定义

English:
definition Smooth
  signature: (f : R ->+* S)
  body: letI : Algebra R S := f.toAlgebra
  Algebra.Smooth R S

中文:
定义 光滑
  签名: (f : R ->+* S)
  定义体: letI : Algebra R S := f.toAlgebra
  Algebra.Smooth R S

Depends on / 依赖: Algebra, Algebra.Smooth, Smooth, f.toAlgebra, toAlgebra
-/
def Smooth (f : R ->+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  Algebra.Smooth R S

/--
lemma `Smooth.toAlgebra` / 引理 `Smooth.toAlgebra`

English:
lemma Smooth.toAlgebra
  given: {f : R ->+* S} (hf : Smooth f)
  proof: hf

中文:
引理 光滑.toAlgebra
  条件: {f : R ->+* S} (hf : 光滑 f)
  证明: hf
-/
lemma Smooth.toAlgebra {f : R ->+* S} (hf : Smooth f) :
    @Algebra.Smooth R _ S _ f.toAlgebra := hf

/--
lemma `smooth_algebraMap` / 引理 `smooth_algebraMap`

English:
lemma smooth_algebraMap
  given: [Algebra R S]
  proof: by
  rw [RingHom.Smooth]; rw [toAlgebra_algebraMap]

中文:
引理 smooth_algebraMap
  条件: [代数 R S]
  证明: by
  rw [RingHom.Smooth]; rw [toAlgebra_algebraMap]

Depends on / 依赖: RingHom, RingHom.Smooth, Smooth, toAlgebra_algebraMap
-/
lemma smooth_algebraMap [Algebra R S] :
    (algebraMap R S).Smooth ↔ Algebra.Smooth R S := by
  rw [RingHom.Smooth]; rw [toAlgebra_algebraMap]

/--
lemma `smooth_def` / 引理 `smooth_def`

English:
lemma smooth_def
  given: {f : R ->+* S}
  statement: f.Smooth ↔ f.FormallySmooth ∧ f.FinitePresentation
  proof: letI := f.toAlgebra
  Algebra.smooth_iff _ _

中文:
引理 smooth_def
  条件: {f : R ->+* S}
  结论: f.光滑 ↔ f.形式光滑 ∧ f.有限呈现
  证明: letI := f.toAlgebra
  Algebra.smooth_iff _ _

Depends on / 依赖: Algebra, Algebra.smooth_iff, f.toAlgebra, smooth_iff, toAlgebra
-/
lemma smooth_def {f : R ->+* S} : f.Smooth ↔ f.FormallySmooth ∧ f.FinitePresentation :=
  letI := f.toAlgebra
  Algebra.smooth_iff _ _

namespace Smooth

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/--
lemma `formallySmooth` / 引理 `formallySmooth`

English:
lemma formallySmooth
  given: {f : R ->+* S} (hf : f.Smooth)
  statement: f.FormallySmooth
  proof: by
  rw [smooth_def] at hf
  exact hf.1

中文:
引理 formallySmooth
  条件: {f : R ->+* S} (hf : f.光滑)
  结论: f.形式光滑
  证明: by
  rw [smooth_def] at hf
  exact hf.1

Depends on / 依赖: smooth_def
-/
lemma formallySmooth {f : R ->+* S} (hf : f.Smooth) : f.FormallySmooth := by
  rw [smooth_def] at hf
  exact hf.1

/--
lemma `finitePresentation` / 引理 `finitePresentation`

English:
lemma finitePresentation
  given: {f : R ->+* S} (hf : f.Smooth)
  statement: f.FinitePresentation
  proof: by
  rw [smooth_def] at hf
  exact hf.2

中文:
引理 finitePresentation
  条件: {f : R ->+* S} (hf : f.光滑)
  结论: f.有限呈现
  证明: by
  rw [smooth_def] at hf
  exact hf.2

Depends on / 依赖: smooth_def
-/
lemma finitePresentation {f : R ->+* S} (hf : f.Smooth) : f.FinitePresentation := by
  rw [smooth_def] at hf
  exact hf.2

/--
lemma `comp` / 引理 `comp`

English:
lemma comp
  given: {f : R ->+* S} {g : S ->+* T} (hf : f.Smooth) (hg : g.Smooth)
  statement: (g.comp f).Smooth
  proof: by
  algebraize [f, g, g.comp f]
  exact Algebra.Smooth.comp R S T

中文:
引理 comp
  条件: {f : R ->+* S} {g : S ->+* T} (hf : f.光滑) (hg : g.光滑)
  结论: (g.comp f).光滑
  证明: by
  algebraize [f, g, g.comp f]
  exact Algebra.Smooth.comp R S T

Depends on / 依赖: Algebra, Algebra.Smooth.comp, Smooth, algebraize, g.comp
-/
lemma comp {f : R ->+* S} {g : S ->+* T} (hf : f.Smooth) (hg : g.Smooth) : (g.comp f).Smooth := by
  algebraize [f, g, g.comp f]
  exact Algebra.Smooth.comp R S T

/--
lemma `stableUnderComposition` / 引理 `stableUnderComposition`

English:
lemma stableUnderComposition
  statement: StableUnderComposition Smooth
  proof: fun _ _ _ _ _ _ _ _ => RingHom.Smooth.comp

中文:
引理 stableUnderComposition
  结论: StableUnderComposition 光滑
  证明: fun _ _ _ _ _ _ _ _ => RingHom.Smooth.comp

Depends on / 依赖: RingHom, RingHom.Smooth.comp, Smooth
-/
lemma stableUnderComposition : StableUnderComposition Smooth :=
  fun _ _ _ _ _ _ _ _ => RingHom.Smooth.comp

/--
lemma `isStableUnderBaseChange` / 引理 `isStableUnderBaseChange`

English:
lemma isStableUnderBaseChange
  statement: IsStableUnderBaseChange Smooth
  proof: by
  convert!
    RingHom.FormallySmooth.isStableUnderBaseChange.and
      RingHom.finitePresentation_isStableUnderBaseChange
  rw [smooth_def]

中文:
引理 isStableUnderBaseChange
  结论: 是StableUnderBaseChange 光滑
  证明: by
  convert!
    RingHom.FormallySmooth.isStableUnderBaseChange.and
      RingHom.finitePresentation_isStableUnderBaseChange
  rw [smooth_def]

Depends on / 依赖: FormallySmooth, RingHom, RingHom.FormallySmooth.isStableUnderBaseChange.and, RingHom.finitePresentation_isStableUnderBaseChange, convert, finitePresentation_isStableUnderBaseChange, isStableUnderBaseChange, smooth_def
-/
lemma isStableUnderBaseChange : IsStableUnderBaseChange Smooth := by
  convert!
    RingHom.FormallySmooth.isStableUnderBaseChange.and
      RingHom.finitePresentation_isStableUnderBaseChange
  rw [smooth_def]

/--
lemma `holdsForLocalizationAway` / 引理 `holdsForLocalizationAway`

English:
lemma holdsForLocalizationAway
  statement: HoldsForLocalizationAway Smooth
  proof: by
  introv R h
  rw [smooth_algebraMap]
  exact ⟨Algebra.FormallySmooth.of_isLocalization (.powers r),
    IsLocalization.Away.finitePresentation r⟩

中文:
引理 holdsForLocalizationAway
  结论: HoldsForLocalizationAway 光滑
  证明: by
  introv R h
  rw [smooth_algebraMap]
  exact ⟨Algebra.FormallySmooth.of_isLocalization (.powers r),
    IsLocalization.Away.finitePresentation r⟩

Depends on / 依赖: Algebra, Algebra.FormallySmooth.of_isLocalization, FormallySmooth, IsLocalization, IsLocalization.Away.finitePresentation, finitePresentation, introv, of_isLocalization, powers, smooth_algebraMap
-/
lemma holdsForLocalizationAway : HoldsForLocalizationAway Smooth := by
  introv R h
  rw [smooth_algebraMap]
  exact ⟨Algebra.FormallySmooth.of_isLocalization (.powers r),
    IsLocalization.Away.finitePresentation r⟩

/--
lemma `of_bijective` / 引理 `of_bijective`

English:
lemma of_bijective
  given: {f : R ->+* S} (hf : Function.Bijective f)
  statement: f.Smooth
  proof: by
  rw [RingHom.smooth_def]
  exact ⟨.of_bijective hf, .of_bijective hf⟩

中文:
引理 of_bijective
  条件: {f : R ->+* S} (hf : 函数.双射 f)
  结论: f.光滑
  证明: by
  rw [RingHom.smooth_def]
  exact ⟨.of_bijective hf, .of_bijective hf⟩

Depends on / 依赖: RingHom, RingHom.smooth_def, of_bijective, smooth_def
-/
lemma of_bijective {f : R ->+* S} (hf : Function.Bijective f) : f.Smooth := by
  rw [RingHom.smooth_def]
  exact ⟨.of_bijective hf, .of_bijective hf⟩

variable (R) in
/--
lemma `id` / 引理 `id`

English:
lemma id
  statement: RingHom.Smooth (RingHom.id R)
  proof: holdsForLocalizationAway.containsIdentities R

中文:
引理 id
  结论: 环态射.光滑 (环态射.id R)
  证明: holdsForLocalizationAway.containsIdentities R

Depends on / 依赖: containsIdentities, holdsForLocalizationAway, holdsForLocalizationAway.containsIdentities
-/
lemma id : RingHom.Smooth (RingHom.id R) :=
  holdsForLocalizationAway.containsIdentities R

/--
lemma `ofLocalizationSpanTarget` / 引理 `ofLocalizationSpanTarget`

English:
lemma ofLocalizationSpanTarget
  statement: OfLocalizationSpanTarget Smooth
  proof: by
  introv R hs hf
  have : f.FinitePresentation :=
    finitePresentation_ofLocalizationSpanTarget _ s hs fun r => (hf r).finitePresentation
  algebraize [f]
  refine ⟨?_, ‹_›⟩
  rw [← Algebra.smoothLocus_eq_univ_iff]; rw [← Set.univ_subset_iff]; rw [← TopologicalSpace.Opens.coe_top]; rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr hs]
  simp only [TopologicalSpace.Opens.coe_iSup, Set.iUnion_subset_iff,
    Algebra.basicOpen_subset_smoothLocus_iff, ← formallySmooth_algebraMap]
  exact fun r hr => (hf ⟨r, hr⟩).1

中文:
引理 ofLocalizationSpanTarget
  结论: OfLocalizationSpanTarget 光滑
  证明: by
  introv R hs hf
  have : f.FinitePresentation :=
    finitePresentation_ofLocalizationSpanTarget _ s hs fun r => (hf r).finitePresentation
  algebraize [f]
  refine ⟨?_, ‹_›⟩
  rw [← Algebra.smoothLocus_eq_univ_iff]; rw [← Set.univ_subset_iff]; rw [← TopologicalSpace.Opens.coe_top]; rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr hs]
  simp only [TopologicalSpace.Opens.coe_iSup, Set.iUnion_subset_iff,
    Algebra.basicOpen_subset_smoothLocus_iff, ← formallySmooth_algebraMap]
  exact fun r hr => (hf ⟨r, hr⟩).1

Depends on / 依赖: Algebra, Algebra.basicOpen_subset_smoothLocus_iff, Algebra.smoothLocus_eq_univ_iff, FinitePresentation, PrimeSpectrum, PrimeSpectrum.iSup_basicOpen_eq_top_iff, Set.iUnion_subset_iff, Set.univ_subset_iff, TopologicalSpace, TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, algebraize, basicOpen_subset_smoothLocus_iff, coe_iSup, coe_top, f.FinitePresentation, finitePresentation, finitePresentation_ofLocalizationSpanTarget, formallySmooth_algebraMap, iSup_basicOpen_eq_top_iff
-/
lemma ofLocalizationSpanTarget : OfLocalizationSpanTarget Smooth := by
  introv R hs hf
  have : f.FinitePresentation :=
    finitePresentation_ofLocalizationSpanTarget _ s hs fun r => (hf r).finitePresentation
  algebraize [f]
  refine ⟨?_, ‹_›⟩
  rw [← Algebra.smoothLocus_eq_univ_iff]; rw [← Set.univ_subset_iff]; rw [← TopologicalSpace.Opens.coe_top]; rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr hs]
  simp only [TopologicalSpace.Opens.coe_iSup, Set.iUnion_subset_iff,
    Algebra.basicOpen_subset_smoothLocus_iff, ← formallySmooth_algebraMap]
  exact fun r hr => (hf ⟨r, hr⟩).1

/--
lemma `propertyIsLocal` / 引理 `propertyIsLocal`

English:
lemma propertyIsLocal
  statement: PropertyIsLocal Smooth where
  proof: isStableUnderBaseChange.localizationPreserves.away
  ofLocalizationSpanTarget := ofLocalizationSpanTarget
  ofLocalizationSpan := ofLocalizationSpanTarget.ofLocalizationSpan
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).left
  StableUnderCompositionWithLocalizationAwayTarget :=
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).right

中文:
引理 propertyIsLocal
  结论: PropertyIsLocal 光滑 where
  证明: isStableUnderBaseChange.localizationPreserves.away
  ofLocalizationSpanTarget := ofLocalizationSpanTarget
  ofLocalizationSpan := ofLocalizationSpanTarget.ofLocalizationSpan
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).left
  StableUnderCompositionWithLocalizationAwayTarget :=
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).right

Depends on / 依赖: isStableUnderBaseChange, isStableUnderBaseChange.localizationPreserves.away, localizationPreserves
-/
lemma propertyIsLocal : PropertyIsLocal Smooth where
  localizationAwayPreserves := isStableUnderBaseChange.localizationPreserves.away
  ofLocalizationSpanTarget := ofLocalizationSpanTarget
  ofLocalizationSpan := ofLocalizationSpanTarget.ofLocalizationSpan
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).left
  StableUnderCompositionWithLocalizationAwayTarget :=
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).right

/--
lemma `respectsIso` / 引理 `respectsIso`

English:
lemma respectsIso
  statement: RespectsIso Smooth
  proof: propertyIsLocal.respectsIso

中文:
引理 respectsIso
  结论: RespectsIso 光滑
  证明: propertyIsLocal.respectsIso

Depends on / 依赖: propertyIsLocal, propertyIsLocal.respectsIso, respectsIso
-/
lemma respectsIso : RespectsIso Smooth :=
  propertyIsLocal.respectsIso

end RingHom.Smooth
