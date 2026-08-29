/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Smooth.Flat

/-!
# Étale ring homomorphisms

We show the meta properties of étale morphisms.
-/

@[expose] public section

universe u

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A ring hom `R →+* S` is étale, if `S` is an étale `R`-algebra. -/
@[algebraize RingHom.Etale.toAlgebra]
/--
Definition of `Etale` / `Etale` 的定义

English:
definition Etale
  signature: {R S : Type*} [CommRing R] [CommRing S] (f : R ->+* S)
  body: @Algebra.Etale R S _ _ f.toAlgebra

中文:
定义 平展
  签名: {R S : 类型} [交换环 R] [交换环 S] (f : R ->+* S)
  定义体: @Algebra.Etale R S _ _ f.toAlgebra

Depends on / 依赖: Algebra, Algebra.Etale, f.toAlgebra, toAlgebra
-/
def Etale {R S : Type*} [CommRing R] [CommRing S] (f : R ->+* S) : Prop :=
  @Algebra.Etale R S _ _ f.toAlgebra

/--
lemma `Etale.toAlgebra` / 引理 `Etale.toAlgebra`

English:
lemma Etale.toAlgebra
  given: {f : R ->+* S} (hf : Etale f)
  proof: hf

中文:
引理 平展.toAlgebra
  条件: {f : R ->+* S} (hf : 平展 f)
  证明: hf
-/
lemma Etale.toAlgebra {f : R ->+* S} (hf : Etale f) :
    @Algebra.Etale R S _ _ f.toAlgebra := hf

variable {R S : Type*} [CommRing R] [CommRing S] (f : R ->+* S)

/--
lemma `etale_algebraMap` / 引理 `etale_algebraMap`

English:
lemma etale_algebraMap
  given: [Algebra R S]
  statement: (algebraMap R S).Etale ↔ Algebra.Etale R S
  proof: by
  rw [RingHom.Etale]; rw [toAlgebra_algebraMap]

中文:
引理 etale_algebraMap
  条件: [代数 R S]
  结论: (algebraMap R S).平展 ↔ 代数.平展 R S
  证明: by
  rw [RingHom.Etale]; rw [toAlgebra_algebraMap]

Depends on / 依赖: RingHom, RingHom.Etale, toAlgebra_algebraMap
-/
lemma etale_algebraMap [Algebra R S] : (algebraMap R S).Etale ↔ Algebra.Etale R S := by
  rw [RingHom.Etale]; rw [toAlgebra_algebraMap]

/--
lemma `etale_iff_formallyUnramified_and_smooth` / 引理 `etale_iff_formallyUnramified_and_smooth`

English:
lemma etale_iff_formallyUnramified_and_smooth
  statement: f.Etale ↔ f.FormallyUnramified ∧ f.Smooth
  proof: by
  algebraize [f]
  simp only [Etale, Smooth, FormallyUnramified]
  exact ⟨fun h => ⟨inferInstance, inferInstance, inferInstance⟩,
    fun ⟨h1, h2⟩ => ⟨.of_formallyUnramified_and_formallySmooth, inferInstance⟩⟩

中文:
引理 etale_iff_formallyUnramified_and_smooth
  结论: f.平展 ↔ f.形式非分歧 ∧ f.光滑
  证明: by
  algebraize [f]
  simp only [Etale, Smooth, FormallyUnramified]
  exact ⟨fun h => ⟨inferInstance, inferInstance, inferInstance⟩,
    fun ⟨h1, h2⟩ => ⟨.of_formallyUnramified_and_formallySmooth, inferInstance⟩⟩

Depends on / 依赖: FormallyUnramified, Smooth, algebraize, of_formallyUnramified_and_formallySmooth
-/
lemma etale_iff_formallyUnramified_and_smooth : f.Etale ↔ f.FormallyUnramified ∧ f.Smooth := by
  algebraize [f]
  simp only [Etale, Smooth, FormallyUnramified]
  exact ⟨fun h => ⟨inferInstance, inferInstance, inferInstance⟩,
    fun ⟨h1, h2⟩ => ⟨.of_formallyUnramified_and_formallySmooth, inferInstance⟩⟩

/--
lemma `Etale.eq_formallyUnramified_and_smooth` / 引理 `Etale.eq_formallyUnramified_and_smooth`

English:
lemma Etale.eq_formallyUnramified_and_smooth
  proof: by
  ext
  rw [etale_iff_formallyUnramified_and_smooth]

中文:
引理 平展.eq_formallyUnramified_and_smooth
  证明: by
  ext
  rw [etale_iff_formallyUnramified_and_smooth]

Depends on / 依赖: etale_iff_formallyUnramified_and_smooth
-/
lemma Etale.eq_formallyUnramified_and_smooth :
    @Etale = fun R S (_ : CommRing R) (_ : CommRing S) f => f.FormallyUnramified ∧ f.Smooth := by
  ext
  rw [etale_iff_formallyUnramified_and_smooth]

/--
lemma `Etale.formallyUnramified` / 引理 `Etale.formallyUnramified`

English:
lemma Etale.formallyUnramified
  given: (hf : f.Etale)
  statement: f.FormallyUnramified
  proof: by
  rw [etale_iff_formallyUnramified_and_smooth] at hf
  exact hf.1

中文:
引理 平展.formallyUnramified
  条件: (hf : f.平展)
  结论: f.形式非分歧
  证明: by
  rw [etale_iff_formallyUnramified_and_smooth] at hf
  exact hf.1

Depends on / 依赖: etale_iff_formallyUnramified_and_smooth
-/
lemma Etale.formallyUnramified (hf : f.Etale) : f.FormallyUnramified := by
  rw [etale_iff_formallyUnramified_and_smooth] at hf
  exact hf.1

/--
lemma `Etale.of_bijective` / 引理 `Etale.of_bijective`

English:
lemma Etale.of_bijective
  given: {f : R ->+* S} (hf : Function.Bijective f)
  statement: f.Etale
  proof: by
  rw [etale_iff_formallyUnramified_and_smooth]
  exact ⟨.of_surjective hf.2, .of_bijective hf⟩

中文:
引理 平展.of_bijective
  条件: {f : R ->+* S} (hf : 函数.双射 f)
  结论: f.平展
  证明: by
  rw [etale_iff_formallyUnramified_and_smooth]
  exact ⟨.of_surjective hf.2, .of_bijective hf⟩

Depends on / 依赖: etale_iff_formallyUnramified_and_smooth, of_bijective, of_surjective
-/
lemma Etale.of_bijective {f : R ->+* S} (hf : Function.Bijective f) : f.Etale := by
  rw [etale_iff_formallyUnramified_and_smooth]
  exact ⟨.of_surjective hf.2, .of_bijective hf⟩

/--
lemma `Etale.containsIdentities` / 引理 `Etale.containsIdentities`

English:
lemma Etale.containsIdentities
  statement: ContainsIdentities Etale
  proof: fun _ _ => .of_bijective Function.bijective_id

中文:
引理 平展.containsIdentities
  结论: 余ntainsIdentities 平展
  证明: fun _ _ => .of_bijective Function.bijective_id

Depends on / 依赖: Function, Function.bijective_id, bijective_id, of_bijective
-/
lemma Etale.containsIdentities : ContainsIdentities Etale :=
  fun _ _ => .of_bijective Function.bijective_id

/--
lemma `Etale.isStableUnderBaseChange` / 引理 `Etale.isStableUnderBaseChange`

English:
lemma Etale.isStableUnderBaseChange
  statement: IsStableUnderBaseChange Etale
  proof: by
  rw [eq_formallyUnramified_and_smooth]
  exact FormallyUnramified.isStableUnderBaseChange.and Smooth.isStableUnderBaseChange

中文:
引理 平展.isStableUnderBaseChange
  结论: 是StableUnderBaseChange 平展
  证明: by
  rw [eq_formallyUnramified_and_smooth]
  exact FormallyUnramified.isStableUnderBaseChange.and Smooth.isStableUnderBaseChange

Depends on / 依赖: FormallyUnramified, FormallyUnramified.isStableUnderBaseChange.and, Smooth, Smooth.isStableUnderBaseChange, eq_formallyUnramified_and_smooth, isStableUnderBaseChange
-/
lemma Etale.isStableUnderBaseChange : IsStableUnderBaseChange Etale := by
  rw [eq_formallyUnramified_and_smooth]
  exact FormallyUnramified.isStableUnderBaseChange.and Smooth.isStableUnderBaseChange

/--
lemma `Etale.propertyIsLocal` / 引理 `Etale.propertyIsLocal`

English:
lemma Etale.propertyIsLocal
  statement: PropertyIsLocal Etale
  proof: by
  rw [eq_formallyUnramified_and_smooth]
  exact FormallyUnramified.propertyIsLocal.and Smooth.propertyIsLocal

中文:
引理 平展.propertyIsLocal
  结论: PropertyIsLocal 平展
  证明: by
  rw [eq_formallyUnramified_and_smooth]
  exact FormallyUnramified.propertyIsLocal.and Smooth.propertyIsLocal

Depends on / 依赖: FormallyUnramified, FormallyUnramified.propertyIsLocal.and, Smooth, Smooth.propertyIsLocal, eq_formallyUnramified_and_smooth, propertyIsLocal
-/
lemma Etale.propertyIsLocal : PropertyIsLocal Etale := by
  rw [eq_formallyUnramified_and_smooth]
  exact FormallyUnramified.propertyIsLocal.and Smooth.propertyIsLocal

/--
lemma `Etale.respectsIso` / 引理 `Etale.respectsIso`

English:
lemma Etale.respectsIso
  statement: RespectsIso Etale
  proof: propertyIsLocal.respectsIso

中文:
引理 平展.respectsIso
  结论: RespectsIso 平展
  证明: propertyIsLocal.respectsIso

Depends on / 依赖: propertyIsLocal, propertyIsLocal.respectsIso, respectsIso
-/
lemma Etale.respectsIso : RespectsIso Etale :=
  propertyIsLocal.respectsIso

/--
lemma `Etale.ofLocalizationSpanTarget` / 引理 `Etale.ofLocalizationSpanTarget`

English:
lemma Etale.ofLocalizationSpanTarget
  statement: OfLocalizationSpanTarget Etale
  proof: propertyIsLocal.ofLocalizationSpanTarget

中文:
引理 平展.ofLocalizationSpanTarget
  结论: OfLocalizationSpanTarget 平展
  证明: propertyIsLocal.ofLocalizationSpanTarget

Depends on / 依赖: ofLocalizationSpanTarget, propertyIsLocal, propertyIsLocal.ofLocalizationSpanTarget
-/
lemma Etale.ofLocalizationSpanTarget : OfLocalizationSpanTarget Etale :=
  propertyIsLocal.ofLocalizationSpanTarget

/--
lemma `Etale.ofLocalizationSpan` / 引理 `Etale.ofLocalizationSpan`

English:
lemma Etale.ofLocalizationSpan
  statement: OfLocalizationSpan Etale
  proof: propertyIsLocal.ofLocalizationSpan

中文:
引理 平展.ofLocalizationSpan
  结论: OfLocalizationSpan 平展
  证明: propertyIsLocal.ofLocalizationSpan

Depends on / 依赖: ofLocalizationSpan, propertyIsLocal, propertyIsLocal.ofLocalizationSpan
-/
lemma Etale.ofLocalizationSpan : OfLocalizationSpan Etale :=
  propertyIsLocal.ofLocalizationSpan

/--
lemma `Etale.stableUnderComposition` / 引理 `Etale.stableUnderComposition`

English:
lemma Etale.stableUnderComposition
  statement: StableUnderComposition Etale
  proof: by
  rw [eq_formallyUnramified_and_smooth]
  exact FormallyUnramified.stableUnderComposition.and Smooth.stableUnderComposition

中文:
引理 平展.stableUnderComposition
  结论: StableUnderComposition 平展
  证明: by
  rw [eq_formallyUnramified_and_smooth]
  exact FormallyUnramified.stableUnderComposition.and Smooth.stableUnderComposition

Depends on / 依赖: FormallyUnramified, FormallyUnramified.stableUnderComposition.and, Smooth, Smooth.stableUnderComposition, eq_formallyUnramified_and_smooth, stableUnderComposition
-/
lemma Etale.stableUnderComposition : StableUnderComposition Etale := by
  rw [eq_formallyUnramified_and_smooth]
  exact FormallyUnramified.stableUnderComposition.and Smooth.stableUnderComposition

/--
lemma `Etale.iff_flat_and_formallyUnramified` / 引理 `Etale.iff_flat_and_formallyUnramified`

English:
lemma Etale.iff_flat_and_formallyUnramified
  given: {f : R ->+* S}
  proof: by
  algebraize [f]
  simp_rw [← f.algebraMap_toAlgebra, RingHom.etale_algebraMap, RingHom.flat_algebraMap_iff,
    RingHom.formallyUnramified_algebraMap, RingHom.finitePresentation_algebraMap]
  refine ⟨fun h => ⟨inferInstance, inferInstance, inferInstance⟩,
    fun ⟨_, _, _⟩ => .of_formallyUnramif

中文:
引理 平展.iff_flat_and_formallyUnramified
  条件: {f : R ->+* S}
  证明: by
  algebraize [f]
  simp_rw [← f.algebraMap_toAlgebra, RingHom.etale_algebraMap, RingHom.flat_algebraMap_iff,
    RingHom.formallyUnramified_algebraMap, RingHom.finitePresentation_algebraMap]
  refine ⟨fun h => ⟨inferInstance, inferInstance, inferInstance⟩,
    fun ⟨_, _, _⟩ => .of_formallyUnramif

Depends on / 依赖: RingHom, RingHom.etale_algebraMap, RingHom.finitePresentation_algebraMap, RingHom.flat_algebraMap_iff, RingHom.formallyUnramified_algebraMap, algebraMap_toAlgebra, algebraize, etale_algebraMap, f.algebraMap_toAlgebra, finitePresentation_algebraMap, flat_algebraMap_iff, formallyUnramified_algebraMap, of_formallyUnramified_of_flat, simp_rw
-/
lemma Etale.iff_flat_and_formallyUnramified {f : R ->+* S} :
    f.Etale ↔ f.Flat ∧ f.FormallyUnramified ∧ f.FinitePresentation := by
  algebraize [f]
  simp_rw [← f.algebraMap_toAlgebra, RingHom.etale_algebraMap, RingHom.flat_algebraMap_iff,
    RingHom.formallyUnramified_algebraMap, RingHom.finitePresentation_algebraMap]
  refine ⟨fun h => ⟨inferInstance, inferInstance, inferInstance⟩,
    fun ⟨_, _, _⟩ => .of_formallyUnramified_of_flat⟩

end RingHom
