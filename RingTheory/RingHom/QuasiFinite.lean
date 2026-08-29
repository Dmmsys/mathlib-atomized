/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RingHom.OpenImmersion

/-! # The meta properties of quasi-finite ring homomorphisms. -/

@[expose] public section

universe u

namespace RingHom

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- A ring hom `R →+* S` is quasi-finite if `S` is a quasi-finite `R`-algebra. -/
@[algebraize RingHom.QuasiFinite.toAlgebra]
/--
Definition of `QuasiFinite` / `QuasiFinite` 的定义

English:
definition QuasiFinite
  signature: {R S : Type*} [CommRing R] [CommRing S] (f : R ->+* S)
  body: @Algebra.QuasiFinite R S _ _ f.toAlgebra

中文:
定义 拟有限
  签名: {R S : 类型} [交换环 R] [交换环 S] (f : R ->+* S)
  定义体: @Algebra.QuasiFinite R S _ _ f.toAlgebra

Depends on / 依赖: Algebra, Algebra.QuasiFinite, QuasiFinite, f.toAlgebra, toAlgebra
-/
def QuasiFinite {R S : Type*} [CommRing R] [CommRing S] (f : R ->+* S) : Prop :=
  @Algebra.QuasiFinite R S _ _ f.toAlgebra

/--
lemma `QuasiFinite.toAlgebra` / 引理 `QuasiFinite.toAlgebra`

English:
lemma QuasiFinite.toAlgebra
  given: {f : R ->+* S} (hf : QuasiFinite f)
  proof: hf

中文:
引理 拟有限.toAlgebra
  条件: {f : R ->+* S} (hf : 拟有限 f)
  证明: hf
-/
lemma QuasiFinite.toAlgebra {f : R ->+* S} (hf : QuasiFinite f) :
    @Algebra.QuasiFinite R S _ _ f.toAlgebra := hf

variable {R S : Type*} [CommRing R] [CommRing S] (f : R ->+* S)

/--
lemma `quasiFinite_algebraMap` / 引理 `quasiFinite_algebraMap`

English:
lemma quasiFinite_algebraMap
  given: [Algebra R S]
  proof: by
  rw [RingHom.QuasiFinite]; rw [toAlgebra_algebraMap]

中文:
引理 quasiFinite_algebraMap
  条件: [代数 R S]
  证明: by
  rw [RingHom.QuasiFinite]; rw [toAlgebra_algebraMap]

Depends on / 依赖: QuasiFinite, RingHom, RingHom.QuasiFinite, toAlgebra_algebraMap
-/
lemma quasiFinite_algebraMap [Algebra R S] :
    (algebraMap R S).QuasiFinite ↔ Algebra.QuasiFinite R S := by
  rw [RingHom.QuasiFinite]; rw [toAlgebra_algebraMap]

/--
lemma `QuasiFinite.comp` / 引理 `QuasiFinite.comp`

English:
lemma QuasiFinite.comp
  given: {f : S ->+* T} {g : R ->+* S} (hf : f.QuasiFinite) (hg : g.QuasiFinite)
  proof: by
  algebraize [f, g, (f.comp g)]
  exact .trans R S T

中文:
引理 拟有限.comp
  条件: {f : S ->+* T} {g : R ->+* S} (hf : f.拟有限) (hg : g.拟有限)
  证明: by
  algebraize [f, g, (f.comp g)]
  exact .trans R S T

Depends on / 依赖: algebraize, f.comp
-/
lemma QuasiFinite.comp {f : S ->+* T} {g : R ->+* S} (hf : f.QuasiFinite) (hg : g.QuasiFinite) :
    (f.comp g).QuasiFinite := by
  algebraize [f, g, (f.comp g)]
  exact .trans R S T

/--
lemma `QuasiFinite.of_comp` / 引理 `QuasiFinite.of_comp`

English:
lemma QuasiFinite.of_comp
  given: {f : S ->+* T} {g : R ->+* S} (h : (f.comp g).QuasiFinite)
  proof: by
  algebraize [f, g, (f.comp g)]
  exact .of_restrictScalars R S T

中文:
引理 拟有限.of_comp
  条件: {f : S ->+* T} {g : R ->+* S} (h : (f.comp g).拟有限)
  证明: by
  algebraize [f, g, (f.comp g)]
  exact .of_restrictScalars R S T

Depends on / 依赖: algebraize, f.comp, of_restrictScalars
-/
lemma QuasiFinite.of_comp {f : S ->+* T} {g : R ->+* S} (h : (f.comp g).QuasiFinite) :
    f.QuasiFinite := by
  algebraize [f, g, (f.comp g)]
  exact .of_restrictScalars R S T

/--
lemma `QuasiFinite.comp_iff` / 引理 `QuasiFinite.comp_iff`

English:
lemma QuasiFinite.comp_iff
  given: {f : S ->+* T} {g : R ->+* S} (hg : g.QuasiFinite)
  proof: ⟨.of_comp, (.comp · hg)⟩

中文:
引理 拟有限.comp_iff
  条件: {f : S ->+* T} {g : R ->+* S} (hg : g.拟有限)
  证明: ⟨.of_comp, (.comp · hg)⟩

Depends on / 依赖: of_comp
-/
lemma QuasiFinite.comp_iff {f : S ->+* T} {g : R ->+* S} (hg : g.QuasiFinite) :
    (f.comp g).QuasiFinite ↔ f.QuasiFinite :=
  ⟨.of_comp, (.comp · hg)⟩

/--
lemma `QuasiFinite.of_finite` / 引理 `QuasiFinite.of_finite`

English:
lemma QuasiFinite.of_finite
  given: {f : S ->+* T} (hf : f.Finite)
  statement: f.QuasiFinite
  proof: by
  algebraize [f]
  exact inferInstanceAs (Algebra.QuasiFinite _ _)

中文:
引理 拟有限.of_finite
  条件: {f : S ->+* T} (hf : f.有限)
  结论: f.拟有限
  证明: by
  algebraize [f]
  exact inferInstanceAs (Algebra.QuasiFinite _ _)

Depends on / 依赖: Algebra, Algebra.QuasiFinite, QuasiFinite, algebraize
-/
lemma QuasiFinite.of_finite {f : S ->+* T} (hf : f.Finite) : f.QuasiFinite := by
  algebraize [f]
  exact inferInstanceAs (Algebra.QuasiFinite _ _)

/--
lemma `QuasiFinite.stableUnderComposition` / 引理 `QuasiFinite.stableUnderComposition`

English:
lemma QuasiFinite.stableUnderComposition
  statement: StableUnderComposition QuasiFinite
  proof: fun _ _ _ _ _ _ _ _ hf hg => comp hg hf

中文:
引理 拟有限.stableUnderComposition
  结论: StableUnderComposition 拟有限
  证明: fun _ _ _ _ _ _ _ _ hf hg => comp hg hf
-/
lemma QuasiFinite.stableUnderComposition : StableUnderComposition QuasiFinite :=
  fun _ _ _ _ _ _ _ _ hf hg => comp hg hf

/--
lemma `QuasiFinite.respectsIso` / 引理 `QuasiFinite.respectsIso`

English:
lemma QuasiFinite.respectsIso
  statement: RespectsIso QuasiFinite
  proof: stableUnderComposition.respectsIso fun e => .of_finite e.finite

中文:
引理 拟有限.respectsIso
  结论: RespectsIso 拟有限
  证明: stableUnderComposition.respectsIso fun e => .of_finite e.finite

Depends on / 依赖: e.finite, finite, of_finite, respectsIso, stableUnderComposition, stableUnderComposition.respectsIso
-/
lemma QuasiFinite.respectsIso : RespectsIso QuasiFinite :=
  stableUnderComposition.respectsIso fun e => .of_finite e.finite

/--
lemma `QuasiFinite.isStableUnderBaseChange` / 引理 `QuasiFinite.isStableUnderBaseChange`

English:
lemma QuasiFinite.isStableUnderBaseChange
  statement: IsStableUnderBaseChange QuasiFinite
  proof: by
  refine .mk respectsIso ?_
  introv H
  rw [quasiFinite_algebraMap] at H ⊢
  infer_instance

中文:
引理 拟有限.isStableUnderBaseChange
  结论: 是StableUnderBaseChange 拟有限
  证明: by
  refine .mk respectsIso ?_
  introv H
  rw [quasiFinite_algebraMap] at H ⊢
  infer_instance

Depends on / 依赖: infer_instance, introv, quasiFinite_algebraMap, respectsIso
-/
lemma QuasiFinite.isStableUnderBaseChange : IsStableUnderBaseChange QuasiFinite := by
  refine .mk respectsIso ?_
  introv H
  rw [quasiFinite_algebraMap] at H ⊢
  infer_instance

/--
lemma `QuasiFinite.holdsForLocalizationAway` / 引理 `QuasiFinite.holdsForLocalizationAway`

English:
lemma QuasiFinite.holdsForLocalizationAway
  statement: HoldsForLocalizationAway QuasiFinite
  proof: by
  introv R _
  exact quasiFinite_algebraMap.mpr (.of_isLocalization (.powers r))

中文:
引理 拟有限.holdsForLocalizationAway
  结论: HoldsForLocalizationAway 拟有限
  证明: by
  introv R _
  exact quasiFinite_algebraMap.mpr (.of_isLocalization (.powers r))

Depends on / 依赖: introv, of_isLocalization, powers, quasiFinite_algebraMap, quasiFinite_algebraMap.mpr
-/
lemma QuasiFinite.holdsForLocalizationAway : HoldsForLocalizationAway QuasiFinite := by
  introv R _
  exact quasiFinite_algebraMap.mpr (.of_isLocalization (.powers r))

attribute [local instance high] Algebra.TensorProduct.leftAlgebra Algebra.toModule
    IsScalarTower.right DivisionRing.instIsArtinianRing in
/--
lemma `QuasiFinite.ofLocalizationSpanTarget` / 引理 `QuasiFinite.ofLocalizationSpanTarget`

English:
lemma QuasiFinite.ofLocalizationSpanTarget
  statement: OfLocalizationSpanTarget QuasiFinite
  proof: by
  rw [RingHom.ofLocalizationSpanTarget_iff_finite]
  introv R hs H
  algebraize [f]
  refine ⟨fun P _ => ?_⟩
  have (r : s) : Module.Finite P.ResidueField (P.Fiber (Localization.Away r.1)) := by
    have : Algebra.QuasiFinite R (Localization.Away r.1) := quasiFinite_algebraMap.mp (H r)
    infer_

中文:
引理 拟有限.ofLocalizationSpanTarget
  结论: OfLocalizationSpanTarget 拟有限
  证明: by
  rw [RingHom.ofLocalizationSpanTarget_iff_finite]
  introv R hs H
  algebraize [f]
  refine ⟨fun P _ => ?_⟩
  have (r : s) : Module.Finite P.ResidueField (P.Fiber (Localization.Away r.1)) := by
    have : Algebra.QuasiFinite R (Localization.Away r.1) := quasiFinite_algebraMap.mp (H r)
    infer_

Depends on / 依赖: Algebra, Algebra.QuasiFinite, Algebra.TensorProduct.map, Finite, IsScalarTower, IsScalarTower.toAlgHom, Localization, Localization.Away, Module, Module.Finite, P.Fiber, P.ResidueField, QuasiFinite, ResidueField, RingHom, RingHom.ofLocalizationSpanTarget_iff_finite, TensorProduct, algebraize, infer_instance, introv
-/
lemma QuasiFinite.ofLocalizationSpanTarget : OfLocalizationSpanTarget QuasiFinite := by
  rw [RingHom.ofLocalizationSpanTarget_iff_finite]
  introv R hs H
  algebraize [f]
  refine ⟨fun P _ => ?_⟩
  have (r : s) : Module.Finite P.ResidueField (P.Fiber (Localization.Away r.1)) := by
    have : Algebra.QuasiFinite R (Localization.Away r.1) := quasiFinite_algebraMap.mp (H r)
    infer_instance
  let φ (r : s) : P.Fiber S ->ₐ[P.ResidueField] P.Fiber (Localization.Away r.1) :=
    Algebra.TensorProduct.map (.id _ _) (IsScalarTower.toAlgHom _ _ _)
  let f : P.Fiber S ->ₐ[P.ResidueField] Π r : s, (P.Fiber (Localization.Away r.1)) :=
    AlgHom.pi φ
  have : IsNoetherian P.ResidueField (Π r : s, (P.Fiber (Localization.Away r.1))) :=
    isNoetherian_of_isNoetherianRing_of_finite ..
  suffices Function.Injective f from .of_injective f.toLinearMap this
  rw [injective_iff_map_eq_zero]
  intro a ha
  apply eq_zero_of_localization _ fun J hJ => ?_
  let I := (PrimeSpectrum.primesOverOrderIsoFiber R S P).symm ⟨J, inferInstance⟩
  have : ¬ (s : Set S) subseteq I.1 := fun h =>
    Ideal.IsPrime.ne_top' (top_le_iff.mp (hs.symm.trans_le (Ideal.span_le.mpr h)))
  obtain ⟨r, hrs, hrI⟩ := Set.not_subset.mp this
  let ψ : P.Fiber (Localization.Away r) ->ₐ[P.ResidueField] Localization.AtPrime J :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) ⟨IsLocalization.map (M := .powers r)
      (T := J.primeCompl) _ Algebra.TensorProduct.includeRight.toRingHom (by
      simpa [Submonoid.powers_le] using! hrI), by
      simp [IsScalarTower.algebraMap_apply R S (Localization.Away r),
        -Algebra.TensorProduct.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply R _ (Localization.AtPrime J)]⟩ (fun _ _ => .all _ _)
  have hψ : ψ.comp (φ ⟨r, hrs⟩) = IsScalarTower.toAlgHom _ _ _ := by ext; simp [φ, ψ]
  refine congr($hψ a).symm.trans
    (show ψ (f a ⟨r, hrs⟩) = 0 by simp only [ha, Pi.zero_apply, map_zero])

/--
lemma `QuasiFinite.propertyIsLocal` / 引理 `QuasiFinite.propertyIsLocal`

English:
lemma QuasiFinite.propertyIsLocal
  statement: PropertyIsLocal QuasiFinite where
  proof: isStableUnderBaseChange.localizationPreserves.away
  ofLocalizationSpanTarget := ofLocalizationSpanTarget
  ofLocalizationSpan := ofLocalizationSpanTarget.ofLocalizationSpan
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).left
  StableUnderCompo

中文:
引理 拟有限.propertyIsLocal
  结论: PropertyIsLocal 拟有限 where
  证明: isStableUnderBaseChange.localizationPreserves.away
  ofLocalizationSpanTarget := ofLocalizationSpanTarget
  ofLocalizationSpan := ofLocalizationSpanTarget.ofLocalizationSpan
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).left
  StableUnderCompo

Depends on / 依赖: isStableUnderBaseChange, isStableUnderBaseChange.localizationPreserves.away, localizationPreserves
-/
lemma QuasiFinite.propertyIsLocal : PropertyIsLocal QuasiFinite where
  localizationAwayPreserves := isStableUnderBaseChange.localizationPreserves.away
  ofLocalizationSpanTarget := ofLocalizationSpanTarget
  ofLocalizationSpan := ofLocalizationSpanTarget.ofLocalizationSpan
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).left
  StableUnderCompositionWithLocalizationAwayTarget :=
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).right

open TensorProduct in
/--
lemma `QuasiFinite.of_isIntegral_of_finiteType` / 引理 `QuasiFinite.of_isIntegral_of_finiteType`

English:
lemma QuasiFinite.of_isIntegral_of_finiteType
  proof: by
  algebraize [f, g, g.comp f]
  obtain ⟨s, hs⟩ := Algebra.IsStandardOpenImmersion.exists_away S T
  exact Algebra.QuasiFinite.of_isIntegral_of_finiteType s

中文:
引理 拟有限.of_is整数egral_of_finiteType
  证明: by
  algebraize [f, g, g.comp f]
  obtain ⟨s, hs⟩ := Algebra.IsStandardOpenImmersion.exists_away S T
  exact Algebra.QuasiFinite.of_isIntegral_of_finiteType s

Depends on / 依赖: Algebra, Algebra.IsStandardOpenImmersion.exists_away, Algebra.QuasiFinite.of_isIntegral_of_finiteType, IsStandardOpenImmersion, QuasiFinite, algebraize, exists_away, g.comp, of_isIntegral_of_finiteType
-/
lemma QuasiFinite.of_isIntegral_of_finiteType
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {f : R ->+* S} (hf : f.IsIntegral)
    {g : S ->+* T} (hg : g.IsStandardOpenImmersion) (hg : (g.comp f).FiniteType) :
    (g.comp f).QuasiFinite := by
  algebraize [f, g, g.comp f]
  obtain ⟨s, hs⟩ := Algebra.IsStandardOpenImmersion.exists_away S T
  exact Algebra.QuasiFinite.of_isIntegral_of_finiteType s

/--
Definition of `QuasiFiniteAt` / `QuasiFiniteAt` 的定义

English:
abbreviation QuasiFiniteAt
  signature: {R S : Type*} [CommRing R] [CommRing S] (f : R ->+* S) (p : Ideal S)
  body: letI := f.toAlgebra; Algebra.QuasiFiniteAt R p

中文:
缩写 QuasiFiniteAt
  签名: {R S : 类型} [交换环 R] [交换环 S] (f : R ->+* S) (p : 理想 S)
  定义体: letI := f.toAlgebra; Algebra.QuasiFiniteAt R p

Depends on / 依赖: Algebra, Algebra.QuasiFiniteAt, QuasiFiniteAt, f.toAlgebra, toAlgebra
-/
abbrev QuasiFiniteAt {R S : Type*} [CommRing R] [CommRing S] (f : R ->+* S) (p : Ideal S)
    [p.IsPrime] : Prop := letI := f.toAlgebra; Algebra.QuasiFiniteAt R p

end RingHom
