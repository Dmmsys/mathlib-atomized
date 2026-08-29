/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Ideal.GoingDown

/-!
# Flat ring homomorphisms

In this file we define flat ring homomorphisms and show their meta properties.

-/

@[expose] public section

universe u₁ u₂ u v

open TensorProduct

/-- A ring homomorphism `f : R →+* S` is flat if `S` is flat as an `R` module. -/
@[algebraize Module.Flat]
/--
Definition of `RingHom.Flat` / `RingHom.Flat` 的定义

English:
definition RingHom.Flat
  signature: {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R ->+* S)
  body: letI : Algebra R S := f.toAlgebra
  Module.Flat R S

中文:
定义 环态射.平坦
  签名: {R : 类型u} {S : 类型v} [交换环 R] [交换环 S] (f : R ->+* S)
  定义体: letI : Algebra R S := f.toAlgebra
  Module.Flat R S

Depends on / 依赖: Algebra, Module, Module.Flat, f.toAlgebra, toAlgebra
-/
def RingHom.Flat {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R ->+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  Module.Flat R S

/--
lemma `RingHom.flat_algebraMap_iff` / 引理 `RingHom.flat_algebraMap_iff`

English:
lemma RingHom.flat_algebraMap_iff
  given: {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  proof: by
  rw [RingHom.Flat]; rw [toAlgebra_algebraMap]

中文:
引理 环态射.flat_algebraMap_iff
  条件: {R S : 类型} [交换环 R] [交换环 S] [代数 R S]
  证明: by
  rw [RingHom.Flat]; rw [toAlgebra_algebraMap]

Depends on / 依赖: RingHom, RingHom.Flat, toAlgebra_algebraMap
-/
lemma RingHom.flat_algebraMap_iff {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    (algebraMap R S).Flat ↔ Module.Flat R S := by
  rw [RingHom.Flat]; rw [toAlgebra_algebraMap]

namespace RingHom.Flat

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

variable (R) in
/--
lemma `id` / 引理 `id`

English:
lemma id
  statement: RingHom.Flat (RingHom.id R)
  proof: Module.Flat.self

中文:
引理 id
  结论: 环态射.平坦 (环态射.id R)
  证明: Module.Flat.self

Depends on / 依赖: Module, Module.Flat.self
-/
lemma id : RingHom.Flat (RingHom.id R) :=
  Module.Flat.self

/--
lemma `comp` / 引理 `comp`

English:
lemma comp
  given: {f : R ->+* S} {g : S ->+* T} (hf : f.Flat) (hg : g.Flat)
  statement: Flat (g.comp f)
  proof: by
  algebraize [f, g, (g.comp f)]
  exact Module.Flat.trans R S T

中文:
引理 comp
  条件: {f : R ->+* S} {g : S ->+* T} (hf : f.平坦) (hg : g.平坦)
  结论: 平坦 (g.comp f)
  证明: by
  algebraize [f, g, (g.comp f)]
  exact Module.Flat.trans R S T

Depends on / 依赖: Module, Module.Flat.trans, algebraize, g.comp
-/
lemma comp {f : R ->+* S} {g : S ->+* T} (hf : f.Flat) (hg : g.Flat) : Flat (g.comp f) := by
  algebraize [f, g, (g.comp f)]
  exact Module.Flat.trans R S T

/--
lemma `of_bijective` / 引理 `of_bijective`

English:
lemma of_bijective
  given: {f : R ->+* S} (hf : Function.Bijective f)
  statement: Flat f
  proof: by
  algebraize [f]
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective (Algebra.linearMap R S) hf).symm

中文:
引理 of_bijective
  条件: {f : R ->+* S} (hf : 函数.双射 f)
  结论: 平坦 f
  证明: by
  algebraize [f]
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective (Algebra.linearMap R S) hf).symm

Depends on / 依赖: Algebra, Algebra.linearMap, LinearEquiv, LinearEquiv.ofBijective, Module, Module.Flat.of_linearEquiv, algebraize, linearMap, ofBijective, of_linearEquiv
-/
lemma of_bijective {f : R ->+* S} (hf : Function.Bijective f) : Flat f := by
  algebraize [f]
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective (Algebra.linearMap R S) hf).symm

/--
lemma `containsIdentities` / 引理 `containsIdentities`

English:
lemma containsIdentities
  statement: ContainsIdentities Flat
  proof: id

中文:
引理 containsIdentities
  结论: 余ntainsIdentities 平坦
  证明: id
-/
lemma containsIdentities : ContainsIdentities Flat := id

/--
lemma `stableUnderComposition` / 引理 `stableUnderComposition`

English:
lemma stableUnderComposition
  statement: StableUnderComposition Flat
  proof: by
  introv R hf hg
  exact hf.comp hg

中文:
引理 stableUnderComposition
  结论: StableUnderComposition 平坦
  证明: by
  introv R hf hg
  exact hf.comp hg

Depends on / 依赖: hf.comp, introv
-/
lemma stableUnderComposition : StableUnderComposition Flat := by
  introv R hf hg
  exact hf.comp hg

/--
lemma `respectsIso` / 引理 `respectsIso`

English:
lemma respectsIso
  statement: RespectsIso Flat
  proof: by
  apply stableUnderComposition.respectsIso
  introv
  exact of_bijective e.bijective

中文:
引理 respectsIso
  结论: RespectsIso 平坦
  证明: by
  apply stableUnderComposition.respectsIso
  introv
  exact of_bijective e.bijective

Depends on / 依赖: bijective, e.bijective, introv, of_bijective, respectsIso, stableUnderComposition, stableUnderComposition.respectsIso
-/
lemma respectsIso : RespectsIso Flat := by
  apply stableUnderComposition.respectsIso
  introv
  exact of_bijective e.bijective

/--
lemma `isStableUnderBaseChange` / 引理 `isStableUnderBaseChange`

English:
lemma isStableUnderBaseChange
  statement: IsStableUnderBaseChange Flat
  proof: by
  apply IsStableUnderBaseChange.mk respectsIso
  introv h
  rw [flat_algebraMap_iff] at h ⊢
  infer_instance

中文:
引理 isStableUnderBaseChange
  结论: 是StableUnderBaseChange 平坦
  证明: by
  apply IsStableUnderBaseChange.mk respectsIso
  introv h
  rw [flat_algebraMap_iff] at h ⊢
  infer_instance

Depends on / 依赖: IsStableUnderBaseChange, IsStableUnderBaseChange.mk, flat_algebraMap_iff, infer_instance, introv, respectsIso
-/
lemma isStableUnderBaseChange : IsStableUnderBaseChange Flat := by
  apply IsStableUnderBaseChange.mk respectsIso
  introv h
  rw [flat_algebraMap_iff] at h ⊢
  infer_instance

/--
lemma `holdsForLocalizationAway` / 引理 `holdsForLocalizationAway`

English:
lemma holdsForLocalizationAway
  statement: HoldsForLocalizationAway Flat
  proof: by
  introv R h
  exact flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers r))

中文:
引理 holdsForLocalizationAway
  结论: HoldsForLocalizationAway 平坦
  证明: by
  introv R h
  exact flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers r))

Depends on / 依赖: IsLocalization, IsLocalization.flat, Submonoid, Submonoid.powers, flat_algebraMap_iff, flat_algebraMap_iff.mpr, introv, powers
-/
lemma holdsForLocalizationAway : HoldsForLocalizationAway Flat := by
  introv R h
  exact flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers r))

/--
lemma `ofLocalizationSpanTarget` / 引理 `ofLocalizationSpanTarget`

English:
lemma ofLocalizationSpanTarget
  statement: OfLocalizationSpanTarget Flat
  proof: by
  introv R hsp h
  algebraize_only [f]
  refine Module.flat_of_isLocalized_span _ _ s hsp _
    (fun r => Algebra.linearMap S <| Localization.Away r.1) ?_
  dsimp only [RingHom.Flat] at h
  convert! h; ext
  apply Algebra.smul_def

中文:
引理 ofLocalizationSpanTarget
  结论: OfLocalizationSpanTarget 平坦
  证明: by
  introv R hsp h
  algebraize_only [f]
  refine Module.flat_of_isLocalized_span _ _ s hsp _
    (fun r => Algebra.linearMap S <| Localization.Away r.1) ?_
  dsimp only [RingHom.Flat] at h
  convert! h; ext
  apply Algebra.smul_def

Depends on / 依赖: Algebra, Algebra.linearMap, Algebra.smul_def, Localization, Localization.Away, Module, Module.flat_of_isLocalized_span, RingHom, RingHom.Flat, algebraize_only, convert, flat_of_isLocalized_span, introv, linearMap, smul_def
-/
lemma ofLocalizationSpanTarget : OfLocalizationSpanTarget Flat := by
  introv R hsp h
  algebraize_only [f]
  refine Module.flat_of_isLocalized_span _ _ s hsp _
    (fun r => Algebra.linearMap S <| Localization.Away r.1) ?_
  dsimp only [RingHom.Flat] at h
  convert! h; ext
  apply Algebra.smul_def

/--
lemma `propertyIsLocal` / 引理 `propertyIsLocal`

English:
lemma propertyIsLocal
  statement: PropertyIsLocal Flat where
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
  结论: PropertyIsLocal 平坦 where
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
lemma propertyIsLocal : PropertyIsLocal Flat where
  localizationAwayPreserves := isStableUnderBaseChange.localizationPreserves.away
  ofLocalizationSpanTarget := ofLocalizationSpanTarget
  ofLocalizationSpan := ofLocalizationSpanTarget.ofLocalizationSpan
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).left
  StableUnderCompositionWithLocalizationAwayTarget :=
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).right

/--
lemma `ofLocalizationPrime` / 引理 `ofLocalizationPrime`

English:
lemma ofLocalizationPrime
  statement: OfLocalizationPrime Flat
  proof: by
  introv R h
  algebraize_only [f]
  rw [RingHom.Flat]
  apply Module.flat_of_isLocalized_maximal S S (fun P => Localization.AtPrime P)
    (fun P => Algebra.linearMap S _)
  intro P _
  algebraize_only [Localization.localRingHom (Ideal.comap f P) P f rfl]
  have : IsScalarTower R (Localization.AtPrime (Ideal.comap f P)) (Localization.AtPrime P) :=
    .of_algebraMap_eq fun x => (Localization.localRingHom_to_map _ _ _ rfl x).symm
  replace h : Module.Flat (Localization.AtPrime (Ideal.comap f P)) (Localization.AtPrime P) := h ..
  exact Module.Flat.trans R (Localization.AtPrime <| Ideal.comap f P) (Localization.AtPrime P)

中文:
引理 ofLocalizationPrime
  结论: OfLocalizationPrime 平坦
  证明: by
  introv R h
  algebraize_only [f]
  rw [RingHom.Flat]
  apply Module.flat_of_isLocalized_maximal S S (fun P => Localization.AtPrime P)
    (fun P => Algebra.linearMap S _)
  intro P _
  algebraize_only [Localization.localRingHom (Ideal.comap f P) P f rfl]
  have : IsScalarTower R (Localization.AtPrime (Ideal.comap f P)) (Localization.AtPrime P) :=
    .of_algebraMap_eq fun x => (Localization.localRingHom_to_map _ _ _ rfl x).symm
  replace h : Module.Flat (Localization.AtPrime (Ideal.comap f P)) (Localization.AtPrime P) := h ..
  exact Module.Flat.trans R (Localization.AtPrime <| Ideal.comap f P) (Localization.AtPrime P)

Depends on / 依赖: Algebra, Algebra.linearMap, AtPrim, AtPrime, Ideal.comap, IsScalarTower, Localization, Localization.AtPrim, Localization.AtPrime, Localization.localRingHom, Localization.localRingHom_to_map, Module, Module.Flat, Module.flat_of_isLocalized_maximal, RingHom, RingHom.Flat, algebraize_only, flat_of_isLocalized_maximal, introv, linearMap
-/
lemma ofLocalizationPrime : OfLocalizationPrime Flat := by
  introv R h
  algebraize_only [f]
  rw [RingHom.Flat]
  apply Module.flat_of_isLocalized_maximal S S (fun P => Localization.AtPrime P)
    (fun P => Algebra.linearMap S _)
  intro P _
  algebraize_only [Localization.localRingHom (Ideal.comap f P) P f rfl]
  have : IsScalarTower R (Localization.AtPrime (Ideal.comap f P)) (Localization.AtPrime P) :=
    .of_algebraMap_eq fun x => (Localization.localRingHom_to_map _ _ _ rfl x).symm
  replace h : Module.Flat (Localization.AtPrime (Ideal.comap f P)) (Localization.AtPrime P) := h ..
  exact Module.Flat.trans R (Localization.AtPrime <| Ideal.comap f P) (Localization.AtPrime P)

/--
lemma `localRingHom` / 引理 `localRingHom`

English:
lemma localRingHom
  statement: {f : R ->+* S} (hf : f.Flat)
  proof: by
  subst hQP
  algebraize [f, Localization.localRingHom (Ideal.comap f P) P f rfl]
  have : IsScalarTower R (Localization.AtPrime (Ideal.comap f P)) (Localization.AtPrime P) :=
    .of_algebraMap_eq fun x => (Localization.localRingHom_to_map _ _ _ rfl x).symm
  rw [RingHom.Flat]; rw [Module.flat_iff_of_isLocalization
    (S := (Localization.AtPrime (Ideal.comap f P))) (p := (Ideal.comap f P).primeCompl)]
  exact Module.Flat.trans R S (Localization.AtPrime P)

中文:
引理 localRingHom
  结论: {f : R ->+* S} (hf : f.平坦)
  证明: by
  subst hQP
  algebraize [f, Localization.localRingHom (Ideal.comap f P) P f rfl]
  have : IsScalarTower R (Localization.AtPrime (Ideal.comap f P)) (Localization.AtPrime P) :=
    .of_algebraMap_eq fun x => (Localization.localRingHom_to_map _ _ _ rfl x).symm
  rw [RingHom.Flat]; rw [Module.flat_iff_of_isLocalization
    (S := (Localization.AtPrime (Ideal.comap f P))) (p := (Ideal.comap f P).primeCompl)]
  exact Module.Flat.trans R S (Localization.AtPrime P)

Depends on / 依赖: AtPrime, Ideal.comap, IsScalarTower, Localization, Localization.AtPrime, Localization.localRingHom, Localization.localRingHom_to_map, Module, Module.Flat.trans, Module.flat_iff_of_isLocalization, RingHom, RingHom.Flat, algebraize, flat_iff_of_isLocalization, localRingHom, localRingHom_to_map, of_algebraMap_eq, primeCompl
-/
lemma localRingHom {f : R ->+* S} (hf : f.Flat)
    (P : Ideal S) [P.IsPrime] (Q : Ideal R) [Q.IsPrime] (hQP : Q = Ideal.comap f P) :
    (Localization.localRingHom Q P f hQP).Flat := by
  subst hQP
  algebraize [f, Localization.localRingHom (Ideal.comap f P) P f rfl]
  have : IsScalarTower R (Localization.AtPrime (Ideal.comap f P)) (Localization.AtPrime P) :=
    .of_algebraMap_eq fun x => (Localization.localRingHom_to_map _ _ _ rfl x).symm
  rw [RingHom.Flat]; rw [Module.flat_iff_of_isLocalization
    (S := (Localization.AtPrime (Ideal.comap f P))) (p := (Ideal.comap f P).primeCompl)]
  exact Module.Flat.trans R S (Localization.AtPrime P)

open PrimeSpectrum

/--
lemma `generalizingMap_comap` / 引理 `generalizingMap_comap`

English:
lemma generalizingMap_comap
  given: {f : R ->+* S} (hf : f.Flat)
  statement: GeneralizingMap (comap f)
  proof: by
  algebraize [f]
  change GeneralizingMap (comap (algebraMap R S))
  rw [← Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap]
  infer_instance

中文:
引理 generalizingMap_comap
  条件: {f : R ->+* S} (hf : f.平坦)
  结论: GeneralizingMap (comap f)
  证明: by
  algebraize [f]
  change GeneralizingMap (comap (algebraMap R S))
  rw [← Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap]
  infer_instance

Depends on / 依赖: Algebra, Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap, GeneralizingMap, HasGoingDown, algebraMap, algebraize, iff_generalizingMap_primeSpectrumComap, infer_instance
-/
lemma generalizingMap_comap {f : R ->+* S} (hf : f.Flat) : GeneralizingMap (comap f) := by
  algebraize [f]
  change GeneralizingMap (comap (algebraMap R S))
  rw [← Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap]
  infer_instance

/--
lemma `of_isField` / 引理 `of_isField`

English:
lemma of_isField
  given: (hR : IsField R) (f : R ->+* S)
  statement: f.Flat
  proof: by
  let := f.toAlgebra
  let := hR.toField
  rw [← f.algebraMap_toAlgebra]; rw [RingHom.flat_algebraMap_iff]
  infer_instance

中文:
引理 of_isField
  条件: (hR : 是域 R) (f : R ->+* S)
  结论: f.平坦
  证明: by
  let := f.toAlgebra
  let := hR.toField
  rw [← f.algebraMap_toAlgebra]; rw [RingHom.flat_algebraMap_iff]
  infer_instance

Depends on / 依赖: RingHom, RingHom.flat_algebraMap_iff, algebraMap_toAlgebra, f.algebraMap_toAlgebra, f.toAlgebra, flat_algebraMap_iff, hR.toField, infer_instance, toAlgebra, toField
-/
lemma of_isField (hR : IsField R) (f : R ->+* S) : f.Flat := by
  let := f.toAlgebra
  let := hR.toField
  rw [← f.algebraMap_toAlgebra]; rw [RingHom.flat_algebraMap_iff]
  infer_instance

section

variable [Algebra R S]
variable (A : Type*) {B C D : Type*} [CommRing A] [Algebra R A] [Algebra S A]
  [IsScalarTower R S A] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] [Algebra S C]
  [IsScalarTower R S C] [CommRing D] [Algebra R D]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/--
lemma `lTensor` / 引理 `lTensor`

English:
lemma lTensor
  given: {f : B ->ₐ[R] D} (hf : f.Flat)
  proof: by
  algebraize [f.toRingHom, (Algebra.TensorProduct.lTensor (S := A) A f).toRingHom]
  let e : A otimes[R] D ≃ₐ[A otimes[R] B] (A otimes[R] B) otimes[B] D :=
    { __ := (Algebra.IsPushout.cancelBaseChangeAlg _ _ _ _ _).symm,
      commutes' x := congr($(Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor R B D A) x) }
  exact .of_linearEquiv e.toLinearEquiv

中文:
引理 lTensor
  条件: {f : B ->ₐ[R] D} (hf : f.平坦)
  证明: by
  algebraize [f.toRingHom, (Algebra.TensorProduct.lTensor (S := A) A f).toRingHom]
  let e : A otimes[R] D ≃ₐ[A otimes[R] B] (A otimes[R] B) otimes[B] D :=
    { __ := (Algebra.IsPushout.cancelBaseChangeAlg _ _ _ _ _).symm,
      commutes' x := congr($(Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor R B D A) x) }
  exact .of_linearEquiv e.toLinearEquiv

Depends on / 依赖: Algebra, Algebra.IsPushout.cancelBaseChangeAlg, Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor, Algebra.TensorProduct.lTensor, IsPushout, TensorProduct, algebraize, cancelBaseChangeAlg, cancelBaseChange_symm_comp_lTensor, commutes, e.toLinearEquiv, f.toRingHom, lTensor, of_linearEquiv, otimes, toLinearEquiv, toRingHom
-/
lemma lTensor {f : B ->ₐ[R] D} (hf : f.Flat) :
    (Algebra.TensorProduct.lTensor (S := S) A f).Flat := by
  algebraize [f.toRingHom, (Algebra.TensorProduct.lTensor (S := A) A f).toRingHom]
  let e : A otimes[R] D ≃ₐ[A otimes[R] B] (A otimes[R] B) otimes[B] D :=
    { __ := (Algebra.IsPushout.cancelBaseChangeAlg _ _ _ _ _).symm,
      commutes' x := congr($(Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor R B D A) x) }
  exact .of_linearEquiv e.toLinearEquiv

variable {A} in
/--
lemma `tensorProductMap` / 引理 `tensorProductMap`

English:
lemma tensorProductMap
  given: {f : A ->ₐ[S] C} {g : B ->ₐ[R] D} (hf : f.Flat) (hg : g.Flat)
  proof: by
  have heq : Algebra.TensorProduct.map f g =
      (Algebra.TensorProduct.map f (.id R D)).comp (Algebra.TensorProduct.map (.id _ _) g) := by
    ext <;> simp
  rw [heq]
  refine RingHom.Flat.comp ?_ ?_
  · exact hg.lTensor _
  · have : (Algebra.TensorProduct.map f (AlgHom.id R D)).restrictScalars R =
        (Algebra.TensorProduct.comm _ _ _).toAlgHom.comp
          ((Algebra.TensorProduct.lTensor _ (f.restrictScalars R)).comp
            (Algebra.TensorProduct.comm _ _ _).toAlgHom) := by
      ext <;> simp
    change ((Algebra.TensorProduct.map f (AlgHom.id R D)).restrictScalars R).Flat
    rw [this]
    refine RingHom.Flat.comp ?_ (.of_bijective <| AlgEquiv.bijective _)
    change RingHom.Flat (RingHom.comp (Algebra.TensorProduct.lTensor D
      (AlgHom.restrictScalars R f)).toRingHom _)
    exact RingHom.Flat.comp (.of_bijective <| (TensorProduct.comm R A D).bijective) (lTensor D hf)

中文:
引理 tensorProductMap
  条件: {f : A ->ₐ[S] C} {g : B ->ₐ[R] D} (hf : f.平坦) (hg : g.平坦)
  证明: by
  have heq : Algebra.TensorProduct.map f g =
      (Algebra.TensorProduct.map f (.id R D)).comp (Algebra.TensorProduct.map (.id _ _) g) := by
    ext <;> simp
  rw [heq]
  refine RingHom.Flat.comp ?_ ?_
  · exact hg.lTensor _
  · have : (Algebra.TensorProduct.map f (AlgHom.id R D)).restrictScalars R =
        (Algebra.TensorProduct.comm _ _ _).toAlgHom.comp
          ((Algebra.TensorProduct.lTensor _ (f.restrictScalars R)).comp
            (Algebra.TensorProduct.comm _ _ _).toAlgHom) := by
      ext <;> simp
    change ((Algebra.TensorProduct.map f (AlgHom.id R D)).restrictScalars R).Flat
    rw [this]
    refine RingHom.Flat.comp ?_ (.of_bijective <| AlgEquiv.bijective _)
    change RingHom.Flat (RingHom.comp (Algebra.TensorProduct.lTensor D
      (AlgHom.restrictScalars R f)).toRingHom _)
    exact RingHom.Flat.comp (.of_bijective <| (TensorProduct.comm R A D).bijective) (lTensor D hf)

Depends on / 依赖: AlgHom, AlgHom.id, Algebra, Algebra.TensorProduct.comm, Algebra.TensorProduct.lTensor, Algebra.TensorProduct.map, RingHom, RingHom.Flat.comp, TensorProduct, f.restrictScalars, hg.lTensor, lTensor, restrictScalars, toAlgHom, toAlgHom.comp
-/
lemma tensorProductMap {f : A ->ₐ[S] C} {g : B ->ₐ[R] D} (hf : f.Flat) (hg : g.Flat) :
    (Algebra.TensorProduct.map f g).Flat := by
  have heq : Algebra.TensorProduct.map f g =
      (Algebra.TensorProduct.map f (.id R D)).comp (Algebra.TensorProduct.map (.id _ _) g) := by
    ext <;> simp
  rw [heq]
  refine RingHom.Flat.comp ?_ ?_
  · exact hg.lTensor _
  · have : (Algebra.TensorProduct.map f (AlgHom.id R D)).restrictScalars R =
        (Algebra.TensorProduct.comm _ _ _).toAlgHom.comp
          ((Algebra.TensorProduct.lTensor _ (f.restrictScalars R)).comp
            (Algebra.TensorProduct.comm _ _ _).toAlgHom) := by
      ext <;> simp
    change ((Algebra.TensorProduct.map f (AlgHom.id R D)).restrictScalars R).Flat
    rw [this]
    refine RingHom.Flat.comp ?_ (.of_bijective <| AlgEquiv.bijective _)
    change RingHom.Flat (RingHom.comp (Algebra.TensorProduct.lTensor D
      (AlgHom.restrictScalars R f)).toRingHom _)
    exact RingHom.Flat.comp (.of_bijective <| (TensorProduct.comm R A D).bijective) (lTensor D hf)

end

/--
lemma `comp_iff_of_bijective_left` / 引理 `comp_iff_of_bijective_left`

English:
lemma comp_iff_of_bijective_left
  given: {f : R ->+* S} {g : S ->+* T} (hg : Function.Bijective g)
  proof: by
  refine ⟨fun hf => ?_, fun hf => .comp hf (.of_bijective hg)⟩
  let e := RingEquiv.ofBijective g hg
  have : f = e.symm.toRingHom.comp (e.toRingHom.comp f) := by ext; simp
  rw [this]
  exact .comp hf (.of_bijective e.symm.bijective)

中文:
引理 comp_iff_of_bijective_left
  条件: {f : R ->+* S} {g : S ->+* T} (hg : 函数.双射 g)
  证明: by
  refine ⟨fun hf => ?_, fun hf => .comp hf (.of_bijective hg)⟩
  let e := RingEquiv.ofBijective g hg
  have : f = e.symm.toRingHom.comp (e.toRingHom.comp f) := by ext; simp
  rw [this]
  exact .comp hf (.of_bijective e.symm.bijective)

Depends on / 依赖: RingEquiv, RingEquiv.ofBijective, bijective, e.symm.bijective, e.symm.toRingHom.comp, e.toRingHom.comp, ofBijective, of_bijective, toRingHom
-/
lemma comp_iff_of_bijective_left {f : R ->+* S} {g : S ->+* T} (hg : Function.Bijective g) :
    (g.comp f).Flat ↔ f.Flat := by
  refine ⟨fun hf => ?_, fun hf => .comp hf (.of_bijective hg)⟩
  let e := RingEquiv.ofBijective g hg
  have : f = e.symm.toRingHom.comp (e.toRingHom.comp f) := by ext; simp
  rw [this]
  exact .comp hf (.of_bijective e.symm.bijective)

/--
lemma `comp_iff_of_bijective_right` / 引理 `comp_iff_of_bijective_right`

English:
lemma comp_iff_of_bijective_right
  given: {f : R ->+* S} {g : T ->+* R} (hg : Function.Bijective g)
  proof: by
  refine ⟨fun hf => ?_, fun hf => .comp (.of_bijective hg) hf⟩
  let e := RingEquiv.ofBijective g hg
  have : f = (f.comp e.toRingHom).comp e.symm.toRingHom := by ext; simp
  rw [this]
  exact .comp (.of_bijective e.symm.bijective) hf

@[simp]

中文:
引理 comp_iff_of_bijective_right
  条件: {f : R ->+* S} {g : T ->+* R} (hg : 函数.双射 g)
  证明: by
  refine ⟨fun hf => ?_, fun hf => .comp (.of_bijective hg) hf⟩
  let e := RingEquiv.ofBijective g hg
  have : f = (f.comp e.toRingHom).comp e.symm.toRingHom := by ext; simp
  rw [this]
  exact .comp (.of_bijective e.symm.bijective) hf

@[simp]

Depends on / 依赖: RingEquiv, RingEquiv.ofBijective, bijective, e.symm.bijective, e.symm.toRingHom, e.toRingHom, f.comp, ofBijective, of_bijective, toRingHom
-/
lemma comp_iff_of_bijective_right {f : R ->+* S} {g : T ->+* R} (hg : Function.Bijective g) :
    (f.comp g).Flat ↔ f.Flat := by
  refine ⟨fun hf => ?_, fun hf => .comp (.of_bijective hg) hf⟩
  let e := RingEquiv.ofBijective g hg
  have : f = (f.comp e.toRingHom).comp e.symm.toRingHom := by ext; simp
  rw [this]
  exact .comp (.of_bijective e.symm.bijective) hf

@[simp]
/--
lemma `ulift_iff` / 引理 `ulift_iff`

English:
lemma ulift_iff
  given: {f : R ->+* S}
  statement: (ulift.{u₁, u₂} f).Flat ↔ f.Flat
  proof: by
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · rwa [← comp_ulift_eq.{u₁, u₂} f, comp_iff_of_bijective_left (Equiv.bijective _),
      comp_iff_of_bijective_right (Equiv.bijective _)]
  · exact .comp (.comp (.of_bijective <| Equiv.bijective _) hf)
      (.of_bijective <| Equiv.bijective _)

中文:
引理 ulift_iff
  条件: {f : R ->+* S}
  结论: (ulift.{u₁, u₂} f).平坦 ↔ f.平坦
  证明: by
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · rwa [← comp_ulift_eq.{u₁, u₂} f, comp_iff_of_bijective_left (Equiv.bijective _),
      comp_iff_of_bijective_right (Equiv.bijective _)]
  · exact .comp (.comp (.of_bijective <| Equiv.bijective _) hf)
      (.of_bijective <| Equiv.bijective _)

Depends on / 依赖: Equiv.bijective, bijective, comp_iff_of_bijective_left, comp_iff_of_bijective_right, comp_ulift_eq, of_bijective
-/
lemma ulift_iff {f : R ->+* S} : (ulift.{u₁, u₂} f).Flat ↔ f.Flat := by
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · rwa [← comp_ulift_eq.{u₁, u₂} f, comp_iff_of_bijective_left (Equiv.bijective _),
      comp_iff_of_bijective_right (Equiv.bijective _)]
  · exact .comp (.comp (.of_bijective <| Equiv.bijective _) hf)
      (.of_bijective <| Equiv.bijective _)

end RingHom.Flat

section

open CategoryTheory Limits

variable {R S T : CommRingCat} (f : R ⟶ S) (g : R ⟶ T)

/--
lemma `CommRingCat.inr_injective_of_flat` / 引理 `CommRingCat.inr_injective_of_flat`

English:
lemma CommRingCat.inr_injective_of_flat
  proof: by
  algebraize [f.hom, g.hom]
  have : _ = pushout.inr f g := (CommRingCat.isPushout_tensorProduct R S T).inr_isoPushout_hom
  rw [← this]
  exact (CommRingCat.isPushout_tensorProduct R S T).isoPushout.commRingCatIsoToRingEquiv
.injective.comp (Algebra.TensorProduct.includeRight_injective (B := T) hf)

中文:
引理 交换环范畴.inr_injective_of_flat
  证明: by
  algebraize [f.hom, g.hom]
  have : _ = pushout.inr f g := (CommRingCat.isPushout_tensorProduct R S T).inr_isoPushout_hom
  rw [← this]
  exact (CommRingCat.isPushout_tensorProduct R S T).isoPushout.commRingCatIsoToRingEquiv
.injective.comp (Algebra.TensorProduct.includeRight_injective (B := T) hf)

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeRight_injective, CommRingCat, CommRingCat.isPushout_tensorProduct, TensorProduct, algebraize, commRingCatIsoToRingEquiv, f.hom, g.hom, includeRight_injective, injective, injective.comp, inr_isoPushout_hom, isPushout_tensorProduct, isoPushout, isoPushout.commRingCatIsoToRingEquiv, pushout, pushout.inr
-/
lemma CommRingCat.inr_injective_of_flat
    (hf : Function.Injective f) (hg : g.hom.Flat) : Function.Injective (pushout.inr f g) := by
  algebraize [f.hom, g.hom]
  have : _ = pushout.inr f g := (CommRingCat.isPushout_tensorProduct R S T).inr_isoPushout_hom
  rw [← this]
  exact (CommRingCat.isPushout_tensorProduct R S T).isoPushout.commRingCatIsoToRingEquiv
.injective.comp (Algebra.TensorProduct.includeRight_injective (B := T) hf)

/--
lemma `CommRingCat.inl_injective_of_flat` / 引理 `CommRingCat.inl_injective_of_flat`

English:
lemma CommRingCat.inl_injective_of_flat
  proof: by
  algebraize [f.hom, g.hom]
  have : _ = pushout.inl f g := (CommRingCat.isPushout_tensorProduct R S T).inl_isoPushout_hom
  rw [← this]
  exact (CommRingCat.isPushout_tensorProduct R S T).isoPushout.commRingCatIsoToRingEquiv
.injective.comp (Algebra.TensorProduct.includeLeft_injective (S := R) (A := S) hg)

中文:
引理 交换环范畴.inl_injective_of_flat
  证明: by
  algebraize [f.hom, g.hom]
  have : _ = pushout.inl f g := (CommRingCat.isPushout_tensorProduct R S T).inl_isoPushout_hom
  rw [← this]
  exact (CommRingCat.isPushout_tensorProduct R S T).isoPushout.commRingCatIsoToRingEquiv
.injective.comp (Algebra.TensorProduct.includeLeft_injective (S := R) (A := S) hg)

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeLeft_injective, CommRingCat, CommRingCat.isPushout_tensorProduct, TensorProduct, algebraize, commRingCatIsoToRingEquiv, f.hom, g.hom, includeLeft_injective, injective, injective.comp, inl_isoPushout_hom, isPushout_tensorProduct, isoPushout, isoPushout.commRingCatIsoToRingEquiv, pushout, pushout.inl
-/
lemma CommRingCat.inl_injective_of_flat
    (hf : f.hom.Flat) (hg : Function.Injective g) : Function.Injective (pushout.inl f g) := by
  algebraize [f.hom, g.hom]
  have : _ = pushout.inl f g := (CommRingCat.isPushout_tensorProduct R S T).inl_isoPushout_hom
  rw [← this]
  exact (CommRingCat.isPushout_tensorProduct R S T).isoPushout.commRingCatIsoToRingEquiv
.injective.comp (Algebra.TensorProduct.includeLeft_injective (S := R) (A := S) hg)

end

open CategoryTheory

namespace CommRingCat

/--
Definition of `flat` / `flat` 的定义

English:
definition flat
  signature: : MorphismProperty CommRingCat.{u}
  body: RingHom.toMorphismProperty fun f => f.Flat

@[simp]

中文:
定义 flat
  签名: : MorphismProperty 交换环范畴.{u}
  定义体: RingHom.toMorphismProperty fun f => f.Flat

@[simp]

Depends on / 依赖: RingHom, RingHom.toMorphismProperty, f.Flat, toMorphismProperty
-/
def flat : MorphismProperty CommRingCat.{u} :=
  RingHom.toMorphismProperty fun f => f.Flat

@[simp]
/--
lemma `flat_iff` / 引理 `flat_iff`

English:
lemma flat_iff
  given: {R S : CommRingCat.{u}} (f : R ⟶ S)
  proof: .rfl

中文:
引理 flat_iff
  条件: {R S : 交换环范畴.{u}} (f : R ⟶ S)
  证明: .rfl
-/
lemma flat_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    flat f ↔ f.hom.Flat := .rfl

/--
lemma `flat_ofHom_iff` / 引理 `flat_ofHom_iff`

English:
lemma flat_ofHom_iff
  given: {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S)
  proof: .rfl

中文:
引理 flat_ofHom_iff
  条件: {R S : 类型u} [交换环 R] [交换环 S] (f : R ->+* S)
  证明: .rfl
-/
lemma flat_ofHom_iff {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S) :
    flat (ofHom f) ↔ f.Flat := .rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: flat.IsStableUnderCobaseChange
  body: by
  rw [flat]; rw [RingHom.isStableUnderCobaseChange_toMorphismProperty_iff]
  exact RingHom.Flat.isStableUnderBaseChange

中文:
实例 :
  签名: flat.是StableUnderCobaseChange
  定义体: by
  rw [flat]; rw [RingHom.isStableUnderCobaseChange_toMorphismProperty_iff]
  exact RingHom.Flat.isStableUnderBaseChange

Depends on / 依赖: RingHom, RingHom.Flat.isStableUnderBaseChange, RingHom.isStableUnderCobaseChange_toMorphismProperty_iff, isStableUnderBaseChange, isStableUnderCobaseChange_toMorphismProperty_iff
-/
instance : flat.IsStableUnderCobaseChange := by
  rw [flat]; rw [RingHom.isStableUnderCobaseChange_toMorphismProperty_iff]
  exact RingHom.Flat.isStableUnderBaseChange

end CommRingCat

open CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false in
-- TODO: If necessary, generalize the universes here by composing with suitable `ULift`
-- isomorphisms.
/--
lemma `RingHom.Flat.mapOfCompatibleSMul` / 引理 `RingHom.Flat.mapOfCompatibleSMul`

English:
lemma RingHom.Flat.mapOfCompatibleSMul
  statement: {R S : Type u} (T A : Type u)
  proof: by
  rw [← CommRingCat.flat_ofHom_iff] at h ⊢
  apply MorphismProperty.of_isPushout _ h
  · exact CommRingCat.ofHom
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S T)
      (IsScalarTower.toAlgHom R S A)).toRingHom
  · exact CommRingCat.ofHom
      (RingHom.comp (Algebra.TensorProduct.includeLeft (S := R)).toRingHom (algebraMap S T))
  · refine .of_iso
      (isPushout_map_codiagonal (CommRingCat.ofHom <| algebraMap S T)
        (CommRingCat.ofHom <| algebraMap S A) (CommRingCat.ofHom <| algebraMap R S))
      ?_ ?_ (.refl _) ?_ ?_ ?_ ?_ ?_
    · exact (CommRingCat.isPushout_tensorProduct R S S).isoPushout.symm
    · exact pushout.congrHom (by simp [IsScalarTower.algebraMap_eq R S T])
          (by simp [IsScalarTower.algebraMap_eq R S A]) ≪≫
        (CommRingCat.isPushout_tensorProduct R T A).isoPushout.symm
    · exact (CommRingCat.isPushout_tensorProduct S T A).isoPushout.symm
    all_goals ext <;> simp

中文:
引理 环态射.平坦.mapOfCompatibleSMul
  结论: {R S : 类型u} (T A : 类型u)
  证明: by
  rw [← CommRingCat.flat_ofHom_iff] at h ⊢
  apply MorphismProperty.of_isPushout _ h
  · exact CommRingCat.ofHom
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S T)
      (IsScalarTower.toAlgHom R S A)).toRingHom
  · exact CommRingCat.ofHom
      (RingHom.comp (Algebra.TensorProduct.includeLeft (S := R)).toRingHom (algebraMap S T))
  · refine .of_iso
      (isPushout_map_codiagonal (CommRingCat.ofHom <| algebraMap S T)
        (CommRingCat.ofHom <| algebraMap S A) (CommRingCat.ofHom <| algebraMap R S))
      ?_ ?_ (.refl _) ?_ ?_ ?_ ?_ ?_
    · exact (CommRingCat.isPushout_tensorProduct R S S).isoPushout.symm
    · exact pushout.congrHom (by simp [IsScalarTower.algebraMap_eq R S T])
          (by simp [IsScalarTower.algebraMap_eq R S A]) ≪≫
        (CommRingCat.isPushout_tensorProduct R T A).isoPushout.symm
    · exact (CommRingCat.isPushout_tensorProduct S T A).isoPushout.symm
    all_goals ext <;> simp
-/
lemma RingHom.Flat.mapOfCompatibleSMul {R S : Type u} (T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A] [Algebra R S]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    (h : (Algebra.TensorProduct.lmul' (S := S) R).Flat) :
    (Algebra.TensorProduct.mapOfCompatibleSMul S R T T A).Flat := by
  rw [← CommRingCat.flat_ofHom_iff] at h ⊢
  apply MorphismProperty.of_isPushout _ h
  · exact CommRingCat.ofHom
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S T)
      (IsScalarTower.toAlgHom R S A)).toRingHom
  · exact CommRingCat.ofHom
      (RingHom.comp (Algebra.TensorProduct.includeLeft (S := R)).toRingHom (algebraMap S T))
  · refine .of_iso
      (isPushout_map_codiagonal (CommRingCat.ofHom <| algebraMap S T)
        (CommRingCat.ofHom <| algebraMap S A) (CommRingCat.ofHom <| algebraMap R S))
      ?_ ?_ (.refl _) ?_ ?_ ?_ ?_ ?_
    · exact (CommRingCat.isPushout_tensorProduct R S S).isoPushout.symm
    · exact pushout.congrHom (by simp [IsScalarTower.algebraMap_eq R S T])
          (by simp [IsScalarTower.algebraMap_eq R S A]) ≪≫
        (CommRingCat.isPushout_tensorProduct R T A).isoPushout.symm
    · exact (CommRingCat.isPushout_tensorProduct S T A).isoPushout.symm
    all_goals ext <;> simp
