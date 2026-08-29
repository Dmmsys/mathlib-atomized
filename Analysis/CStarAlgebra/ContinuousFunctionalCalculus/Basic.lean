/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

/-! # Continuous functional calculus

In this file we construct the `continuousFunctionalCalculus` for a normal element `a` of a
(unital) C⋆-algebra over `ℂ`. This is a star algebra equivalence
`C(spectrum ℂ a, ℂ) ≃⋆ₐ[ℂ] elemental ℂ a` which sends the (restriction of) the
identity map `ContinuousMap.id ℂ` to the (unique) preimage of `a` under the coercion of
`elemental ℂ a` to `A`.

Being a star algebra equivalence between C⋆-algebras, this map is continuous (even an isometry),
and by the Stone-Weierstrass theorem it is the unique star algebra equivalence which extends the
polynomial functional calculus (i.e., `Polynomial.aeval`).

For any continuous function `f : spectrum ℂ a → ℂ`, this makes it possible to define an element
`f a` (not valid notation) in the original algebra, which heuristically has the same eigenspaces as
`a` and acts on eigenvector of `a` for an eigenvalue `λ` as multiplication by `f λ`. This
description is perfectly accurate in finite dimension, but only heuristic in infinite dimension as
there might be no genuine eigenvector. In particular, when `f` is a polynomial `∑ cᵢ Xⁱ`, then
`f a` is `∑ cᵢ aⁱ`. Also, `id a = a`.

The result we have established here is the strongest possible, but it is not the version which is
most useful in practice. The generic API for the continuous functional calculus can be found in
`Analysis.CStarAlgebra.ContinuousFunctionalCalculus` in the `Unital` and `NonUnital` files. The
relevant instances on C⋆-algebra can be found in the `Instances` file.

## Main definitions

* `continuousFunctionalCalculus : C(spectrum ℂ a, ℂ) ≃⋆ₐ[ℂ] elemental ℂ a`: this
  is the composition of the inverse of the `gelfandStarTransform` with the natural isomorphism
  induced by the homeomorphism `elemental.characterSpaceHomeo`.
* `elemental.characterSpaceHomeo` :
  `characterSpace ℂ (elemental ℂ a) ≃ₜ spectrum ℂ a`: this homeomorphism is defined
  by evaluating a character `φ` at `a`, and noting that `φ a ∈ spectrum ℂ a` since `φ` is an
  algebra homomorphism. Moreover, this map is continuous and bijective and since the spaces involved
  are compact Hausdorff, it is a homeomorphism.
* `IsStarNormal.instContinuousFunctionalCalculus`: the continuous functional calculus for normal
  elements in a unital C⋆-algebra over `ℂ`.
* `CStarAlgebra.instNonnegSpectrumClass`: In a unital C⋆-algebra over `ℂ` which is also a
  `StarOrderedRing`, the spectrum of a nonnegative element is nonnegative.

-/

@[expose] public section


open scoped Pointwise ENNReal NNReal ComplexOrder CStarAlgebra

open WeakDual WeakDual.CharacterSpace

variable {A : Type*}

namespace StarAlgebra.elemental

variable [CStarAlgebra A]

instance {R A : Type*} [CommRing R] [StarRing R] [NormedRing A] [Algebra R A] [StarRing A]
    [ContinuousStar A] [StarModule R A] (a : A) [IsStarNormal a] :
    NormedCommRing (elemental R a) :=
  { SubringClass.toNormedRing (elemental R a) with
    mul_comm := mul_comm }

noncomputable instance (a : A) [IsStarNormal a] : CommCStarAlgebra (elemental Complex a) where

variable (a : A) [IsStarNormal a]

set_option backward.isDefEq.respectTransparency false in
/-- The natural map from `characterSpace ℂ (elemental ℂ x)` to `spectrum ℂ x` given
by evaluating `φ` at `x`. This is essentially just evaluation of the `gelfandTransform` of `x`,
but because we want something in `spectrum ℂ x`, as opposed to
`spectrum ℂ ⟨x, elemental.self_mem ℂ x⟩` there is slightly more work to do. -/
@[simps]
/--
Definition of `characterSpaceToSpectrum` / `characterSpaceToSpectrum` 的定义

English:
definition characterSpaceToSpectrum
  signature: (x : A)
  body: φ ⟨x, self_mem Complex x⟩
  property := by
    simpa only [StarSubalgebra.spectrum_eq (hS := isClosed Complex x)
      (a := ⟨x, self_mem Complex x⟩)] using AlgHom.apply_mem_spectrum φ ⟨x, self_mem Complex x⟩

中文:
定义 characterSpaceToSpectrum
  签名: (x : A)
  定义体: φ ⟨x, self_mem Complex x⟩
  property := by
    simpa only [StarSubalgebra.spectrum_eq (hS := isClosed Complex x)
      (a := ⟨x, self_mem Complex x⟩)] using AlgHom.apply_mem_spectrum φ ⟨x, self_mem Complex x⟩

Depends on / 依赖: self_mem
-/
noncomputable def characterSpaceToSpectrum (x : A)
    (φ : characterSpace Complex (elemental Complex x)) : spectrum Complex x where
  val := φ ⟨x, self_mem Complex x⟩
  property := by
    simpa only [StarSubalgebra.spectrum_eq (hS := isClosed Complex x)
      (a := ⟨x, self_mem Complex x⟩)] using AlgHom.apply_mem_spectrum φ ⟨x, self_mem Complex x⟩

/--
theorem `continuous_characterSpaceToSpectrum` / 定理 `continuous_characterSpaceToSpectrum`

English:
theorem continuous_characterSpaceToSpectrum
  given: (x : A)
  proof: continuous_induced_rng.2
    (map_continuous <| gelfandTransform Complex (elemental Complex x) ⟨x, self_mem Complex x⟩)

中文:
定理 continuous_characterSpaceToSpectrum
  条件: (x : A)
  证明: continuous_induced_rng.2
    (map_continuous <| gelfandTransform Complex (elemental Complex x) ⟨x, self_mem Complex x⟩)

Depends on / 依赖: continuous_induced_rng, elemental, gelfandTransform, map_continuous, self_mem
-/
theorem continuous_characterSpaceToSpectrum (x : A) :
    Continuous (characterSpaceToSpectrum x) :=
  continuous_induced_rng.2
    (map_continuous <| gelfandTransform Complex (elemental Complex x) ⟨x, self_mem Complex x⟩)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `bijective_characterSpaceToSpectrum` / 定理 `bijective_characterSpaceToSpectrum`

English:
theorem bijective_characterSpaceToSpectrum
  proof: by
  refine ⟨fun φ ψ h => starAlgHomClass_ext Complex ?_ ?_ ?_, ?_⟩
  · exact (map_continuous φ)
  · exact (map_continuous ψ)
  · simpa only [characterSpaceToSpectrum, Subtype.mk_eq_mk,
      ContinuousMap.coe_mk] using h
  · rintro ⟨z, hz⟩
    have hz' := (StarSubalgebra.spectrum_eq (hS := isClosed Complex a)
      (a := ⟨a, self_mem Complex a⟩) ▸ hz)
    rw [CharacterSpace.mem_spectrum_iff_exists] at hz'
    obtain ⟨φ, rfl⟩ := hz'
    exact ⟨φ, rfl⟩

中文:
定理 bijective_characterSpaceToSpectrum
  证明: by
  refine ⟨fun φ ψ h => starAlgHomClass_ext Complex ?_ ?_ ?_, ?_⟩
  · exact (map_continuous φ)
  · exact (map_continuous ψ)
  · simpa only [characterSpaceToSpectrum, Subtype.mk_eq_mk,
      ContinuousMap.coe_mk] using h
  · rintro ⟨z, hz⟩
    have hz' := (StarSubalgebra.spectrum_eq (hS := isClosed Complex a)
      (a := ⟨a, self_mem Complex a⟩) ▸ hz)
    rw [CharacterSpace.mem_spectrum_iff_exists] at hz'
    obtain ⟨φ, rfl⟩ := hz'
    exact ⟨φ, rfl⟩

Depends on / 依赖: CharacterSpace, CharacterSpace.mem_spectrum_iff_exists, ContinuousMap, ContinuousMap.coe_mk, StarSubalgebra, StarSubalgebra.spectrum_eq, Subtype, Subtype.mk_eq_mk, characterSpaceToSpectrum, coe_mk, isClosed, map_continuous, mem_spectrum_iff_exists, mk_eq_mk, self_mem, spectrum_eq, starAlgHomClass_ext
-/
theorem bijective_characterSpaceToSpectrum :
    Function.Bijective (characterSpaceToSpectrum a) := by
  refine ⟨fun φ ψ h => starAlgHomClass_ext Complex ?_ ?_ ?_, ?_⟩
  · exact (map_continuous φ)
  · exact (map_continuous ψ)
  · simpa only [characterSpaceToSpectrum, Subtype.mk_eq_mk,
      ContinuousMap.coe_mk] using h
  · rintro ⟨z, hz⟩
    have hz' := (StarSubalgebra.spectrum_eq (hS := isClosed Complex a)
      (a := ⟨a, self_mem Complex a⟩) ▸ hz)
    rw [CharacterSpace.mem_spectrum_iff_exists] at hz'
    obtain ⟨φ, rfl⟩ := hz'
    exact ⟨φ, rfl⟩

/--
Definition of `characterSpaceHomeo` / `characterSpaceHomeo` 的定义

English:
definition characterSpaceHomeo
  signature: :
  body: @Continuous.homeoOfEquivCompactToT2 _ _ _ _ _ _
    (Equiv.ofBijective (characterSpaceToSpectrum a)
      (bijective_characterSpaceToSpectrum a))
    (continuous_characterSpaceToSpectrum a)

中文:
定义 characterSpaceHomeo
  签名: :
  定义体: @Continuous.homeoOfEquivCompactToT2 _ _ _ _ _ _
    (Equiv.ofBijective (characterSpaceToSpectrum a)
      (bijective_characterSpaceToSpectrum a))
    (continuous_characterSpaceToSpectrum a)

Depends on / 依赖: Continuous, Continuous.homeoOfEquivCompactToT2, Equiv.ofBijective, bijective_characterSpaceToSpectrum, characterSpaceToSpectrum, continuous_characterSpaceToSpectrum, homeoOfEquivCompactToT2, ofBijective
-/
noncomputable def characterSpaceHomeo :
    characterSpace Complex (elemental Complex a) ≃ₜ spectrum Complex a :=
  @Continuous.homeoOfEquivCompactToT2 _ _ _ _ _ _
    (Equiv.ofBijective (characterSpaceToSpectrum a)
      (bijective_characterSpaceToSpectrum a))
    (continuous_characterSpaceToSpectrum a)

end StarAlgebra.elemental

open StarAlgebra elemental


/--
Definition of `continuousFunctionalCalculus` / `continuousFunctionalCalculus` 的定义

English:
definition continuousFunctionalCalculus
  signature: [CStarAlgebra A] (a : A) [IsStarNormal a]
  body: ((characterSpaceHomeo a).compStarAlgEquiv' Complex Complex).trans
    (gelfandStarTransform (elemental Complex a)).symm

中文:
定义 continuousFunctionalCalculus
  签名: [CStar代数 A] (a : A) [是StarNormal a]
  定义体: ((characterSpaceHomeo a).compStarAlgEquiv' Complex Complex).trans
    (gelfandStarTransform (elemental Complex a)).symm

Depends on / 依赖: characterSpaceHomeo, compStarAlgEquiv, elemental, gelfandStarTransform
-/
noncomputable def continuousFunctionalCalculus [CStarAlgebra A] (a : A) [IsStarNormal a] :
    C(spectrum Complex a, Complex) ≃⋆ₐ[Complex] elemental Complex a :=
  ((characterSpaceHomeo a).compStarAlgEquiv' Complex Complex).trans
    (gelfandStarTransform (elemental Complex a)).symm

/--
theorem `continuousFunctionalCalculus_map_id` / 定理 `continuousFunctionalCalculus_map_id`

English:
theorem continuousFunctionalCalculus_map_id
  given: [CStarAlgebra A] (a : A) [IsStarNormal a]
  proof: (gelfandStarTransform (elemental Complex a)).symm_apply_apply _

中文:
定理 continuousFunctionalCalculus_map_id
  条件: [CStar代数 A] (a : A) [是StarNormal a]
  证明: (gelfandStarTransform (elemental Complex a)).symm_apply_apply _

Depends on / 依赖: elemental, gelfandStarTransform, symm_apply_apply
-/
theorem continuousFunctionalCalculus_map_id [CStarAlgebra A] (a : A) [IsStarNormal a] :
    continuousFunctionalCalculus a ((ContinuousMap.id Complex).restrict (spectrum Complex a)) =
      ⟨a, self_mem Complex a⟩ :=
  (gelfandStarTransform (elemental Complex a)).symm_apply_apply _

/-!
### Continuous functional calculus for normal elements
-/

local notation "σₙ" => quasispectrum

section Normal

section Unital

variable [CStarAlgebra A]

/--
theorem `IsStarNormal.instContinuousFunctionalCalculus` / 定理 `IsStarNormal.instContinuousFunctionalCalculus`

English:
theorem IsStarNormal.instContinuousFunctionalCalculus
  proof: .zero
  spectrum_nonempty a _ := spectrum.nonempty a
  exists_cfc_of_predicate a ha := by
    have : Isometry ((StarAlgebra.elemental Complex a).subtype.comp <| continuousFunctionalCalculus a :
        C(spectrum Complex a, Complex) ->⋆ₐ[Complex] A) :=
isometry_subtype_coe.comp StarAlgEquiv.isometry (continuousFunctionalCalculus a)
    refine ⟨_, this.continuous, this.injective, ?hom_id, ?hom_map_spectrum, ?predicate_hom⟩
case hom_id => exact congr_arg Subtype.val continuousFunctionalCalculus_map_id a
    case hom_map_spectrum =>
      intro f
      simp only [StarAlgHom.comp_apply, StarAlgHom.coe_coe, StarSubalgebra.coe_subtype]
      rw [← StarSubalgebra.spectrum_eq (hS := StarAlgebra.elemental.isClosed Complex a)]; rw [AlgEquiv.spectrum_eq (continuousFunctionalCalculus a)]; rw [ContinuousMap.spectrum_eq_range]
.map _⟩ case predicate_hom => exact fun f => ⟨by rw [← map_star]; exact Commute.all (star f) f

中文:
定理 是StarNormal.instContinuousFunctionalCalculus
  证明: .zero
  spectrum_nonempty a _ := spectrum.nonempty a
  exists_cfc_of_predicate a ha := by
    have : Isometry ((StarAlgebra.elemental Complex a).subtype.comp <| continuousFunctionalCalculus a :
        C(spectrum Complex a, Complex) ->⋆ₐ[Complex] A) :=
isometry_subtype_coe.comp StarAlgEquiv.isometry (continuousFunctionalCalculus a)
    refine ⟨_, this.continuous, this.injective, ?hom_id, ?hom_map_spectrum, ?predicate_hom⟩
case hom_id => exact congr_arg Subtype.val continuousFunctionalCalculus_map_id a
    case hom_map_spectrum =>
      intro f
      simp only [StarAlgHom.comp_apply, StarAlgHom.coe_coe, StarSubalgebra.coe_subtype]
      rw [← StarSubalgebra.spectrum_eq (hS := StarAlgebra.elemental.isClosed Complex a)]; rw [AlgEquiv.spectrum_eq (continuousFunctionalCalculus a)]; rw [ContinuousMap.spectrum_eq_range]
.map _⟩ case predicate_hom => exact fun f => ⟨by rw [← map_star]; exact Commute.all (star f) f
-/
theorem IsStarNormal.instContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus Complex A IsStarNormal where
  predicate_zero := .zero
  spectrum_nonempty a _ := spectrum.nonempty a
  exists_cfc_of_predicate a ha := by
    have : Isometry ((StarAlgebra.elemental Complex a).subtype.comp <| continuousFunctionalCalculus a :
        C(spectrum Complex a, Complex) ->⋆ₐ[Complex] A) :=
isometry_subtype_coe.comp StarAlgEquiv.isometry (continuousFunctionalCalculus a)
    refine ⟨_, this.continuous, this.injective, ?hom_id, ?hom_map_spectrum, ?predicate_hom⟩
case hom_id => exact congr_arg Subtype.val continuousFunctionalCalculus_map_id a
    case hom_map_spectrum =>
      intro f
      simp only [StarAlgHom.comp_apply, StarAlgHom.coe_coe, StarSubalgebra.coe_subtype]
      rw [← StarSubalgebra.spectrum_eq (hS := StarAlgebra.elemental.isClosed Complex a)]; rw [AlgEquiv.spectrum_eq (continuousFunctionalCalculus a)]; rw [ContinuousMap.spectrum_eq_range]
.map _⟩ case predicate_hom => exact fun f => ⟨by rw [← map_star]; exact Commute.all (star f) f

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/--
lemma `cfcHom_eq_of_isStarNormal` / 引理 `cfcHom_eq_of_isStarNormal`

English:
lemma cfcHom_eq_of_isStarNormal
  given: (a : A) [ha : IsStarNormal a]
  proof: by
  refine cfcHom_eq_of_continuous_of_map_id ha _ ?_ ?_
· exact continuous_subtype_val.comp
      (StarAlgEquiv.isometry (continuousFunctionalCalculus a)).continuous
  · simp [continuousFunctionalCalculus_map_id a]

中文:
引理 cfcHom_eq_of_isStarNormal
  条件: (a : A) [ha : 是StarNormal a]
  证明: by
  refine cfcHom_eq_of_continuous_of_map_id ha _ ?_ ?_
· exact continuous_subtype_val.comp
      (StarAlgEquiv.isometry (continuousFunctionalCalculus a)).continuous
  · simp [continuousFunctionalCalculus_map_id a]

Depends on / 依赖: StarAlgEquiv, StarAlgEquiv.isometry, cfcHom_eq_of_continuous_of_map_id, continuous, continuousFunctionalCalculus, continuousFunctionalCalculus_map_id, continuous_subtype_val, continuous_subtype_val.comp, isometry
-/
lemma cfcHom_eq_of_isStarNormal (a : A) [ha : IsStarNormal a] :
    cfcHom ha = (StarAlgebra.elemental Complex a).subtype.comp (continuousFunctionalCalculus a) := by
  refine cfcHom_eq_of_continuous_of_map_id ha _ ?_ ?_
· exact continuous_subtype_val.comp
      (StarAlgEquiv.isometry (continuousFunctionalCalculus a)).continuous
  · simp [continuousFunctionalCalculus_map_id a]

/--
Instance `IsStarNormal.instIsometricContinuousFunctionalCalculus` / 实例 `IsStarNormal.instIsometricContinuousFunctionalCalculus`

English:
instance IsStarNormal.instIsometricContinuousFunctionalCalculus
  signature: :
  body: by
    rw [cfcHom_eq_of_isStarNormal]
exact isometry_subtype_coe.comp StarAlgEquiv.isometry (continuousFunctionalCalculus a)

中文:
实例 是StarNormal.instIsometricContinuousFunctionalCalculus
  签名: :
  定义体: by
    rw [cfcHom_eq_of_isStarNormal]
exact isometry_subtype_coe.comp StarAlgEquiv.isometry (continuousFunctionalCalculus a)

Depends on / 依赖: StarAlgEquiv, StarAlgEquiv.isometry, cfcHom_eq_of_isStarNormal, continuousFunctionalCalculus, isometry, isometry_subtype_coe, isometry_subtype_coe.comp
-/
instance IsStarNormal.instIsometricContinuousFunctionalCalculus :
    IsometricContinuousFunctionalCalculus Complex A IsStarNormal where
  isometric a ha := by
    rw [cfcHom_eq_of_isStarNormal]
exact isometry_subtype_coe.comp StarAlgEquiv.isometry (continuousFunctionalCalculus a)

/--
Instance `IsSelfAdjoint.instIsometricContinuousFunctionalCalculus` / 实例 `IsSelfAdjoint.instIsometricContinuousFunctionalCalculus`

English:
instance IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  signature: :
  body: SpectrumRestricts.isometric_cfc Complex.reCLM Complex.isometry_ofReal (.zero _)
    fun _ => isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts

中文:
实例 IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  签名: :
  定义体: SpectrumRestricts.isometric_cfc Complex.reCLM Complex.isometry_ofReal (.zero _)
    fun _ => isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts

Depends on / 依赖: Complex.isometry_ofReal, Complex.reCLM, SpectrumRestricts, SpectrumRestricts.isometric_cfc, isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts, isometric_cfc, isometry_ofReal
-/
instance IsSelfAdjoint.instIsometricContinuousFunctionalCalculus :
    IsometricContinuousFunctionalCalculus Real A IsSelfAdjoint :=
  SpectrumRestricts.isometric_cfc Complex.reCLM Complex.isometry_ofReal (.zero _)
    fun _ => isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts

end Unital

section NonUnital

variable [NonUnitalCStarAlgebra A]

open Unitization

/--
theorem `IsStarNormal.instNonUnitalContinuousFunctionalCalculus` / 定理 `IsStarNormal.instNonUnitalContinuousFunctionalCalculus`

English:
theorem IsStarNormal.instNonUnitalContinuousFunctionalCalculus
  proof: RCLike.nonUnitalContinuousFunctionalCalculusIsClosedEmbedding Unitization.isStarNormal_inr

中文:
定理 是StarNormal.instNonUnitalContinuousFunctionalCalculus
  证明: RCLike.nonUnitalContinuousFunctionalCalculusIsClosedEmbedding Unitization.isStarNormal_inr

Depends on / 依赖: RCLike, RCLike.nonUnitalContinuousFunctionalCalculusIsClosedEmbedding, Unitization, Unitization.isStarNormal_inr, isStarNormal_inr, nonUnitalContinuousFunctionalCalculusIsClosedEmbedding
-/
theorem IsStarNormal.instNonUnitalContinuousFunctionalCalculus :
    NonUnitalClosedEmbeddingContinuousFunctionalCalculus Complex A IsStarNormal :=
  RCLike.nonUnitalContinuousFunctionalCalculusIsClosedEmbedding Unitization.isStarNormal_inr

attribute [local instance] IsStarNormal.instNonUnitalContinuousFunctionalCalculus

open scoped CStarAlgebra in
/--
lemma `inr_comp_cfcₙHom_eq_cfcₙAux` / 引理 `inr_comp_cfcₙHom_eq_cfcₙAux`

English:
lemma inr_comp_cfcₙHom_eq_cfcₙAux
  given: (a : A) [ha : IsStarNormal a]
  proof: inrNonUnitalStarAlgHom_comp_cfcₙHom_eq_cfcₙAux isStarNormal_inr a ha

中文:
引理 inr_comp_cfcₙHom_eq_cfcₙAux
  条件: (a : A) [ha : 是StarNormal a]
  证明: inrNonUnitalStarAlgHom_comp_cfcₙHom_eq_cfcₙAux isStarNormal_inr a ha
-/
lemma inr_comp_cfcₙHom_eq_cfcₙAux (a : A) [ha : IsStarNormal a] :
    (inrNonUnitalStarAlgHom Complex A).comp (cfcₙHom ha) = cfcₙAux (isStarNormal_inr (R := Complex)) a ha :=
  inrNonUnitalStarAlgHom_comp_cfcₙHom_eq_cfcₙAux isStarNormal_inr a ha

open ContinuousMapZero in
/--
Instance `IsStarNormal.instNonUnitalIsometricContinuousFunctionalCalculus` / 实例 `IsStarNormal.instNonUnitalIsometricContinuousFunctionalCalculus`

English:
instance IsStarNormal.instNonUnitalIsometricContinuousFunctionalCalculus
  signature: :
  body: by
    refine AddMonoidHomClass.isometry_of_norm _ fun f => ?_
    rw [← norm_inr (𝕜 := Complex)]; rw [← inrNonUnitalStarAlgHom_apply]; rw [← NonUnitalStarAlgHom.comp_apply]; rw [inr_comp_cfcₙHom_eq_cfcₙAux a]; rw [cfcₙAux]
    simp only [NonUnitalStarAlgHom.comp_assoc, NonUnitalStarAlgHom.comp_apply,
      NonUnitalStarAlgHom.coe_coe]
    rw [norm_cfcHom (a : Unitization Complex A)]; rw [StarAlgEquiv.norm_map]
    rfl

中文:
实例 是StarNormal.instNonUnitalIsometricContinuousFunctionalCalculus
  签名: :
  定义体: by
    refine AddMonoidHomClass.isometry_of_norm _ fun f => ?_
    rw [← norm_inr (𝕜 := Complex)]; rw [← inrNonUnitalStarAlgHom_apply]; rw [← NonUnitalStarAlgHom.comp_apply]; rw [inr_comp_cfcₙHom_eq_cfcₙAux a]; rw [cfcₙAux]
    simp only [NonUnitalStarAlgHom.comp_assoc, NonUnitalStarAlgHom.comp_apply,
      NonUnitalStarAlgHom.coe_coe]
    rw [norm_cfcHom (a : Unitization Complex A)]; rw [StarAlgEquiv.norm_map]
    rfl

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.isometry_of_norm, NonUnitalStarAlgHom, NonUnitalStarAlgHom.coe_coe, NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.comp_assoc, StarAlgEquiv, StarAlgEquiv.norm_map, Unitization, coe_coe, comp_apply, comp_assoc, inrNonUnitalStarAlgHom_apply, isometry_of_norm, norm_cfcHom, norm_inr, norm_map
-/
instance IsStarNormal.instNonUnitalIsometricContinuousFunctionalCalculus :
    NonUnitalIsometricContinuousFunctionalCalculus Complex A IsStarNormal where
  isometric a ha := by
    refine AddMonoidHomClass.isometry_of_norm _ fun f => ?_
    rw [← norm_inr (𝕜 := Complex)]; rw [← inrNonUnitalStarAlgHom_apply]; rw [← NonUnitalStarAlgHom.comp_apply]; rw [inr_comp_cfcₙHom_eq_cfcₙAux a]; rw [cfcₙAux]
    simp only [NonUnitalStarAlgHom.comp_assoc, NonUnitalStarAlgHom.comp_apply,
      NonUnitalStarAlgHom.coe_coe]
    rw [norm_cfcHom (a : Unitization Complex A)]; rw [StarAlgEquiv.norm_map]
    rfl

/--
Instance `IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus` / 实例 `IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus`

English:
instance IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
  signature: :
  body: QuasispectrumRestricts.isometric_cfc Complex.reCLM Complex.isometry_ofReal (.zero _)
    fun _ => isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts

中文:
实例 IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
  签名: :
  定义体: QuasispectrumRestricts.isometric_cfc Complex.reCLM Complex.isometry_ofReal (.zero _)
    fun _ => isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts

Depends on / 依赖: Complex.isometry_ofReal, Complex.reCLM, QuasispectrumRestricts, QuasispectrumRestricts.isometric_cfc, isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts, isometric_cfc, isometry_ofReal
-/
instance IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus :
    NonUnitalIsometricContinuousFunctionalCalculus Real A IsSelfAdjoint :=
  QuasispectrumRestricts.isometric_cfc Complex.reCLM Complex.isometry_ofReal (.zero _)
    fun _ => isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts

end NonUnital

end Normal

/-!
### The spectrum of a nonnegative element is nonnegative
-/

section SpectrumRestricts

open NNReal ENNReal

variable [CStarAlgebra A]

/--
lemma `SpectrumRestricts.nnreal_iff_nnnorm` / 引理 `SpectrumRestricts.nnreal_iff_nnnorm`

English:
lemma SpectrumRestricts.nnreal_iff_nnnorm
  given: {a : A} {t : Real>=0} (ha : IsSelfAdjoint a) (ht : ‖a‖₊ <= t)
  proof: by
.sub ha have : IsSelfAdjoint (algebraMap Real A t - a) := IsSelfAdjoint.algebraMap A (.all (t : Real))
  rw [← ENNReal.coe_le_coe]; rw [← IsSelfAdjoint.spectralRadius_eq_nnnorm]; rw [← SpectrumRestricts.spectralRadius_eq (f := Complex.reCLM)] at ht ⊢
  · exact SpectrumRestricts.nnreal_iff_spectralRadius_le ht
  all_goals
    try apply IsSelfAdjoint.spectrumRestricts
    assumption

中文:
引理 SpectrumRestricts.nnreal_iff_nnnorm
  条件: {a : A} {t : 实数>=0} (ha : IsSelfAdjoint a) (ht : ‖a‖₊ <= t)
  证明: by
.sub ha have : IsSelfAdjoint (algebraMap Real A t - a) := IsSelfAdjoint.algebraMap A (.all (t : Real))
  rw [← ENNReal.coe_le_coe]; rw [← IsSelfAdjoint.spectralRadius_eq_nnnorm]; rw [← SpectrumRestricts.spectralRadius_eq (f := Complex.reCLM)] at ht ⊢
  · exact SpectrumRestricts.nnreal_iff_spectralRadius_le ht
  all_goals
    try apply IsSelfAdjoint.spectrumRestricts
    assumption

Depends on / 依赖: Complex.reCLM, ENNReal, ENNReal.coe_le_coe, IsSelfAdjoint, IsSelfAdjoint.algebraMap, IsSelfAdjoint.spectralRadius_eq_nnnorm, IsSelfAdjoint.spectrumRestricts, SpectrumRestricts, SpectrumRestricts.nnreal_iff_spectralRadius_le, SpectrumRestricts.spectralRadius_eq, algebraMap, all_goals, coe_le_coe, nnreal_iff_spectralRadius_le, spectralRadius_eq, spectralRadius_eq_nnnorm, spectrumRestricts
-/
lemma SpectrumRestricts.nnreal_iff_nnnorm {a : A} {t : Real>=0} (ha : IsSelfAdjoint a) (ht : ‖a‖₊ <= t) :
    SpectrumRestricts a ContinuousMap.realToNNReal ↔ ‖algebraMap Real A t - a‖₊ <= t := by
.sub ha have : IsSelfAdjoint (algebraMap Real A t - a) := IsSelfAdjoint.algebraMap A (.all (t : Real))
  rw [← ENNReal.coe_le_coe]; rw [← IsSelfAdjoint.spectralRadius_eq_nnnorm]; rw [← SpectrumRestricts.spectralRadius_eq (f := Complex.reCLM)] at ht ⊢
  · exact SpectrumRestricts.nnreal_iff_spectralRadius_le ht
  all_goals
    try apply IsSelfAdjoint.spectrumRestricts
    assumption

/--
lemma `SpectrumRestricts.nnreal_add` / 引理 `SpectrumRestricts.nnreal_add`

English:
lemma SpectrumRestricts.nnreal_add
  statement: {a b : A} (ha₁ : IsSelfAdjoint a)
  proof: by
  rw [SpectrumRestricts.nnreal_iff_nnnorm (ha₁.add hb₁) (nnnorm_add_le a b)]; rw [NNReal.coe_add]; rw [map_add]; rw [add_sub_add_comm]
.trans ?_ refine nnnorm_add_le _ _
  gcongr
  all_goals rw [← SpectrumRestricts.nnreal_iff_nnnorm] <;> first | rfl | assumption

中文:
引理 SpectrumRestricts.nnreal_add
  结论: {a b : A} (ha₁ : IsSelfAdjoint a)
  证明: by
  rw [SpectrumRestricts.nnreal_iff_nnnorm (ha₁.add hb₁) (nnnorm_add_le a b)]; rw [NNReal.coe_add]; rw [map_add]; rw [add_sub_add_comm]
.trans ?_ refine nnnorm_add_le _ _
  gcongr
  all_goals rw [← SpectrumRestricts.nnreal_iff_nnnorm] <;> first | rfl | assumption

Depends on / 依赖: NNReal, NNReal.coe_add, SpectrumRestricts, SpectrumRestricts.nnreal_iff_nnnorm, add_sub_add_comm, all_goals, coe_add, map_add, nnnorm_add_le, nnreal_iff_nnnorm
-/
lemma SpectrumRestricts.nnreal_add {a b : A} (ha₁ : IsSelfAdjoint a)
    (hb₁ : IsSelfAdjoint b) (ha₂ : SpectrumRestricts a ContinuousMap.realToNNReal)
    (hb₂ : SpectrumRestricts b ContinuousMap.realToNNReal) :
    SpectrumRestricts (a + b) ContinuousMap.realToNNReal := by
  rw [SpectrumRestricts.nnreal_iff_nnnorm (ha₁.add hb₁) (nnnorm_add_le a b)]; rw [NNReal.coe_add]; rw [map_add]; rw [add_sub_add_comm]
.trans ?_ refine nnnorm_add_le _ _
  gcongr
  all_goals rw [← SpectrumRestricts.nnreal_iff_nnnorm] <;> first | rfl | assumption

/--
lemma `IsSelfAdjoint.sq_spectrumRestricts` / 引理 `IsSelfAdjoint.sq_spectrumRestricts`

English:
lemma IsSelfAdjoint.sq_spectrumRestricts
  given: {a : A} (ha : IsSelfAdjoint a)
  proof: by
  rw [SpectrumRestricts.nnreal_iff]; rw [← cfc_id (R := Real) a]; rw [← cfc_pow ..]; rw [cfc_map_spectrum ..]
  rintro - ⟨x, -, rfl⟩
  exact sq_nonneg x

中文:
引理 IsSelfAdjoint.sq_spectrumRestricts
  条件: {a : A} (ha : IsSelfAdjoint a)
  证明: by
  rw [SpectrumRestricts.nnreal_iff]; rw [← cfc_id (R := Real) a]; rw [← cfc_pow ..]; rw [cfc_map_spectrum ..]
  rintro - ⟨x, -, rfl⟩
  exact sq_nonneg x

Depends on / 依赖: SpectrumRestricts, SpectrumRestricts.nnreal_iff, cfc_id, cfc_map_spectrum, cfc_pow, nnreal_iff, sq_nonneg
-/
lemma IsSelfAdjoint.sq_spectrumRestricts {a : A} (ha : IsSelfAdjoint a) :
    SpectrumRestricts (a ^ 2) ContinuousMap.realToNNReal := by
  rw [SpectrumRestricts.nnreal_iff]; rw [← cfc_id (R := Real) a]; rw [← cfc_pow ..]; rw [cfc_map_spectrum ..]
  rintro - ⟨x, -, rfl⟩
  exact sq_nonneg x

open ComplexStarModule

/--
lemma `SpectrumRestricts.eq_zero_of_neg` / 引理 `SpectrumRestricts.eq_zero_of_neg`

English:
lemma SpectrumRestricts.eq_zero_of_neg
  statement: {a : A} (ha : IsSelfAdjoint a)
  proof: by
  rw [SpectrumRestricts.nnreal_iff] at ha₁ ha₂
  apply CFC.eq_zero_of_spectrum_subset_zero (R := Real) a
  rw [Set.subset_singleton_iff]
  simp only [← spectrum.neg_eq, Set.mem_neg] at ha₂
  peel ha₁ with x hx _
  linarith [ha₂ (-x) ((neg_neg x).symm ▸ hx)]

中文:
引理 SpectrumRestricts.eq_zero_of_neg
  结论: {a : A} (ha : IsSelfAdjoint a)
  证明: by
  rw [SpectrumRestricts.nnreal_iff] at ha₁ ha₂
  apply CFC.eq_zero_of_spectrum_subset_zero (R := Real) a
  rw [Set.subset_singleton_iff]
  simp only [← spectrum.neg_eq, Set.mem_neg] at ha₂
  peel ha₁ with x hx _
  linarith [ha₂ (-x) ((neg_neg x).symm ▸ hx)]

Depends on / 依赖: CFC.eq_zero_of_spectrum_subset_zero, Set.mem_neg, Set.subset_singleton_iff, SpectrumRestricts, SpectrumRestricts.nnreal_iff, eq_zero_of_spectrum_subset_zero, mem_neg, neg_eq, neg_neg, nnreal_iff, spectrum, spectrum.neg_eq, subset_singleton_iff
-/
lemma SpectrumRestricts.eq_zero_of_neg {a : A} (ha : IsSelfAdjoint a)
    (ha₁ : SpectrumRestricts a ContinuousMap.realToNNReal)
    (ha₂ : SpectrumRestricts (-a) ContinuousMap.realToNNReal) :
    a = 0 := by
  rw [SpectrumRestricts.nnreal_iff] at ha₁ ha₂
  apply CFC.eq_zero_of_spectrum_subset_zero (R := Real) a
  rw [Set.subset_singleton_iff]
  simp only [← spectrum.neg_eq, Set.mem_neg] at ha₂
  peel ha₁ with x hx _
  linarith [ha₂ (-x) ((neg_neg x).symm ▸ hx)]

/--
lemma `SpectrumRestricts.smul_of_nonneg` / 引理 `SpectrumRestricts.smul_of_nonneg`

English:
lemma SpectrumRestricts.smul_of_nonneg
  statement: {A : Type*} [Ring A] [Algebra Real A] {a : A}
  proof: by
  rw [SpectrumRestricts.nnreal_iff] at ha ⊢
  nontriviality A
  intro x hx
  by_cases hr' : r = 0
  · simp only [hr', zero_smul, spectrum.zero_eq, Set.mem_singleton_iff] at hx ⊢
    exact hx.symm.le
  · lift r to Realˣ using IsUnit.mk0 r hr'
    rw [← Units.smul_def]; rw [spectrum.unit_smul_eq_smul]; rw [Set.mem_smul_set_iff_inv_smul_mem] at hx
    refine le_of_smul_le_smul_left ?_ (inv_pos.mpr <| lt_of_le_of_ne hr <| ne_comm.mpr hr')
    simpa [Units.smul_def] using ha _ hx

中文:
引理 SpectrumRestricts.smul_of_nonneg
  结论: {A : 类型} [环 A] [代数 实数 A] {a : A}
  证明: by
  rw [SpectrumRestricts.nnreal_iff] at ha ⊢
  nontriviality A
  intro x hx
  by_cases hr' : r = 0
  · simp only [hr', zero_smul, spectrum.zero_eq, Set.mem_singleton_iff] at hx ⊢
    exact hx.symm.le
  · lift r to Realˣ using IsUnit.mk0 r hr'
    rw [← Units.smul_def]; rw [spectrum.unit_smul_eq_smul]; rw [Set.mem_smul_set_iff_inv_smul_mem] at hx
    refine le_of_smul_le_smul_left ?_ (inv_pos.mpr <| lt_of_le_of_ne hr <| ne_comm.mpr hr')
    simpa [Units.smul_def] using ha _ hx

Depends on / 依赖: IsUnit, IsUnit.mk0, Set.mem_singleton_iff, Set.mem_smul_set_iff_inv_smul_mem, SpectrumRestricts, SpectrumRestricts.nnreal_iff, Units.smul_def, hx.symm.le, inv_pos, inv_pos.mpr, le_of_smul_le_smul_left, lt_of_le_of_ne, mem_singleton_iff, mem_smul_set_iff_inv_smul_mem, ne_comm, ne_comm.mpr, nnreal_iff, nontriviality, smul_def, spectrum
-/
lemma SpectrumRestricts.smul_of_nonneg {A : Type*} [Ring A] [Algebra Real A] {a : A}
    (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : Real} (hr : 0 <= r) :
    SpectrumRestricts (r • a) ContinuousMap.realToNNReal := by
  rw [SpectrumRestricts.nnreal_iff] at ha ⊢
  nontriviality A
  intro x hx
  by_cases hr' : r = 0
  · simp only [hr', zero_smul, spectrum.zero_eq, Set.mem_singleton_iff] at hx ⊢
    exact hx.symm.le
  · lift r to Realˣ using IsUnit.mk0 r hr'
    rw [← Units.smul_def]; rw [spectrum.unit_smul_eq_smul]; rw [Set.mem_smul_set_iff_inv_smul_mem] at hx
    refine le_of_smul_le_smul_left ?_ (inv_pos.mpr <| lt_of_le_of_ne hr <| ne_comm.mpr hr')
    simpa [Units.smul_def] using ha _ hx

/--
lemma `spectrum_star_mul_self_nonneg` / 引理 `spectrum_star_mul_self_nonneg`

English:
lemma spectrum_star_mul_self_nonneg
  given: {b : A}
  statement: forall x in spectrum Real (star b * b), 0 <= x
  proof: by
  -- for convenience we'll work with `a := star b * b`, which is selfadjoint.
  set a := star b * b with a_def
  have ha : IsSelfAdjoint a := by simp [a_def]
  -- the key element to consider is `c := b * a⁻`, which satisfies `- (star c * c) = a⁻ ^ 3`.
  set c := b * a⁻
  have h_eq_negPart_a : -(star c * c) = a⁻ ^ 3 := calc
    -(star c * c) = - a⁻ * a * a⁻ := by
      simp only [star_mul, c, mul_assoc, ← mul_assoc (star b), ← a_def, CFC.negPart_def,
        neg_mul, IsSelfAdjoint.cfcₙ (f := (·⁻)).star_eq]
    _ = - a⁻ * (a⁺ - a⁻) * a⁻ :=
      congr(- a⁻ * $(CFC.posPart_sub_negPart a ha) * a⁻).symm
    _ = a⁻ ^ 3 := by simp [mul_sub, pow_succ]
  -- the spectrum of `- (star c * c) = a⁻ ^ 3` is nonnegative, since the function on the right
  -- is nonnegative on the spectrum of `a`.
  have h_c_spec₀ : SpectrumRestricts (-(star c * c)) (ContinuousMap.realToNNReal ·) := by
    simp only [SpectrumRestricts.nnreal_iff, h_eq_negPart_a, CFC.negPart_def]
    rw [cfcₙ_eq_cfc (hf0 := by simp)]; rw [← cfc_pow (ha := ha) ..]; rw [cfc_map_spectrum (ha := ha) ..]
    rintro - ⟨x, -, rfl⟩
    positivity
  -- the spectrum of `c * star c` is nonnegative, since squares of selfadjoint elements have
  -- nonnegative spectrum, and `c * star c = 2 • (ℜ c ^ 2 + ℑ c ^ 2) + (- (star c * c))`,
  -- and selfadjoint elements with nonnegative spectrum are closed under addition.
  have h_c_spec₁ : SpectrumRestricts (c * star c) ContinuousMap.realToNNReal := by
    rw [eq_sub_iff_add_eq'.mpr <| star_mul_self_add_self_mul_star c]; rw [sub_eq_add_neg]; rw [← sq]; rw [← sq]
    refine SpectrumRestricts.nnreal_add ?_ ?_ ?_ h_c_spec₀
· exact .smul (star_trivial _) ((ℜ c).prop.pow 2).add ((ℑ c).prop.pow 2)
· exact .neg .star_mul_self c
    · rw [← Nat.cast_smul_eq_nsmul Real]
      refine (ℜ c).2.sq_spectrumRestricts.nnreal_add ((ℜ c).2.pow 2) ((ℑ c).2.pow 2)
.smul_of_nonneg by simp (ℑ c).2.sq_spectrumRestricts
  -- therefore `- (star c * c) = 0` and so `a⁻ ^ 3 = 0`. By properties of the continuous functional
  -- calculus, `fun x ↦ x⁻ ^ 3` is zero on the spectrum of `a`, `0 ≤ x` for `x ∈ spectrum ℝ a`.
  rw [h_c_spec₁.mul_comm.eq_zero_of_neg (.star_mul_self c) h_c_spec₀]; rw [neg_zero]; rw [CFC.negPart_def]; rw [cfcₙ_eq_cfc (hf0 := by simp)]; rw [← cfc_pow _ _ (ha := ha)]; rw [← cfc_zero a (R := Real)] at h_eq_negPart_a
  have h_eqOn := eqOn_of_cfc_eq_cfc (ha := ha) h_eq_negPart_a
exact fun x hx => negPart_eq_zero.mp eq_zero_of_pow_eq_zero (h_eqOn hx).symm

中文:
引理 spectrum_star_mul_self_nonneg
  条件: {b : A}
  结论: 对任意 x in spectrum 实数 (star b * b), 0 <= x
  证明: by
  -- for convenience we'll work with `a := star b * b`, which is selfadjoint.
  set a := star b * b with a_def
  have ha : IsSelfAdjoint a := by simp [a_def]
  -- the key element to consider is `c := b * a⁻`, which satisfies `- (star c * c) = a⁻ ^ 3`.
  set c := b * a⁻
  have h_eq_negPart_a : -(star c * c) = a⁻ ^ 3 := calc
    -(star c * c) = - a⁻ * a * a⁻ := by
      simp only [star_mul, c, mul_assoc, ← mul_assoc (star b), ← a_def, CFC.negPart_def,
        neg_mul, IsSelfAdjoint.cfcₙ (f := (·⁻)).star_eq]
    _ = - a⁻ * (a⁺ - a⁻) * a⁻ :=
      congr(- a⁻ * $(CFC.posPart_sub_negPart a ha) * a⁻).symm
    _ = a⁻ ^ 3 := by simp [mul_sub, pow_succ]
  -- the spectrum of `- (star c * c) = a⁻ ^ 3` is nonnegative, since the function on the right
  -- is nonnegative on the spectrum of `a`.
  have h_c_spec₀ : SpectrumRestricts (-(star c * c)) (ContinuousMap.realToNNReal ·) := by
    simp only [SpectrumRestricts.nnreal_iff, h_eq_negPart_a, CFC.negPart_def]
    rw [cfcₙ_eq_cfc (hf0 := by simp)]; rw [← cfc_pow (ha := ha) ..]; rw [cfc_map_spectrum (ha := ha) ..]
    rintro - ⟨x, -, rfl⟩
    positivity
  -- the spectrum of `c * star c` is nonnegative, since squares of selfadjoint elements have
  -- nonnegative spectrum, and `c * star c = 2 • (ℜ c ^ 2 + ℑ c ^ 2) + (- (star c * c))`,
  -- and selfadjoint elements with nonnegative spectrum are closed under addition.
  have h_c_spec₁ : SpectrumRestricts (c * star c) ContinuousMap.realToNNReal := by
    rw [eq_sub_iff_add_eq'.mpr <| star_mul_self_add_self_mul_star c]; rw [sub_eq_add_neg]; rw [← sq]; rw [← sq]
    refine SpectrumRestricts.nnreal_add ?_ ?_ ?_ h_c_spec₀
· exact .smul (star_trivial _) ((ℜ c).prop.pow 2).add ((ℑ c).prop.pow 2)
· exact .neg .star_mul_self c
    · rw [← Nat.cast_smul_eq_nsmul Real]
      refine (ℜ c).2.sq_spectrumRestricts.nnreal_add ((ℜ c).2.pow 2) ((ℑ c).2.pow 2)
.smul_of_nonneg by simp (ℑ c).2.sq_spectrumRestricts
  -- therefore `- (star c * c) = 0` and so `a⁻ ^ 3 = 0`. By properties of the continuous functional
  -- calculus, `fun x ↦ x⁻ ^ 3` is zero on the spectrum of `a`, `0 ≤ x` for `x ∈ spectrum ℝ a`.
  rw [h_c_spec₁.mul_comm.eq_zero_of_neg (.star_mul_self c) h_c_spec₀]; rw [neg_zero]; rw [CFC.negPart_def]; rw [cfcₙ_eq_cfc (hf0 := by simp)]; rw [← cfc_pow _ _ (ha := ha)]; rw [← cfc_zero a (R := Real)] at h_eq_negPart_a
  have h_eqOn := eqOn_of_cfc_eq_cfc (ha := ha) h_eq_negPart_a
exact fun x hx => negPart_eq_zero.mp eq_zero_of_pow_eq_zero (h_eqOn hx).symm
-/
lemma spectrum_star_mul_self_nonneg {b : A} : forall x in spectrum Real (star b * b), 0 <= x := by
  -- for convenience we'll work with `a := star b * b`, which is selfadjoint.
  set a := star b * b with a_def
  have ha : IsSelfAdjoint a := by simp [a_def]
  -- the key element to consider is `c := b * a⁻`, which satisfies `- (star c * c) = a⁻ ^ 3`.
  set c := b * a⁻
  have h_eq_negPart_a : -(star c * c) = a⁻ ^ 3 := calc
    -(star c * c) = - a⁻ * a * a⁻ := by
      simp only [star_mul, c, mul_assoc, ← mul_assoc (star b), ← a_def, CFC.negPart_def,
        neg_mul, IsSelfAdjoint.cfcₙ (f := (·⁻)).star_eq]
    _ = - a⁻ * (a⁺ - a⁻) * a⁻ :=
      congr(- a⁻ * $(CFC.posPart_sub_negPart a ha) * a⁻).symm
    _ = a⁻ ^ 3 := by simp [mul_sub, pow_succ]
  -- the spectrum of `- (star c * c) = a⁻ ^ 3` is nonnegative, since the function on the right
  -- is nonnegative on the spectrum of `a`.
  have h_c_spec₀ : SpectrumRestricts (-(star c * c)) (ContinuousMap.realToNNReal ·) := by
    simp only [SpectrumRestricts.nnreal_iff, h_eq_negPart_a, CFC.negPart_def]
    rw [cfcₙ_eq_cfc (hf0 := by simp)]; rw [← cfc_pow (ha := ha) ..]; rw [cfc_map_spectrum (ha := ha) ..]
    rintro - ⟨x, -, rfl⟩
    positivity
  -- the spectrum of `c * star c` is nonnegative, since squares of selfadjoint elements have
  -- nonnegative spectrum, and `c * star c = 2 • (ℜ c ^ 2 + ℑ c ^ 2) + (- (star c * c))`,
  -- and selfadjoint elements with nonnegative spectrum are closed under addition.
  have h_c_spec₁ : SpectrumRestricts (c * star c) ContinuousMap.realToNNReal := by
    rw [eq_sub_iff_add_eq'.mpr <| star_mul_self_add_self_mul_star c]; rw [sub_eq_add_neg]; rw [← sq]; rw [← sq]
    refine SpectrumRestricts.nnreal_add ?_ ?_ ?_ h_c_spec₀
· exact .smul (star_trivial _) ((ℜ c).prop.pow 2).add ((ℑ c).prop.pow 2)
· exact .neg .star_mul_self c
    · rw [← Nat.cast_smul_eq_nsmul Real]
      refine (ℜ c).2.sq_spectrumRestricts.nnreal_add ((ℜ c).2.pow 2) ((ℑ c).2.pow 2)
.smul_of_nonneg by simp (ℑ c).2.sq_spectrumRestricts
  -- therefore `- (star c * c) = 0` and so `a⁻ ^ 3 = 0`. By properties of the continuous functional
  -- calculus, `fun x ↦ x⁻ ^ 3` is zero on the spectrum of `a`, `0 ≤ x` for `x ∈ spectrum ℝ a`.
  rw [h_c_spec₁.mul_comm.eq_zero_of_neg (.star_mul_self c) h_c_spec₀]; rw [neg_zero]; rw [CFC.negPart_def]; rw [cfcₙ_eq_cfc (hf0 := by simp)]; rw [← cfc_pow _ _ (ha := ha)]; rw [← cfc_zero a (R := Real)] at h_eq_negPart_a
  have h_eqOn := eqOn_of_cfc_eq_cfc (ha := ha) h_eq_negPart_a
exact fun x hx => negPart_eq_zero.mp eq_zero_of_pow_eq_zero (h_eqOn hx).symm

/--
lemma `IsSelfAdjoint.coe_mem_spectrum_complex` / 引理 `IsSelfAdjoint.coe_mem_spectrum_complex`

English:
lemma IsSelfAdjoint.coe_mem_spectrum_complex
  statement: {A : Type*} [TopologicalSpace A] [Ring A]
  proof: by
  simp [← ha.spectrumRestricts.algebraMap_image]

中文:
引理 IsSelfAdjoint.coe_mem_spectrum_complex
  结论: {A : 类型} [拓扑空间 A] [环 A]
  证明: by
  simp [← ha.spectrumRestricts.algebraMap_image]

Depends on / 依赖: algebraMap_image, cfc_tac, ha.spectrumRestricts.algebraMap_image, spectrum, spectrumRestricts
-/
lemma IsSelfAdjoint.coe_mem_spectrum_complex {A : Type*} [TopologicalSpace A] [Ring A]
    [StarRing A] [Algebra Complex A] [ContinuousFunctionalCalculus Complex A IsStarNormal]
    {a : A} {x : Real} (ha : IsSelfAdjoint a := by cfc_tac) :
    (x : Complex) in spectrum Complex a ↔ x in spectrum Real a := by
  simp [← ha.spectrumRestricts.algebraMap_image]

end SpectrumRestricts

section NonnegSpectrumClass

variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/--
Instance `CStarAlgebra.instNonnegSpectrumClass` / 实例 `CStarAlgebra.instNonnegSpectrumClass`

English:
instance CStarAlgebra.instNonnegSpectrumClass
  signature: : NonnegSpectrumClass Real A
  body: .of_spectrum_nonneg fun a ha => by
    rw [StarOrderedRing.nonneg_iff] at ha
    induction ha using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      exact spectrum_star_mul_self_nonneg
    | zero =>
      nontriviality A
      simp
    | add x y x_mem y_mem hx hy =>
      rw [← SpectrumRestricts.nnreal_iff] at hx hy ⊢
      rw [← StarOrderedRing.nonneg_iff] at x_mem y_mem
      exact hx.nnreal_add (.of_nonneg x_mem) (.of_nonneg y_mem) hy

中文:
实例 CStar代数.instNonnegSpectrumClass
  签名: : NonnegSpectrum类 实数 A
  定义体: .of_spectrum_nonneg fun a ha => by
    rw [StarOrderedRing.nonneg_iff] at ha
    induction ha using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      exact spectrum_star_mul_self_nonneg
    | zero =>
      nontriviality A
      simp
    | add x y x_mem y_mem hx hy =>
      rw [← SpectrumRestricts.nnreal_iff] at hx hy ⊢
      rw [← StarOrderedRing.nonneg_iff] at x_mem y_mem
      exact hx.nnreal_add (.of_nonneg x_mem) (.of_nonneg y_mem) hy

Depends on / 依赖: AddSubmonoid, AddSubmonoid.closure_induction, SpectrumRestricts, SpectrumRestricts.nnreal_iff, StarOrderedRing, StarOrderedRing.nonneg_iff, closure_induction, hx.nnreal_add, nnreal_add, nnreal_iff, nonneg_iff, nontriviality, of_nonneg, of_spectrum_nonneg, spectrum_star_mul_self_nonneg, x_mem, y_mem
-/
instance CStarAlgebra.instNonnegSpectrumClass : NonnegSpectrumClass Real A :=
  .of_spectrum_nonneg fun a ha => by
    rw [StarOrderedRing.nonneg_iff] at ha
    induction ha using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      exact spectrum_star_mul_self_nonneg
    | zero =>
      nontriviality A
      simp
    | add x y x_mem y_mem hx hy =>
      rw [← SpectrumRestricts.nnreal_iff] at hx hy ⊢
      rw [← StarOrderedRing.nonneg_iff] at x_mem y_mem
      exact hx.nnreal_add (.of_nonneg x_mem) (.of_nonneg y_mem) hy

open ComplexOrder in
/--
Instance `CStarAlgebra.instNonnegSpectrumClassComplexUnital` / 实例 `CStarAlgebra.instNonnegSpectrumClassComplexUnital`

English:
instance CStarAlgebra.instNonnegSpectrumClassComplexUnital
  signature: : NonnegSpectrumClass Complex A where
  body: by
    rw [mem_quasispectrum_iff]
    refine (Or.elim · ge_of_eq fun hx => ?_)
    obtain ⟨y, hy, rfl⟩ := (IsSelfAdjoint.of_nonneg ha).spectrumRestricts.algebraMap_image ▸ hx
    simpa using spectrum_nonneg_of_nonneg ha hy

中文:
实例 CStar代数.instNonnegSpectrumClassComplexUnital
  签名: : NonnegSpectrum类 复形 A where
  定义体: by
    rw [mem_quasispectrum_iff]
    refine (Or.elim · ge_of_eq fun hx => ?_)
    obtain ⟨y, hy, rfl⟩ := (IsSelfAdjoint.of_nonneg ha).spectrumRestricts.algebraMap_image ▸ hx
    simpa using spectrum_nonneg_of_nonneg ha hy

Depends on / 依赖: IsSelfAdjoint, IsSelfAdjoint.of_nonneg, Or.elim, algebraMap_image, ge_of_eq, mem_quasispectrum_iff, of_nonneg, spectrumRestricts, spectrumRestricts.algebraMap_image, spectrum_nonneg_of_nonneg
-/
instance CStarAlgebra.instNonnegSpectrumClassComplexUnital : NonnegSpectrumClass Complex A where
  quasispectrum_nonneg_of_nonneg a ha x := by
    rw [mem_quasispectrum_iff]
    refine (Or.elim · ge_of_eq fun hx => ?_)
    obtain ⟨y, hy, rfl⟩ := (IsSelfAdjoint.of_nonneg ha).spectrumRestricts.algebraMap_image ▸ hx
    simpa using spectrum_nonneg_of_nonneg ha hy

end NonnegSpectrumClass

section SpectralOrder

variable [NonUnitalCStarAlgebra A]

open scoped CStarAlgebra

variable (A) in
/-- The partial order on a C⋆-algebra defined by `x ≤ y` if and only if `y - x` is
selfadjoint and has nonnegative spectrum.

This is not declared as an instance because one may already have a partial order with better
definitional properties. However, it can be useful to invoke this as an instance in proofs. -/
@[reducible]
/--
Definition of `CStarAlgebra.spectralOrder` / `CStarAlgebra.spectralOrder` 的定义

English:
definition CStarAlgebra.spectralOrder
  signature: : PartialOrder A where
  body: IsSelfAdjoint (y - x) ∧ QuasispectrumRestricts (y - x) ContinuousMap.realToNNReal
  le_refl := by
    simp only [sub_self, IsSelfAdjoint.zero, true_and, forall_const]
    rw [quasispectrumRestricts_iff_spectrumRestricts_inr' Complex]; rw [SpectrumRestricts.nnreal_iff]
    nontriviality A
    simp
  le_antisymm x y hxy hyx := by
    rw [← Unitization.isSelfAdjoint_inr (R := Complex)]; rw [quasispectrumRestricts_iff_spectrumRestricts_inr' Complex]; rw [Unitization.inr_sub Complex] at hxy hyx
    rw [← sub_eq_zero]
    apply Unitization.inr_injective (R := Complex)
    rw [Unitization.inr_zero]; rw [Unitization.inr_sub]
    exact hyx.2.eq_zero_of_neg hyx.1 (neg_sub (x : A⁺¹) (y : A⁺¹) ▸ hxy.2)
  le_trans x y z hxy hyz := by
    simp +singlePass only [← Unitization.isSelfAdjoint_inr (R := Complex),
      quasispectrumRestricts_iff_spectrumRestricts_inr' Complex] at hxy hyz ⊢
    exact ⟨by simpa using hyz.1.add hxy.1, by simpa using hyz.2.nnreal_add hyz.1 hxy.1 hxy.2⟩

中文:
定义 CStar代数.spectralOrder
  签名: : 偏序 A where
  定义体: IsSelfAdjoint (y - x) ∧ QuasispectrumRestricts (y - x) ContinuousMap.realToNNReal
  le_refl := by
    simp only [sub_self, IsSelfAdjoint.zero, true_and, forall_const]
    rw [quasispectrumRestricts_iff_spectrumRestricts_inr' Complex]; rw [SpectrumRestricts.nnreal_iff]
    nontriviality A
    simp
  le_antisymm x y hxy hyx := by
    rw [← Unitization.isSelfAdjoint_inr (R := Complex)]; rw [quasispectrumRestricts_iff_spectrumRestricts_inr' Complex]; rw [Unitization.inr_sub Complex] at hxy hyx
    rw [← sub_eq_zero]
    apply Unitization.inr_injective (R := Complex)
    rw [Unitization.inr_zero]; rw [Unitization.inr_sub]
    exact hyx.2.eq_zero_of_neg hyx.1 (neg_sub (x : A⁺¹) (y : A⁺¹) ▸ hxy.2)
  le_trans x y z hxy hyz := by
    simp +singlePass only [← Unitization.isSelfAdjoint_inr (R := Complex),
      quasispectrumRestricts_iff_spectrumRestricts_inr' Complex] at hxy hyz ⊢
    exact ⟨by simpa using hyz.1.add hxy.1, by simpa using hyz.2.nnreal_add hyz.1 hxy.1 hxy.2⟩

Depends on / 依赖: ContinuousMap, ContinuousMap.realToNNReal, IsSelfAdjoint, QuasispectrumRestricts, realToNNReal
-/
def CStarAlgebra.spectralOrder : PartialOrder A where
  le x y := IsSelfAdjoint (y - x) ∧ QuasispectrumRestricts (y - x) ContinuousMap.realToNNReal
  le_refl := by
    simp only [sub_self, IsSelfAdjoint.zero, true_and, forall_const]
    rw [quasispectrumRestricts_iff_spectrumRestricts_inr' Complex]; rw [SpectrumRestricts.nnreal_iff]
    nontriviality A
    simp
  le_antisymm x y hxy hyx := by
    rw [← Unitization.isSelfAdjoint_inr (R := Complex)]; rw [quasispectrumRestricts_iff_spectrumRestricts_inr' Complex]; rw [Unitization.inr_sub Complex] at hxy hyx
    rw [← sub_eq_zero]
    apply Unitization.inr_injective (R := Complex)
    rw [Unitization.inr_zero]; rw [Unitization.inr_sub]
    exact hyx.2.eq_zero_of_neg hyx.1 (neg_sub (x : A⁺¹) (y : A⁺¹) ▸ hxy.2)
  le_trans x y z hxy hyz := by
    simp +singlePass only [← Unitization.isSelfAdjoint_inr (R := Complex),
      quasispectrumRestricts_iff_spectrumRestricts_inr' Complex] at hxy hyz ⊢
    exact ⟨by simpa using hyz.1.add hxy.1, by simpa using hyz.2.nnreal_add hyz.1 hxy.1 hxy.2⟩

variable (A) in
/--
lemma `CStarAlgebra.spectralOrderedRing` / 引理 `CStarAlgebra.spectralOrderedRing`

English:
lemma CStarAlgebra.spectralOrderedRing
  statement: @StarOrderedRing A _ (CStarAlgebra.spectralOrder A) _
  proof: let _ := CStarAlgebra.spectralOrder A
  { le_iff := by
      intro x y
      constructor
      · intro h
        obtain ⟨s, hs₁, _, hs₂⟩ :=
          CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts h.1 h.2
        refine ⟨s * s, ?_, by rwa [eq_sub_iff_add_eq', eq_comm] at hs₂⟩
        exact AddSubmonoid.subset_closure ⟨s, by simp [hs₁.star_eq]⟩
      · rintro ⟨p, hp, rfl⟩
        simp +instances only [spectralOrder, add_sub_cancel_left]
        induction hp using AddSubmonoid.closure_induction with
        | mem x hx =>
          obtain ⟨s, rfl⟩ := hx
          refine ⟨IsSelfAdjoint.star_mul_self s, ?_⟩
          rw [quasispectrumRestricts_iff_spectrumRestricts_inr' Complex]; rw [SpectrumRestricts.nnreal_iff]; rw [Unitization.inr_mul]; rw [Unitization.inr_star]
          exact spectrum_star_mul_self_nonneg
        | zero =>
          rw [quasispectrumRestricts_iff_spectrumRestricts_inr' Complex]; rw [SpectrumRestricts.nnreal_iff]
          simp
        | add x y _ _ hx hy =>
          simp +singlePass only [← Unitization.isSelfAdjoint_inr (R := Complex),
            quasispectrumRestricts_iff_spectrumRestricts_inr' Complex] at hx hy ⊢
          rw [Unitization.inr_add]
          exact ⟨hx.1.add hy.1, hx.2.nnreal_add hx.1 hy.1 hy.2⟩ }

中文:
引理 CStar代数.spectralOrderedRing
  结论: @StarOrdered环 A _ (CStar代数.spectralOrder A) _
  证明: let _ := CStarAlgebra.spectralOrder A
  { le_iff := by
      intro x y
      constructor
      · intro h
        obtain ⟨s, hs₁, _, hs₂⟩ :=
          CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts h.1 h.2
        refine ⟨s * s, ?_, by rwa [eq_sub_iff_add_eq', eq_comm] at hs₂⟩
        exact AddSubmonoid.subset_closure ⟨s, by simp [hs₁.star_eq]⟩
      · rintro ⟨p, hp, rfl⟩
        simp +instances only [spectralOrder, add_sub_cancel_left]
        induction hp using AddSubmonoid.closure_induction with
        | mem x hx =>
          obtain ⟨s, rfl⟩ := hx
          refine ⟨IsSelfAdjoint.star_mul_self s, ?_⟩
          rw [quasispectrumRestricts_iff_spectrumRestricts_inr' Complex]; rw [SpectrumRestricts.nnreal_iff]; rw [Unitization.inr_mul]; rw [Unitization.inr_star]
          exact spectrum_star_mul_self_nonneg
        | zero =>
          rw [quasispectrumRestricts_iff_spectrumRestricts_inr' Complex]; rw [SpectrumRestricts.nnreal_iff]
          simp
        | add x y _ _ hx hy =>
          simp +singlePass only [← Unitization.isSelfAdjoint_inr (R := Complex),
            quasispectrumRestricts_iff_spectrumRestricts_inr' Complex] at hx hy ⊢
          rw [Unitization.inr_add]
          exact ⟨hx.1.add hy.1, hx.2.nnreal_add hx.1 hy.1 hy.2⟩ }

Depends on / 依赖: AddSubmonoid, AddSubmonoid.closure_induction, AddSubmonoid.subset_closure, CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts, CStarAlgebra, CStarAlgebra.spectralOrder, IsSelfAdjoint, IsSelfAdjoint.sta, add_sub_cancel_left, closure_induction, eq_comm, eq_sub_iff_add_eq, exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts, instances, le_iff, spectralOrder, star_eq, subset_closure
-/
lemma CStarAlgebra.spectralOrderedRing : @StarOrderedRing A _ (CStarAlgebra.spectralOrder A) _ :=
  let _ := CStarAlgebra.spectralOrder A
  { le_iff := by
      intro x y
      constructor
      · intro h
        obtain ⟨s, hs₁, _, hs₂⟩ :=
          CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts h.1 h.2
        refine ⟨s * s, ?_, by rwa [eq_sub_iff_add_eq', eq_comm] at hs₂⟩
        exact AddSubmonoid.subset_closure ⟨s, by simp [hs₁.star_eq]⟩
      · rintro ⟨p, hp, rfl⟩
        simp +instances only [spectralOrder, add_sub_cancel_left]
        induction hp using AddSubmonoid.closure_induction with
        | mem x hx =>
          obtain ⟨s, rfl⟩ := hx
          refine ⟨IsSelfAdjoint.star_mul_self s, ?_⟩
          rw [quasispectrumRestricts_iff_spectrumRestricts_inr' Complex]; rw [SpectrumRestricts.nnreal_iff]; rw [Unitization.inr_mul]; rw [Unitization.inr_star]
          exact spectrum_star_mul_self_nonneg
        | zero =>
          rw [quasispectrumRestricts_iff_spectrumRestricts_inr' Complex]; rw [SpectrumRestricts.nnreal_iff]
          simp
        | add x y _ _ hx hy =>
          simp +singlePass only [← Unitization.isSelfAdjoint_inr (R := Complex),
            quasispectrumRestricts_iff_spectrumRestricts_inr' Complex] at hx hy ⊢
          rw [Unitization.inr_add]
          exact ⟨hx.1.add hy.1, hx.2.nnreal_add hx.1 hy.1 hy.2⟩ }

end SpectralOrder

section NonnegSpectrumClass

variable [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped CStarAlgebra in
/--
Instance `CStarAlgebra.instNonnegSpectrumClass'` / 实例 `CStarAlgebra.instNonnegSpectrumClass'`

English:
instance CStarAlgebra.instNonnegSpectrumClass'
  signature: : NonnegSpectrumClass Real A where
  body: by
    rw [Unitization.quasispectrum_eq_spectrum_inr' _ Complex]
    -- should this actually be an instance on the `Unitization`? (probably scoped)
    let _ := CStarAlgebra.spectralOrder A⁺¹
    have := CStarAlgebra.spectralOrderedRing A⁺¹
    apply spectrum_nonneg_of_nonneg
    rw [StarOrderedRing.nonneg_iff] at ha ⊢
    have := AddSubmonoid.mem_map_of_mem (Unitization.inrNonUnitalStarAlgHom Complex A) ha
    rw [AddMonoidHom.map_mclosure]; rw [← Set.range_comp] at this
    apply AddSubmonoid.closure_mono ?_ this
    rintro _ ⟨s, rfl⟩
    exact ⟨s, by simp⟩

中文:
实例 CStar代数.instNonnegSpectrumClass'
  签名: : NonnegSpectrum类 实数 A where
  定义体: by
    rw [Unitization.quasispectrum_eq_spectrum_inr' _ Complex]
    -- should this actually be an instance on the `Unitization`? (probably scoped)
    let _ := CStarAlgebra.spectralOrder A⁺¹
    have := CStarAlgebra.spectralOrderedRing A⁺¹
    apply spectrum_nonneg_of_nonneg
    rw [StarOrderedRing.nonneg_iff] at ha ⊢
    have := AddSubmonoid.mem_map_of_mem (Unitization.inrNonUnitalStarAlgHom Complex A) ha
    rw [AddMonoidHom.map_mclosure]; rw [← Set.range_comp] at this
    apply AddSubmonoid.closure_mono ?_ this
    rintro _ ⟨s, rfl⟩
    exact ⟨s, by simp⟩

Depends on / 依赖: Unitization, Unitization.quasispectrum_eq_spectrum_inr, quasispectrum_eq_spectrum_inr
-/
instance CStarAlgebra.instNonnegSpectrumClass' : NonnegSpectrumClass Real A where
  quasispectrum_nonneg_of_nonneg a ha := by
    rw [Unitization.quasispectrum_eq_spectrum_inr' _ Complex]
    -- should this actually be an instance on the `Unitization`? (probably scoped)
    let _ := CStarAlgebra.spectralOrder A⁺¹
    have := CStarAlgebra.spectralOrderedRing A⁺¹
    apply spectrum_nonneg_of_nonneg
    rw [StarOrderedRing.nonneg_iff] at ha ⊢
    have := AddSubmonoid.mem_map_of_mem (Unitization.inrNonUnitalStarAlgHom Complex A) ha
    rw [AddMonoidHom.map_mclosure]; rw [← Set.range_comp] at this
    apply AddSubmonoid.closure_mono ?_ this
    rintro _ ⟨s, rfl⟩
    exact ⟨s, by simp⟩

end NonnegSpectrumClass

section cfc_inr

open CStarAlgebra

variable [NonUnitalCStarAlgebra A]

open scoped NonUnitalContinuousFunctionalCalculus in
/--
lemma `Unitization.cfcₙ_eq_cfc_inr` / 引理 `Unitization.cfcₙ_eq_cfc_inr`

English:
lemma Unitization.cfcₙ_eq_cfc_inr
  statement: {R : Type*} [Semifield R] [StarRing R] [MetricSpace R]
  proof: by
  by_cases h : ContinuousOn f (σₙ R a) ∧ p a
  · obtain ⟨hf, ha⟩ := h
    rw [← cfcₙ_eq_cfc (quasispectrum_inr_eq R Complex a ▸ hf)]
    exact (inrNonUnitalStarAlgHom Complex A).map_cfcₙ f a
  · obtain (hf | ha) := not_and_or.mp h
    · rw [cfcₙ_apply_of_not_continuousOn a hf, inr_zero,
        cfc_apply_of_not_continuousOn _ (quasispectrum_eq_spectrum_inr' R Complex a ▸ hf)]
    · rw [cfcₙ_apply_of_not_predicate a ha, inr_zero,
        cfc_apply_of_not_predicate _ (not_iff_not.mpr hp |>.mpr ha)]

中文:
引理 Unitization.cfcₙ_eq_cfc_inr
  结论: {R : 类型} [半域 R] [对合环 R] [度量空间 R]
  证明: by
  by_cases h : ContinuousOn f (σₙ R a) ∧ p a
  · obtain ⟨hf, ha⟩ := h
    rw [← cfcₙ_eq_cfc (quasispectrum_inr_eq R Complex a ▸ hf)]
    exact (inrNonUnitalStarAlgHom Complex A).map_cfcₙ f a
  · obtain (hf | ha) := not_and_or.mp h
    · rw [cfcₙ_apply_of_not_continuousOn a hf, inr_zero,
        cfc_apply_of_not_continuousOn _ (quasispectrum_eq_spectrum_inr' R Complex a ▸ hf)]
    · rw [cfcₙ_apply_of_not_predicate a ha, inr_zero,
        cfc_apply_of_not_predicate _ (not_iff_not.mpr hp |>.mpr ha)]

Depends on / 依赖: ContinuousOn, cfc_apply_of_not_continuousOn, cfc_apply_of_not_predicate, cfc_zero_tac, inrNonUnitalStarAlgHom, inr_zero, not_and_or, not_and_or.mp, not_iff_not, not_iff_not.mpr, quasispectrum_eq_spectrum_inr, quasispectrum_inr_eq
-/
lemma Unitization.cfcₙ_eq_cfc_inr {R : Type*} [Semifield R] [StarRing R] [MetricSpace R]
    [IsTopologicalSemiring R] [ContinuousStar R] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] [Algebra R Complex] [IsScalarTower R Complex A]
    {p : A -> Prop} {p' : A⁺¹ -> Prop} [NonUnitalContinuousFunctionalCalculus R A p]
    [ContinuousFunctionalCalculus R A⁺¹ p']
    [ContinuousMapZero.UniqueHom R (Unitization Complex A)]
    (hp : forall {a : A}, p' (a : A⁺¹) ↔ p a) (a : A) (f : R -> R) (hf₀ : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a = cfc f (a : A⁺¹) := by
  by_cases h : ContinuousOn f (σₙ R a) ∧ p a
  · obtain ⟨hf, ha⟩ := h
    rw [← cfcₙ_eq_cfc (quasispectrum_inr_eq R Complex a ▸ hf)]
    exact (inrNonUnitalStarAlgHom Complex A).map_cfcₙ f a
  · obtain (hf | ha) := not_and_or.mp h
    · rw [cfcₙ_apply_of_not_continuousOn a hf, inr_zero,
        cfc_apply_of_not_continuousOn _ (quasispectrum_eq_spectrum_inr' R Complex a ▸ hf)]
    · rw [cfcₙ_apply_of_not_predicate a ha, inr_zero,
        cfc_apply_of_not_predicate _ (not_iff_not.mpr hp |>.mpr ha)]

/--
lemma `Unitization.complex_cfcₙ_eq_cfc_inr` / 引理 `Unitization.complex_cfcₙ_eq_cfc_inr`

English:
lemma Unitization.complex_cfcₙ_eq_cfc_inr
  given: (a : A) (f : Complex -> Complex) (hf₀ : f 0 = 0 := by cfc_zero_tac)
  proof: Unitization.cfcₙ_eq_cfc_inr isStarNormal_inr ..

中文:
引理 Unitization.complex_cfcₙ_eq_cfc_inr
  条件: (a : A) (f : 复形 -> 复形) (hf₀ : f 0 = 0 := by cfc_zero_tac)
  证明: Unitization.cfcₙ_eq_cfc_inr isStarNormal_inr ..

Depends on / 依赖: Unitization, Unitization.cfc, cfc_zero_tac, isStarNormal_inr
-/
lemma Unitization.complex_cfcₙ_eq_cfc_inr (a : A) (f : Complex -> Complex) (hf₀ : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a = cfc f (a : A⁺¹) :=
  Unitization.cfcₙ_eq_cfc_inr isStarNormal_inr ..

/--
lemma `Unitization.real_cfcₙ_eq_cfc_inr` / 引理 `Unitization.real_cfcₙ_eq_cfc_inr`

English:
lemma Unitization.real_cfcₙ_eq_cfc_inr
  given: (a : A) (f : Real -> Real) (hf₀ : f 0 = 0 := by cfc_zero_tac)
  proof: Unitization.cfcₙ_eq_cfc_inr isSelfAdjoint_inr ..

中文:
引理 Unitization.real_cfcₙ_eq_cfc_inr
  条件: (a : A) (f : 实数 -> 实数) (hf₀ : f 0 = 0 := by cfc_zero_tac)
  证明: Unitization.cfcₙ_eq_cfc_inr isSelfAdjoint_inr ..

Depends on / 依赖: Unitization, Unitization.cfc, cfc_zero_tac, isSelfAdjoint_inr
-/
lemma Unitization.real_cfcₙ_eq_cfc_inr (a : A) (f : Real -> Real) (hf₀ : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a = cfc f (a : A⁺¹) :=
  Unitization.cfcₙ_eq_cfc_inr isSelfAdjoint_inr ..

end cfc_inr
