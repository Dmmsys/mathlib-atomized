/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital

/-! # Restriction of the continuous functional calculus to a scalar subring

The main declaration in this file is:

+ `SpectrumRestricts.cfc`: builds a continuous functional calculus over a subring of scalars.
  This is used for automatically deriving the continuous functional calculi on selfadjoint or
  positive elements from the one for normal elements.

This will allow us to take an instance of the
`ContinuousFunctionalCalculus ℂ A IsStarNormal` and produce both of the instances
`ContinuousFunctionalCalculus ℝ A IsSelfAdjoint` and `ContinuousFunctionalCalculus ℝ≥0 A (0 ≤ ·)`
simply by proving:

1. `IsSelfAdjoint x ↔ IsStarNormal x ∧ SpectrumRestricts Complex.re x`,
2. `0 ≤ x ↔ IsSelfAdjoint x ∧ SpectrumRestricts Real.toNNReal x`.
-/

@[expose] public section

open Set Topology

namespace SpectrumRestricts

/--
Definition of `homeomorph` / `homeomorph` 的定义

English:
definition homeomorph
  signature: {R S A : Type*} [Semifield R] [Semifield S] [Ring A]
  body: MapsTo.restrict f _ _ h.subset_preimage
  invFun := MapsTo.restrict (algebraMap R S) _ _ (image_subset_iff.mp h.algebraMap_image.subset)
left_inv x := Subtype.ext h.rightInvOn x.2
right_inv x := Subtype.ext h.left_inv x

中文:
定义 homeomorph
  签名: {R S A : 类型} [半域 R] [半域 S] [环 A]
  定义体: MapsTo.restrict f _ _ h.subset_preimage
  invFun := MapsTo.restrict (algebraMap R S) _ _ (image_subset_iff.mp h.algebraMap_image.subset)
left_inv x := Subtype.ext h.rightInvOn x.2
right_inv x := Subtype.ext h.left_inv x

Depends on / 依赖: MapsTo, MapsTo.restrict, h.subset_preimage, restrict, subset_preimage
-/
def homeomorph {R S A : Type*} [Semifield R] [Semifield S] [Ring A]
    [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [TopologicalSpace R]
    [TopologicalSpace S] [ContinuousSMul R S] {a : A} {f : C(S, R)} (h : SpectrumRestricts a f) :
    spectrum S a ≃ₜ spectrum R a where
  toFun := MapsTo.restrict f _ _ h.subset_preimage
  invFun := MapsTo.restrict (algebraMap R S) _ _ (image_subset_iff.mp h.algebraMap_image.subset)
left_inv x := Subtype.ext h.rightInvOn x.2
right_inv x := Subtype.ext h.left_inv x

/--
lemma `compactSpace` / 引理 `compactSpace`

English:
lemma compactSpace
  statement: {R S A : Type*} [Semifield R] [Semifield S] [Ring A]
  proof: by
  rw [← isCompact_iff_compactSpace] at h_cpct ⊢
  exact h.image ▸ h_cpct.image (map_continuous f)

universe u v w

中文:
引理 compactSpace
  结论: {R S A : 类型} [半域 R] [半域 S] [环 A]
  证明: by
  rw [← isCompact_iff_compactSpace] at h_cpct ⊢
  exact h.image ▸ h_cpct.image (map_continuous f)

universe u v w

Depends on / 依赖: h.image, h_cpct, h_cpct.image, isCompact_iff_compactSpace, map_continuous
-/
lemma compactSpace {R S A : Type*} [Semifield R] [Semifield S] [Ring A]
    [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [TopologicalSpace R]
    [TopologicalSpace S] {a : A} (f : C(S, R)) (h : SpectrumRestricts a f)
    [h_cpct : CompactSpace (spectrum S a)] : CompactSpace (spectrum R a) := by
  rw [← isCompact_iff_compactSpace] at h_cpct ⊢
  exact h.image ▸ h_cpct.image (map_continuous f)

universe u v w

set_option backward.isDefEq.respectTransparency.types false in
/-- If the spectrum of an element restricts to a smaller scalar ring, then a continuous functional
calculus over the larger scalar ring descends to the smaller one. -/
@[simps!]
/--
Definition of `starAlgHom` / `starAlgHom` 的定义

English:
definition starAlgHom
  signature: {R : Type u} {S : Type v} {A : Type w} [Semifield R]
  body: (φ.restrictScalars R).comp
(ContinuousMap.compStarAlgHom (spectrum S a) (.ofId R S) (algebraMapCLM R S).continuous).comp
      ContinuousMap.compStarAlgHom' R R
        ⟨Subtype.map f h.subset_preimage, (map_continuous f).subtype_map
          fun x (hx : x in spectrum S a) => h.subset_preimage hx⟩

中文:
定义 starAlgHom
  签名: {R : 类型u} {S : 类型v} {A : 类型 w} [半域 R]
  定义体: (φ.restrictScalars R).comp
(ContinuousMap.compStarAlgHom (spectrum S a) (.ofId R S) (algebraMapCLM R S).continuous).comp
      ContinuousMap.compStarAlgHom' R R
        ⟨Subtype.map f h.subset_preimage, (map_continuous f).subtype_map
          fun x (hx : x in spectrum S a) => h.subset_preimage hx⟩

Depends on / 依赖: ContinuousMap, ContinuousMap.compStarAlgHom, Subtype, Subtype.map, algebraMapCLM, compStarAlgHom, continuous, h.subset_preimage, map_continuous, restrictScalars, spectrum, subset_preimage, subtype_map
-/
def starAlgHom {R : Type u} {S : Type v} {A : Type w} [Semifield R]
    [StarRing R] [TopologicalSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Semifield S]
    [StarRing S] [TopologicalSpace S] [IsTopologicalSemiring S] [ContinuousStar S] [Ring A]
    [StarRing A] [Algebra R S] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S] {a : A}
    (φ : C(spectrum S a, S) ->⋆ₐ[S] A) {f : C(S, R)} (h : SpectrumRestricts a f) :
    C(spectrum R a, R) ->⋆ₐ[R] A :=
(φ.restrictScalars R).comp
(ContinuousMap.compStarAlgHom (spectrum S a) (.ofId R S) (algebraMapCLM R S).continuous).comp
      ContinuousMap.compStarAlgHom' R R
        ⟨Subtype.map f h.subset_preimage, (map_continuous f).subtype_map
          fun x (hx : x in spectrum S a) => h.subset_preimage hx⟩

variable {R S A : Type*} {p q : A -> Prop}
variable [Semifield R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
variable [Semifield S] [StarRing S] [MetricSpace S] [IsTopologicalSemiring S] [ContinuousStar S]
variable [Ring A] [StarRing A] [Algebra S A]
variable [Algebra R S] [Algebra R A] [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S]

/--
lemma `starAlgHom_id` / 引理 `starAlgHom_id`

English:
lemma starAlgHom_id
  statement: {a : A} {φ : C(spectrum S a, S) ->⋆ₐ[S] A} {f : C(S, R)}
  proof: by
  simp only [SpectrumRestricts.starAlgHom_apply]
  convert! h_id
  ext x
  exact h.rightInvOn x.2

中文:
引理 starAlgHom_id
  结论: {a : A} {φ : C(spectrum S a, S) ->⋆ₐ[S] A} {f : C(S, R)}
  证明: by
  simp only [SpectrumRestricts.starAlgHom_apply]
  convert! h_id
  ext x
  exact h.rightInvOn x.2

Depends on / 依赖: SpectrumRestricts, SpectrumRestricts.starAlgHom_apply, convert, h.rightInvOn, h_id, rightInvOn, starAlgHom_apply
-/
lemma starAlgHom_id {a : A} {φ : C(spectrum S a, S) ->⋆ₐ[S] A} {f : C(S, R)}
    (h : SpectrumRestricts a f) (h_id : φ (.restrict (spectrum S a) <| .id S) = a) :
    h.starAlgHom φ (.restrict (spectrum R a) <| .id R) = a := by
  simp only [SpectrumRestricts.starAlgHom_apply]
  convert! h_id
  ext x
  exact h.rightInvOn x.2

open ContinuousMap in
/--
lemma `starAlgHom_injective` / 引理 `starAlgHom_injective`

English:
lemma starAlgHom_injective
  statement: {a : A} {φ : C(spectrum S a, S) ->⋆ₐ[S] A}
  proof: hφ.comp (postcomp_injective _ halg).comp
.injective h.homeomorph.symm.arrowCongr (.refl _)

中文:
引理 starAlgHom_injective
  结论: {a : A} {φ : C(spectrum S a, S) ->⋆ₐ[S] A}
  证明: hφ.comp (postcomp_injective _ halg).comp
.injective h.homeomorph.symm.arrowCongr (.refl _)

Depends on / 依赖: arrowCongr, h.homeomorph.symm.arrowCongr, homeomorph, injective, postcomp_injective
-/
lemma starAlgHom_injective {a : A} {φ : C(spectrum S a, S) ->⋆ₐ[S] A}
    (hφ : Function.Injective φ) {f : C(S, R)} (h : SpectrumRestricts a f)
    (halg : Function.Injective (algebraMap R S)) :
    Function.Injective (h.starAlgHom φ) :=
hφ.comp (postcomp_injective _ halg).comp
.injective h.homeomorph.symm.arrowCongr (.refl _)

variable [TopologicalSpace A]

section Generic

variable [ContinuousFunctionalCalculus S A q]

open ContinuousMap in
/--
lemma `continuous_starAlgHom` / 引理 `continuous_starAlgHom`

English:
lemma continuous_starAlgHom
  statement: {a : A} {φ : C(spectrum S a, S) ->⋆ₐ[S] A}
  proof: hφ.comp (continuous_postcomp _).comp (continuous_precomp _)

中文:
引理 continuous_starAlgHom
  结论: {a : A} {φ : C(spectrum S a, S) ->⋆ₐ[S] A}
  证明: hφ.comp (continuous_postcomp _).comp (continuous_precomp _)

Depends on / 依赖: continuous_postcomp, continuous_precomp
-/
lemma continuous_starAlgHom {a : A} {φ : C(spectrum S a, S) ->⋆ₐ[S] A}
    (hφ : Continuous φ) {f : C(S, R)} (h : SpectrumRestricts a f) :
    Continuous (h.starAlgHom φ) :=
hφ.comp (continuous_postcomp _).comp (continuous_precomp _)

variable [CompleteSpace R] in
/--
lemma `isClosedEmbedding_starAlgHom` / 引理 `isClosedEmbedding_starAlgHom`

English:
lemma isClosedEmbedding_starAlgHom
  statement: {a : A} {φ : C(spectrum S a, S) ->⋆ₐ[S] A}
  proof: hφ.comp IsUniformEmbedding.isClosedEmbedding .comp
    (ContinuousMap.isUniformEmbedding_comp _ halg)
    (UniformEquiv.arrowCongr h.homeomorph.symm (.refl _) |>.isUniformEmbedding)

中文:
引理 isClosedEmbedding_starAlgHom
  结论: {a : A} {φ : C(spectrum S a, S) ->⋆ₐ[S] A}
  证明: hφ.comp IsUniformEmbedding.isClosedEmbedding .comp
    (ContinuousMap.isUniformEmbedding_comp _ halg)
    (UniformEquiv.arrowCongr h.homeomorph.symm (.refl _) |>.isUniformEmbedding)

Depends on / 依赖: ContinuousMap, ContinuousMap.isUniformEmbedding_comp, IsUniformEmbedding, IsUniformEmbedding.isClosedEmbedding, UniformEquiv, UniformEquiv.arrowCongr, arrowCongr, h.homeomorph.symm, homeomorph, isClosedEmbedding, isUniformEmbedding, isUniformEmbedding_comp
-/
lemma isClosedEmbedding_starAlgHom {a : A} {φ : C(spectrum S a, S) ->⋆ₐ[S] A}
    (hφ : IsClosedEmbedding φ) {f : C(S, R)} (h : SpectrumRestricts a f)
    (halg : IsUniformEmbedding (algebraMap R S)) :
    IsClosedEmbedding (h.starAlgHom φ) :=
hφ.comp IsUniformEmbedding.isClosedEmbedding .comp
    (ContinuousMap.isUniformEmbedding_comp _ halg)
    (UniformEquiv.arrowCongr h.homeomorph.symm (.refl _) |>.isUniformEmbedding)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `cfc` / 定理 `cfc`

English:
theorem cfc
  statement: (f : C(S, R)) (halg : IsClosedEmbedding (algebraMap R S)) (h0 : p 0)
  proof: h0
  spectrum_nonempty a ha := ((h a).mp ha).2.image ▸
    (ContinuousFunctionalCalculus.spectrum_nonempty a ((h a).mp ha).1 |>.image f)
  compactSpace_spectrum a := by
    have := ContinuousFunctionalCalculus.compactSpace_spectrum (R := S) a
    rw [← isCompact_iff_compactSpace] at this ⊢
    simpa

中文:
定理 cfc
  结论: (f : C(S, R)) (halg : 是闭嵌入 (algebraMap R S)) (h0 : p 0)
  证明: h0
  spectrum_nonempty a ha := ((h a).mp ha).2.image ▸
    (ContinuousFunctionalCalculus.spectrum_nonempty a ((h a).mp ha).1 |>.image f)
  compactSpace_spectrum a := by
    have := ContinuousFunctionalCalculus.compactSpace_spectrum (R := S) a
    rw [← isCompact_iff_compactSpace] at this ⊢
    simpa
-/
protected theorem cfc (f : C(S, R)) (halg : IsClosedEmbedding (algebraMap R S)) (h0 : p 0)
    (h : forall a, p a ↔ q a ∧ SpectrumRestricts a f) :
    ContinuousFunctionalCalculus R A p where
  predicate_zero := h0
  spectrum_nonempty a ha := ((h a).mp ha).2.image ▸
    (ContinuousFunctionalCalculus.spectrum_nonempty a ((h a).mp ha).1 |>.image f)
  compactSpace_spectrum a := by
    have := ContinuousFunctionalCalculus.compactSpace_spectrum (R := S) a
    rw [← isCompact_iff_compactSpace] at this ⊢
    simpa using halg.isCompact_preimage this
  exists_cfc_of_predicate a ha := by
    refine ⟨((h a).mp ha).2.starAlgHom (cfcHom ((h a).mp ha).1 (R := S)),
      ?hom_continuous, ?hom_injective, ?hom_id, ?hom_map_spectrum, ?predicate_hom⟩
    case hom_continuous =>
      exact ((h a).mp ha).2.continuous_starAlgHom (cfcHom_continuous ((h a).mp ha).1)
    case hom_injective =>
      exact ((h a).mp ha).2.starAlgHom_injective (cfcHom_injective ((h a).mp ha).1) halg.injective
case hom_id => exact ((h a).mp ha).2.starAlgHom_id cfcHom_id ((h a).mp ha).1
    case hom_map_spectrum =>
      simp only [SpectrumRestricts.starAlgHom_apply, ← @spectrum.preimage_algebraMap (R := R) S,
        cfcHom_map_spectrum, Set.ext_iff, Set.mem_preimage, Set.mem_range, ContinuousMap.comp_apply,
        ContinuousMap.coe_mk, StarAlgHom.ofId_apply, halg.injective.eq_iff]
      exact fun _ _ => ((h a).mp ha).2.homeomorph.exists_congr fun _ => Iff.rfl
    case predicate_hom =>
      intro g
      rw [h]
      refine ⟨cfcHom_predicate _ _, ?_⟩
      refine .of_rightInvOn (((h a).mp ha).2.left_inv) fun s hs => ?_
      rw [SpectrumRestricts.starAlgHom_apply]; rw [cfcHom_map_spectrum] at hs
      obtain ⟨r, rfl⟩ := hs
      simp [((h a).mp ha).2.left_inv _]

variable [ContinuousFunctionalCalculus R A p] [ContinuousMap.UniqueHom R A]

/--
lemma `cfcHom_eq_restrict` / 引理 `cfcHom_eq_restrict`

English:
lemma cfcHom_eq_restrict
  given: (f : C(S, R)) {a : A} (hpa : p a) (hqa : q a) (h : SpectrumRestricts a f)
  proof: by
  apply cfcHom_eq_of_continuous_of_map_id
  · exact h.continuous_starAlgHom (cfcHom_continuous hqa)
  · exact h.starAlgHom_id (cfcHom_id hqa)

中文:
引理 cfcHom_eq_restrict
  条件: (f : C(S, R)) {a : A} (hpa : p a) (hqa : q a) (h : SpectrumRestricts a f)
  证明: by
  apply cfcHom_eq_of_continuous_of_map_id
  · exact h.continuous_starAlgHom (cfcHom_continuous hqa)
  · exact h.starAlgHom_id (cfcHom_id hqa)

Depends on / 依赖: cfcHom_continuous, cfcHom_eq_of_continuous_of_map_id, cfcHom_id, continuous_starAlgHom, h.continuous_starAlgHom, h.starAlgHom_id, starAlgHom_id
-/
lemma cfcHom_eq_restrict (f : C(S, R)) {a : A} (hpa : p a) (hqa : q a) (h : SpectrumRestricts a f) :
    cfcHom hpa = h.starAlgHom (cfcHom hqa) := by
  apply cfcHom_eq_of_continuous_of_map_id
  · exact h.continuous_starAlgHom (cfcHom_continuous hqa)
  · exact h.starAlgHom_id (cfcHom_id hqa)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `cfc_eq_restrict` / 引理 `cfc_eq_restrict`

English:
lemma cfc_eq_restrict
  statement: (f : C(S, R)) (halg : IsClosedEmbedding (algebraMap R S)) {a : A} (hpa : p a)
  proof: by
  by_cases hg : ContinuousOn g (spectrum R a)
  · rw [cfc_apply g a, cfcHom_eq_restrict f hpa hqa h, SpectrumRestricts.starAlgHom_apply,
      cfcHom_eq_cfc_extend 0]
    apply cfc_congr fun x hx => ?_
    lift x to spectrum S a using hx
    simp [Function.comp]
  · have : ¬ ContinuousOn (fun x =

中文:
引理 cfc_eq_restrict
  结论: (f : C(S, R)) (halg : 是闭嵌入 (algebraMap R S)) {a : A} (hpa : p a)
  证明: by
  by_cases hg : ContinuousOn g (spectrum R a)
  · rw [cfc_apply g a, cfcHom_eq_restrict f hpa hqa h, SpectrumRestricts.starAlgHom_apply,
      cfcHom_eq_cfc_extend 0]
    apply cfc_congr fun x hx => ?_
    lift x to spectrum S a using hx
    simp [Function.comp]
  · have : ¬ ContinuousOn (fun x =

Depends on / 依赖: ContinuousOn, Function, Function.comp, Function.comp_def, SpectrumRestricts, SpectrumRestricts.starAlgHom_apply, algebraMap, cfcHom_eq_cfc_extend, cfcHom_eq_restrict, cfc_apply, cfc_congr, comp_def, continuousOn_iff, h.left_inv, halg.isEmbedd, halg.isEmbedding.continuousOn_iff, isEmbedd, isEmbedding, left_inv, spectrum
-/
lemma cfc_eq_restrict (f : C(S, R)) (halg : IsClosedEmbedding (algebraMap R S)) {a : A} (hpa : p a)
    (hqa : q a) (h : SpectrumRestricts a f) (g : R -> R) :
    cfc g a = cfc (fun x => algebraMap R S (g (f x))) a := by
  by_cases hg : ContinuousOn g (spectrum R a)
  · rw [cfc_apply g a, cfcHom_eq_restrict f hpa hqa h, SpectrumRestricts.starAlgHom_apply,
      cfcHom_eq_cfc_extend 0]
    apply cfc_congr fun x hx => ?_
    lift x to spectrum S a using hx
    simp [Function.comp]
  · have : ¬ ContinuousOn (fun x => algebraMap R S (g (f x)) : S -> S) (spectrum S a) := by
      refine fun hg' => hg ?_
      rw [halg.isEmbedding.continuousOn_iff]
      simpa [halg.isEmbedding.continuousOn_iff, Function.comp_def, h.left_inv _] using
        hg'.comp halg.isEmbedding.continuous.continuousOn (fun _ : R => spectrum.algebraMap_mem S)
    rw [cfc_apply_of_not_continuousOn a hg]; rw [cfc_apply_of_not_continuousOn a this]

end Generic

variable [ClosedEmbeddingContinuousFunctionalCalculus S A q]
  [ContinuousMap.UniqueHom R A] [CompleteSpace R]

open ContinuousFunctionalCalculus in
/--
theorem `closedEmbeddingCFC` / 定理 `closedEmbeddingCFC`

English:
theorem closedEmbeddingCFC
  statement: (f : C(S, R)) (halg : IsUniformEmbedding (algebraMap R S))
  proof: SpectrumRestricts.cfc f halg.isClosedEmbedding h0 h
  isClosedEmbedding a ha := by
    have := SpectrumRestricts.cfc f halg.isClosedEmbedding h0 h
    rw [cfcHom_eq_restrict f ha ((h a).mp ha).1 ((h a).mp ha).2]
    exact isClosedEmbedding_starAlgHom (cfcHom_isClosedEmbedding ((h a).mp ha).1)
      

中文:
定理 closedEmbeddingCFC
  结论: (f : C(S, R)) (halg : 是一致嵌入 (algebraMap R S))
  证明: SpectrumRestricts.cfc f halg.isClosedEmbedding h0 h
  isClosedEmbedding a ha := by
    have := SpectrumRestricts.cfc f halg.isClosedEmbedding h0 h
    rw [cfcHom_eq_restrict f ha ((h a).mp ha).1 ((h a).mp ha).2]
    exact isClosedEmbedding_starAlgHom (cfcHom_isClosedEmbedding ((h a).mp ha).1)
      
-/
protected theorem closedEmbeddingCFC (f : C(S, R)) (halg : IsUniformEmbedding (algebraMap R S))
    (h0 : p 0) (h : forall a, p a ↔ q a ∧ SpectrumRestricts a f) :
    ClosedEmbeddingContinuousFunctionalCalculus R A p where
  toContinuousFunctionalCalculus := SpectrumRestricts.cfc f halg.isClosedEmbedding h0 h
  isClosedEmbedding a ha := by
    have := SpectrumRestricts.cfc f halg.isClosedEmbedding h0 h
    rw [cfcHom_eq_restrict f ha ((h a).mp ha).1 ((h a).mp ha).2]
    exact isClosedEmbedding_starAlgHom (cfcHom_isClosedEmbedding ((h a).mp ha).1)
      ((h a).mp ha).2 halg

end SpectrumRestricts


namespace QuasispectrumRestricts

local notation "σₙ" => quasispectrum
open ContinuousMapZero Set

/--
Definition of `homeomorph` / `homeomorph` 的定义

English:
definition homeomorph
  signature: {R S A : Type*} [Semifield R] [Field S] [NonUnitalRing A]
  body: MapsTo.restrict f _ _ h.subset_preimage
  invFun := MapsTo.restrict (algebraMap R S) _ _ (image_subset_iff.mp h.algebraMap_image.subset)
left_inv x := Subtype.ext h.rightInvOn x.2
right_inv x := Subtype.ext h.left_inv x

universe u v w

中文:
定义 homeomorph
  签名: {R S A : 类型} [半域 R] [域 S] [非幺环 A]
  定义体: MapsTo.restrict f _ _ h.subset_preimage
  invFun := MapsTo.restrict (algebraMap R S) _ _ (image_subset_iff.mp h.algebraMap_image.subset)
left_inv x := Subtype.ext h.rightInvOn x.2
right_inv x := Subtype.ext h.left_inv x

universe u v w

Depends on / 依赖: MapsTo, MapsTo.restrict, h.subset_preimage, restrict, subset_preimage
-/
def homeomorph {R S A : Type*} [Semifield R] [Field S] [NonUnitalRing A]
    [Algebra R S] [Module R A] [Module S A] [IsScalarTower R S A] [TopologicalSpace R]
    [TopologicalSpace S] [ContinuousSMul R S] [IsScalarTower S A A] [SMulCommClass S A A]
    {a : A} {f : C(S, R)} (h : QuasispectrumRestricts a f) :
    σₙ S a ≃ₜ σₙ R a where
  toFun := MapsTo.restrict f _ _ h.subset_preimage
  invFun := MapsTo.restrict (algebraMap R S) _ _ (image_subset_iff.mp h.algebraMap_image.subset)
left_inv x := Subtype.ext h.rightInvOn x.2
right_inv x := Subtype.ext h.left_inv x

universe u v w

open ContinuousMapZero
set_option backward.isDefEq.respectTransparency.types false in
/-- If the quasispectrum of an element restricts to a smaller scalar ring, then a non-unital
continuous functional calculus over the larger scalar ring descends to the smaller one. -/
@[simps!]
/--
Definition of `nonUnitalStarAlgHom` / `nonUnitalStarAlgHom` 的定义

English:
definition nonUnitalStarAlgHom
  signature: {R : Type u} {S : Type v} {A : Type w} [Semifield R]
  body: (φ.restrictScalars R).comp
    (nonUnitalStarAlgHom_postcomp (σₙ S a) (StarAlgHom.ofId R S) (algebraMapCLM R S).continuous)
.comp nonUnitalStarAlgHom_precomp R
        ⟨⟨Subtype.map f h.subset_preimage, (map_continuous f).subtype_map
          fun x (hx : x in σₙ S a) => h.subset_preimage hx⟩, Subty

中文:
定义 nonUnitalStarAlgHom
  签名: {R : 类型u} {S : 类型v} {A : 类型 w} [半域 R]
  定义体: (φ.restrictScalars R).comp
    (nonUnitalStarAlgHom_postcomp (σₙ S a) (StarAlgHom.ofId R S) (algebraMapCLM R S).continuous)
.comp nonUnitalStarAlgHom_precomp R
        ⟨⟨Subtype.map f h.subset_preimage, (map_continuous f).subtype_map
          fun x (hx : x in σₙ S a) => h.subset_preimage hx⟩, Subty

Depends on / 依赖: StarAlgHom, StarAlgHom.ofId, Subtype, Subtype.ext, Subtype.map, algebraMapCLM, continuous, h.map_zero, h.subset_preimage, map_continuous, map_zero, nonUnitalStarAlgHom_postcomp, nonUnitalStarAlgHom_precomp, restrictScalars, subset_preimage, subtype_map
-/
def nonUnitalStarAlgHom {R : Type u} {S : Type v} {A : Type w} [Semifield R]
    [StarRing R] [TopologicalSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Field S]
    [StarRing S] [TopologicalSpace S] [IsTopologicalRing S] [ContinuousStar S] [NonUnitalRing A]
    [StarRing A] [Algebra R S] [Module R A] [Module S A] [IsScalarTower S A A] [SMulCommClass S A A]
    [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S] {a : A}
    (φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A) {f : C(S, R)} (h : QuasispectrumRestricts a f) :
    C(σₙ R a, R)₀ ->⋆ₙₐ[R] A :=
(φ.restrictScalars R).comp
    (nonUnitalStarAlgHom_postcomp (σₙ S a) (StarAlgHom.ofId R S) (algebraMapCLM R S).continuous)
.comp nonUnitalStarAlgHom_precomp R
        ⟨⟨Subtype.map f h.subset_preimage, (map_continuous f).subtype_map
          fun x (hx : x in σₙ S a) => h.subset_preimage hx⟩, Subtype.ext h.map_zero⟩

variable {R S A : Type*} {p q : A -> Prop}
variable [Semifield R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
variable [Field S] [StarRing S] [MetricSpace S] [IsTopologicalRing S] [ContinuousStar S]
variable [NonUnitalRing A] [StarRing A] [Module S A] [IsScalarTower S A A]
variable [SMulCommClass S A A]
variable [Algebra R S] [Module R A] [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S]

/--
lemma `nonUnitalStarAlgHom_id` / 引理 `nonUnitalStarAlgHom_id`

English:
lemma nonUnitalStarAlgHom_id
  statement: {a : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A} {f : C(S, R)}
  proof: by
  simp only [QuasispectrumRestricts.nonUnitalStarAlgHom_apply]
  convert! h_id
  ext x
  exact h.rightInvOn x.2

中文:
引理 nonUnitalStarAlgHom_id
  结论: {a : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A} {f : C(S, R)}
  证明: by
  simp only [QuasispectrumRestricts.nonUnitalStarAlgHom_apply]
  convert! h_id
  ext x
  exact h.rightInvOn x.2

Depends on / 依赖: QuasispectrumRestricts, QuasispectrumRestricts.nonUnitalStarAlgHom_apply, convert, h.rightInvOn, h_id, nonUnitalStarAlgHom_apply, rightInvOn
-/
lemma nonUnitalStarAlgHom_id {a : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A} {f : C(S, R)}
    (h : QuasispectrumRestricts a f) (h_id : φ (.id _) = a) :
    h.nonUnitalStarAlgHom φ (.id _) = a := by
  simp only [QuasispectrumRestricts.nonUnitalStarAlgHom_apply]
  convert! h_id
  ext x
  exact h.rightInvOn x.2

open ContinuousMapZero in
/--
lemma `nonUnitalStarAlgHom_injective` / 引理 `nonUnitalStarAlgHom_injective`

English:
lemma nonUnitalStarAlgHom_injective
  statement: {a : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A}
  proof: have : h.homeomorph.symm 0 = 0 := Subtype.ext (map_zero <| algebraMap _ _)
hφ.comp
(postcomp_injective ⟨⟨(StarAlgHom.ofId R S), (algebraMapCLM R S).continuous⟩, _⟩ halg).comp
    (UniformEquiv.arrowCongrLeft₀ h.homeomorph.symm this |>.injective)

中文:
引理 nonUnitalStarAlgHom_injective
  结论: {a : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A}
  证明: have : h.homeomorph.symm 0 = 0 := Subtype.ext (map_zero <| algebraMap _ _)
hφ.comp
(postcomp_injective ⟨⟨(StarAlgHom.ofId R S), (algebraMapCLM R S).continuous⟩, _⟩ halg).comp
    (UniformEquiv.arrowCongrLeft₀ h.homeomorph.symm this |>.injective)

Depends on / 依赖: StarAlgHom, StarAlgHom.ofId, Subtype, Subtype.ext, UniformEquiv, UniformEquiv.arrowCongrLeft, algebraMap, algebraMapCLM, continuous, h.homeomorph.symm, homeomorph, injective, map_zero, postcomp_injective
-/
lemma nonUnitalStarAlgHom_injective {a : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A}
    (hφ : Function.Injective φ) {f : C(S, R)} (h : QuasispectrumRestricts a f)
    (halg : Function.Injective (algebraMap R S)) :
    Function.Injective (h.nonUnitalStarAlgHom φ) :=
  have : h.homeomorph.symm 0 = 0 := Subtype.ext (map_zero <| algebraMap _ _)
hφ.comp
(postcomp_injective ⟨⟨(StarAlgHom.ofId R S), (algebraMapCLM R S).continuous⟩, _⟩ halg).comp
    (UniformEquiv.arrowCongrLeft₀ h.homeomorph.symm this |>.injective)

variable [TopologicalSpace A]

section Generic

variable [NonUnitalContinuousFunctionalCalculus S A q]

open ContinuousMapZero in
/--
lemma `continuous_nonUnitalStarAlgHom` / 引理 `continuous_nonUnitalStarAlgHom`

English:
lemma continuous_nonUnitalStarAlgHom
  statement: {a : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A}
  proof: hφ.comp (continuous_postcomp _).comp (continuous_precomp _)

中文:
引理 continuous_nonUnitalStarAlgHom
  结论: {a : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A}
  证明: hφ.comp (continuous_postcomp _).comp (continuous_precomp _)

Depends on / 依赖: continuous_postcomp, continuous_precomp
-/
lemma continuous_nonUnitalStarAlgHom {a : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A}
    (hφ : Continuous φ) {f : C(S, R)} (h : QuasispectrumRestricts a f) :
    Continuous (h.nonUnitalStarAlgHom φ) :=
hφ.comp (continuous_postcomp _).comp (continuous_precomp _)

variable [CompleteSpace R] in
/--
lemma `isClosedEmbedding_nonUnitalStarAlgHom` / 引理 `isClosedEmbedding_nonUnitalStarAlgHom`

English:
lemma isClosedEmbedding_nonUnitalStarAlgHom
  statement: {a : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A}
  proof: by
  have : h.homeomorph.symm 0 = 0 := Subtype.ext (map_zero <| algebraMap _ _)
refine hφ.comp IsUniformEmbedding.isClosedEmbedding .comp
    (ContinuousMapZero.isUniformEmbedding_comp _ halg)
    (UniformEquiv.arrowCongrLeft₀ h.homeomorph.symm this |>.isUniformEmbedding)

中文:
引理 isClosedEmbedding_nonUnitalStarAlgHom
  结论: {a : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A}
  证明: by
  have : h.homeomorph.symm 0 = 0 := Subtype.ext (map_zero <| algebraMap _ _)
refine hφ.comp IsUniformEmbedding.isClosedEmbedding .comp
    (ContinuousMapZero.isUniformEmbedding_comp _ halg)
    (UniformEquiv.arrowCongrLeft₀ h.homeomorph.symm this |>.isUniformEmbedding)

Depends on / 依赖: ContinuousMapZero, ContinuousMapZero.isUniformEmbedding_comp, IsUniformEmbedding, IsUniformEmbedding.isClosedEmbedding, Subtype, Subtype.ext, UniformEquiv, UniformEquiv.arrowCongrLeft, algebraMap, h.homeomorph.symm, homeomorph, isClosedEmbedding, isUniformEmbedding, isUniformEmbedding_comp, map_zero
-/
lemma isClosedEmbedding_nonUnitalStarAlgHom {a : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A}
    (hφ : IsClosedEmbedding φ) {f : C(S, R)} (h : QuasispectrumRestricts a f)
    (halg : IsUniformEmbedding (algebraMap R S)) :
    IsClosedEmbedding (h.nonUnitalStarAlgHom φ) := by
  have : h.homeomorph.symm 0 = 0 := Subtype.ext (map_zero <| algebraMap _ _)
refine hφ.comp IsUniformEmbedding.isClosedEmbedding .comp
    (ContinuousMapZero.isUniformEmbedding_comp _ halg)
    (UniformEquiv.arrowCongrLeft₀ h.homeomorph.symm this |>.isUniformEmbedding)

variable [IsScalarTower R A A] [SMulCommClass R A A]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `cfc` / 定理 `cfc`

English:
theorem cfc
  statement: (f : C(S, R)) (halg : IsClosedEmbedding (algebraMap R S)) (h0 : p 0)
  proof: h0
  compactSpace_quasispectrum a := by
    have := NonUnitalContinuousFunctionalCalculus.compactSpace_quasispectrum (R := S) a
    rw [← isCompact_iff_compactSpace] at this ⊢
    simpa using halg.isCompact_preimage this
  exists_cfc_of_predicate a ha := by
    refine ⟨((h a).mp ha).2.nonUnitalStarA

中文:
定理 cfc
  结论: (f : C(S, R)) (halg : 是闭嵌入 (algebraMap R S)) (h0 : p 0)
  证明: h0
  compactSpace_quasispectrum a := by
    have := NonUnitalContinuousFunctionalCalculus.compactSpace_quasispectrum (R := S) a
    rw [← isCompact_iff_compactSpace] at this ⊢
    simpa using halg.isCompact_preimage this
  exists_cfc_of_predicate a ha := by
    refine ⟨((h a).mp ha).2.nonUnitalStarA
-/
protected theorem cfc (f : C(S, R)) (halg : IsClosedEmbedding (algebraMap R S)) (h0 : p 0)
    (h : forall a, p a ↔ q a ∧ QuasispectrumRestricts a f) :
    NonUnitalContinuousFunctionalCalculus R A p where
  predicate_zero := h0
  compactSpace_quasispectrum a := by
    have := NonUnitalContinuousFunctionalCalculus.compactSpace_quasispectrum (R := S) a
    rw [← isCompact_iff_compactSpace] at this ⊢
    simpa using halg.isCompact_preimage this
  exists_cfc_of_predicate a ha := by
    refine ⟨((h a).mp ha).2.nonUnitalStarAlgHom (cfcₙHom ((h a).mp ha).1 (R := S)),
      ?hom_continuous, ?hom_injective, ?hom_id, ?hom_map_spectrum, ?predicate_hom⟩
    case hom_continuous => exact continuous_nonUnitalStarAlgHom (cfcₙHom_continuous _) _
    case hom_injective => exact nonUnitalStarAlgHom_injective (cfcₙHom_injective _) _ halg.injective
case hom_id => exact ((h a).mp ha).2.nonUnitalStarAlgHom_id cfcₙHom_id ((h a).mp ha).1
    case hom_map_spectrum =>
      simp only [nonUnitalStarAlgHom_apply, ← @quasispectrum.preimage_algebraMap (R := R) S,
        cfcₙHom_map_quasispectrum, Set.ext_iff, Set.mem_preimage, Set.mem_range, comp_apply, coe_mk,
        ContinuousMap.coe_mk, StarAlgHom.ofId_apply, halg.injective.eq_iff]
      exact fun _ _ => ((h a).mp ha).2.homeomorph.exists_congr fun b => Iff.rfl
    case predicate_hom =>
      intro g
      rw [h]
      refine ⟨cfcₙHom_predicate _ _, ?_⟩
      refine { rightInvOn := fun s hs => ?_, left_inv := ((h a).mp ha).2.left_inv }
      rw [nonUnitalStarAlgHom_apply]; rw [cfcₙHom_map_quasispectrum] at hs
      obtain ⟨r, rfl⟩ := hs
      simp [((h a).mp ha).2.left_inv _]

variable [NonUnitalContinuousFunctionalCalculus R A p]
variable [ContinuousMapZero.UniqueHom R A]

/--
lemma `cfcₙHom_eq_restrict` / 引理 `cfcₙHom_eq_restrict`

English:
lemma cfcₙHom_eq_restrict
  statement: (f : C(S, R)) {a : A} (hpa : p a) (hqa : q a)
  proof: by
  apply cfcₙHom_eq_of_continuous_of_map_id
  · exact h.continuous_nonUnitalStarAlgHom (cfcₙHom_continuous hqa)
  · exact h.nonUnitalStarAlgHom_id (cfcₙHom_id hqa)

中文:
引理 cfcₙHom_eq_restrict
  结论: (f : C(S, R)) {a : A} (hpa : p a) (hqa : q a)
  证明: by
  apply cfcₙHom_eq_of_continuous_of_map_id
  · exact h.continuous_nonUnitalStarAlgHom (cfcₙHom_continuous hqa)
  · exact h.nonUnitalStarAlgHom_id (cfcₙHom_id hqa)

Depends on / 依赖: continuous_nonUnitalStarAlgHom, h.continuous_nonUnitalStarAlgHom, h.nonUnitalStarAlgHom_id, nonUnitalStarAlgHom_id
-/
lemma cfcₙHom_eq_restrict (f : C(S, R)) {a : A} (hpa : p a) (hqa : q a)
    (h : QuasispectrumRestricts a f) :
    cfcₙHom hpa = h.nonUnitalStarAlgHom (cfcₙHom hqa) := by
  apply cfcₙHom_eq_of_continuous_of_map_id
  · exact h.continuous_nonUnitalStarAlgHom (cfcₙHom_continuous hqa)
  · exact h.nonUnitalStarAlgHom_id (cfcₙHom_id hqa)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `cfcₙ_eq_restrict` / 引理 `cfcₙ_eq_restrict`

English:
lemma cfcₙ_eq_restrict
  statement: (f : C(S, R)) (halg : IsClosedEmbedding (algebraMap R S)) {a : A}
  proof: by
  by_cases hg : ContinuousOn g (σₙ R a) ∧ g 0 = 0
  · obtain ⟨hg, hg0⟩ := hg
    rw [cfcₙ_apply g a]; rw [cfcₙHom_eq_restrict f hpa hqa h]; rw [nonUnitalStarAlgHom_apply]; rw [cfcₙHom_eq_cfcₙ_extend 0]
    apply cfcₙ_congr fun x hx => ?_
    lift x to σₙ S a using hx
    simp
  · simp only [not_a

中文:
引理 cfcₙ_eq_restrict
  结论: (f : C(S, R)) (halg : 是闭嵌入 (algebraMap R S)) {a : A}
  证明: by
  by_cases hg : ContinuousOn g (σₙ R a) ∧ g 0 = 0
  · obtain ⟨hg, hg0⟩ := hg
    rw [cfcₙ_apply g a]; rw [cfcₙHom_eq_restrict f hpa hqa h]; rw [nonUnitalStarAlgHom_apply]; rw [cfcₙHom_eq_cfcₙ_extend 0]
    apply cfcₙ_congr fun x hx => ?_
    lift x to σₙ S a using hx
    simp
  · simp only [not_a

Depends on / 依赖: ContinuousOn, algebraMap, continuousOn_if, continuousOn_iff, halg.isEmbedding.continuousOn_if, halg.isEmbedding.continuousOn_iff, isEmbedding, nonUnitalStarAlgHom_apply, not_and_or
-/
lemma cfcₙ_eq_restrict (f : C(S, R)) (halg : IsClosedEmbedding (algebraMap R S)) {a : A}
    (hpa : p a) (hqa : q a) (h : QuasispectrumRestricts a f) (g : R -> R) :
    cfcₙ g a = cfcₙ (fun x => algebraMap R S (g (f x))) a := by
  by_cases hg : ContinuousOn g (σₙ R a) ∧ g 0 = 0
  · obtain ⟨hg, hg0⟩ := hg
    rw [cfcₙ_apply g a]; rw [cfcₙHom_eq_restrict f hpa hqa h]; rw [nonUnitalStarAlgHom_apply]; rw [cfcₙHom_eq_cfcₙ_extend 0]
    apply cfcₙ_congr fun x hx => ?_
    lift x to σₙ S a using hx
    simp
  · simp only [not_and_or] at hg
    obtain (hg | hg) := hg
    · have : ¬ ContinuousOn (fun x => algebraMap R S (g (f x)) : S -> S) (σₙ S a) := by
        refine fun hg' => hg ?_
        rw [halg.isEmbedding.continuousOn_iff]
        simpa [halg.isEmbedding.continuousOn_iff, Function.comp_def, h.left_inv _] using
          hg'.comp halg.isEmbedding.continuous.continuousOn
          (fun _ : R => quasispectrum.algebraMap_mem S)
      rw [cfcₙ_apply_of_not_continuousOn a hg]; rw [cfcₙ_apply_of_not_continuousOn a this]
    · rw [cfcₙ_apply_of_not_map_zero a hg, cfcₙ_apply_of_not_map_zero a (by simpa [h.map_zero])]

end Generic

variable [NonUnitalClosedEmbeddingContinuousFunctionalCalculus S A q]
  [IsScalarTower R A A] [SMulCommClass R A A]
  [ContinuousMapZero.UniqueHom R A] [CompleteSpace R]

open NonUnitalContinuousFunctionalCalculus in
/--
theorem `nonUnitalClosedEmbeddingCFC` / 定理 `nonUnitalClosedEmbeddingCFC`

English:
theorem nonUnitalClosedEmbeddingCFC
  statement: (f : C(S, R))
  proof: QuasispectrumRestricts.cfc f halg.isClosedEmbedding h0 h
  isClosedEmbedding a ha := by
    have := QuasispectrumRestricts.cfc f halg.isClosedEmbedding h0 h
    rw [cfcₙHom_eq_restrict f ha ((h a).mp ha).1 ((h a).mp ha).2]
    exact isClosedEmbedding_nonUnitalStarAlgHom (cfcₙHom_isClosedEmbedding ((

中文:
定理 nonUnitalClosedEmbeddingCFC
  结论: (f : C(S, R))
  证明: QuasispectrumRestricts.cfc f halg.isClosedEmbedding h0 h
  isClosedEmbedding a ha := by
    have := QuasispectrumRestricts.cfc f halg.isClosedEmbedding h0 h
    rw [cfcₙHom_eq_restrict f ha ((h a).mp ha).1 ((h a).mp ha).2]
    exact isClosedEmbedding_nonUnitalStarAlgHom (cfcₙHom_isClosedEmbedding ((
-/
protected theorem nonUnitalClosedEmbeddingCFC (f : C(S, R))
    (halg : IsUniformEmbedding (algebraMap R S))
    (h0 : p 0) (h : forall a, p a ↔ q a ∧ QuasispectrumRestricts a f) :
    NonUnitalClosedEmbeddingContinuousFunctionalCalculus R A p where
  toNonUnitalContinuousFunctionalCalculus :=
    QuasispectrumRestricts.cfc f halg.isClosedEmbedding h0 h
  isClosedEmbedding a ha := by
    have := QuasispectrumRestricts.cfc f halg.isClosedEmbedding h0 h
    rw [cfcₙHom_eq_restrict f ha ((h a).mp ha).1 ((h a).mp ha).2]
    exact isClosedEmbedding_nonUnitalStarAlgHom (cfcₙHom_isClosedEmbedding ((h a).mp ha).1)
      ((h a).mp ha).2 halg

end QuasispectrumRestricts
