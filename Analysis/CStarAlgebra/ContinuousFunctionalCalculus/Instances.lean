/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Complex.Spectrum
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Restrict
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.RCLike.Lemmas

/-! # Instances of the continuous functional calculus

## Main theorems

* `IsSelfAdjoint.instContinuousFunctionalCalculus`: the continuous functional calculus for
  selfadjoint elements in a `ℂ`-algebra with a continuous functional calculus for normal elements
  and where every element has compact spectrum. In particular, this includes unital C⋆-algebras
  over `ℂ`.
* `Nonneg.instContinuousFunctionalCalculus`: the continuous functional calculus for nonnegative
  elements in an `ℝ`-algebra with a continuous functional calculus for selfadjoint elements,
  where every element has compact spectrum, and where nonnegative elements have nonnegative
  spectrum. In particular, this includes unital C⋆-algebras over `ℝ`.

## Tags

continuous functional calculus, normal, selfadjoint
-/

@[expose] public section

open Topology

noncomputable section

local notation "σₙ" => quasispectrum
local notation "σ" => spectrum

/-!
### Pull back a non-unital instance from a unital one on the unitization
-/

section RCLike

variable {𝕜 A : Type*} [RCLike 𝕜] [NonUnitalNormedRing A] [StarRing A]
variable [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
variable [StarModule 𝕜 A] {p : A -> Prop} {p₁ : Unitization 𝕜 A -> Prop}

local postfix:max "⁺¹" => Unitization 𝕜

variable (hp₁ : forall {x : A}, p₁ x ↔ p x) (a : A) (ha : p a)
variable [ClosedEmbeddingContinuousFunctionalCalculus 𝕜 (Unitization 𝕜 A) p₁]

open scoped ContinuousMapZero


open Unitization in
/--
Definition of `cfcₙAux` / `cfcₙAux` 的定义

English:
definition cfcₙAux
  signature: : C(σₙ 𝕜 a, 𝕜)₀ ->⋆ₙₐ[𝕜] A⁺¹
  body: .comp (cfcHom (R := 𝕜) (hp₁.mpr ha) : C(σ 𝕜 (a : A⁺¹), 𝕜) ->⋆ₙₐ[𝕜] A⁺¹)
    (Homeomorph.compStarAlgEquiv' 𝕜 𝕜 <| .setCongr <| (quasispectrum_eq_spectrum_inr' 𝕜 𝕜 a).symm)
.comp ContinuousMapZero.toContinuousMapHom

中文:
定义 cfcₙAux
  签名: : C(σₙ 𝕜 a, 𝕜)₀ ->⋆ₙₐ[𝕜] A⁺¹
  定义体: .comp (cfcHom (R := 𝕜) (hp₁.mpr ha) : C(σ 𝕜 (a : A⁺¹), 𝕜) ->⋆ₙₐ[𝕜] A⁺¹)
    (Homeomorph.compStarAlgEquiv' 𝕜 𝕜 <| .setCongr <| (quasispectrum_eq_spectrum_inr' 𝕜 𝕜 a).symm)
.comp ContinuousMapZero.toContinuousMapHom

Depends on / 依赖: ContinuousMapZero, ContinuousMapZero.toContinuousMapHom, Homeomorph, Homeomorph.compStarAlgEquiv, cfcHom, compStarAlgEquiv, quasispectrum_eq_spectrum_inr, setCongr, toContinuousMapHom
-/
noncomputable def cfcₙAux : C(σₙ 𝕜 a, 𝕜)₀ ->⋆ₙₐ[𝕜] A⁺¹ :=
.comp (cfcHom (R := 𝕜) (hp₁.mpr ha) : C(σ 𝕜 (a : A⁺¹), 𝕜) ->⋆ₙₐ[𝕜] A⁺¹)
    (Homeomorph.compStarAlgEquiv' 𝕜 𝕜 <| .setCongr <| (quasispectrum_eq_spectrum_inr' 𝕜 𝕜 a).symm)
.comp ContinuousMapZero.toContinuousMapHom

/--
lemma `cfcₙAux_id` / 引理 `cfcₙAux_id`

English:
lemma cfcₙAux_id
  statement: cfcₙAux hp₁ a ha (.id _) = a
  proof: cfcHom_id (hp₁.mpr ha)

中文:
引理 cfcₙAux_id
  结论: cfcₙAux hp₁ a ha (.id _) = a
  证明: cfcHom_id (hp₁.mpr ha)

Depends on / 依赖: cfcHom_id
-/
lemma cfcₙAux_id : cfcₙAux hp₁ a ha (.id _) = a := cfcHom_id (hp₁.mpr ha)

/--
lemma `continuous_cfcₙAux` / 引理 `continuous_cfcₙAux`

English:
lemma continuous_cfcₙAux
  statement: Continuous (cfcₙAux hp₁ a ha)
  proof: (cfcHom_continuous (hp₁.mpr ha)).comp
(ContinuousMap.continuous_precomp _).comp
    ContinuousMapZero.isEmbedding_toContinuousMap.continuous

中文:
引理 continuous_cfcₙAux
  结论: 连续 (cfcₙAux hp₁ a ha)
  证明: (cfcHom_continuous (hp₁.mpr ha)).comp
(ContinuousMap.continuous_precomp _).comp
    ContinuousMapZero.isEmbedding_toContinuousMap.continuous

Depends on / 依赖: ContinuousMap, ContinuousMap.continuous_precomp, ContinuousMapZero, ContinuousMapZero.isEmbedding_toContinuousMap.continuous, cfcHom_continuous, continuous, continuous_precomp, isEmbedding_toContinuousMap
-/
lemma continuous_cfcₙAux : Continuous (cfcₙAux hp₁ a ha) :=
(cfcHom_continuous (hp₁.mpr ha)).comp
(ContinuousMap.continuous_precomp _).comp
    ContinuousMapZero.isEmbedding_toContinuousMap.continuous

/--
lemma `cfcₙAux_injective` / 引理 `cfcₙAux_injective`

English:
lemma cfcₙAux_injective
  statement: Function.Injective (cfcₙAux hp₁ a ha)
  proof: (cfcHom_injective (hp₁.mpr ha)).comp
    .comp (Equiv.injective _) ContinuousMapZero.isEmbedding_toContinuousMap.injective

中文:
引理 cfcₙAux_injective
  结论: 函数.单射 (cfcₙAux hp₁ a ha)
  证明: (cfcHom_injective (hp₁.mpr ha)).comp
    .comp (Equiv.injective _) ContinuousMapZero.isEmbedding_toContinuousMap.injective

Depends on / 依赖: ContinuousMapZero, ContinuousMapZero.isEmbedding_toContinuousMap.injective, Equiv.injective, cfcHom_injective, injective, isEmbedding_toContinuousMap
-/
lemma cfcₙAux_injective : Function.Injective (cfcₙAux hp₁ a ha) :=
(cfcHom_injective (hp₁.mpr ha)).comp
    .comp (Equiv.injective _) ContinuousMapZero.isEmbedding_toContinuousMap.injective

/--
lemma `spec_cfcₙAux` / 引理 `spec_cfcₙAux`

English:
lemma spec_cfcₙAux
  given: (f : C(σₙ 𝕜 a, 𝕜)₀)
  statement: σ 𝕜 (cfcₙAux hp₁ a ha f) = Set.range f
  proof: by
  rw [cfcₙAux]; rw [NonUnitalStarAlgHom.comp_assoc]; rw [NonUnitalStarAlgHom.comp_apply]
  simp only [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_coe]
  rw [cfcHom_map_spectrum (hp₁.mpr ha) (R := 𝕜) _]
  simp

中文:
引理 spec_cfcₙAux
  条件: (f : C(σₙ 𝕜 a, 𝕜)₀)
  结论: σ 𝕜 (cfcₙAux hp₁ a ha f) = 集合.range f
  证明: by
  rw [cfcₙAux]; rw [NonUnitalStarAlgHom.comp_assoc]; rw [NonUnitalStarAlgHom.comp_apply]
  simp only [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_coe]
  rw [cfcHom_map_spectrum (hp₁.mpr ha) (R := 𝕜) _]
  simp

Depends on / 依赖: NonUnitalStarAlgHom, NonUnitalStarAlgHom.coe_coe, NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.comp_assoc, cfcHom_map_spectrum, coe_coe, comp_apply, comp_assoc
-/
lemma spec_cfcₙAux (f : C(σₙ 𝕜 a, 𝕜)₀) : σ 𝕜 (cfcₙAux hp₁ a ha f) = Set.range f := by
  rw [cfcₙAux]; rw [NonUnitalStarAlgHom.comp_assoc]; rw [NonUnitalStarAlgHom.comp_apply]
  simp only [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_coe]
  rw [cfcHom_map_spectrum (hp₁.mpr ha) (R := 𝕜) _]
  simp

open Unitization in
/--
lemma `isClosedEmbedding_cfcₙAux` / 引理 `isClosedEmbedding_cfcₙAux`

English:
lemma isClosedEmbedding_cfcₙAux
  statement: IsClosedEmbedding (cfcₙAux hp₁ a ha)
  proof: by
  simp only [cfcₙAux, NonUnitalStarAlgHom.coe_comp]
  refine ((cfcHom_isClosedEmbedding (hp₁.mpr ha)).comp ?_).comp
    ContinuousMapZero.isClosedEmbedding_toContinuousMap
  let e : C(σₙ 𝕜 a, 𝕜) ≃ₜ C(σ 𝕜 (a : A⁺¹), 𝕜) :=
    (Homeomorph.setCongr (quasispectrum_eq_spectrum_inr' 𝕜 𝕜 a)).arrowCongr 

中文:
引理 isClosedEmbedding_cfcₙAux
  结论: 是闭嵌入 (cfcₙAux hp₁ a ha)
  证明: by
  simp only [cfcₙAux, NonUnitalStarAlgHom.coe_comp]
  refine ((cfcHom_isClosedEmbedding (hp₁.mpr ha)).comp ?_).comp
    ContinuousMapZero.isClosedEmbedding_toContinuousMap
  let e : C(σₙ 𝕜 a, 𝕜) ≃ₜ C(σ 𝕜 (a : A⁺¹), 𝕜) :=
    (Homeomorph.setCongr (quasispectrum_eq_spectrum_inr' 𝕜 𝕜 a)).arrowCongr 

Depends on / 依赖: ContinuousMapZero, ContinuousMapZero.isClosedEmbedding_toContinuousMap, Homeomorph, Homeomorph.setCongr, NonUnitalStarAlgHom, NonUnitalStarAlgHom.coe_comp, arrowCongr, cfcHom_isClosedEmbedding, coe_comp, e.isClosedEmbedding, isClosedEmbedding, isClosedEmbedding_toContinuousMap, quasispectrum_eq_spectrum_inr, setCongr
-/
lemma isClosedEmbedding_cfcₙAux : IsClosedEmbedding (cfcₙAux hp₁ a ha) := by
  simp only [cfcₙAux, NonUnitalStarAlgHom.coe_comp]
  refine ((cfcHom_isClosedEmbedding (hp₁.mpr ha)).comp ?_).comp
    ContinuousMapZero.isClosedEmbedding_toContinuousMap
  let e : C(σₙ 𝕜 a, 𝕜) ≃ₜ C(σ 𝕜 (a : A⁺¹), 𝕜) :=
    (Homeomorph.setCongr (quasispectrum_eq_spectrum_inr' 𝕜 𝕜 a)).arrowCongr (.refl _)
  exact e.isClosedEmbedding

variable [CompleteSpace A]

/--
lemma `cfcₙAux_mem_range_inr` / 引理 `cfcₙAux_mem_range_inr`

English:
lemma cfcₙAux_mem_range_inr
  given: (f : C(σₙ 𝕜 a, 𝕜)₀)
  proof: by
  have h₁ := (continuous_cfcₙAux hp₁ a ha).range_subset_closure_image_dense
    (ContinuousMapZero.adjoin_id_dense (σₙ 𝕜 a)) ⟨f, rfl⟩
  rw [← SetLike.mem_coe]
  refine closure_minimal ?_ ?_ h₁
  · rw [← NonUnitalStarSubalgebra.coe_map, SetLike.coe_subset_coe, NonUnitalStarSubalgebra.map_le]
    a

中文:
引理 cfcₙAux_mem_range_inr
  条件: (f : C(σₙ 𝕜 a, 𝕜)₀)
  证明: by
  have h₁ := (continuous_cfcₙAux hp₁ a ha).range_subset_closure_image_dense
    (ContinuousMapZero.adjoin_id_dense (σₙ 𝕜 a)) ⟨f, rfl⟩
  rw [← SetLike.mem_coe]
  refine closure_minimal ?_ ?_ h₁
  · rw [← NonUnitalStarSubalgebra.coe_map, SetLike.coe_subset_coe, NonUnitalStarSubalgebra.map_le]
    a

Depends on / 依赖: ContinuousMapZero, ContinuousMapZero.adjoin_id_dense, NonUnitalStarAlgHom, NonUnitalStarAlgHom.coe_range, NonUnitalStarAlgebra, NonUnitalStarAlgebra.adjoin_le, NonUnitalStarSubalgebra, NonUnitalStarSubalgebra.coe_map, NonUnitalStarSubalgebra.map_le, NonUnitalStarSubalgebra.mem_comap, Set.singleton_subset_iff.mpr, SetLike, SetLike.coe_subset_coe, SetLike.mem_coe, adjoin_id_dense, adjoin_le, closure_minimal, coe_map, coe_range, coe_subset_coe
-/
lemma cfcₙAux_mem_range_inr (f : C(σₙ 𝕜 a, 𝕜)₀) :
    cfcₙAux hp₁ a ha f in NonUnitalStarAlgHom.range (Unitization.inrNonUnitalStarAlgHom 𝕜 A) := by
  have h₁ := (continuous_cfcₙAux hp₁ a ha).range_subset_closure_image_dense
    (ContinuousMapZero.adjoin_id_dense (σₙ 𝕜 a)) ⟨f, rfl⟩
  rw [← SetLike.mem_coe]
  refine closure_minimal ?_ ?_ h₁
  · rw [← NonUnitalStarSubalgebra.coe_map, SetLike.coe_subset_coe, NonUnitalStarSubalgebra.map_le]
    apply NonUnitalStarAlgebra.adjoin_le
    apply Set.singleton_subset_iff.mpr
    rw [SetLike.mem_coe]; rw [NonUnitalStarSubalgebra.mem_comap]; rw [cfcₙAux_id hp₁ a ha]
    exact ⟨a, rfl⟩
  · simp only [NonUnitalStarAlgHom.coe_range]
    convert! IsClosed.preimage (Unitization.continuous_fst (𝕜 := 𝕜)) isClosed_singleton
    aesop

variable [CStarRing A]

include hp₁ in
open Unitization NonUnitalStarAlgHom in
/--
theorem `RCLike.nonUnitalContinuousFunctionalCalculus` / 定理 `RCLike.nonUnitalContinuousFunctionalCalculus`

English:
theorem RCLike.nonUnitalContinuousFunctionalCalculus
  proof: by
    rw [← hp₁]; rw [Unitization.inr_zero 𝕜]
    exact cfc_predicate_zero 𝕜
  exists_cfc_of_predicate a ha := by
let ψ : C(σₙ 𝕜 a, 𝕜)₀ ->⋆ₙₐ[𝕜] A := comp (inrRangeEquiv 𝕜 A).symm
      codRestrict (cfcₙAux hp₁ a ha) _ (cfcₙAux_mem_range_inr hp₁ a ha)
    have coe_ψ (f : C(σₙ 𝕜 a, 𝕜)₀) : ψ f = cfcₙ

中文:
定理 RCLike.nonUnitalContinuousFunctionalCalculus
  证明: by
    rw [← hp₁]; rw [Unitization.inr_zero 𝕜]
    exact cfc_predicate_zero 𝕜
  exists_cfc_of_predicate a ha := by
let ψ : C(σₙ 𝕜 a, 𝕜)₀ ->⋆ₙₐ[𝕜] A := comp (inrRangeEquiv 𝕜 A).symm
      codRestrict (cfcₙAux hp₁ a ha) _ (cfcₙAux_mem_range_inr hp₁ a ha)
    have coe_ψ (f : C(σₙ 𝕜 a, 𝕜)₀) : ψ f = cfcₙ

Depends on / 依赖: Subtype, Subtype.val, Unitization, Unitization.inr_zero, apply_symm_apply, cfc_predicate_zero, codRestrict, congr_arg, continuous, exists_cfc_of_predicate, injective, inrRangeEquiv, inr_zero, isStarNormal, map_id, map_spec
-/
theorem RCLike.nonUnitalContinuousFunctionalCalculus :
    NonUnitalContinuousFunctionalCalculus 𝕜 A p where
  predicate_zero := by
    rw [← hp₁]; rw [Unitization.inr_zero 𝕜]
    exact cfc_predicate_zero 𝕜
  exists_cfc_of_predicate a ha := by
let ψ : C(σₙ 𝕜 a, 𝕜)₀ ->⋆ₙₐ[𝕜] A := comp (inrRangeEquiv 𝕜 A).symm
      codRestrict (cfcₙAux hp₁ a ha) _ (cfcₙAux_mem_range_inr hp₁ a ha)
    have coe_ψ (f : C(σₙ 𝕜 a, 𝕜)₀) : ψ f = cfcₙAux hp₁ a ha f :=
congr_arg Subtype.val (inrRangeEquiv 𝕜 A).apply_symm_apply
        ⟨cfcₙAux hp₁ a ha f, cfcₙAux_mem_range_inr hp₁ a ha f⟩
    refine ⟨ψ, ?continuous, ?injective, ?map_id, fun f => ?map_spec, fun f => ?isStarNormal⟩
    case continuous =>
      rw [isometry_inr (𝕜 := 𝕜) |>.isEmbedding.continuous_iff]
      have := continuous_cfcₙAux hp₁ a ha
      simp only [coe_comp, NonUnitalStarAlgHom.coe_coe, Function.comp_def,
        inrRangeEquiv_symm_apply, coe_codRestrict, ψ]
      fun_prop
    case injective =>
      have h₁ : Function.Injective ⇑(codRestrict (cfcₙAux hp₁ a ha) _
          (cfcₙAux_mem_range_inr hp₁ a ha)) :=
        (Set.injective_codRestrict _).mpr (cfcₙAux_injective hp₁ a ha)
      simpa [ψ] using (inrRangeEquiv 𝕜 A).symm.injective.comp h₁
case map_id => exact inr_injective (R := 𝕜) coe_ψ _ ▸ cfcₙAux_id hp₁ a ha
    case map_spec =>
      exact quasispectrum_eq_spectrum_inr' 𝕜 𝕜 (ψ f) ▸ coe_ψ _ ▸ spec_cfcₙAux hp₁ a ha f
case isStarNormal => exact hp₁.mp coe_ψ _ ▸ cfcHom_predicate (R := 𝕜) (hp₁.mpr ha) _

open Unitization in
open scoped NonUnitalContinuousFunctionalCalculus in
/--
lemma `inrNonUnitalStarAlgHom_comp_cfcₙHom_eq_cfcₙAux` / 引理 `inrNonUnitalStarAlgHom_comp_cfcₙHom_eq_cfcₙAux`

English:
lemma inrNonUnitalStarAlgHom_comp_cfcₙHom_eq_cfcₙAux
  given: (a : A) (ha : p a)
  proof: RCLike.nonUnitalContinuousFunctionalCalculus hp₁
    (inrNonUnitalStarAlgHom 𝕜 A).comp (cfcₙHom ha) = cfcₙAux hp₁ a ha := by
  let _ := RCLike.nonUnitalContinuousFunctionalCalculus hp₁
  apply ContinuousMapZero.UniqueHom.eq_of_continuous_of_map_id _ _ _
    (Unitization.continuous_inr.comp <| cfcₙHo

中文:
引理 inrNonUnitalStarAlgHom_comp_cfcₙHom_eq_cfcₙAux
  条件: (a : A) (ha : p a)
  证明: RCLike.nonUnitalContinuousFunctionalCalculus hp₁
    (inrNonUnitalStarAlgHom 𝕜 A).comp (cfcₙHom ha) = cfcₙAux hp₁ a ha := by
  let _ := RCLike.nonUnitalContinuousFunctionalCalculus hp₁
  apply ContinuousMapZero.UniqueHom.eq_of_continuous_of_map_id _ _ _
    (Unitization.continuous_inr.comp <| cfcₙHo

Depends on / 依赖: RCLike, RCLike.nonUnitalContinuousFunctionalCalculus, nonUnitalContinuousFunctionalCalculus
-/
lemma inrNonUnitalStarAlgHom_comp_cfcₙHom_eq_cfcₙAux (a : A) (ha : p a) :
    letI _ := RCLike.nonUnitalContinuousFunctionalCalculus hp₁
    (inrNonUnitalStarAlgHom 𝕜 A).comp (cfcₙHom ha) = cfcₙAux hp₁ a ha := by
  let _ := RCLike.nonUnitalContinuousFunctionalCalculus hp₁
  apply ContinuousMapZero.UniqueHom.eq_of_continuous_of_map_id _ _ _
    (Unitization.continuous_inr.comp <| cfcₙHom_continuous ha)
    (continuous_cfcₙAux hp₁ a ha)
    (by simp [cfcₙHom_id ha, cfcₙAux_id hp₁ a ha])
  all_goals infer_instance


include hp₁ in
open Unitization NonUnitalStarAlgHom in
/--
theorem `RCLike.nonUnitalContinuousFunctionalCalculusIsClosedEmbedding` / 定理 `RCLike.nonUnitalContinuousFunctionalCalculusIsClosedEmbedding`

English:
theorem RCLike.nonUnitalContinuousFunctionalCalculusIsClosedEmbedding
  proof: RCLike.nonUnitalContinuousFunctionalCalculus hp₁
  isClosedEmbedding a ha := by
.of_comp_iff.mp .isClosedEmbedding apply isometry_inr (𝕜 := 𝕜) (A := A)
    convert! isClosedEmbedding_cfcₙAux hp₁ a ha
    congrm (⇑$(inrNonUnitalStarAlgHom_comp_cfcₙHom_eq_cfcₙAux hp₁ a ha))

中文:
定理 RCLike.nonUnitalContinuousFunctionalCalculusIsClosedEmbedding
  证明: RCLike.nonUnitalContinuousFunctionalCalculus hp₁
  isClosedEmbedding a ha := by
.of_comp_iff.mp .isClosedEmbedding apply isometry_inr (𝕜 := 𝕜) (A := A)
    convert! isClosedEmbedding_cfcₙAux hp₁ a ha
    congrm (⇑$(inrNonUnitalStarAlgHom_comp_cfcₙHom_eq_cfcₙAux hp₁ a ha))

Depends on / 依赖: RCLike, RCLike.nonUnitalContinuousFunctionalCalculus, nonUnitalContinuousFunctionalCalculus
-/
theorem RCLike.nonUnitalContinuousFunctionalCalculusIsClosedEmbedding :
    NonUnitalClosedEmbeddingContinuousFunctionalCalculus 𝕜 A p where
  toNonUnitalContinuousFunctionalCalculus := RCLike.nonUnitalContinuousFunctionalCalculus hp₁
  isClosedEmbedding a ha := by
.of_comp_iff.mp .isClosedEmbedding apply isometry_inr (𝕜 := 𝕜) (A := A)
    convert! isClosedEmbedding_cfcₙAux hp₁ a ha
    congrm (⇑$(inrNonUnitalStarAlgHom_comp_cfcₙHom_eq_cfcₙAux hp₁ a ha))

end RCLike

/-!
### Continuous functional calculus for selfadjoint elements
-/

section SelfAdjointNonUnital

variable {A : Type*} [TopologicalSpace A] [NonUnitalRing A] [StarRing A] [Module Complex A]
  [IsScalarTower Complex A A] [SMulCommClass Complex A A]
  [NonUnitalContinuousFunctionalCalculus Complex A IsStarNormal]

/--
lemma `isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts` / 引理 `isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts`

English:
lemma isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts
  given: {a : A}
  proof: by
  refine ⟨fun ha => ⟨ha.isStarNormal, ⟨fun x hx => ?_, Complex.ofReal_re⟩⟩, ?_⟩
· have := eqOn_of_cfcₙ_eq_cfcₙ
      (cfcₙ_star (id : Complex -> Complex) a).symm ▸ (cfcₙ_id Complex a).symm ▸ ha.star_eq
    exact Complex.conj_eq_iff_re.mp (by simpa using this hx)
  · rintro ⟨ha₁, ha₂⟩
    rw [isSe

中文:
引理 isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts
  条件: {a : A}
  证明: by
  refine ⟨fun ha => ⟨ha.isStarNormal, ⟨fun x hx => ?_, Complex.ofReal_re⟩⟩, ?_⟩
· have := eqOn_of_cfcₙ_eq_cfcₙ
      (cfcₙ_star (id : Complex -> Complex) a).symm ▸ (cfcₙ_id Complex a).symm ▸ ha.star_eq
    exact Complex.conj_eq_iff_re.mp (by simpa using this hx)
  · rintro ⟨ha₁, ha₂⟩
    rw [isSe

Depends on / 依赖: Complex.conj_eq_iff_re.mp, Complex.conj_ofReal, Complex.ofReal_re, algebraMap_image, algebraMap_image.symm, conj_eq_iff_re, conj_ofReal, ha.isStarNormal, ha.star_eq, isSelfAdjoint_iff, isStarNormal, nth_rw, ofReal_re, star_eq
-/
lemma isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts {a : A} :
    IsSelfAdjoint a ↔ IsStarNormal a ∧ QuasispectrumRestricts a Complex.reCLM := by
  refine ⟨fun ha => ⟨ha.isStarNormal, ⟨fun x hx => ?_, Complex.ofReal_re⟩⟩, ?_⟩
· have := eqOn_of_cfcₙ_eq_cfcₙ
      (cfcₙ_star (id : Complex -> Complex) a).symm ▸ (cfcₙ_id Complex a).symm ▸ ha.star_eq
    exact Complex.conj_eq_iff_re.mp (by simpa using this hx)
  · rintro ⟨ha₁, ha₂⟩
    rw [isSelfAdjoint_iff]
    nth_rw 2 [← cfcₙ_id Complex a]
    rw [← cfcₙ_star_id a (R := Complex)]
    refine cfcₙ_congr fun x hx => ?_
    obtain ⟨x, -, rfl⟩ := ha₂.algebraMap_image.symm ▸ hx
    exact Complex.conj_ofReal _

/--
lemma `IsSelfAdjoint.quasispectrumRestricts` / 引理 `IsSelfAdjoint.quasispectrumRestricts`

English:
lemma IsSelfAdjoint.quasispectrumRestricts
  given: {a : A} (ha : IsSelfAdjoint a)
  proof: .2 .mp ha isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts

中文:
引理 IsSelfAdjoint.quasispectrumRestricts
  条件: {a : A} (ha : IsSelfAdjoint a)
  证明: .2 .mp ha isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts

Depends on / 依赖: isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts
-/
lemma IsSelfAdjoint.quasispectrumRestricts {a : A} (ha : IsSelfAdjoint a) :
    QuasispectrumRestricts a Complex.reCLM :=
.2 .mp ha isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts

/--
lemma `QuasispectrumRestricts.isSelfAdjoint` / 引理 `QuasispectrumRestricts.isSelfAdjoint`

English:
lemma QuasispectrumRestricts.isSelfAdjoint
  statement: (a : A) (ha : QuasispectrumRestricts a Complex.reCLM)
  proof: isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts.mpr ⟨‹_›, ha⟩

中文:
引理 QuasispectrumRestricts.isSelfAdjoint
  结论: (a : A) (ha : QuasispectrumRestricts a 复形.reCLM)
  证明: isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts.mpr ⟨‹_›, ha⟩

Depends on / 依赖: isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts, isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts.mpr
-/
lemma QuasispectrumRestricts.isSelfAdjoint (a : A) (ha : QuasispectrumRestricts a Complex.reCLM)
    [IsStarNormal a] : IsSelfAdjoint a :=
  isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts.mpr ⟨‹_›, ha⟩

/--
Instance `IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus` / 实例 `IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus`

English:
instance IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  signature: :
  body: QuasispectrumRestricts.cfc (q := IsStarNormal) (p := IsSelfAdjoint) Complex.reCLM
    Complex.isometry_ofReal.isClosedEmbedding (.zero _)
    (fun _ => isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts)

中文:
实例 IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  签名: :
  定义体: QuasispectrumRestricts.cfc (q := IsStarNormal) (p := IsSelfAdjoint) Complex.reCLM
    Complex.isometry_ofReal.isClosedEmbedding (.zero _)
    (fun _ => isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts)

Depends on / 依赖: Complex.isometry_ofReal.isClosedEmbedding, Complex.reCLM, IsSelfAdjoint, IsStarNormal, QuasispectrumRestricts, QuasispectrumRestricts.cfc, isClosedEmbedding, isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts, isometry_ofReal
-/
instance IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus :
    NonUnitalContinuousFunctionalCalculus Real A IsSelfAdjoint :=
  QuasispectrumRestricts.cfc (q := IsStarNormal) (p := IsSelfAdjoint) Complex.reCLM
    Complex.isometry_ofReal.isClosedEmbedding (.zero _)
    (fun _ => isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts)

end SelfAdjointNonUnital

section SelfAdjointUnital


variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [Algebra Complex A]
  [ContinuousFunctionalCalculus Complex A IsStarNormal]

/--
lemma `IsSelfAdjoint.spectrumRestricts` / 引理 `IsSelfAdjoint.spectrumRestricts`

English:
lemma IsSelfAdjoint.spectrumRestricts
  given: {a : A} (ha : IsSelfAdjoint a)
  proof: ha.quasispectrumRestricts

中文:
引理 IsSelfAdjoint.spectrumRestricts
  条件: {a : A} (ha : IsSelfAdjoint a)
  证明: ha.quasispectrumRestricts

Depends on / 依赖: ha.quasispectrumRestricts, quasispectrumRestricts
-/
lemma IsSelfAdjoint.spectrumRestricts {a : A} (ha : IsSelfAdjoint a) :
    SpectrumRestricts a Complex.reCLM :=
  ha.quasispectrumRestricts

/--
Instance `IsSelfAdjoint.instContinuousFunctionalCalculus` / 实例 `IsSelfAdjoint.instContinuousFunctionalCalculus`

English:
instance IsSelfAdjoint.instContinuousFunctionalCalculus
  signature: :
  body: SpectrumRestricts.cfc (q := IsStarNormal) (p := IsSelfAdjoint) Complex.reCLM
    Complex.isometry_ofReal.isClosedEmbedding (.zero _)
    (fun _ => isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts)

@[deprecated "Use `ContinuousFunctionalCalculus.spectrum_nonempty a ha` instead."
    (since 

中文:
实例 IsSelfAdjoint.instContinuousFunctionalCalculus
  签名: :
  定义体: SpectrumRestricts.cfc (q := IsStarNormal) (p := IsSelfAdjoint) Complex.reCLM
    Complex.isometry_ofReal.isClosedEmbedding (.zero _)
    (fun _ => isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts)

@[deprecated "Use `ContinuousFunctionalCalculus.spectrum_nonempty a ha` instead."
    (since 

Depends on / 依赖: Complex.isometry_ofReal.isClosedEmbedding, Complex.reCLM, IsSelfAdjoint, IsStarNormal, SpectrumRestricts, SpectrumRestricts.cfc, isClosedEmbedding, isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts, isometry_ofReal
-/
instance IsSelfAdjoint.instContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus Real A IsSelfAdjoint :=
  SpectrumRestricts.cfc (q := IsStarNormal) (p := IsSelfAdjoint) Complex.reCLM
    Complex.isometry_ofReal.isClosedEmbedding (.zero _)
    (fun _ => isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts)

@[deprecated "Use `ContinuousFunctionalCalculus.spectrum_nonempty a ha` instead."
    (since := "2026-03-08")]
/--
lemma `IsSelfAdjoint.spectrum_nonempty` / 引理 `IsSelfAdjoint.spectrum_nonempty`

English:
lemma IsSelfAdjoint.spectrum_nonempty
  statement: {A : Type*} [Ring A] [StarRing A]
  proof: ContinuousFunctionalCalculus.spectrum_nonempty a ha

中文:
引理 IsSelfAdjoint.spectrum_nonempty
  结论: {A : 类型} [环 A] [对合环 A]
  证明: ContinuousFunctionalCalculus.spectrum_nonempty a ha

Depends on / 依赖: ContinuousFunctionalCalculus, ContinuousFunctionalCalculus.spectrum_nonempty, spectrum_nonempty
-/
lemma IsSelfAdjoint.spectrum_nonempty {A : Type*} [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra Real A] [ContinuousFunctionalCalculus Real A IsSelfAdjoint]
    [Nontrivial A] {a : A} (ha : IsSelfAdjoint a) : (σ Real a).Nonempty :=
  ContinuousFunctionalCalculus.spectrum_nonempty a ha

end SelfAdjointUnital

/-!
### Continuous functional calculus for nonnegative elements
-/

section Nonneg

/--
lemma `CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts` / 引理 `CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts`

English:
lemma CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
  statement: {A : Type*} [NonUnitalRing A]
  proof: by
  use cfcₙ (√·) a, cfcₙ_predicate (√·) a
  constructor
  · simpa only [QuasispectrumRestricts.nnreal_iff, cfcₙ_map_quasispectrum (√·) a,
      Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        using fun x _ => Real.sqrt_nonneg x
  · rw [← cfcₙ_mul ..]
    nth_rw 2 [← 

中文:
引理 CFC.存在_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
  结论: {A : 类型} [非幺环 A]
  证明: by
  use cfcₙ (√·) a, cfcₙ_predicate (√·) a
  constructor
  · simpa only [QuasispectrumRestricts.nnreal_iff, cfcₙ_map_quasispectrum (√·) a,
      Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        using fun x _ => Real.sqrt_nonneg x
  · rw [← cfcₙ_mul ..]
    nth_rw 2 [← 

Depends on / 依赖: QuasispectrumRestricts, QuasispectrumRestricts.nnreal_iff, Real.sq_sqrt, Real.sqrt_nonneg, Set.mem_image, and_imp, forall_exists_index, mem_image, nnreal_iff, nth_rw, sq_sqrt, sqrt_nonneg
-/
lemma CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts {A : Type*} [NonUnitalRing A]
    [StarRing A] [TopologicalSpace A] [Module Real A] [IsScalarTower Real A A] [SMulCommClass Real A A]
    [NonUnitalContinuousFunctionalCalculus Real A IsSelfAdjoint]
    {a : A} (ha₁ : IsSelfAdjoint a) (ha₂ : QuasispectrumRestricts a ContinuousMap.realToNNReal) :
    exists x : A, IsSelfAdjoint x ∧ QuasispectrumRestricts x ContinuousMap.realToNNReal ∧ x * x = a := by
  use cfcₙ (√·) a, cfcₙ_predicate (√·) a
  constructor
  · simpa only [QuasispectrumRestricts.nnreal_iff, cfcₙ_map_quasispectrum (√·) a,
      Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        using fun x _ => Real.sqrt_nonneg x
  · rw [← cfcₙ_mul ..]
    nth_rw 2 [← cfcₙ_id Real a]
    apply cfcₙ_congr fun x hx => ?_
    rw [QuasispectrumRestricts.nnreal_iff] at ha₂
    apply ha₂ x at hx
    simp [← sq, Real.sq_sqrt hx]

variable {A : Type*} [NonUnitalRing A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
variable [TopologicalSpace A] [Module Real A] [IsScalarTower Real A A] [SMulCommClass Real A A]
variable [NonUnitalContinuousFunctionalCalculus Real A IsSelfAdjoint]
variable [NonnegSpectrumClass Real A]

/--
lemma `nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts` / 引理 `nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts`

English:
lemma nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts
  given: {a : A}
  proof: by
  refine ⟨fun ha => ⟨.of_nonneg ha, .nnreal_of_nonneg ha⟩, ?_⟩
  rintro ⟨ha₁, ha₂⟩
  obtain ⟨x, hx, -, rfl⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts ha₁ ha₂
  simpa [sq, hx.star_eq] using star_mul_self_nonneg x

中文:
引理 nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts
  条件: {a : A}
  证明: by
  refine ⟨fun ha => ⟨.of_nonneg ha, .nnreal_of_nonneg ha⟩, ?_⟩
  rintro ⟨ha₁, ha₂⟩
  obtain ⟨x, hx, -, rfl⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts ha₁ ha₂
  simpa [sq, hx.star_eq] using star_mul_self_nonneg x

Depends on / 依赖: CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts, exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts, hx.star_eq, nnreal_of_nonneg, of_nonneg, star_eq, star_mul_self_nonneg
-/
lemma nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts {a : A} :
    0 <= a ↔ IsSelfAdjoint a ∧ QuasispectrumRestricts a ContinuousMap.realToNNReal := by
  refine ⟨fun ha => ⟨.of_nonneg ha, .nnreal_of_nonneg ha⟩, ?_⟩
  rintro ⟨ha₁, ha₂⟩
  obtain ⟨x, hx, -, rfl⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts ha₁ ha₂
  simpa [sq, hx.star_eq] using star_mul_self_nonneg x

open NNReal in
/--
Instance `Nonneg.instNonUnitalContinuousFunctionalCalculus` / 实例 `Nonneg.instNonUnitalContinuousFunctionalCalculus`

English:
instance Nonneg.instNonUnitalContinuousFunctionalCalculus
  signature: :
  body: QuasispectrumRestricts.cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    NNReal.isClosedEmbedding_coe le_rfl
    (fun _ => nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts)

中文:
实例 Nonneg.instNonUnitalContinuousFunctionalCalculus
  签名: :
  定义体: QuasispectrumRestricts.cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    NNReal.isClosedEmbedding_coe le_rfl
    (fun _ => nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts)

Depends on / 依赖: ContinuousMap, ContinuousMap.realToNNReal, IsSelfAdjoint, NNReal, NNReal.isClosedEmbedding_coe, QuasispectrumRestricts, QuasispectrumRestricts.cfc, isClosedEmbedding_coe, le_rfl, nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts, realToNNReal
-/
instance Nonneg.instNonUnitalContinuousFunctionalCalculus :
    NonUnitalContinuousFunctionalCalculus Real>=0 A (0 <= ·) :=
  QuasispectrumRestricts.cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    NNReal.isClosedEmbedding_coe le_rfl
    (fun _ => nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts)

/--
lemma `Commute.mul_nonneg` / 引理 `Commute.mul_nonneg`

English:
lemma Commute.mul_nonneg
  given: {a b : A} (ha : 0 <= a) (hb : 0 <= b) (h : Commute a b)
  proof: by
  rw [nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts]
.mp h, ?_⟩ refine ⟨ha.isSelfAdjoint.commute_iff hb.isSelfAdjoint
  rw [nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts] at hb
  obtain ⟨x, hx₁, hx₂, rfl⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hb.1 hb.2
  have h

中文:
引理 Commute.mul_nonneg
  条件: {a b : A} (ha : 0 <= a) (hb : 0 <= b) (h : Commute a b)
  证明: by
  rw [nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts]
.mp h, ?_⟩ refine ⟨ha.isSelfAdjoint.commute_iff hb.isSelfAdjoint
  rw [nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts] at hb
  obtain ⟨x, hx₁, hx₂, rfl⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hb.1 hb.2
  have h

Depends on / 依赖: CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts, commute_iff, exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts, ha.isSelfAdjoint.commute_iff, hb.isSelfAdjoint, isSelfAdjoint, mul_assoc, mul_comm, nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts, nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts.mpr, quasispectrum, quasispectrum.mul_comm, quasispectrumRestricts_iff
-/
lemma Commute.mul_nonneg {a b : A} (ha : 0 <= a) (hb : 0 <= b) (h : Commute a b) :
    0 <= a * b := by
  rw [nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts]
.mp h, ?_⟩ refine ⟨ha.isSelfAdjoint.commute_iff hb.isSelfAdjoint
  rw [nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts] at hb
  obtain ⟨x, hx₁, hx₂, rfl⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hb.1 hb.2
  have hx := nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts.mpr ⟨hx₁, hx₂⟩
  rw [← mul_assoc]; rw [quasispectrumRestricts_iff]; rw [quasispectrum.mul_comm]; rw [← quasispectrumRestricts_iff]; rw [← mul_assoc]
exact QuasispectrumRestricts.nnreal_of_nonneg conjugate_nonneg_of_nonneg ha hx

/--
lemma `commute_iff_mul_nonneg` / 引理 `commute_iff_mul_nonneg`

English:
lemma commute_iff_mul_nonneg
  given: {a b : A} (ha : 0 <= a) (hb : 0 <= b)
  proof: ⟨Commute.mul_nonneg ha hb,
.mpr h.isSelfAdjoint⟩ fun h => ha.isSelfAdjoint.commute_iff hb.isSelfAdjoint

中文:
引理 commute_iff_mul_nonneg
  条件: {a b : A} (ha : 0 <= a) (hb : 0 <= b)
  证明: ⟨Commute.mul_nonneg ha hb,
.mpr h.isSelfAdjoint⟩ fun h => ha.isSelfAdjoint.commute_iff hb.isSelfAdjoint

Depends on / 依赖: Commute, Commute.mul_nonneg, commute_iff, h.isSelfAdjoint, ha.isSelfAdjoint.commute_iff, hb.isSelfAdjoint, isSelfAdjoint, mul_nonneg
-/
lemma commute_iff_mul_nonneg {a b : A} (ha : 0 <= a) (hb : 0 <= b) :
    Commute a b ↔ 0 <= a * b :=
  ⟨Commute.mul_nonneg ha hb,
.mpr h.isSelfAdjoint⟩ fun h => ha.isSelfAdjoint.commute_iff hb.isSelfAdjoint

open NNReal in
@[deprecated "Use `ContinuousFunctionalCalculus.spectrum_nonempty a ha` instead"
  (since := "2026-03-08")]
/--
lemma `NNReal.spectrum_nonempty` / 引理 `NNReal.spectrum_nonempty`

English:
lemma NNReal.spectrum_nonempty
  statement: {A : Type*} [Ring A] [StarRing A] [LE A]
  proof: ContinuousFunctionalCalculus.spectrum_nonempty a ha

中文:
引理 非负实数.spectrum_nonempty
  结论: {A : 类型} [环 A] [对合环 A] [LE A]
  证明: ContinuousFunctionalCalculus.spectrum_nonempty a ha

Depends on / 依赖: ContinuousFunctionalCalculus, ContinuousFunctionalCalculus.spectrum_nonempty, spectrum_nonempty
-/
lemma NNReal.spectrum_nonempty {A : Type*} [Ring A] [StarRing A] [LE A]
    [TopologicalSpace A] [Algebra Real>=0 A] [ContinuousFunctionalCalculus Real>=0 A (0 <= ·)]
    [Nontrivial A] {a : A} (ha : 0 <= a) : (spectrum Real>=0 a).Nonempty :=
  ContinuousFunctionalCalculus.spectrum_nonempty a ha

end Nonneg

section Nonneg

variable {A : Type*} [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A] [TopologicalSpace A]
variable [Algebra Real A] [ContinuousFunctionalCalculus Real A IsSelfAdjoint]
variable [NonnegSpectrumClass Real A]

open NNReal in
/--
Instance `Nonneg.instContinuousFunctionalCalculus` / 实例 `Nonneg.instContinuousFunctionalCalculus`

English:
instance Nonneg.instContinuousFunctionalCalculus
  signature: :
  body: SpectrumRestricts.cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    NNReal.isClosedEmbedding_coe le_rfl
    (fun _ => nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts)

中文:
实例 Nonneg.instContinuousFunctionalCalculus
  签名: :
  定义体: SpectrumRestricts.cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    NNReal.isClosedEmbedding_coe le_rfl
    (fun _ => nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts)

Depends on / 依赖: ContinuousMap, ContinuousMap.realToNNReal, IsSelfAdjoint, NNReal, NNReal.isClosedEmbedding_coe, SpectrumRestricts, SpectrumRestricts.cfc, isClosedEmbedding_coe, le_rfl, nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts, realToNNReal
-/
instance Nonneg.instContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus Real>=0 A (0 <= ·) :=
  SpectrumRestricts.cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    NNReal.isClosedEmbedding_coe le_rfl
    (fun _ => nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts)

/--
theorem `IsStrictlyPositive.commute_iff` / 定理 `IsStrictlyPositive.commute_iff`

English:
theorem IsStrictlyPositive.commute_iff
  statement: {a b : A} (ha : IsStrictlyPositive a)
  proof: by
  rw [commute_iff_mul_nonneg ha.nonneg hb.nonneg]
.isStrictlyPositive h, fun h => h.nonneg⟩ exact ⟨fun h => ha.isUnit.mul hb.isUnit

中文:
定理 IsStrictlyPositive.commute_iff
  结论: {a b : A} (ha : IsStrictlyPositive a)
  证明: by
  rw [commute_iff_mul_nonneg ha.nonneg hb.nonneg]
.isStrictlyPositive h, fun h => h.nonneg⟩ exact ⟨fun h => ha.isUnit.mul hb.isUnit

Depends on / 依赖: commute_iff_mul_nonneg, h.nonneg, ha.isUnit.mul, ha.nonneg, hb.isUnit, hb.nonneg, isStrictlyPositive, isUnit, nonneg
-/
theorem IsStrictlyPositive.commute_iff {a b : A} (ha : IsStrictlyPositive a)
    (hb : IsStrictlyPositive b) : Commute a b ↔ IsStrictlyPositive (a * b) := by
  rw [commute_iff_mul_nonneg ha.nonneg hb.nonneg]
.isStrictlyPositive h, fun h => h.nonneg⟩ exact ⟨fun h => ha.isUnit.mul hb.isUnit

end Nonneg

/-!
### The restriction of a continuous functional calculus is equal to the original one
-/
section RealEqComplex

variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [Algebra Complex A]
  [ContinuousFunctionalCalculus Complex A IsStarNormal] [T2Space A]

/--
lemma `cfcHom_real_eq_restrict` / 引理 `cfcHom_real_eq_restrict`

English:
lemma cfcHom_real_eq_restrict
  given: {a : A} (ha : IsSelfAdjoint a)
  proof: ha.spectrumRestricts.cfcHom_eq_restrict _ ha ha.isStarNormal

中文:
引理 cfcHom_real_eq_restrict
  条件: {a : A} (ha : IsSelfAdjoint a)
  证明: ha.spectrumRestricts.cfcHom_eq_restrict _ ha ha.isStarNormal
-/
lemma cfcHom_real_eq_restrict {a : A} (ha : IsSelfAdjoint a) :
    cfcHom ha =
      ha.spectrumRestricts.starAlgHom (R := Real) (S := Complex)
        (cfcHom ha.isStarNormal) (f := Complex.reCLM) :=
  ha.spectrumRestricts.cfcHom_eq_restrict _ ha ha.isStarNormal

/--
lemma `cfc_real_eq_complex` / 引理 `cfc_real_eq_complex`

English:
lemma cfc_real_eq_complex
  given: {a : A} (f : Real -> Real) (ha : IsSelfAdjoint a := by cfc_tac)
  proof: by
  exact ha.spectrumRestricts.cfc_eq_restrict (f := Complex.reCLM)
    Complex.isometry_ofReal.isClosedEmbedding ha ha.isStarNormal f

中文:
引理 cfc_real_eq_complex
  条件: {a : A} (f : 实数 -> 实数) (ha : IsSelfAdjoint a := by cfc_tac)
  证明: by
  exact ha.spectrumRestricts.cfc_eq_restrict (f := Complex.reCLM)
    Complex.isometry_ofReal.isClosedEmbedding ha ha.isStarNormal f

Depends on / 依赖: Complex.isometry_ofReal.isClosedEmbedding, Complex.reCLM, cfc_eq_restrict, cfc_tac, ha.isStarNormal, ha.spectrumRestricts.cfc_eq_restrict, isClosedEmbedding, isStarNormal, isometry_ofReal, spectrumRestricts, x.re
-/
lemma cfc_real_eq_complex {a : A} (f : Real -> Real) (ha : IsSelfAdjoint a := by cfc_tac) :
    cfc f a = cfc (fun x => f x.re : Complex -> Complex) a := by
  exact ha.spectrumRestricts.cfc_eq_restrict (f := Complex.reCLM)
    Complex.isometry_ofReal.isClosedEmbedding ha ha.isStarNormal f

/--
lemma `cfc_complex_eq_real` / 引理 `cfc_complex_eq_real`

English:
lemma cfc_complex_eq_real
  statement: {f : Complex -> Complex} (a : A) (hf_real : forall x in spectrum Complex a, star (f x) = f x)
  proof: by
  rw [cfc_real_eq_complex ..]
  refine cfc_congr fun x hx => ?_
  simp_rw [RCLike.star_def, RCLike.conj_eq_iff_re, RCLike.re_eq_complex_re,
    RCLike.ofReal_eq_complex_ofReal] at hf_real
  rw [← SpectrumRestricts.real_iff.mp ha.spectrumRestricts _ hx]; rw [hf_real _ hx]

中文:
引理 cfc_complex_eq_real
  结论: {f : 复形 -> 复形} (a : A) (hf_real : 对任意 x in spectrum 复形 a, star (f x) = f x)
  证明: by
  rw [cfc_real_eq_complex ..]
  refine cfc_congr fun x hx => ?_
  simp_rw [RCLike.star_def, RCLike.conj_eq_iff_re, RCLike.re_eq_complex_re,
    RCLike.ofReal_eq_complex_ofReal] at hf_real
  rw [← SpectrumRestricts.real_iff.mp ha.spectrumRestricts _ hx]; rw [hf_real _ hx]

Depends on / 依赖: RCLike, RCLike.conj_eq_iff_re, RCLike.ofReal_eq_complex_ofReal, RCLike.re_eq_complex_re, RCLike.star_def, SpectrumRestricts, SpectrumRestricts.real_iff.mp, cfc_congr, cfc_real_eq_complex, cfc_tac, conj_eq_iff_re, ha.spectrumRestricts, hf_real, ofReal_eq_complex_ofReal, re_eq_complex_re, real_iff, simp_rw, spectrumRestricts, star_def
-/
lemma cfc_complex_eq_real {f : Complex -> Complex} (a : A) (hf_real : forall x in spectrum Complex a, star (f x) = f x)
    (ha : IsSelfAdjoint a := by cfc_tac) :
    cfc f a = cfc (fun x : Real => (f x).re) a := by
  rw [cfc_real_eq_complex ..]
  refine cfc_congr fun x hx => ?_
  simp_rw [RCLike.star_def, RCLike.conj_eq_iff_re, RCLike.re_eq_complex_re,
    RCLike.ofReal_eq_complex_ofReal] at hf_real
  rw [← SpectrumRestricts.real_iff.mp ha.spectrumRestricts _ hx]; rw [hf_real _ hx]

end RealEqComplex

section RealEqComplexNonUnital

variable {A : Type*} [TopologicalSpace A] [NonUnitalRing A] [StarRing A] [Module Complex A]
  [IsScalarTower Complex A A] [SMulCommClass Complex A A] [T2Space A]
  [NonUnitalContinuousFunctionalCalculus Complex A IsStarNormal]

/--
lemma `cfcₙHom_real_eq_restrict` / 引理 `cfcₙHom_real_eq_restrict`

English:
lemma cfcₙHom_real_eq_restrict
  given: {a : A} (ha : IsSelfAdjoint a)
  proof: ha.quasispectrumRestricts.cfcₙHom_eq_restrict _ ha ha.isStarNormal

中文:
引理 cfcₙHom_real_eq_restrict
  条件: {a : A} (ha : IsSelfAdjoint a)
  证明: ha.quasispectrumRestricts.cfcₙHom_eq_restrict _ ha ha.isStarNormal

Depends on / 依赖: Complex.reCLM
-/
lemma cfcₙHom_real_eq_restrict {a : A} (ha : IsSelfAdjoint a) :
    cfcₙHom ha = ha.quasispectrumRestricts.nonUnitalStarAlgHom (cfcₙHom ha.isStarNormal)
      (R := Real) (S := Complex) (f := Complex.reCLM) :=
  ha.quasispectrumRestricts.cfcₙHom_eq_restrict _ ha ha.isStarNormal

/--
lemma `cfcₙ_real_eq_complex` / 引理 `cfcₙ_real_eq_complex`

English:
lemma cfcₙ_real_eq_complex
  given: {a : A} (f : Real -> Real) (ha : IsSelfAdjoint a := by cfc_tac)
  proof: by
  exact ha.quasispectrumRestricts.cfcₙ_eq_restrict (f := Complex.reCLM)
    Complex.isometry_ofReal.isClosedEmbedding ha ha.isStarNormal f

中文:
引理 cfcₙ_real_eq_complex
  条件: {a : A} (f : 实数 -> 实数) (ha : IsSelfAdjoint a := by cfc_tac)
  证明: by
  exact ha.quasispectrumRestricts.cfcₙ_eq_restrict (f := Complex.reCLM)
    Complex.isometry_ofReal.isClosedEmbedding ha ha.isStarNormal f

Depends on / 依赖: Complex.isometry_ofReal.isClosedEmbedding, Complex.reCLM, cfc_tac, ha.isStarNormal, ha.quasispectrumRestricts.cfc, isClosedEmbedding, isStarNormal, isometry_ofReal, quasispectrumRestricts, x.re
-/
lemma cfcₙ_real_eq_complex {a : A} (f : Real -> Real) (ha : IsSelfAdjoint a := by cfc_tac) :
    cfcₙ f a = cfcₙ (fun x => f x.re : Complex -> Complex) a := by
  exact ha.quasispectrumRestricts.cfcₙ_eq_restrict (f := Complex.reCLM)
    Complex.isometry_ofReal.isClosedEmbedding ha ha.isStarNormal f

/--
lemma `cfcₙ_complex_eq_real` / 引理 `cfcₙ_complex_eq_real`

English:
lemma cfcₙ_complex_eq_real
  statement: {f : Complex -> Complex} (a : A) (hf_real : forall x in σₙ Complex a, star (f x) = f x)
  proof: by
  rw [cfcₙ_real_eq_complex ..]
  refine cfcₙ_congr fun x hx => ?_
  simp_rw [RCLike.star_def, RCLike.conj_eq_iff_re, RCLike.re_eq_complex_re,
    RCLike.ofReal_eq_complex_ofReal] at hf_real
  rw [← QuasispectrumRestricts.real_iff.mp ha.quasispectrumRestricts _ hx]; rw [hf_real _ hx]

中文:
引理 cfcₙ_complex_eq_real
  结论: {f : 复形 -> 复形} (a : A) (hf_real : 对任意 x in σₙ 复形 a, star (f x) = f x)
  证明: by
  rw [cfcₙ_real_eq_complex ..]
  refine cfcₙ_congr fun x hx => ?_
  simp_rw [RCLike.star_def, RCLike.conj_eq_iff_re, RCLike.re_eq_complex_re,
    RCLike.ofReal_eq_complex_ofReal] at hf_real
  rw [← QuasispectrumRestricts.real_iff.mp ha.quasispectrumRestricts _ hx]; rw [hf_real _ hx]

Depends on / 依赖: QuasispectrumRestricts, QuasispectrumRestricts.real_iff.mp, RCLike, RCLike.conj_eq_iff_re, RCLike.ofReal_eq_complex_ofReal, RCLike.re_eq_complex_re, RCLike.star_def, cfc_tac, conj_eq_iff_re, ha.quasispectrumRestricts, hf_real, ofReal_eq_complex_ofReal, quasispectrumRestricts, re_eq_complex_re, real_iff, simp_rw, star_def
-/
lemma cfcₙ_complex_eq_real {f : Complex -> Complex} (a : A) (hf_real : forall x in σₙ Complex a, star (f x) = f x)
    (ha : IsSelfAdjoint a := by cfc_tac) :
    cfcₙ f a = cfcₙ (fun x : Real => (f x).re) a := by
  rw [cfcₙ_real_eq_complex ..]
  refine cfcₙ_congr fun x hx => ?_
  simp_rw [RCLike.star_def, RCLike.conj_eq_iff_re, RCLike.re_eq_complex_re,
    RCLike.ofReal_eq_complex_ofReal] at hf_real
  rw [← QuasispectrumRestricts.real_iff.mp ha.quasispectrumRestricts _ hx]; rw [hf_real _ hx]

end RealEqComplexNonUnital

section NNRealEqReal

open NNReal

variable {A : Type*} [TopologicalSpace A] [Ring A] [PartialOrder A] [StarRing A]
  [StarOrderedRing A] [Algebra Real A] [IsSemitopologicalRing A] [T2Space A]
  [ContinuousFunctionalCalculus Real A IsSelfAdjoint]
  [NonnegSpectrumClass Real A]

/--
lemma `cfcHom_nnreal_eq_restrict` / 引理 `cfcHom_nnreal_eq_restrict`

English:
lemma cfcHom_nnreal_eq_restrict
  given: {a : A} (ha : 0 <= a)
  proof: by
  apply (SpectrumRestricts.nnreal_of_nonneg ha).cfcHom_eq_restrict _

中文:
引理 cfcHom_nnreal_eq_restrict
  条件: {a : A} (ha : 0 <= a)
  证明: by
  apply (SpectrumRestricts.nnreal_of_nonneg ha).cfcHom_eq_restrict _

Depends on / 依赖: SpectrumRestricts, SpectrumRestricts.nnreal_of_nonneg, cfcHom_eq_restrict, nnreal_of_nonneg
-/
lemma cfcHom_nnreal_eq_restrict {a : A} (ha : 0 <= a) :
    cfcHom ha = (SpectrumRestricts.nnreal_of_nonneg ha).starAlgHom
      (cfcHom (IsSelfAdjoint.of_nonneg ha)) := by
  apply (SpectrumRestricts.nnreal_of_nonneg ha).cfcHom_eq_restrict _

/--
lemma `cfc_nnreal_eq_real` / 引理 `cfc_nnreal_eq_real`

English:
lemma cfc_nnreal_eq_real
  given: (f : Real>=0 -> Real>=0) (a : A) (ha : 0 <= a := by cfc_tac)
  proof: by
  apply (SpectrumRestricts.nnreal_of_nonneg ha).cfc_eq_restrict _
    NNReal.isClosedEmbedding_coe ha (.of_nonneg ha)

中文:
引理 cfc_nnreal_eq_real
  条件: (f : 实数>=0 -> 实数>=0) (a : A) (ha : 0 <= a := by cfc_tac)
  证明: by
  apply (SpectrumRestricts.nnreal_of_nonneg ha).cfc_eq_restrict _
    NNReal.isClosedEmbedding_coe ha (.of_nonneg ha)

Depends on / 依赖: NNReal, NNReal.isClosedEmbedding_coe, SpectrumRestricts, SpectrumRestricts.nnreal_of_nonneg, cfc_eq_restrict, cfc_tac, isClosedEmbedding_coe, nnreal_of_nonneg, of_nonneg, toNNReal, x.toNNReal
-/
lemma cfc_nnreal_eq_real (f : Real>=0 -> Real>=0) (a : A) (ha : 0 <= a := by cfc_tac) :
    cfc f a = cfc (fun x => f x.toNNReal : Real -> Real) a := by
  apply (SpectrumRestricts.nnreal_of_nonneg ha).cfc_eq_restrict _
    NNReal.isClosedEmbedding_coe ha (.of_nonneg ha)

/--
lemma `cfc_real_eq_nnreal` / 引理 `cfc_real_eq_nnreal`

English:
lemma cfc_real_eq_nnreal
  statement: {f : Real -> Real} (a : A) (hf_nonneg : forall x in spectrum Real a, 0 <= f x)
  proof: by
  rw [cfc_nnreal_eq_real ..]
  refine cfc_congr fun x hx => ?_
  rw [x.coe_toNNReal (spectrum_nonneg_of_nonneg ha hx)]; rw [(f x).coe_toNNReal (hf_nonneg x hx)]

中文:
引理 cfc_real_eq_nnreal
  结论: {f : 实数 -> 实数} (a : A) (hf_nonneg : 对任意 x in spectrum 实数 a, 0 <= f x)
  证明: by
  rw [cfc_nnreal_eq_real ..]
  refine cfc_congr fun x hx => ?_
  rw [x.coe_toNNReal (spectrum_nonneg_of_nonneg ha hx)]; rw [(f x).coe_toNNReal (hf_nonneg x hx)]

Depends on / 依赖: cfc_congr, cfc_nnreal_eq_real, cfc_tac, coe_toNNReal, hf_nonneg, spectrum_nonneg_of_nonneg, toNNReal, x.coe_toNNReal
-/
lemma cfc_real_eq_nnreal {f : Real -> Real} (a : A) (hf_nonneg : forall x in spectrum Real a, 0 <= f x)
    (ha : 0 <= a := by cfc_tac) : cfc f a = cfc (fun x : Real>=0 => (f x).toNNReal) a := by
  rw [cfc_nnreal_eq_real ..]
  refine cfc_congr fun x hx => ?_
  rw [x.coe_toNNReal (spectrum_nonneg_of_nonneg ha hx)]; rw [(f x).coe_toNNReal (hf_nonneg x hx)]

end NNRealEqReal

section NNRealEqRealNonUnital

open NNReal

variable {A : Type*} [TopologicalSpace A] [NonUnitalRing A] [PartialOrder A] [StarRing A]
  [StarOrderedRing A] [Module Real A] [IsSemitopologicalRing A] [IsScalarTower Real A A]
  [SMulCommClass Real A A] [T2Space A] [NonUnitalContinuousFunctionalCalculus Real A IsSelfAdjoint]
  [NonnegSpectrumClass Real A]

/--
lemma `cfcₙHom_nnreal_eq_restrict` / 引理 `cfcₙHom_nnreal_eq_restrict`

English:
lemma cfcₙHom_nnreal_eq_restrict
  given: {a : A} (ha : 0 <= a)
  proof: by
  apply (QuasispectrumRestricts.nnreal_of_nonneg ha).cfcₙHom_eq_restrict _

中文:
引理 cfcₙHom_nnreal_eq_restrict
  条件: {a : A} (ha : 0 <= a)
  证明: by
  apply (QuasispectrumRestricts.nnreal_of_nonneg ha).cfcₙHom_eq_restrict _

Depends on / 依赖: QuasispectrumRestricts, QuasispectrumRestricts.nnreal_of_nonneg, nnreal_of_nonneg
-/
lemma cfcₙHom_nnreal_eq_restrict {a : A} (ha : 0 <= a) :
    cfcₙHom ha = (QuasispectrumRestricts.nnreal_of_nonneg ha).nonUnitalStarAlgHom
      (cfcₙHom (IsSelfAdjoint.of_nonneg ha)) := by
  apply (QuasispectrumRestricts.nnreal_of_nonneg ha).cfcₙHom_eq_restrict _

/--
lemma `cfcₙ_nnreal_eq_real` / 引理 `cfcₙ_nnreal_eq_real`

English:
lemma cfcₙ_nnreal_eq_real
  given: (f : Real>=0 -> Real>=0) (a : A) (ha : 0 <= a := by cfc_tac)
  proof: by
  apply (QuasispectrumRestricts.nnreal_of_nonneg ha).cfcₙ_eq_restrict _
    NNReal.isClosedEmbedding_coe ha (.of_nonneg ha)

中文:
引理 cfcₙ_nnreal_eq_real
  条件: (f : 实数>=0 -> 实数>=0) (a : A) (ha : 0 <= a := by cfc_tac)
  证明: by
  apply (QuasispectrumRestricts.nnreal_of_nonneg ha).cfcₙ_eq_restrict _
    NNReal.isClosedEmbedding_coe ha (.of_nonneg ha)

Depends on / 依赖: NNReal, NNReal.isClosedEmbedding_coe, QuasispectrumRestricts, QuasispectrumRestricts.nnreal_of_nonneg, cfc_tac, isClosedEmbedding_coe, nnreal_of_nonneg, of_nonneg, toNNReal, x.toNNReal
-/
lemma cfcₙ_nnreal_eq_real (f : Real>=0 -> Real>=0) (a : A) (ha : 0 <= a := by cfc_tac) :
    cfcₙ f a = cfcₙ (fun x => f x.toNNReal : Real -> Real) a := by
  apply (QuasispectrumRestricts.nnreal_of_nonneg ha).cfcₙ_eq_restrict _
    NNReal.isClosedEmbedding_coe ha (.of_nonneg ha)

/--
lemma `cfcₙ_real_eq_nnreal` / 引理 `cfcₙ_real_eq_nnreal`

English:
lemma cfcₙ_real_eq_nnreal
  statement: {f : Real -> Real} (a : A) (hf_nonneg : forall x in σₙ Real a, 0 <= f x)
  proof: by
  rw [cfcₙ_nnreal_eq_real ..]
  refine cfcₙ_congr fun x hx => ?_
  rw [x.coe_toNNReal (quasispectrum_nonneg_of_nonneg _ ha _ hx)]; rw [(f x).coe_toNNReal (hf_nonneg x hx)]

中文:
引理 cfcₙ_real_eq_nnreal
  结论: {f : 实数 -> 实数} (a : A) (hf_nonneg : 对任意 x in σₙ 实数 a, 0 <= f x)
  证明: by
  rw [cfcₙ_nnreal_eq_real ..]
  refine cfcₙ_congr fun x hx => ?_
  rw [x.coe_toNNReal (quasispectrum_nonneg_of_nonneg _ ha _ hx)]; rw [(f x).coe_toNNReal (hf_nonneg x hx)]

Depends on / 依赖: cfc_tac, coe_toNNReal, hf_nonneg, quasispectrum_nonneg_of_nonneg, toNNReal, x.coe_toNNReal
-/
lemma cfcₙ_real_eq_nnreal {f : Real -> Real} (a : A) (hf_nonneg : forall x in σₙ Real a, 0 <= f x)
    (ha : 0 <= a := by cfc_tac) : cfcₙ f a = cfcₙ (fun x : Real>=0 => (f x).toNNReal) a := by
  rw [cfcₙ_nnreal_eq_real ..]
  refine cfcₙ_congr fun x hx => ?_
  rw [x.coe_toNNReal (quasispectrum_nonneg_of_nonneg _ ha _ hx)]; rw [(f x).coe_toNNReal (hf_nonneg x hx)]

end NNRealEqRealNonUnital

end
