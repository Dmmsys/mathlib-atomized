/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.MeasureTheory.SpecificCodomains.ContinuousMapZero
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrals and the continuous functional calculus

This file gives results about integrals of the form `∫ x, cfc (f x) a`. Most notably, we show
that the integral commutes with the continuous functional calculus under appropriate conditions.

## Main declarations

+ `cfc_setIntegral` (resp. `cfc_integral`): given a function `f : X → 𝕜 → 𝕜`, we have that
  `cfc (fun r => ∫ x in s, f x r ∂μ) a = ∫ x in s, cfc (f x) a ∂μ`
  under appropriate conditions (resp. with `s = univ`)
+ `cfcₙ_setIntegral`, `cfcₙ_integral`: the same for the non-unital continuous functional calculus
+ `integrableOn_cfc`, `integrableOn_cfcₙ`, `integrable_cfc`, `integrable_cfcₙ`:
  functions of the form `fun x => cfc (f x) a` are integrable.

## Implementation Notes

The lemmas mentioned above are stated under much stricter hypotheses than necessary
(typically, simultaneous continuity of `f` in the parameter and the spectrum element).
They all come with primed version which only assume what's needed, and may be used together
with the API developed in `Mathlib.MeasureTheory.SpecificCodomains.ContinuousMap`.

## TODO

+ Lift this to the case where the CFC is over `ℝ≥0`
+ Use this to prove operator monotonicity and concavity/convexity of `rpow` and `log`
-/

public section

open MeasureTheory Topology
open scoped ContinuousMapZero

section unital

open ContinuousMap

variable {X : Type*} {𝕜 : Type*} {A : Type*} {p : A -> Prop} [RCLike 𝕜]
  [MeasurableSpace X] {μ : Measure X}
  [NormedRing A] [StarRing A] [NormedAlgebra 𝕜 A]
  [ContinuousFunctionalCalculus 𝕜 A p]
  [CompleteSpace A]

/--
lemma `cfcL_integral` / 引理 `cfcL_integral`

English:
lemma cfcL_integral
  statement: [NormedSpace Real A] (a : A) (f : X -> C(spectrum 𝕜 a, 𝕜)) (hf₁ : Integrable f μ)
  proof: by
  rw [ContinuousLinearMap.integral_comp_comm _ hf₁]

中文:
引理 cfcL_integral
  结论: [NormedSpace 实数 A] (a : A) (f : X -> C(spectrum 𝕜 a, 𝕜)) (hf₁ : 整数egrable f μ)
  证明: by
  rw [ContinuousLinearMap.integral_comp_comm _ hf₁]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.integral_comp_comm, cfc_tac, integral_comp_comm
-/
lemma cfcL_integral [NormedSpace Real A] (a : A) (f : X -> C(spectrum 𝕜 a, 𝕜)) (hf₁ : Integrable f μ)
    (ha : p a := by cfc_tac) :
    ∫ x, cfcL (a := a) ha (f x) ∂μ = cfcL (a := a) ha (∫ x, f x ∂μ) := by
  rw [ContinuousLinearMap.integral_comp_comm _ hf₁]

/--
lemma `cfcL_integrable` / 引理 `cfcL_integrable`

English:
lemma cfcL_integrable
  statement: (a : A) (f : X -> C(spectrum 𝕜 a, 𝕜))
  proof: ContinuousLinearMap.integrable_comp _ hf₁

中文:
引理 cfcL_integrable
  结论: (a : A) (f : X -> C(spectrum 𝕜 a, 𝕜))
  证明: ContinuousLinearMap.integrable_comp _ hf₁

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.integrable_comp, Integrable, cfc_tac, integrable_comp
-/
lemma cfcL_integrable (a : A) (f : X -> C(spectrum 𝕜 a, 𝕜))
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    Integrable (fun x => cfcL (a := a) ha (f x)) μ :=
  ContinuousLinearMap.integrable_comp _ hf₁

/--
lemma `cfcHom_integral` / 引理 `cfcHom_integral`

English:
lemma cfcHom_integral
  statement: [NormedSpace Real A] (a : A) (f : X -> C(spectrum 𝕜 a, 𝕜))
  proof: cfcL_integral a f hf₁ ha

中文:
引理 cfcHom_integral
  结论: [NormedSpace 实数 A] (a : A) (f : X -> C(spectrum 𝕜 a, 𝕜))
  证明: cfcL_integral a f hf₁ ha

Depends on / 依赖: cfcHom, cfcL_integral, cfc_tac
-/
lemma cfcHom_integral [NormedSpace Real A] (a : A) (f : X -> C(spectrum 𝕜 a, 𝕜))
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    ∫ x, cfcHom (a := a) ha (f x) ∂μ = cfcHom (a := a) ha (∫ x, f x ∂μ) :=
  cfcL_integral a f hf₁ ha

/--
lemma `integrable_cfc'` / 引理 `integrable_cfc'`

English:
lemma integrable_cfc'
  statement: (f : X -> 𝕜 -> 𝕜) (a : A)
  proof: by
  conv in cfc _ _ => rw [cfc_eq_cfcL_mkD _ a]
  exact cfcL_integrable _ _ hf ha

中文:
引理 integrable_cfc'
  结论: (f : X -> 𝕜 -> 𝕜) (a : A)
  证明: by
  conv in cfc _ _ => rw [cfc_eq_cfcL_mkD _ a]
  exact cfcL_integrable _ _ hf ha

Depends on / 依赖: Integrable, cfcL_integrable, cfc_eq_cfcL_mkD, cfc_tac
-/
lemma integrable_cfc' (f : X -> 𝕜 -> 𝕜) (a : A)
    (hf : Integrable
      (fun x : X => mkD ((spectrum 𝕜 a).domRestrict (f x)) 0) μ)
    (ha : p a := by cfc_tac) :
    Integrable (fun x => cfc (f x) a) μ := by
  conv in cfc _ _ => rw [cfc_eq_cfcL_mkD _ a]
  exact cfcL_integrable _ _ hf ha

/--
lemma `integrableOn_cfc'` / 引理 `integrableOn_cfc'`

English:
lemma integrableOn_cfc'
  statement: {s : Set X} (f : X -> 𝕜 -> 𝕜) (a : A)
  proof: by
  exact integrable_cfc' _ _ hf ha

中文:
引理 integrableOn_cfc'
  结论: {s : Set X} (f : X -> 𝕜 -> 𝕜) (a : A)
  证明: by
  exact integrable_cfc' _ _ hf ha

Depends on / 依赖: IntegrableOn, cfc_tac, integrable_cfc
-/
lemma integrableOn_cfc' {s : Set X} (f : X -> 𝕜 -> 𝕜) (a : A)
    (hf : IntegrableOn
      (fun x : X => mkD ((spectrum 𝕜 a).domRestrict (f x)) 0) s μ)
    (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfc (f x) a) s μ := by
  exact integrable_cfc' _ _ hf ha

open Set Function in
/--
lemma `integrable_cfc` / 引理 `integrable_cfc`

English:
lemma integrable_cfc
  statement: [TopologicalSpace X] [OpensMeasurableSpace X] (f : X -> 𝕜 -> 𝕜)
  proof: by
  refine integrable_cfc' _ _ ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_mkD_restrict_of_uncurry _ _ hf
  · refine hasFiniteIntegral_mkD_restrict_of_bound f _ ?_ bound bound_int bound_ge
    exact .of_forall fun x =>
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz => ⟨Set.mem_univ 

中文:
引理 integrable_cfc
  结论: [TopologicalSpace X] [OpensMeasurableSpace X] (f : X -> 𝕜 -> 𝕜)
  证明: by
  refine integrable_cfc' _ _ ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_mkD_restrict_of_uncurry _ _ hf
  · refine hasFiniteIntegral_mkD_restrict_of_bound f _ ?_ bound bound_int bound_ge
    exact .of_forall fun x =>
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz => ⟨Set.mem_univ 

Depends on / 依赖: Continuous, Continuous.prodMk_right, Integrable, Set.mem_univ, aeStronglyMeasurable_mkD_restrict_of_uncurry, bound_ge, bound_int, cfc_tac, continuousOn, hasFiniteIntegral_mkD_restrict_of_bound, hf.comp, integrable_cfc, mem_univ, of_forall, prodMk_right
-/
lemma integrable_cfc [TopologicalSpace X] [OpensMeasurableSpace X] (f : X -> 𝕜 -> 𝕜)
    (bound : X -> Real) (a : A) [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (univ ×ˢ spectrum 𝕜 a))
    (bound_ge : forallᵐ x ∂μ, forall z in spectrum 𝕜 a, ‖f x z‖ <= bound x)
    (bound_int : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    Integrable (fun x => cfc (f x) a) μ := by
  refine integrable_cfc' _ _ ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_mkD_restrict_of_uncurry _ _ hf
  · refine hasFiniteIntegral_mkD_restrict_of_bound f _ ?_ bound bound_int bound_ge
    exact .of_forall fun x =>
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz => ⟨Set.mem_univ _, hz⟩

open Set Function in
/--
lemma `integrableOn_cfc` / 引理 `integrableOn_cfc`

English:
lemma integrableOn_cfc
  statement: [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
  proof: by
  refine integrableOn_cfc' _ _ ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry hs _ _ hf
  · refine hasFiniteIntegral_mkD_restrict_of_bound f _ ?_ bound bound_int bound_ge
    exact ae_restrict_of_forall_mem hs fun x hx =>
      hf.comp (Continuous.prodMk_right x).cont

中文:
引理 integrableOn_cfc
  结论: [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
  证明: by
  refine integrableOn_cfc' _ _ ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry hs _ _ hf
  · refine hasFiniteIntegral_mkD_restrict_of_bound f _ ?_ bound bound_int bound_ge
    exact ae_restrict_of_forall_mem hs fun x hx =>
      hf.comp (Continuous.prodMk_right x).cont

Depends on / 依赖: Continuous, Continuous.prodMk_right, IntegrableOn, aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry, ae_restrict_of_forall_mem, bound_ge, bound_int, cfc_tac, continuousOn, hasFiniteIntegral_mkD_restrict_of_bound, hf.comp, integrableOn_cfc, prodMk_right
-/
lemma integrableOn_cfc [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
    (hs : MeasurableSet s) (f : X -> 𝕜 -> 𝕜) (bound : X -> Real) (a : A)
    [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (s ×ˢ spectrum 𝕜 a))
    (bound_ge : forallᵐ x ∂(μ.restrict s), forall z in spectrum 𝕜 a, ‖f x z‖ <= bound x)
    (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfc (f x) a) s μ := by
  refine integrableOn_cfc' _ _ ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry hs _ _ hf
  · refine hasFiniteIntegral_mkD_restrict_of_bound f _ ?_ bound bound_int bound_ge
    exact ae_restrict_of_forall_mem hs fun x hx =>
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz => ⟨hx, hz⟩

open Set in
/--
lemma `cfc_integral'` / 引理 `cfc_integral'`

English:
lemma cfc_integral'
  statement: [NormedSpace Real A] (f : X -> 𝕜 -> 𝕜) (a : A)
  proof: by
  have key₁ (z : spectrum 𝕜 a) :
      ∫ x, f x z ∂μ = (∫ x, mkD ((spectrum 𝕜 a).domRestrict (f x)) 0 ∂μ) z := by
    rw [integral_apply hf₂]
    refine integral_congr_ae ?_
    filter_upwards [hf₁] with x cont_x
    rw [mkD_apply_of_continuousOn cont_x]
  have key₂ (z : spectrum 𝕜 a) :
      ∫ x

中文:
引理 cfc_integral'
  结论: [NormedSpace 实数 A] (f : X -> 𝕜 -> 𝕜) (a : A)
  证明: by
  have key₁ (z : spectrum 𝕜 a) :
      ∫ x, f x z ∂μ = (∫ x, mkD ((spectrum 𝕜 a).domRestrict (f x)) 0 ∂μ) z := by
    rw [integral_apply hf₂]
    refine integral_congr_ae ?_
    filter_upwards [hf₁] with x cont_x
    rw [mkD_apply_of_continuousOn cont_x]
  have key₂ (z : spectrum 𝕜 a) :
      ∫ x

Depends on / 依赖: cfc_tac, cont_x, continuousOn_iff_continuous_domRestrict, domRestrict, filter_upwards, integral_apply, integral_congr_ae, mkD_apply_of_continuousOn, spectrum
-/
lemma cfc_integral' [NormedSpace Real A] (f : X -> 𝕜 -> 𝕜) (a : A)
    (hf₁ : forallᵐ x ∂μ, ContinuousOn (f x) (spectrum 𝕜 a))
    (hf₂ : Integrable
      (fun x : X => mkD ((spectrum 𝕜 a).domRestrict (f x)) 0) μ)
    (ha : p a := by cfc_tac) :
    cfc (fun z => ∫ x, f x z ∂μ) a = ∫ x, cfc (f x) a ∂μ := by
  have key₁ (z : spectrum 𝕜 a) :
      ∫ x, f x z ∂μ = (∫ x, mkD ((spectrum 𝕜 a).domRestrict (f x)) 0 ∂μ) z := by
    rw [integral_apply hf₂]
    refine integral_congr_ae ?_
    filter_upwards [hf₁] with x cont_x
    rw [mkD_apply_of_continuousOn cont_x]
  have key₂ (z : spectrum 𝕜 a) :
      ∫ x, f x z ∂μ = mkD ((spectrum 𝕜 a).domRestrict (fun z => ∫ x, f x z ∂μ)) 0 z := by
    rw [mkD_apply_of_continuousOn]
    rw [continuousOn_iff_continuous_domRestrict]
.mpr ?_ refine continuous_congr key₁
    exact map_continuous (∫ x, mkD ((spectrum 𝕜 a).domRestrict (f x)) 0 ∂μ)
  simp_rw [cfc_eq_cfcL_mkD _ a, cfcL_integral a _ hf₂ ha]
  congr
  ext z
  rw [← key₁]; rw [key₂]

open Set in
/--
lemma `cfc_setIntegral'` / 引理 `cfc_setIntegral'`

English:
lemma cfc_setIntegral'
  statement: {s : Set X} [NormedSpace Real A] (f : X -> 𝕜 -> 𝕜) (a : A)
  proof: cfc_integral' _ _ hf₁ hf₂ ha

中文:
引理 cfc_setIntegral'
  结论: {s : Set X} [NormedSpace 实数 A] (f : X -> 𝕜 -> 𝕜) (a : A)
  证明: cfc_integral' _ _ hf₁ hf₂ ha

Depends on / 依赖: cfc_integral, cfc_tac
-/
lemma cfc_setIntegral' {s : Set X} [NormedSpace Real A] (f : X -> 𝕜 -> 𝕜) (a : A)
    (hf₁ : forallᵐ x ∂(μ.restrict s), ContinuousOn (f x) (spectrum 𝕜 a))
    (hf₂ : IntegrableOn
      (fun x : X => mkD ((spectrum 𝕜 a).domRestrict (f x)) 0) s μ)
    (ha : p a := by cfc_tac) :
    cfc (fun z => ∫ x in s, f x z ∂μ) a = ∫ x in s, cfc (f x) a ∂μ :=
  cfc_integral' _ _ hf₁ hf₂ ha

open Function Set in
/--
lemma `cfc_integral` / 引理 `cfc_integral`

English:
lemma cfc_integral
  statement: [NormedSpace Real A] [TopologicalSpace X] [OpensMeasurableSpace X]
  proof: by
  have : forallᵐ (x : X) ∂μ, ContinuousOn (f x) (spectrum 𝕜 a) := .of_forall fun x =>
    hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz => ⟨Set.mem_univ _, hz⟩
  refine cfc_integral' _ _ this ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_mkD_restrict_of_uncurry _ _ hf
  · exact hasFinite

中文:
引理 cfc_integral
  结论: [NormedSpace 实数 A] [TopologicalSpace X] [OpensMeasurableSpace X]
  证明: by
  have : forallᵐ (x : X) ∂μ, ContinuousOn (f x) (spectrum 𝕜 a) := .of_forall fun x =>
    hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz => ⟨Set.mem_univ _, hz⟩
  refine cfc_integral' _ _ this ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_mkD_restrict_of_uncurry _ _ hf
  · exact hasFinite

Depends on / 依赖: Continuous, Continuous.prodMk_right, ContinuousOn, Set.mem_univ, aeStronglyMeasurable_mkD_restrict_of_uncurry, bound_ge, bound_int, cfc_integral, cfc_tac, continuousOn, hasFiniteIntegral_mkD_restrict_of_bound, hf.comp, mem_univ, of_forall, prodMk_right, spectrum
-/
lemma cfc_integral [NormedSpace Real A] [TopologicalSpace X] [OpensMeasurableSpace X]
    (f : X -> 𝕜 -> 𝕜) (bound : X -> Real) (a : A) [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (univ ×ˢ spectrum 𝕜 a))
    (bound_ge : forallᵐ x ∂μ, forall z in spectrum 𝕜 a, ‖f x z‖ <= bound x)
    (bound_int : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    cfc (fun r => ∫ x, f x r ∂μ) a = ∫ x, cfc (f x) a ∂μ := by
  have : forallᵐ (x : X) ∂μ, ContinuousOn (f x) (spectrum 𝕜 a) := .of_forall fun x =>
    hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz => ⟨Set.mem_univ _, hz⟩
  refine cfc_integral' _ _ this ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_mkD_restrict_of_uncurry _ _ hf
  · exact hasFiniteIntegral_mkD_restrict_of_bound f _ this bound bound_int bound_ge

open Function Set in
/--
lemma `cfc_setIntegral` / 引理 `cfc_setIntegral`

English:
lemma cfc_setIntegral
  statement: [NormedSpace Real A] [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
  proof: by
  have : forallᵐ (x : X) ∂(μ.restrict s), ContinuousOn (f x) (spectrum 𝕜 a) :=
    ae_restrict_of_forall_mem hs fun x hx =>
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz => ⟨hx, hz⟩
  refine cfc_setIntegral' _ _ this ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_mkD_restri

中文:
引理 cfc_setIntegral
  结论: [NormedSpace 实数 A] [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
  证明: by
  have : forallᵐ (x : X) ∂(μ.restrict s), ContinuousOn (f x) (spectrum 𝕜 a) :=
    ae_restrict_of_forall_mem hs fun x hx =>
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz => ⟨hx, hz⟩
  refine cfc_setIntegral' _ _ this ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_mkD_restri

Depends on / 依赖: Continuous, Continuous.prodMk_right, ContinuousOn, aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry, ae_restrict_of_forall_mem, bound_ge, bound_int, cfc_setIntegral, cfc_tac, continuousOn, hasFiniteIntegral_mkD_restrict_of_bound, hf.comp, prodMk_right, restrict, spectrum
-/
lemma cfc_setIntegral [NormedSpace Real A] [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
    (hs : MeasurableSet s) (f : X -> 𝕜 -> 𝕜) (bound : X -> Real) (a : A)
    [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (s ×ˢ spectrum 𝕜 a))
    (bound_ge : forallᵐ x ∂(μ.restrict s), forall z in spectrum 𝕜 a, ‖f x z‖ <= bound x)
    (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    cfc (fun r => ∫ x in s, f x r ∂μ) a = ∫ x in s, cfc (f x) a ∂μ := by
  have : forallᵐ (x : X) ∂(μ.restrict s), ContinuousOn (f x) (spectrum 𝕜 a) :=
    ae_restrict_of_forall_mem hs fun x hx =>
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz => ⟨hx, hz⟩
  refine cfc_setIntegral' _ _ this ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry hs _ _ hf
  · exact hasFiniteIntegral_mkD_restrict_of_bound f _ this bound bound_int bound_ge

end unital

section nonunital

open ContinuousMapZero

variable {X : Type*} {𝕜 : Type*} {A : Type*} {p : A -> Prop} [RCLike 𝕜]
  [MeasurableSpace X] {μ : Measure X} [NonUnitalNormedRing A] [StarRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
  [NonUnitalContinuousFunctionalCalculus 𝕜 A p]
  [CompleteSpace A]

/--
lemma `cfcₙL_integral` / 引理 `cfcₙL_integral`

English:
lemma cfcₙL_integral
  statement: [NormedSpace Real A] (a : A) (f : X -> C(quasispectrum 𝕜 a, 𝕜)₀)
  proof: by
  rw [ContinuousLinearMap.integral_comp_comm _ hf₁]

中文:
引理 cfcₙL_integral
  结论: [NormedSpace 实数 A] (a : A) (f : X -> C(quasispectrum 𝕜 a, 𝕜)₀)
  证明: by
  rw [ContinuousLinearMap.integral_comp_comm _ hf₁]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.integral_comp_comm, cfc_tac, integral_comp_comm
-/
lemma cfcₙL_integral [NormedSpace Real A] (a : A) (f : X -> C(quasispectrum 𝕜 a, 𝕜)₀)
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    ∫ x, cfcₙL (a := a) ha (f x) ∂μ = cfcₙL (a := a) ha (∫ x, f x ∂μ) := by
  rw [ContinuousLinearMap.integral_comp_comm _ hf₁]

/--
lemma `cfcₙHom_integral` / 引理 `cfcₙHom_integral`

English:
lemma cfcₙHom_integral
  statement: [NormedSpace Real A] (a : A) (f : X -> C(quasispectrum 𝕜 a, 𝕜)₀)
  proof: cfcₙL_integral a f hf₁ ha

中文:
引理 cfcₙHom_integral
  结论: [NormedSpace 实数 A] (a : A) (f : X -> C(quasispectrum 𝕜 a, 𝕜)₀)
  证明: cfcₙL_integral a f hf₁ ha

Depends on / 依赖: cfc_tac
-/
lemma cfcₙHom_integral [NormedSpace Real A] (a : A) (f : X -> C(quasispectrum 𝕜 a, 𝕜)₀)
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    ∫ x, cfcₙHom (a := a) ha (f x) ∂μ = cfcₙHom (a := a) ha (∫ x, f x ∂μ) :=
  cfcₙL_integral a f hf₁ ha

/--
lemma `cfcₙL_integrable` / 引理 `cfcₙL_integrable`

English:
lemma cfcₙL_integrable
  statement: (a : A) (f : X -> C(quasispectrum 𝕜 a, 𝕜)₀)
  proof: ContinuousLinearMap.integrable_comp _ hf₁

中文:
引理 cfcₙL_integrable
  结论: (a : A) (f : X -> C(quasispectrum 𝕜 a, 𝕜)₀)
  证明: ContinuousLinearMap.integrable_comp _ hf₁

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.integrable_comp, Integrable, cfc_tac, integrable_comp
-/
lemma cfcₙL_integrable (a : A) (f : X -> C(quasispectrum 𝕜 a, 𝕜)₀)
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    Integrable (fun x => cfcₙL (a := a) ha (f x)) μ :=
  ContinuousLinearMap.integrable_comp _ hf₁

/--
lemma `integrable_cfcₙ'` / 引理 `integrable_cfcₙ'`

English:
lemma integrable_cfcₙ'
  statement: (f : X -> 𝕜 -> 𝕜) (a : A)
  proof: by
  conv in cfcₙ _ _ => rw [cfcₙ_eq_cfcₙL_mkD _ a]
  exact cfcₙL_integrable _ _ hf ha

中文:
引理 integrable_cfcₙ'
  结论: (f : X -> 𝕜 -> 𝕜) (a : A)
  证明: by
  conv in cfcₙ _ _ => rw [cfcₙ_eq_cfcₙL_mkD _ a]
  exact cfcₙL_integrable _ _ hf ha

Depends on / 依赖: Integrable, cfc_tac
-/
lemma integrable_cfcₙ' (f : X -> 𝕜 -> 𝕜) (a : A)
    (hf : Integrable
      (fun x : X => mkD ((quasispectrum 𝕜 a).domRestrict (f x)) 0) μ)
    (ha : p a := by cfc_tac) :
    Integrable (fun x => cfcₙ (f x) a) μ := by
  conv in cfcₙ _ _ => rw [cfcₙ_eq_cfcₙL_mkD _ a]
  exact cfcₙL_integrable _ _ hf ha

/--
lemma `integrableOn_cfcₙ'` / 引理 `integrableOn_cfcₙ'`

English:
lemma integrableOn_cfcₙ'
  statement: {s : Set X} (f : X -> 𝕜 -> 𝕜) (a : A)
  proof: by
  exact integrable_cfcₙ' _ _ hf ha

中文:
引理 integrableOn_cfcₙ'
  结论: {s : Set X} (f : X -> 𝕜 -> 𝕜) (a : A)
  证明: by
  exact integrable_cfcₙ' _ _ hf ha

Depends on / 依赖: IntegrableOn, cfc_tac
-/
lemma integrableOn_cfcₙ' {s : Set X} (f : X -> 𝕜 -> 𝕜) (a : A)
    (hf : IntegrableOn
      (fun x : X => mkD ((quasispectrum 𝕜 a).domRestrict (f x)) 0) s μ)
    (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfcₙ (f x) a) s μ := by
  exact integrable_cfcₙ' _ _ hf ha

open Set Function in
/--
lemma `integrable_cfcₙ` / 引理 `integrable_cfcₙ`

English:
lemma integrable_cfcₙ
  statement: [TopologicalSpace X] [OpensMeasurableSpace X] (f : X -> 𝕜 -> 𝕜)
  proof: by
  refine integrable_cfcₙ' _ _ ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_mkD_restrict_of_uncurry _ _ hf f_zero
  · refine hasFiniteIntegral_mkD_restrict_of_bound f _ ?_ f_zero bound bound_int bound_ge
    exact .of_forall fun x =>
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz =>

中文:
引理 integrable_cfcₙ
  结论: [TopologicalSpace X] [OpensMeasurableSpace X] (f : X -> 𝕜 -> 𝕜)
  证明: by
  refine integrable_cfcₙ' _ _ ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_mkD_restrict_of_uncurry _ _ hf f_zero
  · refine hasFiniteIntegral_mkD_restrict_of_bound f _ ?_ f_zero bound bound_int bound_ge
    exact .of_forall fun x =>
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz =>

Depends on / 依赖: Continuous, Continuous.prodMk_right, Integrable, Set.mem_univ, aeStronglyMeasurable_mkD_restrict_of_uncurry, bound_ge, bound_int, cfc_tac, continuousOn, f_zero, hasFiniteIntegral_mkD_restrict_of_bound, hf.comp, mem_univ, of_forall, prodMk_right
-/
lemma integrable_cfcₙ [TopologicalSpace X] [OpensMeasurableSpace X] (f : X -> 𝕜 -> 𝕜)
    (bound : X -> Real) (a : A)
    [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (univ ×ˢ quasispectrum 𝕜 a))
    (f_zero : forallᵐ x ∂μ, f x 0 = 0)
    (bound_ge : forallᵐ x ∂μ, forall z in quasispectrum 𝕜 a, ‖f x z‖ <= bound x)
    (bound_int : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    Integrable (fun x => cfcₙ (f x) a) μ := by
  refine integrable_cfcₙ' _ _ ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_mkD_restrict_of_uncurry _ _ hf f_zero
  · refine hasFiniteIntegral_mkD_restrict_of_bound f _ ?_ f_zero bound bound_int bound_ge
    exact .of_forall fun x =>
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz => ⟨Set.mem_univ _, hz⟩

open Set Function in
/--
lemma `integrableOn_cfcₙ` / 引理 `integrableOn_cfcₙ`

English:
lemma integrableOn_cfcₙ
  statement: [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
  proof: by
  refine integrableOn_cfcₙ' _ _ ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry hs _ _ hf f_zero
  · refine hasFiniteIntegral_mkD_restrict_of_bound f _ ?_ f_zero bound bound_int bound_ge
    exact ae_restrict_of_forall_mem hs fun x hx =>
      hf.comp (Continuous.prodM

中文:
引理 integrableOn_cfcₙ
  结论: [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
  证明: by
  refine integrableOn_cfcₙ' _ _ ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry hs _ _ hf f_zero
  · refine hasFiniteIntegral_mkD_restrict_of_bound f _ ?_ f_zero bound bound_int bound_ge
    exact ae_restrict_of_forall_mem hs fun x hx =>
      hf.comp (Continuous.prodM

Depends on / 依赖: Continuous, Continuous.prodMk_right, IntegrableOn, aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry, ae_restrict_of_forall_mem, bound_ge, bound_int, cfc_tac, continuousOn, f_zero, hasFiniteIntegral_mkD_restrict_of_bound, hf.comp, prodMk_right
-/
lemma integrableOn_cfcₙ [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
    (hs : MeasurableSet s) (f : X -> 𝕜 -> 𝕜) (bound : X -> Real) (a : A)
    [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (s ×ˢ quasispectrum 𝕜 a))
    (f_zero : forallᵐ x ∂(μ.restrict s), f x 0 = 0)
    (bound_ge : forallᵐ x ∂(μ.restrict s), forall z in quasispectrum 𝕜 a, ‖f x z‖ <= bound x)
    (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfcₙ (f x) a) s μ := by
  refine integrableOn_cfcₙ' _ _ ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry hs _ _ hf f_zero
  · refine hasFiniteIntegral_mkD_restrict_of_bound f _ ?_ f_zero bound bound_int bound_ge
    exact ae_restrict_of_forall_mem hs fun x hx =>
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz => ⟨hx, hz⟩

open Set in
/--
lemma `cfcₙ_integral'` / 引理 `cfcₙ_integral'`

English:
lemma cfcₙ_integral'
  statement: [NormedSpace Real A] (f : X -> 𝕜 -> 𝕜) (a : A)
  proof: by
  have key₁ (z : quasispectrum 𝕜 a) :
      ∫ x, f x z ∂μ = (∫ x, mkD ((quasispectrum 𝕜 a).domRestrict (f x)) 0 ∂μ) z := by
    rw [integral_apply hf₃]
    refine integral_congr_ae ?_
    filter_upwards [hf₁, hf₂] with x cont_x zero_x
    rw [mkD_apply_of_continuousOn cont_x zero_x]
  have key₂ (

中文:
引理 cfcₙ_integral'
  结论: [NormedSpace 实数 A] (f : X -> 𝕜 -> 𝕜) (a : A)
  证明: by
  have key₁ (z : quasispectrum 𝕜 a) :
      ∫ x, f x z ∂μ = (∫ x, mkD ((quasispectrum 𝕜 a).domRestrict (f x)) 0 ∂μ) z := by
    rw [integral_apply hf₃]
    refine integral_congr_ae ?_
    filter_upwards [hf₁, hf₂] with x cont_x zero_x
    rw [mkD_apply_of_continuousOn cont_x zero_x]
  have key₂ (

Depends on / 依赖: cfc_tac, cont_x, domRestrict, filter_upwards, integral_apply, integral_congr_ae, mkD_apply_of_continuousOn, quasispectrum, zero_x
-/
lemma cfcₙ_integral' [NormedSpace Real A] (f : X -> 𝕜 -> 𝕜) (a : A)
    (hf₁ : forallᵐ x ∂μ, ContinuousOn (f x) (quasispectrum 𝕜 a))
    (hf₂ : forallᵐ x ∂μ, f x 0 = 0)
    (hf₃ : Integrable
      (fun x : X => mkD ((quasispectrum 𝕜 a).domRestrict (f x)) 0) μ)
    (ha : p a := by cfc_tac) :
    cfcₙ (fun z => ∫ x, f x z ∂μ) a = ∫ x, cfcₙ (f x) a ∂μ := by
  have key₁ (z : quasispectrum 𝕜 a) :
      ∫ x, f x z ∂μ = (∫ x, mkD ((quasispectrum 𝕜 a).domRestrict (f x)) 0 ∂μ) z := by
    rw [integral_apply hf₃]
    refine integral_congr_ae ?_
    filter_upwards [hf₁, hf₂] with x cont_x zero_x
    rw [mkD_apply_of_continuousOn cont_x zero_x]
  have key₂ (z : quasispectrum 𝕜 a) :
      ∫ x, f x z ∂μ = mkD ((quasispectrum 𝕜 a).domRestrict (fun z => ∫ x, f x z ∂μ)) 0 z := by
    rw [mkD_apply_of_continuousOn]
    · rw [continuousOn_iff_continuous_domRestrict]
.mpr ?_ refine continuous_congr key₁
      exact map_continuous (∫ x, mkD ((quasispectrum 𝕜 a).domRestrict (f x)) 0 ∂μ)
    · exact integral_eq_zero_of_ae hf₂
  simp_rw [cfcₙ_eq_cfcₙL_mkD _ a, cfcₙL_integral a _ hf₃ ha]
  congr
  ext z
  rw [← key₁]; rw [key₂]

open Set in
/--
lemma `cfcₙ_setIntegral'` / 引理 `cfcₙ_setIntegral'`

English:
lemma cfcₙ_setIntegral'
  statement: {s : Set X} [NormedSpace Real A] (f : X -> 𝕜 -> 𝕜) (a : A)
  proof: cfcₙ_integral' _ _ hf₁ hf₂ hf₃ ha

中文:
引理 cfcₙ_setIntegral'
  结论: {s : Set X} [NormedSpace 实数 A] (f : X -> 𝕜 -> 𝕜) (a : A)
  证明: cfcₙ_integral' _ _ hf₁ hf₂ hf₃ ha

Depends on / 依赖: cfc_tac
-/
lemma cfcₙ_setIntegral' {s : Set X} [NormedSpace Real A] (f : X -> 𝕜 -> 𝕜) (a : A)
    (hf₁ : forallᵐ x ∂(μ.restrict s), ContinuousOn (f x) (quasispectrum 𝕜 a))
    (hf₂ : forallᵐ x ∂(μ.restrict s), f x 0 = 0)
    (hf₃ : IntegrableOn
      (fun x : X => mkD ((quasispectrum 𝕜 a).domRestrict (f x)) 0) s μ)
    (ha : p a := by cfc_tac) :
    cfcₙ (fun z => ∫ x in s, f x z ∂μ) a = ∫ x in s, cfcₙ (f x) a ∂μ :=
  cfcₙ_integral' _ _ hf₁ hf₂ hf₃ ha

open Function Set in
/--
lemma `cfcₙ_integral` / 引理 `cfcₙ_integral`

English:
lemma cfcₙ_integral
  statement: [NormedSpace Real A] [TopologicalSpace X] [OpensMeasurableSpace X]
  proof: by
  have : forallᵐ (x : X) ∂μ, ContinuousOn (f x) (quasispectrum 𝕜 a) := .of_forall fun x =>
    hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz => ⟨Set.mem_univ _, hz⟩
  refine cfcₙ_integral' _ _ this f_zero ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_mkD_restrict_of_uncurry _ _ hf f_zero

中文:
引理 cfcₙ_integral
  结论: [NormedSpace 实数 A] [TopologicalSpace X] [OpensMeasurableSpace X]
  证明: by
  have : forallᵐ (x : X) ∂μ, ContinuousOn (f x) (quasispectrum 𝕜 a) := .of_forall fun x =>
    hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz => ⟨Set.mem_univ _, hz⟩
  refine cfcₙ_integral' _ _ this f_zero ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_mkD_restrict_of_uncurry _ _ hf f_zero

Depends on / 依赖: Continuous, Continuous.prodMk_right, ContinuousOn, Set.mem_univ, aeStronglyMeasurable_mkD_restrict_of_uncurry, bound_ge, bound_int, cfc_tac, continuousOn, f_zero, hasFiniteIntegral_mkD_restrict_of_bound, hf.comp, mem_univ, of_forall, prodMk_right, quasispectrum
-/
lemma cfcₙ_integral [NormedSpace Real A] [TopologicalSpace X] [OpensMeasurableSpace X]
    (f : X -> 𝕜 -> 𝕜) (bound : X -> Real) (a : A)
    [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (univ ×ˢ quasispectrum 𝕜 a))
    (f_zero : forallᵐ x ∂μ, f x 0 = 0)
    (bound_ge : forallᵐ x ∂μ, forall z in quasispectrum 𝕜 a, ‖f x z‖ <= bound x)
    (bound_int : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    cfcₙ (fun r => ∫ x, f x r ∂μ) a = ∫ x, cfcₙ (f x) a ∂μ := by
  have : forallᵐ (x : X) ∂μ, ContinuousOn (f x) (quasispectrum 𝕜 a) := .of_forall fun x =>
    hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz => ⟨Set.mem_univ _, hz⟩
  refine cfcₙ_integral' _ _ this f_zero ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_mkD_restrict_of_uncurry _ _ hf f_zero
  · exact hasFiniteIntegral_mkD_restrict_of_bound f _ this f_zero bound bound_int bound_ge

open Function Set in
/--
lemma `cfcₙ_setIntegral` / 引理 `cfcₙ_setIntegral`

English:
lemma cfcₙ_setIntegral
  statement: [NormedSpace Real A] [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
  proof: by
  have : forallᵐ (x : X) ∂(μ.restrict s), ContinuousOn (f x) (quasispectrum 𝕜 a) :=
    ae_restrict_of_forall_mem hs fun x hx =>
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz => ⟨hx, hz⟩
  refine cfcₙ_setIntegral' _ _ this f_zero ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restri

中文:
引理 cfcₙ_setIntegral
  结论: [NormedSpace 实数 A] [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
  证明: by
  have : forallᵐ (x : X) ∂(μ.restrict s), ContinuousOn (f x) (quasispectrum 𝕜 a) :=
    ae_restrict_of_forall_mem hs fun x hx =>
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz => ⟨hx, hz⟩
  refine cfcₙ_setIntegral' _ _ this f_zero ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restri

Depends on / 依赖: Continuous, Continuous.prodMk_right, ContinuousOn, aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry, ae_restrict_of_forall_mem, bound_ge, bound_int, cfc_tac, continuousOn, f_zero, hasFiniteIntegral_mkD_restrict_of_bound, hf.comp, prodMk_right, quasispectrum, restrict
-/
lemma cfcₙ_setIntegral [NormedSpace Real A] [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
    (hs : MeasurableSet s) (f : X -> 𝕜 -> 𝕜) (bound : X -> Real) (a : A)
    [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (s ×ˢ quasispectrum 𝕜 a))
    (f_zero : forallᵐ x ∂(μ.restrict s), f x 0 = 0)
    (bound_ge : forallᵐ x ∂(μ.restrict s), forall z in quasispectrum 𝕜 a, ‖f x z‖ <= bound x)
    (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    cfcₙ (fun r => ∫ x in s, f x r ∂μ) a = ∫ x in s, cfcₙ (f x) a ∂μ := by
  have : forallᵐ (x : X) ∂(μ.restrict s), ContinuousOn (f x) (quasispectrum 𝕜 a) :=
    ae_restrict_of_forall_mem hs fun x hx =>
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz => ⟨hx, hz⟩
  refine cfcₙ_setIntegral' _ _ this f_zero ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry hs _ _ hf f_zero
  · exact hasFiniteIntegral_mkD_restrict_of_bound f _ this f_zero bound bound_int bound_ge

end nonunital
