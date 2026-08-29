/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def
public import Mathlib.Probability.HasLaw

import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Gaussian random variables

In this file we prove basic properties of Gaussian random variables.

## Implementation note

Many lemmas are duplicated with an expanded form of some function. For instance there is
`HasGaussianLaw.add` and `HasGaussianLaw.fun_add`. The reason is that if someone wants for instance
to rewrite using `HasGaussianLaw.charFunDual_map_eq` and provide the proof of `HasGaussianLaw`
directly through dot notation, the lemma used must syntactically correspond to the random variable.

## Tags

Gaussian random variable
-/

public section

open MeasureTheory ENNReal WithLp Complex
open scoped RealInnerProductSpace

namespace ProbabilityTheory

variable {Ω E F ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

section Basic

variable [TopologicalSpace E] [AddCommMonoid E] [Module Real E] [mE : MeasurableSpace E]
  {X Y : Ω -> E}

/--
lemma `HasGaussianLaw.congr` / 引理 `HasGaussianLaw.congr`

English:
lemma HasGaussianLaw.congr
  given: {Y : Ω -> E} (hX : HasGaussianLaw X P) (h : X =ᵐ[P] Y)
  proof: by
    rw [← Measure.map_congr h]
    exact hX.isGaussian_map

中文:
引理 HasGaussianLaw.congr
  条件: {Y : Ω -> E} (hX : HasGaussianLaw X P) (h : X =ᵐ[P] Y)
  证明: by
    rw [← Measure.map_congr h]
    exact hX.isGaussian_map

Depends on / 依赖: Measure, Measure.map_congr, hX.isGaussian_map, isGaussian_map, map_congr
-/
lemma HasGaussianLaw.congr {Y : Ω -> E} (hX : HasGaussianLaw X P) (h : X =ᵐ[P] Y) :
    HasGaussianLaw Y P where
  isGaussian_map := by
    rw [← Measure.map_congr h]
    exact hX.isGaussian_map

/--
lemma `IsGaussian.hasGaussianLaw` / 引理 `IsGaussian.hasGaussianLaw`

English:
lemma IsGaussian.hasGaussianLaw
  given: [IsGaussian (P.map X)]
  statement: HasGaussianLaw X P where
  proof: inferInstance

中文:
引理 IsGaussian.hasGaussianLaw
  条件: [IsGaussian (P.map X)]
  结论: HasGaussianLaw X P where
  证明: inferInstance
-/
lemma IsGaussian.hasGaussianLaw [IsGaussian (P.map X)] : HasGaussianLaw X P where
  isGaussian_map := inferInstance

variable {mE} in
/--
lemma `IsGaussian.hasGaussianLaw_id` / 引理 `IsGaussian.hasGaussianLaw_id`

English:
lemma IsGaussian.hasGaussianLaw_id
  given: {μ : Measure E} [IsGaussian μ]
  statement: HasGaussianLaw id μ where
  proof: by rwa [Measure.map_id]

@[fun_prop]

中文:
引理 IsGaussian.hasGaussianLaw_id
  条件: {μ : Measure E} [IsGaussian μ]
  结论: HasGaussianLaw id μ where
  证明: by rwa [Measure.map_id]

@[fun_prop]

Depends on / 依赖: Measure, Measure.map_id, map_id
-/
lemma IsGaussian.hasGaussianLaw_id {μ : Measure E} [IsGaussian μ] : HasGaussianLaw id μ where
  isGaussian_map := by rwa [Measure.map_id]

@[fun_prop]
/--
lemma `HasGaussianLaw.aemeasurable` / 引理 `HasGaussianLaw.aemeasurable`

English:
lemma HasGaussianLaw.aemeasurable
  given: (hX : HasGaussianLaw X P)
  statement: AEMeasurable X P
  proof: AEMeasurable.of_map_ne_zero hX.isGaussian_map.toIsProbabilityMeasure.ne_zero

中文:
引理 HasGaussianLaw.aemeasurable
  条件: (hX : HasGaussianLaw X P)
  结论: AEMeasurable X P
  证明: AEMeasurable.of_map_ne_zero hX.isGaussian_map.toIsProbabilityMeasure.ne_zero

Depends on / 依赖: AEMeasurable, AEMeasurable.of_map_ne_zero, hX.isGaussian_map.toIsProbabilityMeasure.ne_zero, isGaussian_map, ne_zero, of_map_ne_zero, toIsProbabilityMeasure
-/
lemma HasGaussianLaw.aemeasurable (hX : HasGaussianLaw X P) : AEMeasurable X P :=
  AEMeasurable.of_map_ne_zero hX.isGaussian_map.toIsProbabilityMeasure.ne_zero

/--
lemma `HasGaussianLaw.isProbabilityMeasure` / 引理 `HasGaussianLaw.isProbabilityMeasure`

English:
lemma HasGaussianLaw.isProbabilityMeasure
  given: (hX : HasGaussianLaw X P)
  statement: IsProbabilityMeasure P
  proof: haveI := hX.isGaussian_map
    P.isProbabilityMeasure_of_map X

中文:
引理 HasGaussianLaw.isProbabilityMeasure
  条件: (hX : HasGaussianLaw X P)
  结论: IsProbabilityMeasure P
  证明: haveI := hX.isGaussian_map
    P.isProbabilityMeasure_of_map X

Depends on / 依赖: P.isProbabilityMeasure_of_map, hX.isGaussian_map, isGaussian_map, isProbabilityMeasure_of_map
-/
lemma HasGaussianLaw.isProbabilityMeasure (hX : HasGaussianLaw X P) : IsProbabilityMeasure P :=
    haveI := hX.isGaussian_map
    P.isProbabilityMeasure_of_map X

variable {mE} in
/--
lemma `HasLaw.hasGaussianLaw` / 引理 `HasLaw.hasGaussianLaw`

English:
lemma HasLaw.hasGaussianLaw
  given: {μ : Measure E} (hX : HasLaw X μ P) [IsGaussian μ]
  proof: by rwa [hX.map_eq]

中文:
引理 HasLaw.hasGaussianLaw
  条件: {μ : Measure E} (hX : HasLaw X μ P) [IsGaussian μ]
  证明: by rwa [hX.map_eq]

Depends on / 依赖: hX.map_eq, map_eq
-/
lemma HasLaw.hasGaussianLaw {μ : Measure E} (hX : HasLaw X μ P) [IsGaussian μ] :
    HasGaussianLaw X P where
  isGaussian_map := by rwa [hX.map_eq]

/--
lemma `HasGaussianLaw.map_of_measurable` / 引理 `HasGaussianLaw.map_of_measurable`

English:
lemma HasGaussianLaw.map_of_measurable
  statement: {F : Type*} [TopologicalSpace F] [AddCommMonoid F]
  proof: by
    have := hX.isGaussian_map
    rw [← AEMeasurable.map_map_of_aemeasurable]
    · exact isGaussian_map_of_measurable hL
    all_goals fun_prop

中文:
引理 HasGaussianLaw.map_of_measurable
  结论: {F : 类型} [TopologicalSpace F] [AddCommMonoid F]
  证明: by
    have := hX.isGaussian_map
    rw [← AEMeasurable.map_map_of_aemeasurable]
    · exact isGaussian_map_of_measurable hL
    all_goals fun_prop

Depends on / 依赖: AEMeasurable, AEMeasurable.map_map_of_aemeasurable, all_goals, fun_prop, hX.isGaussian_map, isGaussian_map, isGaussian_map_of_measurable, map_map_of_aemeasurable
-/
lemma HasGaussianLaw.map_of_measurable {F : Type*} [TopologicalSpace F] [AddCommMonoid F]
    [Module Real F] [MeasurableSpace F] [OpensMeasurableSpace F]
    (L : E ->L[Real] F) (hX : HasGaussianLaw X P) (hL : Measurable L) :
    HasGaussianLaw (L ∘ X) P where
  isGaussian_map := by
    have := hX.isGaussian_map
    rw [← AEMeasurable.map_map_of_aemeasurable]
    · exact isGaussian_map_of_measurable hL
    all_goals fun_prop

/--
lemma `HasGaussianLaw.map_eq_gaussianReal` / 引理 `HasGaussianLaw.map_eq_gaussianReal`

English:
lemma HasGaussianLaw.map_eq_gaussianReal
  given: {X : Ω -> Real} (h : HasGaussianLaw X P)
  proof: by
  rw [h.isGaussian_map.eq_gaussianReal (.map _ _)]; rw [integral_map]; rw [variance_map]
  · rfl
  all_goals fun_prop

中文:
引理 HasGaussianLaw.map_eq_gaussianReal
  条件: {X : Ω -> 实数} (h : HasGaussianLaw X P)
  证明: by
  rw [h.isGaussian_map.eq_gaussianReal (.map _ _)]; rw [integral_map]; rw [variance_map]
  · rfl
  all_goals fun_prop

Depends on / 依赖: all_goals, eq_gaussianReal, fun_prop, h.isGaussian_map.eq_gaussianReal, integral_map, isGaussian_map, variance_map
-/
lemma HasGaussianLaw.map_eq_gaussianReal {X : Ω -> Real} (h : HasGaussianLaw X P) :
    P.map X = gaussianReal P[X] Var[X; P].toNNReal := by
  rw [h.isGaussian_map.eq_gaussianReal (.map _ _)]; rw [integral_map]; rw [variance_map]
  · rfl
  all_goals fun_prop

end Basic

namespace HasGaussianLaw

variable [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] {X : Ω -> E}

/--
lemma `of_subsingleton` / 引理 `of_subsingleton`

English:
lemma of_subsingleton
  given: [NormedSpace Real E] [Subsingleton E] [IsProbabilityMeasure P]
  proof: by
    have : IsProbabilityMeasure (P.map X) := P.isProbabilityMeasure_map (by fun_prop)
    exact .of_subsingleton

中文:
引理 of_subsingleton
  条件: [NormedSpace 实数 E] [Subsingleton E] [IsProbabilityMeasure P]
  证明: by
    have : IsProbabilityMeasure (P.map X) := P.isProbabilityMeasure_map (by fun_prop)
    exact .of_subsingleton

Depends on / 依赖: IsProbabilityMeasure, P.isProbabilityMeasure_map, P.map, fun_prop, isProbabilityMeasure_map, of_subsingleton
-/
lemma of_subsingleton [NormedSpace Real E] [Subsingleton E] [IsProbabilityMeasure P] :
    HasGaussianLaw X P where
  isGaussian_map := by
    have : IsProbabilityMeasure (P.map X) := P.isProbabilityMeasure_map (by fun_prop)
    exact .of_subsingleton

/--
lemma `charFun_map_eq` / 引理 `charFun_map_eq`

English:
lemma charFun_map_eq
  given: [InnerProductSpace Real E] (t : E) (hX : HasGaussianLaw X P)
  proof: by
  rw [hX.isGaussian_map.charFun_eq]; rw [integral_map hX.aemeasurable (by fun_prop)]; rw [variance_map (by fun_prop) hX.aemeasurable]; rw [integral_complex_ofReal]; rw [Function.comp_def]

中文:
引理 charFun_map_eq
  条件: [InnerProductSpace 实数 E] (t : E) (hX : HasGaussianLaw X P)
  证明: by
  rw [hX.isGaussian_map.charFun_eq]; rw [integral_map hX.aemeasurable (by fun_prop)]; rw [variance_map (by fun_prop) hX.aemeasurable]; rw [integral_complex_ofReal]; rw [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, aemeasurable, charFun_eq, comp_def, fun_prop, hX.aemeasurable, hX.isGaussian_map.charFun_eq, integral_complex_ofReal, integral_map, isGaussian_map, variance_map
-/
lemma charFun_map_eq [InnerProductSpace Real E] (t : E) (hX : HasGaussianLaw X P) :
    charFun (P.map X) t = exp ((P[fun ω => ⟪t, X ω⟫] : Real) * I - Var[fun ω => ⟪t, X ω⟫; P] / 2) := by
  rw [hX.isGaussian_map.charFun_eq]; rw [integral_map hX.aemeasurable (by fun_prop)]; rw [variance_map (by fun_prop) hX.aemeasurable]; rw [integral_complex_ofReal]; rw [Function.comp_def]

/--
lemma `_root_.ProbabilityTheory.hasGaussianLaw_iff_charFun_map_eq` / 引理 `_root_.ProbabilityTheory.hasGaussianLaw_iff_charFun_map_eq`

English:
lemma _root_.ProbabilityTheory.hasGaussianLaw_iff_charFun_map_eq
  statement: [CompleteSpace E]
  proof: h.charFun_map_eq
  mpr h := by
    refine ⟨isGaussian_iff_charFun_eq.2 fun t => ?_⟩
    rw [h]; rw [integral_map]; rw [variance_map]; rw [integral_complex_ofReal]; rw [Function.comp_def]
    all_goals fun_prop

中文:
引理 _root_.ProbabilityTheory.hasGaussianLaw_iff_charFun_map_eq
  结论: [CompleteSpace E]
  证明: h.charFun_map_eq
  mpr h := by
    refine ⟨isGaussian_iff_charFun_eq.2 fun t => ?_⟩
    rw [h]; rw [integral_map]; rw [variance_map]; rw [integral_complex_ofReal]; rw [Function.comp_def]
    all_goals fun_prop

Depends on / 依赖: charFun_map_eq, h.charFun_map_eq
-/
lemma _root_.ProbabilityTheory.hasGaussianLaw_iff_charFun_map_eq [CompleteSpace E]
    [InnerProductSpace Real E] [IsFiniteMeasure P] (hX : AEMeasurable X P) :
    HasGaussianLaw X P ↔ forall t,
    charFun (P.map X) t = exp ((P[fun ω => ⟪t, X ω⟫] : Real) * I - Var[fun ω => ⟪t, X ω⟫; P] / 2) where
  mp h := h.charFun_map_eq
  mpr h := by
    refine ⟨isGaussian_iff_charFun_eq.2 fun t => ?_⟩
    rw [h]; rw [integral_map]; rw [variance_map]; rw [integral_complex_ofReal]; rw [Function.comp_def]
    all_goals fun_prop

variable [NormedSpace Real E]

/--
lemma `charFunDual_map_eq` / 引理 `charFunDual_map_eq`

English:
lemma charFunDual_map_eq
  given: (L : StrongDual Real E) (hX : HasGaussianLaw X P)
  proof: by
  rw [hX.isGaussian_map.charFunDual_eq]; rw [integral_map hX.aemeasurable (by fun_prop)]; rw [variance_map (by fun_prop) hX.aemeasurable]; rw [integral_complex_ofReal]; rw [Function.comp_def]

中文:
引理 charFunDual_map_eq
  条件: (L : StrongDual 实数 E) (hX : HasGaussianLaw X P)
  证明: by
  rw [hX.isGaussian_map.charFunDual_eq]; rw [integral_map hX.aemeasurable (by fun_prop)]; rw [variance_map (by fun_prop) hX.aemeasurable]; rw [integral_complex_ofReal]; rw [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, aemeasurable, charFunDual_eq, comp_def, fun_prop, hX.aemeasurable, hX.isGaussian_map.charFunDual_eq, integral_complex_ofReal, integral_map, isGaussian_map, variance_map
-/
lemma charFunDual_map_eq (L : StrongDual Real E) (hX : HasGaussianLaw X P) :
    charFunDual (P.map X) L = exp ((P[L ∘ X] : Real) * I - Var[L ∘ X; P] / 2) := by
  rw [hX.isGaussian_map.charFunDual_eq]; rw [integral_map hX.aemeasurable (by fun_prop)]; rw [variance_map (by fun_prop) hX.aemeasurable]; rw [integral_complex_ofReal]; rw [Function.comp_def]

/--
lemma `_root_.ProbabilityTheory.hasGaussianLaw_iff_charFunDual_map_eq` / 引理 `_root_.ProbabilityTheory.hasGaussianLaw_iff_charFunDual_map_eq`

English:
lemma _root_.ProbabilityTheory.hasGaussianLaw_iff_charFunDual_map_eq
  proof: h.charFunDual_map_eq
  mpr h := by
    refine ⟨isGaussian_iff_charFunDual_eq.2 fun t => ?_⟩
    rw [h]; rw [integral_map]; rw [variance_map]; rw [integral_complex_ofReal]; rw [Function.comp_def]
    all_goals fun_prop

中文:
引理 _root_.ProbabilityTheory.hasGaussianLaw_iff_charFunDual_map_eq
  证明: h.charFunDual_map_eq
  mpr h := by
    refine ⟨isGaussian_iff_charFunDual_eq.2 fun t => ?_⟩
    rw [h]; rw [integral_map]; rw [variance_map]; rw [integral_complex_ofReal]; rw [Function.comp_def]
    all_goals fun_prop

Depends on / 依赖: charFunDual_map_eq, h.charFunDual_map_eq
-/
lemma _root_.ProbabilityTheory.hasGaussianLaw_iff_charFunDual_map_eq
    [IsFiniteMeasure P] (hX : AEMeasurable X P) :
    HasGaussianLaw X P ↔ forall L,
    charFunDual (P.map X) L = exp ((P[L ∘ X] : Real) * I - Var[L ∘ X; P] / 2) where
  mp h := h.charFunDual_map_eq
  mpr h := by
    refine ⟨isGaussian_iff_charFunDual_eq.2 fun t => ?_⟩
    rw [h]; rw [integral_map]; rw [variance_map]; rw [integral_complex_ofReal]; rw [Function.comp_def]
    all_goals fun_prop

/--
lemma `charFunDual_map_eq_fun` / 引理 `charFunDual_map_eq_fun`

English:
lemma charFunDual_map_eq_fun
  given: (L : StrongDual Real E) (hX : HasGaussianLaw X P)
  proof: by
  rw [hX.charFunDual_map_eq]; rw [Function.comp_def]

中文:
引理 charFunDual_map_eq_fun
  条件: (L : StrongDual 实数 E) (hX : HasGaussianLaw X P)
  证明: by
  rw [hX.charFunDual_map_eq]; rw [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, charFunDual_map_eq, comp_def, hX.charFunDual_map_eq
-/
lemma charFunDual_map_eq_fun (L : StrongDual Real E) (hX : HasGaussianLaw X P) :
    charFunDual (P.map X) L = exp ((∫ ω, L (X ω) ∂P) * I - Var[fun ω => L (X ω); P] / 2) := by
  rw [hX.charFunDual_map_eq]; rw [Function.comp_def]

/--
lemma `memLp` / 引理 `memLp`

English:
lemma memLp
  statement: [CompleteSpace E] [SecondCountableTopology E] (hX : HasGaussianLaw X P)
  proof: by
  rw [← Function.id_comp X]; rw [← memLp_map_measure_iff]
  · exact hX.isGaussian_map.memLp_id _ p hp
  all_goals fun_prop

中文:
引理 memLp
  结论: [CompleteSpace E] [SecondCountableTopology E] (hX : HasGaussianLaw X P)
  证明: by
  rw [← Function.id_comp X]; rw [← memLp_map_measure_iff]
  · exact hX.isGaussian_map.memLp_id _ p hp
  all_goals fun_prop

Depends on / 依赖: Function, Function.id_comp, all_goals, fun_prop, hX.isGaussian_map.memLp_id, id_comp, isGaussian_map, memLp_id, memLp_map_measure_iff
-/
lemma memLp [CompleteSpace E] [SecondCountableTopology E] (hX : HasGaussianLaw X P)
    {p : Real>=0∞} (hp : p != ∞) :
    MemLp X p P := by
  rw [← Function.id_comp X]; rw [← memLp_map_measure_iff]
  · exact hX.isGaussian_map.memLp_id _ p hp
  all_goals fun_prop

/--
lemma `memLp_two` / 引理 `memLp_two`

English:
lemma memLp_two
  given: [CompleteSpace E] [SecondCountableTopology E] (hX : HasGaussianLaw X P)
  proof: hX.memLp (by norm_num)

中文:
引理 memLp_two
  条件: [CompleteSpace E] [SecondCountableTopology E] (hX : HasGaussianLaw X P)
  证明: hX.memLp (by norm_num)

Depends on / 依赖: hX.memLp
-/
lemma memLp_two [CompleteSpace E] [SecondCountableTopology E] (hX : HasGaussianLaw X P) :
    MemLp X 2 P := hX.memLp (by norm_num)

/--
lemma `integrable` / 引理 `integrable`

English:
lemma integrable
  given: [CompleteSpace E] [SecondCountableTopology E] (hX : HasGaussianLaw X P)
  proof: memLp_one_iff_integrable.1 hX.memLp (by norm_num)

中文:
引理 integrable
  条件: [CompleteSpace E] [SecondCountableTopology E] (hX : HasGaussianLaw X P)
  证明: memLp_one_iff_integrable.1 hX.memLp (by norm_num)

Depends on / 依赖: hX.memLp, memLp_one_iff_integrable
-/
lemma integrable [CompleteSpace E] [SecondCountableTopology E] (hX : HasGaussianLaw X P) :
    Integrable X P :=
memLp_one_iff_integrable.1 hX.memLp (by norm_num)

variable [NormedAddCommGroup F] [NormedSpace Real F] [MeasurableSpace F] [BorelSpace F]

/--
lemma `map` / 引理 `map`

English:
lemma map
  given: (hX : HasGaussianLaw X P) (L : E ->L[Real] F)
  statement: HasGaussianLaw (L ∘ X) P
  proof: hX.map_of_measurable L (by fun_prop)

中文:
引理 map
  条件: (hX : HasGaussianLaw X P) (L : E ->L[实数] F)
  结论: HasGaussianLaw (L ∘ X) P
  证明: hX.map_of_measurable L (by fun_prop)

Depends on / 依赖: fun_prop, hX.map_of_measurable, map_of_measurable
-/
lemma map (hX : HasGaussianLaw X P) (L : E ->L[Real] F) : HasGaussianLaw (L ∘ X) P :=
  hX.map_of_measurable L (by fun_prop)

/--
lemma `map_fun` / 引理 `map_fun`

English:
lemma map_fun
  given: (hX : HasGaussianLaw X P) (L : E ->L[Real] F)
  statement: HasGaussianLaw (fun ω => L (X ω)) P
  proof: hX.map L

中文:
引理 map_fun
  条件: (hX : HasGaussianLaw X P) (L : E ->L[实数] F)
  结论: HasGaussianLaw (fun ω => L (X ω)) P
  证明: hX.map L

Depends on / 依赖: hX.map
-/
lemma map_fun (hX : HasGaussianLaw X P) (L : E ->L[Real] F) : HasGaussianLaw (fun ω => L (X ω)) P :=
  hX.map L

/--
lemma `map_equiv` / 引理 `map_equiv`

English:
lemma map_equiv
  given: (hX : HasGaussianLaw X P) (L : E ≃L[Real] F)
  statement: HasGaussianLaw (L ∘ X) P
  proof: hX.map L.toContinuousLinearMap

中文:
引理 map_equiv
  条件: (hX : HasGaussianLaw X P) (L : E ≃L[实数] F)
  结论: HasGaussianLaw (L ∘ X) P
  证明: hX.map L.toContinuousLinearMap

Depends on / 依赖: L.toContinuousLinearMap, hX.map, toContinuousLinearMap
-/
lemma map_equiv (hX : HasGaussianLaw X P) (L : E ≃L[Real] F) : HasGaussianLaw (L ∘ X) P :=
  hX.map L.toContinuousLinearMap

/--
lemma `map_equiv_fun` / 引理 `map_equiv_fun`

English:
lemma map_equiv_fun
  given: (hX : HasGaussianLaw X P) (L : E ≃L[Real] F)
  proof: hX.map_equiv L

中文:
引理 map_equiv_fun
  条件: (hX : HasGaussianLaw X P) (L : E ≃L[实数] F)
  证明: hX.map_equiv L

Depends on / 依赖: hX.map_equiv, map_equiv
-/
lemma map_equiv_fun (hX : HasGaussianLaw X P) (L : E ≃L[Real] F) :
    HasGaussianLaw (fun ω => L (X ω)) P := hX.map_equiv L

section SpecificMaps

/--
lemma `smul` / 引理 `smul`

English:
lemma smul
  given: (c : Real) (hX : HasGaussianLaw X P)
  statement: HasGaussianLaw (c • X) P
  proof: hX.map (.lsmul Real Real c)

中文:
引理 smul
  条件: (c : 实数) (hX : HasGaussianLaw X P)
  结论: HasGaussianLaw (c • X) P
  证明: hX.map (.lsmul Real Real c)

Depends on / 依赖: hX.map
-/
lemma smul (c : Real) (hX : HasGaussianLaw X P) : HasGaussianLaw (c • X) P :=
  hX.map (.lsmul Real Real c)

/--
lemma `fun_smul` / 引理 `fun_smul`

English:
lemma fun_smul
  given: (c : Real) (hX : HasGaussianLaw X P)
  statement: HasGaussianLaw (fun ω => c • (X ω)) P
  proof: hX.smul c

中文:
引理 fun_smul
  条件: (c : 实数) (hX : HasGaussianLaw X P)
  结论: HasGaussianLaw (fun ω => c • (X ω)) P
  证明: hX.smul c

Depends on / 依赖: hX.smul
-/
lemma fun_smul (c : Real) (hX : HasGaussianLaw X P) : HasGaussianLaw (fun ω => c • (X ω)) P :=
  hX.smul c

/--
lemma `neg` / 引理 `neg`

English:
lemma neg
  given: (hX : HasGaussianLaw X P)
  statement: HasGaussianLaw (-X) P
  proof: by simpa using hX.smul (-1)

中文:
引理 neg
  条件: (hX : HasGaussianLaw X P)
  结论: HasGaussianLaw (-X) P
  证明: by simpa using hX.smul (-1)

Depends on / 依赖: hX.smul
-/
lemma neg (hX : HasGaussianLaw X P) : HasGaussianLaw (-X) P := by simpa using hX.smul (-1)

/--
lemma `fun_neg` / 引理 `fun_neg`

English:
lemma fun_neg
  given: (hX : HasGaussianLaw X P)
  statement: HasGaussianLaw (fun ω => -(X ω)) P
  proof: hX.neg

中文:
引理 fun_neg
  条件: (hX : HasGaussianLaw X P)
  结论: HasGaussianLaw (fun ω => -(X ω)) P
  证明: hX.neg

Depends on / 依赖: hX.neg
-/
lemma fun_neg (hX : HasGaussianLaw X P) : HasGaussianLaw (fun ω => -(X ω)) P :=
  hX.neg

section Prod

variable {Y : Ω -> F}

/--
lemma `toLp_prodMk` / 引理 `toLp_prodMk`

English:
lemma toLp_prodMk
  statement: [SecondCountableTopologyEither E F] (p : Real>=0∞) [Fact (1 <= p)]
  proof: hXY.map_equiv (WithLp.prodContinuousLinearEquiv p Real E F).symm

omit [BorelSpace F] in

中文:
引理 toLp_prodMk
  结论: [SecondCountableTopologyEither E F] (p : 实数>=0∞) [Fact (1 <= p)]
  证明: hXY.map_equiv (WithLp.prodContinuousLinearEquiv p Real E F).symm

omit [BorelSpace F] in

Depends on / 依赖: WithLp, WithLp.prodContinuousLinearEquiv, hXY.map_equiv, map_equiv, prodContinuousLinearEquiv
-/
lemma toLp_prodMk [SecondCountableTopologyEither E F] (p : Real>=0∞) [Fact (1 <= p)]
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P) :
    HasGaussianLaw (fun ω => toLp p (X ω, Y ω)) P :=
  hXY.map_equiv (WithLp.prodContinuousLinearEquiv p Real E F).symm

omit [BorelSpace F] in
/--
lemma `fst` / 引理 `fst`

English:
lemma fst
  given: (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
  statement: HasGaussianLaw X P
  proof: hXY.map_of_measurable (.fst Real E F) measurable_fst

omit [BorelSpace E] in

中文:
引理 fst
  条件: (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
  结论: HasGaussianLaw X P
  证明: hXY.map_of_measurable (.fst Real E F) measurable_fst

omit [BorelSpace E] in

Depends on / 依赖: hXY.map_of_measurable, map_of_measurable, measurable_fst
-/
lemma fst (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P) : HasGaussianLaw X P :=
  hXY.map_of_measurable (.fst Real E F) measurable_fst

omit [BorelSpace E] in
/--
lemma `snd` / 引理 `snd`

English:
lemma snd
  given: (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
  statement: HasGaussianLaw Y P
  proof: hXY.map_of_measurable (.snd Real E F) measurable_snd

中文:
引理 snd
  条件: (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
  结论: HasGaussianLaw Y P
  证明: hXY.map_of_measurable (.snd Real E F) measurable_snd

Depends on / 依赖: hXY.map_of_measurable, map_of_measurable, measurable_snd
-/
lemma snd (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P) : HasGaussianLaw Y P :=
  hXY.map_of_measurable (.snd Real E F) measurable_snd

variable [SecondCountableTopology E] {Y : Ω -> E}

/--
lemma `add` / 引理 `add`

English:
lemma add
  given: (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
  statement: HasGaussianLaw (X + Y) P
  proof: hXY.map (ContinuousLinearMap.fst Real E E + ContinuousLinearMap.snd Real E E)

中文:
引理 add
  条件: (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
  结论: HasGaussianLaw (X + Y) P
  证明: hXY.map (ContinuousLinearMap.fst Real E E + ContinuousLinearMap.snd Real E E)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.fst, ContinuousLinearMap.snd, hXY.map
-/
lemma add (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P) : HasGaussianLaw (X + Y) P :=
  hXY.map (ContinuousLinearMap.fst Real E E + ContinuousLinearMap.snd Real E E)

/--
lemma `fun_add` / 引理 `fun_add`

English:
lemma fun_add
  given: (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
  proof: hXY.add

中文:
引理 fun_add
  条件: (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
  证明: hXY.add

Depends on / 依赖: hXY.add
-/
lemma fun_add (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P) :
    HasGaussianLaw (fun ω => X ω + Y ω) P :=
  hXY.add

/--
lemma `sub` / 引理 `sub`

English:
lemma sub
  given: (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
  statement: HasGaussianLaw (X - Y) P
  proof: hXY.map (ContinuousLinearMap.fst Real E E - ContinuousLinearMap.snd Real E E)

中文:
引理 sub
  条件: (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
  结论: HasGaussianLaw (X - Y) P
  证明: hXY.map (ContinuousLinearMap.fst Real E E - ContinuousLinearMap.snd Real E E)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.fst, ContinuousLinearMap.snd, hXY.map
-/
lemma sub (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P) : HasGaussianLaw (X - Y) P :=
  hXY.map (ContinuousLinearMap.fst Real E E - ContinuousLinearMap.snd Real E E)

/--
lemma `fun_sub` / 引理 `fun_sub`

English:
lemma fun_sub
  given: (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
  proof: hXY.sub

中文:
引理 fun_sub
  条件: (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
  证明: hXY.sub

Depends on / 依赖: hXY.sub
-/
lemma fun_sub (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P) :
    HasGaussianLaw (fun ω => X ω - Y ω) P :=
  hXY.sub

end Prod

section Pi

variable {E : ι -> Type*} [forall i, NormedAddCommGroup (E i)]
  [forall i, NormedSpace Real (E i)] [forall i, MeasurableSpace (E i)] [forall i, BorelSpace (E i)]
  {X : (i : ι) -> Ω -> E i}

/--
lemma `eval` / 引理 `eval`

English:
lemma eval
  given: (hX : HasGaussianLaw (fun ω => (X · ω)) P) (i : ι)
  proof: hX.map_of_measurable (.proj i) (measurable_pi_apply i)

中文:
引理 eval
  条件: (hX : HasGaussianLaw (fun ω => (X · ω)) P) (i : ι)
  证明: hX.map_of_measurable (.proj i) (measurable_pi_apply i)

Depends on / 依赖: hX.map_of_measurable, map_of_measurable, measurable_pi_apply
-/
lemma eval (hX : HasGaussianLaw (fun ω => (X · ω)) P) (i : ι) :
    HasGaussianLaw (X i) P := hX.map_of_measurable (.proj i) (measurable_pi_apply i)

variable [forall i, SecondCountableTopology (E i)]

/--
lemma `prodMk` / 引理 `prodMk`

English:
lemma prodMk
  given: [Finite ι] (hX : HasGaussianLaw (fun ω => (X · ω)) P) (i j : ι)
  proof: letI := Fintype.ofFinite ι
  hX.map (.prod (.proj i) (.proj j))

中文:
引理 prodMk
  条件: [Finite ι] (hX : HasGaussianLaw (fun ω => (X · ω)) P) (i j : ι)
  证明: letI := Fintype.ofFinite ι
  hX.map (.prod (.proj i) (.proj j))

Depends on / 依赖: Fintype, Fintype.ofFinite, hX.map, ofFinite
-/
lemma prodMk [Finite ι] (hX : HasGaussianLaw (fun ω => (X · ω)) P) (i j : ι) :
    HasGaussianLaw (fun ω => (X i ω, X j ω)) P :=
  letI := Fintype.ofFinite ι
  hX.map (.prod (.proj i) (.proj j))

/--
lemma `toLp_pi` / 引理 `toLp_pi`

English:
lemma toLp_pi
  given: [Finite ι] (p : Real>=0∞) [Fact (1 <= p)] (hX : HasGaussianLaw (fun ω => (X · ω)) P)
  proof: have := Fintype.ofFinite ι
  hX.map_equiv (PiLp.continuousLinearEquiv p Real E).symm

中文:
引理 toLp_pi
  条件: [Finite ι] (p : 实数>=0∞) [Fact (1 <= p)] (hX : HasGaussianLaw (fun ω => (X · ω)) P)
  证明: have := Fintype.ofFinite ι
  hX.map_equiv (PiLp.continuousLinearEquiv p Real E).symm

Depends on / 依赖: Fintype, Fintype.ofFinite, PiLp.continuousLinearEquiv, continuousLinearEquiv, hX.map_equiv, map_equiv, ofFinite
-/
lemma toLp_pi [Finite ι] (p : Real>=0∞) [Fact (1 <= p)] (hX : HasGaussianLaw (fun ω => (X · ω)) P) :
    HasGaussianLaw (fun ω => toLp p (X · ω)) P :=
  have := Fintype.ofFinite ι
  hX.map_equiv (PiLp.continuousLinearEquiv p Real E).symm

variable [Fintype ι]

/--
lemma `sum` / 引理 `sum`

English:
lemma sum
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [MeasurableSpace E]
  proof: by
  convert! hX.map (∑ i, .proj i)
  ext; simp

中文:
引理 sum
  结论: {E : 类型} [NormedAddCommGroup E] [NormedSpace 实数 E] [MeasurableSpace E]
  证明: by
  convert! hX.map (∑ i, .proj i)
  ext; simp

Depends on / 依赖: convert, hX.map
-/
lemma sum {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    {X : ι -> Ω -> E} (hX : HasGaussianLaw (fun ω => (X · ω)) P) :
    HasGaussianLaw (∑ i, X i) P := by
  convert! hX.map (∑ i, .proj i)
  ext; simp

/--
lemma `fun_sum` / 引理 `fun_sum`

English:
lemma fun_sum
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [MeasurableSpace E]
  proof: by
  convert! hX.sum
  simp

中文:
引理 fun_sum
  结论: {E : 类型} [NormedAddCommGroup E] [NormedSpace 实数 E] [MeasurableSpace E]
  证明: by
  convert! hX.sum
  simp

Depends on / 依赖: convert, hX.sum
-/
lemma fun_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    {X : ι -> Ω -> E} (hX : HasGaussianLaw (fun ω => (X · ω)) P) :
    HasGaussianLaw (fun ω => ∑ i, X i ω) P := by
  convert! hX.sum
  simp

end Pi

end SpecificMaps

end HasGaussianLaw

end ProbabilityTheory
