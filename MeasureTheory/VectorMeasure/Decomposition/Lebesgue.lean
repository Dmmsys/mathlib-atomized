/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-!
# Lebesgue decomposition

This file proves the Lebesgue decomposition theorem for signed measures. The Lebesgue decomposition
theorem states that, given two σ-finite measures `μ` and `ν`, there exists a σ-finite measure `ξ`
and a measurable function `f` such that `μ = ξ + fν` and `ξ` is mutually singular with respect
to `ν`.

## Main definitions

* `MeasureTheory.SignedMeasure.HaveLebesgueDecomposition` : A signed measure `s` is said to have
  Lebesgue decomposition with respect to a measure `μ` if both the positive part and negative part
  of `s` have Lebesgue decomposition with respect to `μ`.
* `MeasureTheory.SignedMeasure.singularPart` : The singular part between a signed measure `s`
  and a measure `μ` is simply the singular part of the positive part of `s` with respect to `μ`
  minus the singular part of the negative part of `s` with respect to `μ`.
* `MeasureTheory.SignedMeasure.rnDeriv` : The Radon-Nikodym derivative of a signed
  measure `s` with respect to a measure `μ` is the Radon-Nikodym derivative of the positive part of
  `s` with respect to `μ` minus the Radon-Nikodym derivative of the negative part of `s` with
  respect to `μ`.

## Main results

* `MeasureTheory.SignedMeasure.singularPart_add_withDensity_rnDeriv_eq` :
  the Lebesgue decomposition theorem between a signed measure and a σ-finite positive measure.

## Tags

Lebesgue decomposition theorem
-/

@[expose] public section


noncomputable section

open scoped MeasureTheory NNReal ENNReal

open Set

variable {α : Type*} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}

namespace MeasureTheory

namespace SignedMeasure

open Measure

/--
Definition of `HaveLebesgueDecomposition` / `HaveLebesgueDecomposition` 的定义

English:
class HaveLebesgueDecomposition
  parameters: (s : SignedMeasure α) (μ : Measure α)
  axioms and operations (2):
    - posPart : s.toJordanDecomposition.posPart.HaveLebesgueDecomposition μ
    - negPart : s.toJordanDecomposition.negPart.HaveLebesgueDecomposition μ

中文:
类 HaveLebesgueDecomposition
  参数: (s : SignedMeasure α) (μ : Measure α)
  公理与运算 (2 个):
    - posPart : s.toJordanDecomposition.posPart.HaveLebesgueDecomposition μ
    - negPart : s.toJordanDecomposition.negPart.HaveLebesgueDecomposition μ
-/
class HaveLebesgueDecomposition (s : SignedMeasure α) (μ : Measure α) : Prop where
  posPart : s.toJordanDecomposition.posPart.HaveLebesgueDecomposition μ
  negPart : s.toJordanDecomposition.negPart.HaveLebesgueDecomposition μ

attribute [instance] HaveLebesgueDecomposition.posPart

attribute [instance] HaveLebesgueDecomposition.negPart

/--
theorem `not_haveLebesgueDecomposition_iff` / 定理 `not_haveLebesgueDecomposition_iff`

English:
theorem not_haveLebesgueDecomposition_iff
  given: (s : SignedMeasure α) (μ : Measure α)
  proof: ⟨fun h => not_or_of_imp fun hp hn => h ⟨hp, hn⟩, fun h hl => (not_and_or.2 h) ⟨hl.1, hl.2⟩⟩

中文:
定理 not_haveLebesgueDecomposition_iff
  条件: (s : SignedMeasure α) (μ : Measure α)
  证明: ⟨fun h => not_or_of_imp fun hp hn => h ⟨hp, hn⟩, fun h hl => (not_and_or.2 h) ⟨hl.1, hl.2⟩⟩

Depends on / 依赖: not_and_or, not_or_of_imp
-/
theorem not_haveLebesgueDecomposition_iff (s : SignedMeasure α) (μ : Measure α) :
    ¬s.HaveLebesgueDecomposition μ ↔
      ¬s.toJordanDecomposition.posPart.HaveLebesgueDecomposition μ ∨
        ¬s.toJordanDecomposition.negPart.HaveLebesgueDecomposition μ :=
  ⟨fun h => not_or_of_imp fun hp hn => h ⟨hp, hn⟩, fun h hl => (not_and_or.2 h) ⟨hl.1, hl.2⟩⟩

-- `inferInstance` directly does not work
-- see Note [lower instance priority]
instance (priority := 100) haveLebesgueDecomposition_of_sigmaFinite (s : SignedMeasure α)
    (μ : Measure α) [SigmaFinite μ] : s.HaveLebesgueDecomposition μ where
  posPart := inferInstance
  negPart := inferInstance

/--
Instance `haveLebesgueDecomposition_neg` / 实例 `haveLebesgueDecomposition_neg`

English:
instance haveLebesgueDecomposition_neg
  signature: (s : SignedMeasure α) (μ : Measure α)
  body: by
    rw [toJordanDecomposition_neg]; rw [JordanDecomposition.neg_posPart]
    infer_instance
  negPart := by
    rw [toJordanDecomposition_neg]; rw [JordanDecomposition.neg_negPart]
    infer_instance

中文:
实例 haveLebesgueDecomposition_neg
  签名: (s : SignedMeasure α) (μ : Measure α)
  定义体: by
    rw [toJordanDecomposition_neg]; rw [JordanDecomposition.neg_posPart]
    infer_instance
  negPart := by
    rw [toJordanDecomposition_neg]; rw [JordanDecomposition.neg_negPart]
    infer_instance

Depends on / 依赖: JordanDecomposition, JordanDecomposition.neg_negPart, JordanDecomposition.neg_posPart, infer_instance, negPart, neg_negPart, neg_posPart, toJordanDecomposition_neg
-/
instance haveLebesgueDecomposition_neg (s : SignedMeasure α) (μ : Measure α)
    [s.HaveLebesgueDecomposition μ] : (-s).HaveLebesgueDecomposition μ where
  posPart := by
    rw [toJordanDecomposition_neg]; rw [JordanDecomposition.neg_posPart]
    infer_instance
  negPart := by
    rw [toJordanDecomposition_neg]; rw [JordanDecomposition.neg_negPart]
    infer_instance

/--
Instance `haveLebesgueDecomposition_smul` / 实例 `haveLebesgueDecomposition_smul`

English:
instance haveLebesgueDecomposition_smul
  signature: (s : SignedMeasure α) (μ : Measure α)
  body: by
    rw [toJordanDecomposition_smul]; rw [JordanDecomposition.smul_posPart]
    infer_instance
  negPart := by
    rw [toJordanDecomposition_smul]; rw [JordanDecomposition.smul_negPart]
    infer_instance

中文:
实例 haveLebesgueDecomposition_smul
  签名: (s : SignedMeasure α) (μ : Measure α)
  定义体: by
    rw [toJordanDecomposition_smul]; rw [JordanDecomposition.smul_posPart]
    infer_instance
  negPart := by
    rw [toJordanDecomposition_smul]; rw [JordanDecomposition.smul_negPart]
    infer_instance

Depends on / 依赖: JordanDecomposition, JordanDecomposition.smul_negPart, JordanDecomposition.smul_posPart, infer_instance, negPart, smul_negPart, smul_posPart, toJordanDecomposition_smul
-/
instance haveLebesgueDecomposition_smul (s : SignedMeasure α) (μ : Measure α)
    [s.HaveLebesgueDecomposition μ] (r : Real>=0) : (r • s).HaveLebesgueDecomposition μ where
  posPart := by
    rw [toJordanDecomposition_smul]; rw [JordanDecomposition.smul_posPart]
    infer_instance
  negPart := by
    rw [toJordanDecomposition_smul]; rw [JordanDecomposition.smul_negPart]
    infer_instance

/--
Instance `haveLebesgueDecomposition_smul_real` / 实例 `haveLebesgueDecomposition_smul_real`

English:
instance haveLebesgueDecomposition_smul_real
  signature: (s : SignedMeasure α) (μ : Measure α)
  body: by
  by_cases! hr : 0 <= r
  · lift r to Real>=0 using hr
    exact s.haveLebesgueDecomposition_smul μ _
  · refine
      { posPart := by
          rw [toJordanDecomposition_smul_real]; rw [JordanDecomposition.real_smul_posPart_neg _ _ hr]
          infer_instance
        negPart := by
          rw 

中文:
实例 haveLebesgueDecomposition_smul_real
  签名: (s : SignedMeasure α) (μ : Measure α)
  定义体: by
  by_cases! hr : 0 <= r
  · lift r to Real>=0 using hr
    exact s.haveLebesgueDecomposition_smul μ _
  · refine
      { posPart := by
          rw [toJordanDecomposition_smul_real]; rw [JordanDecomposition.real_smul_posPart_neg _ _ hr]
          infer_instance
        negPart := by
          rw 

Depends on / 依赖: JordanDecomposition, JordanDecomposition.real_smul_negPart_neg, JordanDecomposition.real_smul_posPart_neg, haveLebesgueDecomposition_smul, infer_instance, negPart, posPart, real_smul_negPart_neg, real_smul_posPart_neg, s.haveLebesgueDecomposition_smul, toJordanDecomposition_smul_real
-/
instance haveLebesgueDecomposition_smul_real (s : SignedMeasure α) (μ : Measure α)
    [s.HaveLebesgueDecomposition μ] (r : Real) : (r • s).HaveLebesgueDecomposition μ := by
  by_cases! hr : 0 <= r
  · lift r to Real>=0 using hr
    exact s.haveLebesgueDecomposition_smul μ _
  · refine
      { posPart := by
          rw [toJordanDecomposition_smul_real]; rw [JordanDecomposition.real_smul_posPart_neg _ _ hr]
          infer_instance
        negPart := by
          rw [toJordanDecomposition_smul_real]; rw [JordanDecomposition.real_smul_negPart_neg _ _ hr]
          infer_instance }

/--
Definition of `singularPart` / `singularPart` 的定义

English:
definition singularPart
  signature: (s : SignedMeasure α) (μ : Measure α)
  body: (s.toJordanDecomposition.posPart.singularPart μ).toSignedMeasure -
    (s.toJordanDecomposition.negPart.singularPart μ).toSignedMeasure

中文:
定义 singularPart
  签名: (s : SignedMeasure α) (μ : Measure α)
  定义体: (s.toJordanDecomposition.posPart.singularPart μ).toSignedMeasure -
    (s.toJordanDecomposition.negPart.singularPart μ).toSignedMeasure

Depends on / 依赖: negPart, posPart, s.toJordanDecomposition.negPart.singularPart, s.toJordanDecomposition.posPart.singularPart, singularPart, toJordanDecomposition, toSignedMeasure
-/
def singularPart (s : SignedMeasure α) (μ : Measure α) : SignedMeasure α :=
  (s.toJordanDecomposition.posPart.singularPart μ).toSignedMeasure -
    (s.toJordanDecomposition.negPart.singularPart μ).toSignedMeasure

section

/--
theorem `singularPart_mutuallySingular` / 定理 `singularPart_mutuallySingular`

English:
theorem singularPart_mutuallySingular
  given: (s : SignedMeasure α) (μ : Measure α)
  proof: (s.toJordanDecomposition.mutuallySingular.singularPart μ).mono le_rfl (singularPart_le _ _)

中文:
定理 singularPart_mutuallySingular
  条件: (s : SignedMeasure α) (μ : Measure α)
  证明: (s.toJordanDecomposition.mutuallySingular.singularPart μ).mono le_rfl (singularPart_le _ _)

Depends on / 依赖: le_rfl, mutuallySingular, s.toJordanDecomposition.mutuallySingular.singularPart, singularPart, singularPart_le, toJordanDecomposition
-/
theorem singularPart_mutuallySingular (s : SignedMeasure α) (μ : Measure α) :
    s.toJordanDecomposition.posPart.singularPart μ ⟂ₘ
      s.toJordanDecomposition.negPart.singularPart μ :=
  (s.toJordanDecomposition.mutuallySingular.singularPart μ).mono le_rfl (singularPart_le _ _)

/--
theorem `singularPart_totalVariation` / 定理 `singularPart_totalVariation`

English:
theorem singularPart_totalVariation
  given: (s : SignedMeasure α) (μ : Measure α)
  proof: by
  have :
    (s.singularPart μ).toJordanDecomposition =
      ⟨s.toJordanDecomposition.posPart.singularPart μ,
        s.toJordanDecomposition.negPart.singularPart μ, singularPart_mutuallySingular s μ⟩ := by
    refine JordanDecomposition.toSignedMeasure_injective ?_
    rw [toSignedMeasure_toJor

中文:
定理 singularPart_totalVariation
  条件: (s : SignedMeasure α) (μ : Measure α)
  证明: by
  have :
    (s.singularPart μ).toJordanDecomposition =
      ⟨s.toJordanDecomposition.posPart.singularPart μ,
        s.toJordanDecomposition.negPart.singularPart μ, singularPart_mutuallySingular s μ⟩ := by
    refine JordanDecomposition.toSignedMeasure_injective ?_
    rw [toSignedMeasure_toJor

Depends on / 依赖: JordanDecomposition, JordanDecomposition.toSignedMeasure, JordanDecomposition.toSignedMeasure_injective, negPart, posPart, s.singularPart, s.toJordanDecomposition.negPart.singularPart, s.toJordanDecomposition.posPart.singularPart, singularPart, singularPart_mutuallySingular, toJordanDecomposition, toSignedMeasure, toSignedMeasure_injective, toSignedMeasure_toJordanDecomposition, totalVariation
-/
theorem singularPart_totalVariation (s : SignedMeasure α) (μ : Measure α) :
    (s.singularPart μ).totalVariation =
      s.toJordanDecomposition.posPart.singularPart μ +
        s.toJordanDecomposition.negPart.singularPart μ := by
  have :
    (s.singularPart μ).toJordanDecomposition =
      ⟨s.toJordanDecomposition.posPart.singularPart μ,
        s.toJordanDecomposition.negPart.singularPart μ, singularPart_mutuallySingular s μ⟩ := by
    refine JordanDecomposition.toSignedMeasure_injective ?_
    rw [toSignedMeasure_toJordanDecomposition]; rw [singularPart]; rw [JordanDecomposition.toSignedMeasure]
  rw [totalVariation]; rw [this]

nonrec theorem mutuallySingular_singularPart (s : SignedMeasure α) (μ : Measure α) :
    singularPart s μ ⟂ᵥ μ.toENNRealVectorMeasure := by
  rw [mutuallySingular_ennreal_iff]; rw [singularPart_totalVariation]; rw [VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure]
  exact (mutuallySingular_singularPart _ _).add_left (mutuallySingular_singularPart _ _)

end

/--
Definition of `rnDeriv` / `rnDeriv` 的定义

English:
definition rnDeriv
  signature: (s : SignedMeasure α) (μ : Measure α)
  body: fun x =>
  (s.toJordanDecomposition.posPart.rnDeriv μ x).toReal -
    (s.toJordanDecomposition.negPart.rnDeriv μ x).toReal

中文:
定义 rnDeriv
  签名: (s : SignedMeasure α) (μ : Measure α)
  定义体: fun x =>
  (s.toJordanDecomposition.posPart.rnDeriv μ x).toReal -
    (s.toJordanDecomposition.negPart.rnDeriv μ x).toReal
-/
def rnDeriv (s : SignedMeasure α) (μ : Measure α) : α -> Real := fun x =>
  (s.toJordanDecomposition.posPart.rnDeriv μ x).toReal -
    (s.toJordanDecomposition.negPart.rnDeriv μ x).toReal

-- The generated equation theorem is the form of `rnDeriv s μ x = ...`.
/--
theorem `rnDeriv_def` / 定理 `rnDeriv_def`

English:
theorem rnDeriv_def
  given: (s : SignedMeasure α) (μ : Measure α)
  statement: rnDeriv s μ = fun x =>
  proof: rfl

中文:
定理 rnDeriv_def
  条件: (s : SignedMeasure α) (μ : Measure α)
  结论: rnDeriv s μ = fun x =>
  证明: rfl
-/
theorem rnDeriv_def (s : SignedMeasure α) (μ : Measure α) : rnDeriv s μ = fun x =>
    (s.toJordanDecomposition.posPart.rnDeriv μ x).toReal -
      (s.toJordanDecomposition.negPart.rnDeriv μ x).toReal :=
  rfl

variable {s t : SignedMeasure α}

@[fun_prop]
/--
theorem `measurable_rnDeriv` / 定理 `measurable_rnDeriv`

English:
theorem measurable_rnDeriv
  given: (s : SignedMeasure α) (μ : Measure α)
  statement: Measurable (rnDeriv s μ)
  proof: by
  rw [rnDeriv_def]
  fun_prop

中文:
定理 measurable_rnDeriv
  条件: (s : SignedMeasure α) (μ : Measure α)
  结论: Measurable (rnDeriv s μ)
  证明: by
  rw [rnDeriv_def]
  fun_prop

Depends on / 依赖: fun_prop, rnDeriv_def
-/
theorem measurable_rnDeriv (s : SignedMeasure α) (μ : Measure α) : Measurable (rnDeriv s μ) := by
  rw [rnDeriv_def]
  fun_prop

/--
theorem `integrable_rnDeriv` / 定理 `integrable_rnDeriv`

English:
theorem integrable_rnDeriv
  given: (s : SignedMeasure α) (μ : Measure α)
  statement: Integrable (rnDeriv s μ) μ
  proof: by
  refine Integrable.sub ?_ ?_ <;>
    · constructor
      · apply Measurable.aestronglyMeasurable
        fun_prop
      exact hasFiniteIntegral_toReal_of_lintegral_ne_top (lintegral_rnDeriv_lt_top _ μ).ne

中文:
定理 integrable_rnDeriv
  条件: (s : SignedMeasure α) (μ : Measure α)
  结论: 整数egrable (rnDeriv s μ) μ
  证明: by
  refine Integrable.sub ?_ ?_ <;>
    · constructor
      · apply Measurable.aestronglyMeasurable
        fun_prop
      exact hasFiniteIntegral_toReal_of_lintegral_ne_top (lintegral_rnDeriv_lt_top _ μ).ne

Depends on / 依赖: Integrable, Integrable.sub, Measurable, Measurable.aestronglyMeasurable, aestronglyMeasurable, fun_prop, hasFiniteIntegral_toReal_of_lintegral_ne_top, lintegral_rnDeriv_lt_top
-/
theorem integrable_rnDeriv (s : SignedMeasure α) (μ : Measure α) : Integrable (rnDeriv s μ) μ := by
  refine Integrable.sub ?_ ?_ <;>
    · constructor
      · apply Measurable.aestronglyMeasurable
        fun_prop
      exact hasFiniteIntegral_toReal_of_lintegral_ne_top (lintegral_rnDeriv_lt_top _ μ).ne

variable (s μ)

/--
theorem `singularPart_add_withDensity_rnDeriv_eq` / 定理 `singularPart_add_withDensity_rnDeriv_eq`

English:
theorem singularPart_add_withDensity_rnDeriv_eq
  given: [s.HaveLebesgueDecomposition μ]
  proof: by
  conv_rhs =>
    rw [← toSignedMeasure_toJordanDecomposition s]; rw [JordanDecomposition.toSignedMeasure]
  rw [singularPart]; rw [rnDeriv_def]; rw [withDensityᵥ_sub' (integrable_toReal_of_lintegral_ne_top _ _)
      (integrable_toReal_of_lintegral_ne_top _ _)]; rw [withDensityᵥ_toReal]; rw [wit

中文:
定理 singularPart_add_withDensity_rnDeriv_eq
  条件: [s.HaveLebesgueDecomposition μ]
  证明: by
  conv_rhs =>
    rw [← toSignedMeasure_toJordanDecomposition s]; rw [JordanDecomposition.toSignedMeasure]
  rw [singularPart]; rw [rnDeriv_def]; rw [withDensityᵥ_sub' (integrable_toReal_of_lintegral_ne_top _ _)
      (integrable_toReal_of_lintegral_ne_top _ _)]; rw [withDensityᵥ_toReal]; rw [wit

Depends on / 依赖: JordanDecomposition, JordanDecomposition.toSignedMeasure, add_assoc, add_comm, conv_rhs, integrable_toReal_of_lintegral_ne_top, negPart, posPart, rnDeriv_def, s.toJordanDecomposition.negPart.singul, s.toJordanDecomposition.posPart.singularPart, singul, singularPart, sub_eq_add_neg, toJordanDecomposition, toSignedMeasure, toSignedMeasure_toJordanDecomposition
-/
theorem singularPart_add_withDensity_rnDeriv_eq [s.HaveLebesgueDecomposition μ] :
    s.singularPart μ + μ.withDensityᵥ (s.rnDeriv μ) = s := by
  conv_rhs =>
    rw [← toSignedMeasure_toJordanDecomposition s]; rw [JordanDecomposition.toSignedMeasure]
  rw [singularPart]; rw [rnDeriv_def]; rw [withDensityᵥ_sub' (integrable_toReal_of_lintegral_ne_top _ _)
      (integrable_toReal_of_lintegral_ne_top _ _)]; rw [withDensityᵥ_toReal]; rw [withDensityᵥ_toReal]; rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [add_comm (s.toJordanDecomposition.posPart.singularPart μ).toSignedMeasure]; rw [← add_assoc]; rw [add_assoc (-(s.toJordanDecomposition.negPart.singularPart μ).toSignedMeasure)]; rw [← toSignedMeasure_add]; rw [add_comm]; rw [← add_assoc]; rw [← neg_add]; rw [← toSignedMeasure_add]; rw [add_comm]; rw [← sub_eq_add_neg]
  · convert! rfl
    -- `convert rfl` much faster than `congr`
    · exact s.toJordanDecomposition.posPart.haveLebesgueDecomposition_add μ
    · rw [add_comm]
      exact s.toJordanDecomposition.negPart.haveLebesgueDecomposition_add μ
  all_goals
    first
    | exact (lintegral_rnDeriv_lt_top _ _).ne
    | measurability

variable {s μ}

/--
theorem `jordanDecomposition_add_withDensity_mutuallySingular` / 定理 `jordanDecomposition_add_withDensity_mutuallySingular`

English:
theorem jordanDecomposition_add_withDensity_mutuallySingular
  statement: {f : α -> Real} (hf : Measurable f)
  proof: by
  rw [mutuallySingular_ennreal_iff]; rw [totalVariation_mutuallySingular_iff]; rw [VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure] at htμ
  exact
    ((JordanDecomposition.mutuallySingular _).add_right
          (htμ.1.mono_ac (refl _) (withDensity_absolutelyContinuous _ _))).add_left
    

中文:
定理 jordanDecomposition_add_withDensity_mutuallySingular
  结论: {f : α -> 实数} (hf : Measurable f)
  证明: by
  rw [mutuallySingular_ennreal_iff]; rw [totalVariation_mutuallySingular_iff]; rw [VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure] at htμ
  exact
    ((JordanDecomposition.mutuallySingular _).add_right
          (htμ.1.mono_ac (refl _) (withDensity_absolutelyContinuous _ _))).add_left
    

Depends on / 依赖: JordanDecomposition, JordanDecomposition.mutuallySingular, VectorMeasure, VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure, add_left, add_right, ennrealToMeasure_toENNRealVectorMeasure, mono_ac, mutuallySingular, mutuallySingular_ennreal_iff, symm.mono_ac, totalVariation_mutuallySingular_iff, withDensity_absolutelyContinuous, withDensity_ofReal_mutuallySingular
-/
theorem jordanDecomposition_add_withDensity_mutuallySingular {f : α -> Real} (hf : Measurable f)
    (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) :
    (t.toJordanDecomposition.posPart + μ.withDensity fun x : α => ENNReal.ofReal (f x)) ⟂ₘ
      t.toJordanDecomposition.negPart + μ.withDensity fun x : α => ENNReal.ofReal (-f x) := by
  rw [mutuallySingular_ennreal_iff]; rw [totalVariation_mutuallySingular_iff]; rw [VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure] at htμ
  exact
    ((JordanDecomposition.mutuallySingular _).add_right
          (htμ.1.mono_ac (refl _) (withDensity_absolutelyContinuous _ _))).add_left
      ((htμ.2.symm.mono_ac (withDensity_absolutelyContinuous _ _) (refl _)).add_right
        (withDensity_ofReal_mutuallySingular hf))

/--
theorem `toJordanDecomposition_eq_of_eq_add_withDensity` / 定理 `toJordanDecomposition_eq_of_eq_add_withDensity`

English:
theorem toJordanDecomposition_eq_of_eq_add_withDensity
  statement: {f : α -> Real} (hf : Measurable f)
  proof: by
  have := isFiniteMeasure_withDensity_ofReal hfi.2
  have := isFiniteMeasure_withDensity_ofReal hfi.neg.2
  refine toJordanDecomposition_eq ?_
  simp_rw [JordanDecomposition.toSignedMeasure, hadd]
  ext i hi
  rw [_root_.sub_apply]; rw [toSignedMeasure_apply_measurable hi]; rw [toSignedMeasure_ap

中文:
定理 toJordanDecomposition_eq_of_eq_add_withDensity
  结论: {f : α -> 实数} (hf : Measurable f)
  证明: by
  have := isFiniteMeasure_withDensity_ofReal hfi.2
  have := isFiniteMeasure_withDensity_ofReal hfi.neg.2
  refine toJordanDecomposition_eq ?_
  simp_rw [JordanDecomposition.toSignedMeasure, hadd]
  ext i hi
  rw [_root_.sub_apply]; rw [toSignedMeasure_apply_measurable hi]; rw [toSignedMeasure_ap

Depends on / 依赖: infer_instance, isFiniteMeasure_withDensity_ofReal
-/
theorem toJordanDecomposition_eq_of_eq_add_withDensity {f : α -> Real} (hf : Measurable f)
    (hfi : Integrable f μ) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) :
    s.toJordanDecomposition =
      @JordanDecomposition.mk α _
        (t.toJordanDecomposition.posPart + μ.withDensity fun x => ENNReal.ofReal (f x))
        (t.toJordanDecomposition.negPart + μ.withDensity fun x => ENNReal.ofReal (-f x))
        (by have := isFiniteMeasure_withDensity_ofReal hfi.2; infer_instance)
        (by have := isFiniteMeasure_withDensity_ofReal hfi.neg.2; infer_instance)
        (jordanDecomposition_add_withDensity_mutuallySingular hf htμ) := by
  have := isFiniteMeasure_withDensity_ofReal hfi.2
  have := isFiniteMeasure_withDensity_ofReal hfi.neg.2
  refine toJordanDecomposition_eq ?_
  simp_rw [JordanDecomposition.toSignedMeasure, hadd]
  ext i hi
  rw [_root_.sub_apply]; rw [toSignedMeasure_apply_measurable hi]; rw [toSignedMeasure_apply_measurable hi]; rw [measureReal_add_apply]; rw [measureReal_add_apply]; rw [add_sub_add_comm]; rw [← toSignedMeasure_apply_measurable hi]; rw [← toSignedMeasure_apply_measurable hi]; rw [← _root_.sub_apply]; rw [← JordanDecomposition.toSignedMeasure]; rw [toSignedMeasure_toJordanDecomposition]; rw [_root_.add_apply]; rw [← toSignedMeasure_apply_measurable hi]; rw [← toSignedMeasure_apply_measurable hi]; rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hfi]; rw [_root_.sub_apply]

/--
theorem `haveLebesgueDecomposition_mk'` / 定理 `haveLebesgueDecomposition_mk'`

English:
theorem haveLebesgueDecomposition_mk'
  statement: (μ : Measure α) {f : α -> Real} (hf : Measurable f)
  proof: by
  have htμ' := htμ
  rw [mutuallySingular_ennreal_iff] at htμ
  change _ ⟂ₘ VectorMeasure.equivMeasure.toFun (VectorMeasure.equivMeasure.invFun μ) at htμ
  rw [VectorMeasure.equivMeasure.right_inv]; rw [totalVariation_mutuallySingular_iff] at htμ
  refine
    { posPart := by
        use ⟨t.toJord

中文:
定理 haveLebesgueDecomposition_mk'
  结论: (μ : Measure α) {f : α -> 实数} (hf : Measurable f)
  证明: by
  have htμ' := htμ
  rw [mutuallySingular_ennreal_iff] at htμ
  change _ ⟂ₘ VectorMeasure.equivMeasure.toFun (VectorMeasure.equivMeasure.invFun μ) at htμ
  rw [VectorMeasure.equivMeasure.right_inv]; rw [totalVariation_mutuallySingular_iff] at htμ
  refine
    { posPart := by
        use ⟨t.toJord
-/
private theorem haveLebesgueDecomposition_mk' (μ : Measure α) {f : α -> Real} (hf : Measurable f)
    (hfi : Integrable f μ) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) :
    s.HaveLebesgueDecomposition μ := by
  have htμ' := htμ
  rw [mutuallySingular_ennreal_iff] at htμ
  change _ ⟂ₘ VectorMeasure.equivMeasure.toFun (VectorMeasure.equivMeasure.invFun μ) at htμ
  rw [VectorMeasure.equivMeasure.right_inv]; rw [totalVariation_mutuallySingular_iff] at htμ
  refine
    { posPart := by
        use ⟨t.toJordanDecomposition.posPart, fun x => ENNReal.ofReal (f x)⟩
        refine ⟨hf.ennreal_ofReal, htμ.1, ?_⟩
        rw [toJordanDecomposition_eq_of_eq_add_withDensity hf hfi htμ' hadd]
      negPart := by
        use ⟨t.toJordanDecomposition.negPart, fun x => ENNReal.ofReal (-f x)⟩
        refine ⟨hf.neg.ennreal_ofReal, htμ.2, ?_⟩
        rw [toJordanDecomposition_eq_of_eq_add_withDensity hf hfi htμ' hadd] }

/--
theorem `haveLebesgueDecomposition_mk` / 定理 `haveLebesgueDecomposition_mk`

English:
theorem haveLebesgueDecomposition_mk
  statement: (μ : Measure α) {f : α -> Real} (hf : Measurable f)
  proof: by
  by_cases hfi : Integrable f μ
  · exact haveLebesgueDecomposition_mk' μ hf hfi htμ hadd
  · rw [withDensityᵥ, dif_neg hfi, add_zero] at hadd
    refine haveLebesgueDecomposition_mk' μ measurable_zero (integrable_zero _ _ μ) htμ ?_
    rwa [withDensityᵥ_zero, add_zero]

中文:
定理 haveLebesgueDecomposition_mk
  结论: (μ : Measure α) {f : α -> 实数} (hf : Measurable f)
  证明: by
  by_cases hfi : Integrable f μ
  · exact haveLebesgueDecomposition_mk' μ hf hfi htμ hadd
  · rw [withDensityᵥ, dif_neg hfi, add_zero] at hadd
    refine haveLebesgueDecomposition_mk' μ measurable_zero (integrable_zero _ _ μ) htμ ?_
    rwa [withDensityᵥ_zero, add_zero]

Depends on / 依赖: Integrable, add_zero, dif_neg, haveLebesgueDecomposition_mk, integrable_zero, measurable_zero
-/
theorem haveLebesgueDecomposition_mk (μ : Measure α) {f : α -> Real} (hf : Measurable f)
    (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) :
    s.HaveLebesgueDecomposition μ := by
  by_cases hfi : Integrable f μ
  · exact haveLebesgueDecomposition_mk' μ hf hfi htμ hadd
  · rw [withDensityᵥ, dif_neg hfi, add_zero] at hadd
    refine haveLebesgueDecomposition_mk' μ measurable_zero (integrable_zero _ _ μ) htμ ?_
    rwa [withDensityᵥ_zero, add_zero]

/--
theorem `eq_singularPart'` / 定理 `eq_singularPart'`

English:
theorem eq_singularPart'
  statement: (t : SignedMeasure α) {f : α -> Real} (hf : Measurable f)
  proof: by
  have htμ' := htμ
  rw [mutuallySingular_ennreal_iff]; rw [totalVariation_mutuallySingular_iff]; rw [VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure] at htμ
  rw [singularPart]; rw [← t.toSignedMeasure_toJordanDecomposition]; rw [JordanDecomposition.toSignedMeasure]
  congr
  · have hfpos 

中文:
定理 eq_singularPart'
  结论: (t : SignedMeasure α) {f : α -> 实数} (hf : Measurable f)
  证明: by
  have htμ' := htμ
  rw [mutuallySingular_ennreal_iff]; rw [totalVariation_mutuallySingular_iff]; rw [VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure] at htμ
  rw [singularPart]; rw [← t.toSignedMeasure_toJordanDecomposition]; rw [JordanDecomposition.toSignedMeasure]
  congr
  · have hfpos 
-/
private theorem eq_singularPart' (t : SignedMeasure α) {f : α -> Real} (hf : Measurable f)
    (hfi : Integrable f μ) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) :
    t = s.singularPart μ := by
  have htμ' := htμ
  rw [mutuallySingular_ennreal_iff]; rw [totalVariation_mutuallySingular_iff]; rw [VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure] at htμ
  rw [singularPart]; rw [← t.toSignedMeasure_toJordanDecomposition]; rw [JordanDecomposition.toSignedMeasure]
  congr
  · have hfpos : Measurable fun x => ENNReal.ofReal (f x) := by fun_prop
    refine eq_singularPart hfpos htμ.1 ?_
    rw [toJordanDecomposition_eq_of_eq_add_withDensity hf hfi htμ' hadd]
  · have hfneg : Measurable fun x => ENNReal.ofReal (-f x) := by fun_prop
    refine eq_singularPart hfneg htμ.2 ?_
    rw [toJordanDecomposition_eq_of_eq_add_withDensity hf hfi htμ' hadd]

/--
theorem `eq_singularPart` / 定理 `eq_singularPart`

English:
theorem eq_singularPart
  statement: (t : SignedMeasure α) (f : α -> Real) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure)
  proof: by
  by_cases hfi : Integrable f μ
  · refine eq_singularPart' t hfi.1.measurable_mk (hfi.congr hfi.1.ae_eq_mk) htμ ?_
    convert! hadd using 2
    exact WithDensityᵥEq.congr_ae hfi.1.ae_eq_mk.symm
  · rw [withDensityᵥ, dif_neg hfi, add_zero] at hadd
    refine eq_singularPart' t measurable_zero (i

中文:
定理 eq_singularPart
  结论: (t : SignedMeasure α) (f : α -> 实数) (htμ : t ⟂ᵥ μ.toENN实数VectorMeasure)
  证明: by
  by_cases hfi : Integrable f μ
  · refine eq_singularPart' t hfi.1.measurable_mk (hfi.congr hfi.1.ae_eq_mk) htμ ?_
    convert! hadd using 2
    exact WithDensityᵥEq.congr_ae hfi.1.ae_eq_mk.symm
  · rw [withDensityᵥ, dif_neg hfi, add_zero] at hadd
    refine eq_singularPart' t measurable_zero (i

Depends on / 依赖: Eq.congr_ae, Integrable, add_zero, ae_eq_mk, ae_eq_mk.symm, congr_ae, convert, dif_neg, eq_singularPart, hfi.congr, integrable_zero, measurable_mk, measurable_zero
-/
theorem eq_singularPart (t : SignedMeasure α) (f : α -> Real) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure)
    (hadd : s = t + μ.withDensityᵥ f) : t = s.singularPart μ := by
  by_cases hfi : Integrable f μ
  · refine eq_singularPart' t hfi.1.measurable_mk (hfi.congr hfi.1.ae_eq_mk) htμ ?_
    convert! hadd using 2
    exact WithDensityᵥEq.congr_ae hfi.1.ae_eq_mk.symm
  · rw [withDensityᵥ, dif_neg hfi, add_zero] at hadd
    refine eq_singularPart' t measurable_zero (integrable_zero _ _ μ) htμ ?_
    rwa [withDensityᵥ_zero, add_zero]

/--
theorem `singularPart_zero` / 定理 `singularPart_zero`

English:
theorem singularPart_zero
  given: (μ : Measure α)
  statement: (0 : SignedMeasure α).singularPart μ = 0
  proof: by
  refine (eq_singularPart 0 0 VectorMeasure.MutuallySingular.zero_left ?_).symm
  rw [zero_add]; rw [withDensityᵥ_zero]

中文:
定理 singularPart_zero
  条件: (μ : Measure α)
  结论: (0 : SignedMeasure α).singularPart μ = 0
  证明: by
  refine (eq_singularPart 0 0 VectorMeasure.MutuallySingular.zero_left ?_).symm
  rw [zero_add]; rw [withDensityᵥ_zero]

Depends on / 依赖: MutuallySingular, VectorMeasure, VectorMeasure.MutuallySingular.zero_left, eq_singularPart, zero_add, zero_left
-/
theorem singularPart_zero (μ : Measure α) : (0 : SignedMeasure α).singularPart μ = 0 := by
  refine (eq_singularPart 0 0 VectorMeasure.MutuallySingular.zero_left ?_).symm
  rw [zero_add]; rw [withDensityᵥ_zero]

/--
theorem `singularPart_neg` / 定理 `singularPart_neg`

English:
theorem singularPart_neg
  given: (s : SignedMeasure α) (μ : Measure α)
  proof: by
  simp [singularPart, toJordanDecomposition_neg]

中文:
定理 singularPart_neg
  条件: (s : SignedMeasure α) (μ : Measure α)
  证明: by
  simp [singularPart, toJordanDecomposition_neg]

Depends on / 依赖: singularPart, toJordanDecomposition_neg
-/
theorem singularPart_neg (s : SignedMeasure α) (μ : Measure α) :
    (-s).singularPart μ = -s.singularPart μ := by
  simp [singularPart, toJordanDecomposition_neg]

/--
theorem `singularPart_smul_nnreal` / 定理 `singularPart_smul_nnreal`

English:
theorem singularPart_smul_nnreal
  given: (s : SignedMeasure α) (μ : Measure α) (r : Real>=0)
  proof: by
  rw [singularPart]; rw [singularPart]; rw [smul_sub]; rw [← toSignedMeasure_smul]; rw [← toSignedMeasure_smul]
  conv_lhs =>
    congr
    · congr
      · rw [toJordanDecomposition_smul, JordanDecomposition.smul_posPart, singularPart_smul]
    · congr
      rw [toJordanDecomposition_smul]; rw [J

中文:
定理 singularPart_smul_nnreal
  条件: (s : SignedMeasure α) (μ : Measure α) (r : 实数>=0)
  证明: by
  rw [singularPart]; rw [singularPart]; rw [smul_sub]; rw [← toSignedMeasure_smul]; rw [← toSignedMeasure_smul]
  conv_lhs =>
    congr
    · congr
      · rw [toJordanDecomposition_smul, JordanDecomposition.smul_posPart, singularPart_smul]
    · congr
      rw [toJordanDecomposition_smul]; rw [J

Depends on / 依赖: JordanDecomposition, JordanDecomposition.smul_negPart, JordanDecomposition.smul_posPart, conv_lhs, singularPart, singularPart_smul, smul_negPart, smul_posPart, smul_sub, toJordanDecomposition_smul, toSignedMeasure_smul
-/
theorem singularPart_smul_nnreal (s : SignedMeasure α) (μ : Measure α) (r : Real>=0) :
    (r • s).singularPart μ = r • s.singularPart μ := by
  rw [singularPart]; rw [singularPart]; rw [smul_sub]; rw [← toSignedMeasure_smul]; rw [← toSignedMeasure_smul]
  conv_lhs =>
    congr
    · congr
      · rw [toJordanDecomposition_smul, JordanDecomposition.smul_posPart, singularPart_smul]
    · congr
      rw [toJordanDecomposition_smul]; rw [JordanDecomposition.smul_negPart]; rw [singularPart_smul]

nonrec theorem singularPart_smul (s : SignedMeasure α) (μ : Measure α) (r : Real) :
    (r • s).singularPart μ = r • s.singularPart μ := by
  cases le_or_gt 0 r with
  | inl hr =>
    lift r to Real>=0 using hr
    exact singularPart_smul_nnreal s μ r
  | inr hr =>
    rw [singularPart]; rw [singularPart]
    conv_lhs =>
      congr
      · congr
        · rw [toJordanDecomposition_smul_real,
            JordanDecomposition.real_smul_posPart_neg _ _ hr, singularPart_smul]
      · congr
        · rw [toJordanDecomposition_smul_real,
            JordanDecomposition.real_smul_negPart_neg _ _ hr, singularPart_smul]
    rw [toSignedMeasure_smul]; rw [toSignedMeasure_smul]; rw [← neg_sub]; rw [← smul_sub]; rw [NNReal.smul_def]; rw [← neg_smul]; rw [Real.coe_toNNReal _ (le_of_lt (neg_pos.mpr hr))]; rw [neg_neg]

/--
theorem `singularPart_add` / 定理 `singularPart_add`

English:
theorem singularPart_add
  statement: (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
  proof: by
  refine
    (eq_singularPart _ (s.rnDeriv μ + t.rnDeriv μ)
        ((mutuallySingular_singularPart s μ).add_left (mutuallySingular_singularPart t μ))
        ?_).symm
  rw [withDensityᵥ_add (integrable_rnDeriv s μ) (integrable_rnDeriv t μ)]; rw [add_assoc]; rw [add_comm (t.singularPart μ)]; rw [

中文:
定理 singularPart_add
  结论: (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
  证明: by
  refine
    (eq_singularPart _ (s.rnDeriv μ + t.rnDeriv μ)
        ((mutuallySingular_singularPart s μ).add_left (mutuallySingular_singularPart t μ))
        ?_).symm
  rw [withDensityᵥ_add (integrable_rnDeriv s μ) (integrable_rnDeriv t μ)]; rw [add_assoc]; rw [add_comm (t.singularPart μ)]; rw [

Depends on / 依赖: add_assoc, add_comm, add_left, eq_singularPart, integrable_rnDeriv, mutuallySingular_singularPart, rnDeriv, s.rnDeriv, singularPart, singularPart_add_withDensity_rnDeriv_eq, t.rnDeriv, t.singularPart
-/
theorem singularPart_add (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
    [t.HaveLebesgueDecomposition μ] :
    (s + t).singularPart μ = s.singularPart μ + t.singularPart μ := by
  refine
    (eq_singularPart _ (s.rnDeriv μ + t.rnDeriv μ)
        ((mutuallySingular_singularPart s μ).add_left (mutuallySingular_singularPart t μ))
        ?_).symm
  rw [withDensityᵥ_add (integrable_rnDeriv s μ) (integrable_rnDeriv t μ)]; rw [add_assoc]; rw [add_comm (t.singularPart μ)]; rw [add_assoc]; rw [add_comm _ (t.singularPart μ)]; rw [singularPart_add_withDensity_rnDeriv_eq]; rw [← add_assoc]; rw [singularPart_add_withDensity_rnDeriv_eq]

/--
theorem `singularPart_sub` / 定理 `singularPart_sub`

English:
theorem singularPart_sub
  statement: (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
  proof: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [singularPart_add]; rw [singularPart_neg]

中文:
定理 singularPart_sub
  结论: (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
  证明: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [singularPart_add]; rw [singularPart_neg]

Depends on / 依赖: singularPart_add, singularPart_neg, sub_eq_add_neg
-/
theorem singularPart_sub (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
    [t.HaveLebesgueDecomposition μ] :
    (s - t).singularPart μ = s.singularPart μ - t.singularPart μ := by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [singularPart_add]; rw [singularPart_neg]

/--
theorem `eq_rnDeriv` / 定理 `eq_rnDeriv`

English:
theorem eq_rnDeriv
  statement: (t : SignedMeasure α) (f : α -> Real) (hfi : Integrable f μ)
  proof: by
  set f' := hfi.1.mk f
  have hadd' : s = t + μ.withDensityᵥ f' := by
    convert! hadd using 2
    exact WithDensityᵥEq.congr_ae hfi.1.ae_eq_mk.symm
  have := haveLebesgueDecomposition_mk μ hfi.1.measurable_mk htμ hadd'
  refine (Integrable.ae_eq_of_withDensityᵥ_eq (integrable_rnDeriv _ _) hfi ?

中文:
定理 eq_rnDeriv
  结论: (t : SignedMeasure α) (f : α -> 实数) (hfi : 整数egrable f μ)
  证明: by
  set f' := hfi.1.mk f
  have hadd' : s = t + μ.withDensityᵥ f' := by
    convert! hadd using 2
    exact WithDensityᵥEq.congr_ae hfi.1.ae_eq_mk.symm
  have := haveLebesgueDecomposition_mk μ hfi.1.measurable_mk htμ hadd'
  refine (Integrable.ae_eq_of_withDensityᵥ_eq (integrable_rnDeriv _ _) hfi ?

Depends on / 依赖: Eq.congr_ae, Integrable, Integrable.ae_eq_of_withDensity, add_right_inj, ae_eq_mk, ae_eq_mk.symm, congr_ae, convert, eq_singularPart, haveLebesgueDecomposition_mk, integrable_rnDeriv, measurable_mk, singularPart_add_withDensity_rnDeriv_eq
-/
theorem eq_rnDeriv (t : SignedMeasure α) (f : α -> Real) (hfi : Integrable f μ)
    (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) :
    f =ᵐ[μ] s.rnDeriv μ := by
  set f' := hfi.1.mk f
  have hadd' : s = t + μ.withDensityᵥ f' := by
    convert! hadd using 2
    exact WithDensityᵥEq.congr_ae hfi.1.ae_eq_mk.symm
  have := haveLebesgueDecomposition_mk μ hfi.1.measurable_mk htμ hadd'
  refine (Integrable.ae_eq_of_withDensityᵥ_eq (integrable_rnDeriv _ _) hfi ?_).symm
  rw [← add_right_inj t]; rw [← hadd]; rw [eq_singularPart _ f htμ hadd]; rw [singularPart_add_withDensity_rnDeriv_eq]

/--
theorem `rnDeriv_neg` / 定理 `rnDeriv_neg`

English:
theorem rnDeriv_neg
  given: (s : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
  proof: by
  refine
    Integrable.ae_eq_of_withDensityᵥ_eq (integrable_rnDeriv _ _) (integrable_rnDeriv _ _).neg ?_
  rw [withDensityᵥ_neg]; rw [← add_right_inj ((-s).singularPart μ)]; rw [singularPart_add_withDensity_rnDeriv_eq]; rw [singularPart_neg]; rw [← neg_add]; rw [singularPart_add_withDensity_rnDe

中文:
定理 rnDeriv_neg
  条件: (s : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
  证明: by
  refine
    Integrable.ae_eq_of_withDensityᵥ_eq (integrable_rnDeriv _ _) (integrable_rnDeriv _ _).neg ?_
  rw [withDensityᵥ_neg]; rw [← add_right_inj ((-s).singularPart μ)]; rw [singularPart_add_withDensity_rnDeriv_eq]; rw [singularPart_neg]; rw [← neg_add]; rw [singularPart_add_withDensity_rnDe

Depends on / 依赖: Integrable, Integrable.ae_eq_of_withDensity, add_right_inj, integrable_rnDeriv, neg_add, singularPart, singularPart_add_withDensity_rnDeriv_eq, singularPart_neg
-/
theorem rnDeriv_neg (s : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ] :
    (-s).rnDeriv μ =ᵐ[μ] -s.rnDeriv μ := by
  refine
    Integrable.ae_eq_of_withDensityᵥ_eq (integrable_rnDeriv _ _) (integrable_rnDeriv _ _).neg ?_
  rw [withDensityᵥ_neg]; rw [← add_right_inj ((-s).singularPart μ)]; rw [singularPart_add_withDensity_rnDeriv_eq]; rw [singularPart_neg]; rw [← neg_add]; rw [singularPart_add_withDensity_rnDeriv_eq]

/--
theorem `rnDeriv_smul` / 定理 `rnDeriv_smul`

English:
theorem rnDeriv_smul
  given: (s : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ] (r : Real)
  proof: by
  refine
    Integrable.ae_eq_of_withDensityᵥ_eq (integrable_rnDeriv _ _)
      ((integrable_rnDeriv _ _).smul r) ?_
  rw [withDensityᵥ_smul (rnDeriv s μ) r]; rw [← add_right_inj ((r • s).singularPart μ)]; rw [singularPart_add_withDensity_rnDeriv_eq]; rw [singularPart_smul]; rw [← smul_add]; rw [

中文:
定理 rnDeriv_smul
  条件: (s : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ] (r : 实数)
  证明: by
  refine
    Integrable.ae_eq_of_withDensityᵥ_eq (integrable_rnDeriv _ _)
      ((integrable_rnDeriv _ _).smul r) ?_
  rw [withDensityᵥ_smul (rnDeriv s μ) r]; rw [← add_right_inj ((r • s).singularPart μ)]; rw [singularPart_add_withDensity_rnDeriv_eq]; rw [singularPart_smul]; rw [← smul_add]; rw [

Depends on / 依赖: Integrable, Integrable.ae_eq_of_withDensity, add_right_inj, integrable_rnDeriv, rnDeriv, singularPart, singularPart_add_withDensity_rnDeriv_eq, singularPart_smul, smul_add
-/
theorem rnDeriv_smul (s : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ] (r : Real) :
    (r • s).rnDeriv μ =ᵐ[μ] r • s.rnDeriv μ := by
  refine
    Integrable.ae_eq_of_withDensityᵥ_eq (integrable_rnDeriv _ _)
      ((integrable_rnDeriv _ _).smul r) ?_
  rw [withDensityᵥ_smul (rnDeriv s μ) r]; rw [← add_right_inj ((r • s).singularPart μ)]; rw [singularPart_add_withDensity_rnDeriv_eq]; rw [singularPart_smul]; rw [← smul_add]; rw [singularPart_add_withDensity_rnDeriv_eq]

/--
theorem `rnDeriv_add` / 定理 `rnDeriv_add`

English:
theorem rnDeriv_add
  statement: (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
  proof: by
  refine
    Integrable.ae_eq_of_withDensityᵥ_eq (integrable_rnDeriv _ _)
      ((integrable_rnDeriv _ _).add (integrable_rnDeriv _ _)) ?_
  rw [← add_right_inj ((s + t).singularPart μ)]; rw [singularPart_add_withDensity_rnDeriv_eq]; rw [withDensityᵥ_add (integrable_rnDeriv _ _) (integrable_rnDer

中文:
定理 rnDeriv_add
  结论: (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
  证明: by
  refine
    Integrable.ae_eq_of_withDensityᵥ_eq (integrable_rnDeriv _ _)
      ((integrable_rnDeriv _ _).add (integrable_rnDeriv _ _)) ?_
  rw [← add_right_inj ((s + t).singularPart μ)]; rw [singularPart_add_withDensity_rnDeriv_eq]; rw [withDensityᵥ_add (integrable_rnDeriv _ _) (integrable_rnDer

Depends on / 依赖: Integrable, Integrable.ae_eq_of_withDensity, add_assoc, add_comm, add_right_inj, integrable_rnDeriv, singularPar, singularPart, singularPart_add, singularPart_add_withDensity_rnDeriv_eq, t.singularPart
-/
theorem rnDeriv_add (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
    [t.HaveLebesgueDecomposition μ] [(s + t).HaveLebesgueDecomposition μ] :
    (s + t).rnDeriv μ =ᵐ[μ] s.rnDeriv μ + t.rnDeriv μ := by
  refine
    Integrable.ae_eq_of_withDensityᵥ_eq (integrable_rnDeriv _ _)
      ((integrable_rnDeriv _ _).add (integrable_rnDeriv _ _)) ?_
  rw [← add_right_inj ((s + t).singularPart μ)]; rw [singularPart_add_withDensity_rnDeriv_eq]; rw [withDensityᵥ_add (integrable_rnDeriv _ _) (integrable_rnDeriv _ _)]; rw [singularPart_add]; rw [add_assoc]; rw [add_comm (t.singularPart μ)]; rw [add_assoc]; rw [add_comm _ (t.singularPart μ)]; rw [singularPart_add_withDensity_rnDeriv_eq]; rw [← add_assoc]; rw [singularPart_add_withDensity_rnDeriv_eq]

/--
theorem `rnDeriv_sub` / 定理 `rnDeriv_sub`

English:
theorem rnDeriv_sub
  statement: (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
  proof: by
  rw [sub_eq_add_neg] at hst
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]
  grw [rnDeriv_add, rnDeriv_neg]

中文:
定理 rnDeriv_sub
  结论: (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
  证明: by
  rw [sub_eq_add_neg] at hst
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]
  grw [rnDeriv_add, rnDeriv_neg]

Depends on / 依赖: rnDeriv_add, rnDeriv_neg, sub_eq_add_neg
-/
theorem rnDeriv_sub (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
    [t.HaveLebesgueDecomposition μ] [hst : (s - t).HaveLebesgueDecomposition μ] :
    (s - t).rnDeriv μ =ᵐ[μ] s.rnDeriv μ - t.rnDeriv μ := by
  rw [sub_eq_add_neg] at hst
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]
  grw [rnDeriv_add, rnDeriv_neg]

end SignedMeasure

namespace ComplexMeasure

/--
Definition of `HaveLebesgueDecomposition` / `HaveLebesgueDecomposition` 的定义

English:
class HaveLebesgueDecomposition
  parameters: (c : ComplexMeasure α) (μ : Measure α)
  axioms and operations (2):
    - rePart : c.re.HaveLebesgueDecomposition μ
    - imPart : c.im.HaveLebesgueDecomposition μ

中文:
类 HaveLebesgueDecomposition
  参数: (c : ComplexMeasure α) (μ : Measure α)
  公理与运算 (2 个):
    - rePart : c.re.HaveLebesgueDecomposition μ
    - imPart : c.im.HaveLebesgueDecomposition μ
-/
class HaveLebesgueDecomposition (c : ComplexMeasure α) (μ : Measure α) : Prop where
  rePart : c.re.HaveLebesgueDecomposition μ
  imPart : c.im.HaveLebesgueDecomposition μ

attribute [instance] HaveLebesgueDecomposition.rePart

attribute [instance] HaveLebesgueDecomposition.imPart

/--
Definition of `singularPart` / `singularPart` 的定义

English:
definition singularPart
  signature: (c : ComplexMeasure α) (μ : Measure α)
  body: (c.re.singularPart μ).toComplexMeasure (c.im.singularPart μ)

中文:
定义 singularPart
  签名: (c : ComplexMeasure α) (μ : Measure α)
  定义体: (c.re.singularPart μ).toComplexMeasure (c.im.singularPart μ)

Depends on / 依赖: c.im.singularPart, c.re.singularPart, singularPart, toComplexMeasure
-/
def singularPart (c : ComplexMeasure α) (μ : Measure α) : ComplexMeasure α :=
  (c.re.singularPart μ).toComplexMeasure (c.im.singularPart μ)

/--
Definition of `rnDeriv` / `rnDeriv` 的定义

English:
definition rnDeriv
  signature: (c : ComplexMeasure α) (μ : Measure α)
  body: fun x =>
  ⟨c.re.rnDeriv μ x, c.im.rnDeriv μ x⟩

中文:
定义 rnDeriv
  签名: (c : ComplexMeasure α) (μ : Measure α)
  定义体: fun x =>
  ⟨c.re.rnDeriv μ x, c.im.rnDeriv μ x⟩
-/
def rnDeriv (c : ComplexMeasure α) (μ : Measure α) : α -> Complex := fun x =>
  ⟨c.re.rnDeriv μ x, c.im.rnDeriv μ x⟩

variable {c : ComplexMeasure α}

/--
theorem `integrable_rnDeriv` / 定理 `integrable_rnDeriv`

English:
theorem integrable_rnDeriv
  given: (c : ComplexMeasure α) (μ : Measure α)
  statement: Integrable (c.rnDeriv μ) μ
  proof: by
  rw [← memLp_one_iff_integrable]; rw [← memLp_re_im_iff]
  exact
    ⟨memLp_one_iff_integrable.2 (SignedMeasure.integrable_rnDeriv _ _),
      memLp_one_iff_integrable.2 (SignedMeasure.integrable_rnDeriv _ _)⟩

中文:
定理 integrable_rnDeriv
  条件: (c : ComplexMeasure α) (μ : Measure α)
  结论: 整数egrable (c.rnDeriv μ) μ
  证明: by
  rw [← memLp_one_iff_integrable]; rw [← memLp_re_im_iff]
  exact
    ⟨memLp_one_iff_integrable.2 (SignedMeasure.integrable_rnDeriv _ _),
      memLp_one_iff_integrable.2 (SignedMeasure.integrable_rnDeriv _ _)⟩

Depends on / 依赖: SignedMeasure, SignedMeasure.integrable_rnDeriv, integrable_rnDeriv, memLp_one_iff_integrable, memLp_re_im_iff
-/
theorem integrable_rnDeriv (c : ComplexMeasure α) (μ : Measure α) : Integrable (c.rnDeriv μ) μ := by
  rw [← memLp_one_iff_integrable]; rw [← memLp_re_im_iff]
  exact
    ⟨memLp_one_iff_integrable.2 (SignedMeasure.integrable_rnDeriv _ _),
      memLp_one_iff_integrable.2 (SignedMeasure.integrable_rnDeriv _ _)⟩

/--
theorem `singularPart_add_withDensity_rnDeriv_eq` / 定理 `singularPart_add_withDensity_rnDeriv_eq`

English:
theorem singularPart_add_withDensity_rnDeriv_eq
  given: [c.HaveLebesgueDecomposition μ]
  proof: by
  conv_rhs => rw [← c.toComplexMeasure_to_signedMeasure]
  ext i hi : 1
  rw [add_apply]; rw [SignedMeasure.toComplexMeasure_apply]
  apply Complex.ext
  · rw [Complex.add_re, withDensityᵥ_apply (c.integrable_rnDeriv μ) hi, ← RCLike.re_eq_complex_re,
      ← integral_re (c.integrable_rnDeriv μ).i

中文:
定理 singularPart_add_withDensity_rnDeriv_eq
  条件: [c.HaveLebesgueDecomposition μ]
  证明: by
  conv_rhs => rw [← c.toComplexMeasure_to_signedMeasure]
  ext i hi : 1
  rw [add_apply]; rw [SignedMeasure.toComplexMeasure_apply]
  apply Complex.ext
  · rw [Complex.add_re, withDensityᵥ_apply (c.integrable_rnDeriv μ) hi, ← RCLike.re_eq_complex_re,
      ← integral_re (c.integrable_rnDeriv μ).i

Depends on / 依赖: Complex.add_re, Complex.ext, RCLike, RCLike.re_eq_complex_re, SignedMeasure, SignedMeasure.integr, SignedMeasure.toComplexMeasure_apply, add_apply, add_re, c.integrable_rnDeriv, c.re.rnDeriv, c.re.singularPart, c.re.singularPart_add_withDensity_rnDeriv_eq, c.toComplexMeasure_to_signedMeasure, cardinal_bInter_mem, conv_rhs, integr, integrableOn, integrable_rnDeriv, integral_re
-/
theorem singularPart_add_withDensity_rnDeriv_eq [c.HaveLebesgueDecomposition μ] :
    c.singularPart μ + μ.withDensityᵥ (c.rnDeriv μ) = c := by
  conv_rhs => rw [← c.toComplexMeasure_to_signedMeasure]
  ext i hi : 1
  rw [add_apply]; rw [SignedMeasure.toComplexMeasure_apply]
  apply Complex.ext
  · rw [Complex.add_re, withDensityᵥ_apply (c.integrable_rnDeriv μ) hi, ← RCLike.re_eq_complex_re,
      ← integral_re (c.integrable_rnDeriv μ).integrableOn, RCLike.re_eq_complex_re,
      ← withDensityᵥ_apply _ hi]
    · change (c.re.singularPart μ + μ.withDensityᵥ (c.re.rnDeriv μ)) i = _
      rw [c.re.singularPart_add_withDensity_rnDeriv_eq μ]
    · exact SignedMeasure.integrable_rnDeriv _ _
  · rw [Complex.add_im, withDensityᵥ_apply (c.integrable_rnDeriv μ) hi, ← RCLike.im_eq_complex_im,
      ← integral_im (c.integrable_rnDeriv μ).integrableOn, RCLike.im_eq_complex_im,
      ← withDensityᵥ_apply _ hi]
    · change (c.im.singularPart μ + μ.withDensityᵥ (c.im.rnDeriv μ)) i = _
      rw [c.im.singularPart_add_withDensity_rnDeriv_eq μ]
    · exact SignedMeasure.integrable_rnDeriv _ _

end ComplexMeasure

end MeasureTheory
