/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Thomas Zhu
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Lebesgue

/-!
# Radon-Nikodym derivatives of vector measures

This file contains results about Radon-Nikodym derivatives of signed measures
that depend both on the Lebesgue decomposition of signed measures
and the theory of Radon-Nikodym derivatives of usual measures.
-/

public section

namespace MeasureTheory

variable {α : Type*} {m : MeasurableSpace α}

open Measure VectorMeasure

namespace SignedMeasure

/--
theorem `withDensityᵥ_rnDeriv_eq` / 定理 `withDensityᵥ_rnDeriv_eq`

English:
theorem withDensityᵥ_rnDeriv_eq
  statement: (s : SignedMeasure α) (μ : Measure α) [SigmaFinite μ]
  proof: by
  rw [absolutelyContinuous_ennreal_iff]; rw [(_ : μ.toENNRealVectorMeasure.ennrealToMeasure = μ)]; rw [totalVariation_absolutelyContinuous_iff] at h
  · ext1 i hi
    rw [withDensityᵥ_apply (integrable_rnDeriv _ _) hi]; rw [rnDeriv_def]; rw [integral_sub]; rw [setIntegral_toReal_rnDeriv h.1 i]; rw [setIntegral_toReal_rnDeriv h.2 i]
    · conv_rhs => rw [← s.toSignedMeasure_toJordanDecomposition]
      rw [JordanDecomposition.toSignedMeasure]; rw [_root_.sub_apply]; rw [toSignedMeasure_apply_measurable hi]; rw [toSignedMeasure_apply_measurable hi]; rw [measureReal_def]; rw [measureReal_def]
    all_goals
      refine Integrable.integrableOn ?_
      refine ⟨?_, hasFiniteIntegral_toReal_of_lintegral_ne_top ?_⟩
      · apply Measurable.aestronglyMeasurable (by fun_prop)
      · exact (lintegral_rnDeriv_lt_top _ _).ne
  · exact equivMeasure.right_inv μ

中文:
定理 withDensityᵥ_rnDeriv_eq
  结论: (s : 符号测度 α) (μ : 测度 α) [σ有限 μ]
  证明: by
  rw [absolutelyContinuous_ennreal_iff]; rw [(_ : μ.toENNRealVectorMeasure.ennrealToMeasure = μ)]; rw [totalVariation_absolutelyContinuous_iff] at h
  · ext1 i hi
    rw [withDensityᵥ_apply (integrable_rnDeriv _ _) hi]; rw [rnDeriv_def]; rw [integral_sub]; rw [setIntegral_toReal_rnDeriv h.1 i]; rw [setIntegral_toReal_rnDeriv h.2 i]
    · conv_rhs => rw [← s.toSignedMeasure_toJordanDecomposition]
      rw [JordanDecomposition.toSignedMeasure]; rw [_root_.sub_apply]; rw [toSignedMeasure_apply_measurable hi]; rw [toSignedMeasure_apply_measurable hi]; rw [measureReal_def]; rw [measureReal_def]
    all_goals
      refine Integrable.integrableOn ?_
      refine ⟨?_, hasFiniteIntegral_toReal_of_lintegral_ne_top ?_⟩
      · apply Measurable.aestronglyMeasurable (by fun_prop)
      · exact (lintegral_rnDeriv_lt_top _ _).ne
  · exact equivMeasure.right_inv μ

Depends on / 依赖: JordanDecomposition, JordanDecomposition.toSignedMeasure, _root_, _root_.sub_apply, absolutelyContinuous_ennreal_iff, cardinal_bInter_mem, conv_rhs, ennrealToMeasure, integrable_rnDeriv, integral_sub, mem_map, rnDeriv_def, s.toSignedMeasure_toJordanDecomposition, sInter_eq_biInter, setIntegral_toReal_rnDeriv, sub_apply, toENNRealVectorMeasure, toENNRealVectorMeasure.ennrealToMeasure, toSignedMeasure, toSignedMeasure_apply_measurable
-/
theorem withDensityᵥ_rnDeriv_eq (s : SignedMeasure α) (μ : Measure α) [SigmaFinite μ]
    (h : s ≪ᵥ μ.toENNRealVectorMeasure) : μ.withDensityᵥ (s.rnDeriv μ) = s := by
  rw [absolutelyContinuous_ennreal_iff]; rw [(_ : μ.toENNRealVectorMeasure.ennrealToMeasure = μ)]; rw [totalVariation_absolutelyContinuous_iff] at h
  · ext1 i hi
    rw [withDensityᵥ_apply (integrable_rnDeriv _ _) hi]; rw [rnDeriv_def]; rw [integral_sub]; rw [setIntegral_toReal_rnDeriv h.1 i]; rw [setIntegral_toReal_rnDeriv h.2 i]
    · conv_rhs => rw [← s.toSignedMeasure_toJordanDecomposition]
      rw [JordanDecomposition.toSignedMeasure]; rw [_root_.sub_apply]; rw [toSignedMeasure_apply_measurable hi]; rw [toSignedMeasure_apply_measurable hi]; rw [measureReal_def]; rw [measureReal_def]
    all_goals
      refine Integrable.integrableOn ?_
      refine ⟨?_, hasFiniteIntegral_toReal_of_lintegral_ne_top ?_⟩
      · apply Measurable.aestronglyMeasurable (by fun_prop)
      · exact (lintegral_rnDeriv_lt_top _ _).ne
  · exact equivMeasure.right_inv μ

/--
theorem `absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq` / 定理 `absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq`

English:
theorem absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq
  statement: (s : SignedMeasure α) (μ : Measure α)
  proof: ⟨withDensityᵥ_rnDeriv_eq s μ, fun h => h ▸ withDensityᵥ_absolutelyContinuous _ _⟩

中文:
定理 absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq
  结论: (s : 符号测度 α) (μ : 测度 α)
  证明: ⟨withDensityᵥ_rnDeriv_eq s μ, fun h => h ▸ withDensityᵥ_absolutelyContinuous _ _⟩
-/
theorem absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq (s : SignedMeasure α) (μ : Measure α)
    [SigmaFinite μ] : s ≪ᵥ μ.toENNRealVectorMeasure ↔ μ.withDensityᵥ (s.rnDeriv μ) = s :=
  ⟨withDensityᵥ_rnDeriv_eq s μ, fun h => h ▸ withDensityᵥ_absolutelyContinuous _ _⟩

end SignedMeasure

/--
theorem `withDensityᵥ_rnDeriv_smul` / 定理 `withDensityᵥ_rnDeriv_smul`

English:
theorem withDensityᵥ_rnDeriv_smul
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  rw [withDensityᵥ_smul_eq_withDensityᵥ_withDensity' (measurable_rnDeriv μ ν).aemeasurable
    (rnDeriv_lt_top μ ν) ((integrable_rnDeriv_smul_iff hμν).mpr hf)]; rw [withDensity_rnDeriv_eq μ ν hμν]

中文:
定理 withDensityᵥ_rnDeriv_smul
  结论: {E : 类型} [赋范交换加群 E] [赋范空间 实数 E]
  证明: by
  rw [withDensityᵥ_smul_eq_withDensityᵥ_withDensity' (measurable_rnDeriv μ ν).aemeasurable
    (rnDeriv_lt_top μ ν) ((integrable_rnDeriv_smul_iff hμν).mpr hf)]; rw [withDensity_rnDeriv_eq μ ν hμν]

Depends on / 依赖: aemeasurable, integrable_rnDeriv_smul_iff, measurable_rnDeriv, rnDeriv_lt_top, withDensity_rnDeriv_eq
-/
theorem withDensityᵥ_rnDeriv_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {μ ν : Measure α} [μ.HaveLebesgueDecomposition ν] [SigmaFinite μ] {f : α -> E}
    (hμν : μ ≪ ν) (hf : Integrable f μ) :
    ν.withDensityᵥ (fun x => (μ.rnDeriv ν x).toReal • f x) = μ.withDensityᵥ f := by
  rw [withDensityᵥ_smul_eq_withDensityᵥ_withDensity' (measurable_rnDeriv μ ν).aemeasurable
    (rnDeriv_lt_top μ ν) ((integrable_rnDeriv_smul_iff hμν).mpr hf)]; rw [withDensity_rnDeriv_eq μ ν hμν]

end MeasureTheory
