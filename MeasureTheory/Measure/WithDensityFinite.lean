/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Exhaustion
public import Mathlib.Probability.ConditionalProbability

/-!
# s-finite measures can be written as `withDensity` of a finite measure

If `μ` is an s-finite measure, then there exists a finite measure `μ.toFinite`
such that a set is `μ`-null iff it is `μ.toFinite`-null.
In particular, `MeasureTheory.ae μ.toFinite = MeasureTheory.ae μ` and `μ.toFinite = 0` iff `μ = 0`.
As a corollary, `μ` can be represented as `μ.toFinite.withDensity (μ.rnDeriv μ.toFinite)`.

Our definition of `MeasureTheory.Measure.toFinite` ensures some extra properties:

- if `μ` is a finite measure, then `μ.toFinite = μ[|univ] = (μ univ)⁻¹ • μ`;
- in particular, `μ.toFinite = μ` for a probability measure;
- if `μ ≠ 0`, then `μ.toFinite` is a probability measure.

## Main definitions

In this definition and the results below, `μ` is an s-finite measure (`SFinite μ`).

* `MeasureTheory.Measure.toFinite`: a finite measure with `μ ≪ μ.toFinite` and `μ.toFinite ≪ μ`.
  If `μ ≠ 0`, this is a probability measure.

## Main statements

* `absolutelyContinuous_toFinite`: `μ ≪ μ.toFinite`.
* `toFinite_absolutelyContinuous`: `μ.toFinite ≪ μ`.
* `ae_toFinite`: `ae μ.toFinite = ae μ`.

-/

@[expose] public section

open Set
open scoped ENNReal ProbabilityTheory

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/--
Definition of `Measure.toFiniteAux` / `Measure.toFiniteAux` 的定义

English:
definition Measure.toFiniteAux
  signature: (μ : Measure α) [SFinite μ]
  body: letI := Classical.dec
  if IsFiniteMeasure μ then μ else (exists_isFiniteMeasure_absolutelyContinuous μ).choose

中文:
定义 测度.toFiniteAux
  签名: (μ : 测度 α) [SFinite μ]
  定义体: letI := Classical.dec
  if IsFiniteMeasure μ then μ else (exists_isFiniteMeasure_absolutelyContinuous μ).choose

Depends on / 依赖: Classical, Classical.dec, IsFiniteMeasure, exists_isFiniteMeasure_absolutelyContinuous
-/
noncomputable def Measure.toFiniteAux (μ : Measure α) [SFinite μ] : Measure α :=
  letI := Classical.dec
  if IsFiniteMeasure μ then μ else (exists_isFiniteMeasure_absolutelyContinuous μ).choose

/--
Definition of `Measure.toFinite` / `Measure.toFinite` 的定义

English:
definition Measure.toFinite
  signature: (μ : Measure α) [SFinite μ]
  body: μ.toFiniteAux[|univ]

@[local simp]

中文:
定义 测度.toFinite
  签名: (μ : 测度 α) [SFinite μ]
  定义体: μ.toFiniteAux[|univ]

@[local simp]

Depends on / 依赖: toFiniteAux
-/
noncomputable def Measure.toFinite (μ : Measure α) [SFinite μ] : Measure α :=
  μ.toFiniteAux[|univ]

@[local simp]
/--
lemma `ae_toFiniteAux` / 引理 `ae_toFiniteAux`

English:
lemma ae_toFiniteAux
  given: [SFinite μ]
  statement: ae μ.toFiniteAux = ae μ
  proof: by
  rw [Measure.toFiniteAux]
  split_ifs
  · simp
  · obtain ⟨_, h₁, h₂⟩ := (exists_isFiniteMeasure_absolutelyContinuous μ).choose_spec
    exact h₂.ae_le.antisymm h₁.ae_le

@[local instance]

中文:
引理 ae_toFiniteAux
  条件: [SFinite μ]
  结论: ae μ.toFiniteAux = ae μ
  证明: by
  rw [Measure.toFiniteAux]
  split_ifs
  · simp
  · obtain ⟨_, h₁, h₂⟩ := (exists_isFiniteMeasure_absolutelyContinuous μ).choose_spec
    exact h₂.ae_le.antisymm h₁.ae_le

@[local instance]

Depends on / 依赖: Measure, Measure.toFiniteAux, ae_le, ae_le.antisymm, antisymm, choose_spec, exists_isFiniteMeasure_absolutelyContinuous, split_ifs, toFiniteAux
-/
lemma ae_toFiniteAux [SFinite μ] : ae μ.toFiniteAux = ae μ := by
  rw [Measure.toFiniteAux]
  split_ifs
  · simp
  · obtain ⟨_, h₁, h₂⟩ := (exists_isFiniteMeasure_absolutelyContinuous μ).choose_spec
    exact h₂.ae_le.antisymm h₁.ae_le

@[local instance]
/--
theorem `isFiniteMeasure_toFiniteAux` / 定理 `isFiniteMeasure_toFiniteAux`

English:
theorem isFiniteMeasure_toFiniteAux
  given: [SFinite μ]
  statement: IsFiniteMeasure μ.toFiniteAux
  proof: by
  rw [Measure.toFiniteAux]
  split_ifs
  · assumption
  · exact (exists_isFiniteMeasure_absolutelyContinuous μ).choose_spec.1

@[simp]

中文:
定理 isFiniteMeasure_toFiniteAux
  条件: [SFinite μ]
  结论: 是有限测度 μ.toFiniteAux
  证明: by
  rw [Measure.toFiniteAux]
  split_ifs
  · assumption
  · exact (exists_isFiniteMeasure_absolutelyContinuous μ).choose_spec.1

@[simp]

Depends on / 依赖: Measure, Measure.toFiniteAux, choose_spec, exists_isFiniteMeasure_absolutelyContinuous, split_ifs, toFiniteAux
-/
theorem isFiniteMeasure_toFiniteAux [SFinite μ] : IsFiniteMeasure μ.toFiniteAux := by
  rw [Measure.toFiniteAux]
  split_ifs
  · assumption
  · exact (exists_isFiniteMeasure_absolutelyContinuous μ).choose_spec.1

@[simp]
/--
lemma `ae_toFinite` / 引理 `ae_toFinite`

English:
lemma ae_toFinite
  given: [SFinite μ]
  statement: ae μ.toFinite = ae μ
  proof: by
  simp [Measure.toFinite, ProbabilityTheory.cond]

@[simp]

中文:
引理 ae_toFinite
  条件: [SFinite μ]
  结论: ae μ.toFinite = ae μ
  证明: by
  simp [Measure.toFinite, ProbabilityTheory.cond]

@[simp]

Depends on / 依赖: Measure, Measure.toFinite, ProbabilityTheory, ProbabilityTheory.cond, toFinite
-/
lemma ae_toFinite [SFinite μ] : ae μ.toFinite = ae μ := by
  simp [Measure.toFinite, ProbabilityTheory.cond]

@[simp]
/--
lemma `toFinite_apply_eq_zero_iff` / 引理 `toFinite_apply_eq_zero_iff`

English:
lemma toFinite_apply_eq_zero_iff
  given: [SFinite μ] {s : Set α}
  statement: μ.toFinite s = 0 ↔ μ s = 0
  proof: by
  simp only [← compl_mem_ae_iff, ae_toFinite]

@[simp]

中文:
引理 toFinite_apply_eq_zero_iff
  条件: [SFinite μ] {s : 集合 α}
  结论: μ.toFinite s = 0 ↔ μ s = 0
  证明: by
  simp only [← compl_mem_ae_iff, ae_toFinite]

@[simp]

Depends on / 依赖: ae_toFinite, compl_mem_ae_iff
-/
lemma toFinite_apply_eq_zero_iff [SFinite μ] {s : Set α} : μ.toFinite s = 0 ↔ μ s = 0 := by
  simp only [← compl_mem_ae_iff, ae_toFinite]

@[simp]
/--
lemma `toFinite_eq_zero_iff` / 引理 `toFinite_eq_zero_iff`

English:
lemma toFinite_eq_zero_iff
  given: [SFinite μ]
  statement: μ.toFinite = 0 ↔ μ = 0
  proof: by
  simp_rw [← Measure.measure_univ_eq_zero, toFinite_apply_eq_zero_iff]

@[simp]

中文:
引理 toFinite_eq_zero_iff
  条件: [SFinite μ]
  结论: μ.toFinite = 0 ↔ μ = 0
  证明: by
  simp_rw [← Measure.measure_univ_eq_zero, toFinite_apply_eq_zero_iff]

@[simp]

Depends on / 依赖: Measure, Measure.measure_univ_eq_zero, measure_univ_eq_zero, simp_rw, toFinite_apply_eq_zero_iff
-/
lemma toFinite_eq_zero_iff [SFinite μ] : μ.toFinite = 0 ↔ μ = 0 := by
  simp_rw [← Measure.measure_univ_eq_zero, toFinite_apply_eq_zero_iff]

@[simp]
/--
lemma `toFinite_zero` / 引理 `toFinite_zero`

English:
lemma toFinite_zero
  statement: Measure.toFinite (0 : Measure α) = 0
  proof: by simp

中文:
引理 toFinite_zero
  结论: 测度.toFinite (0 : 测度 α) = 0
  证明: by simp
-/
lemma toFinite_zero : Measure.toFinite (0 : Measure α) = 0 := by simp

/--
lemma `toFinite_eq_self` / 引理 `toFinite_eq_self`

English:
lemma toFinite_eq_self
  given: [IsProbabilityMeasure μ]
  statement: μ.toFinite = μ
  proof: by
  rw [Measure.toFinite]; rw [Measure.toFiniteAux]; rw [if_pos]; rw [ProbabilityTheory.cond_univ]
  infer_instance

中文:
引理 toFinite_eq_self
  条件: [是概率测度 μ]
  结论: μ.toFinite = μ
  证明: by
  rw [Measure.toFinite]; rw [Measure.toFiniteAux]; rw [if_pos]; rw [ProbabilityTheory.cond_univ]
  infer_instance

Depends on / 依赖: Measure, Measure.toFinite, Measure.toFiniteAux, ProbabilityTheory, ProbabilityTheory.cond_univ, cond_univ, if_pos, infer_instance, toFinite, toFiniteAux
-/
lemma toFinite_eq_self [IsProbabilityMeasure μ] : μ.toFinite = μ := by
  rw [Measure.toFinite]; rw [Measure.toFiniteAux]; rw [if_pos]; rw [ProbabilityTheory.cond_univ]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SFinite
  signature: μ] : IsFiniteMeasure μ.toFinite
  body: by
  rw [Measure.toFinite]
  infer_instance

中文:
实例 [SFinite
  签名: μ] : 是有限测度 μ.toFinite
  定义体: by
  rw [Measure.toFinite]
  infer_instance

Depends on / 依赖: Measure, Measure.toFinite, infer_instance, toFinite
-/
instance [SFinite μ] : IsFiniteMeasure μ.toFinite := by
  rw [Measure.toFinite]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SFinite
  signature: μ] [NeZero μ] : IsProbabilityMeasure μ.toFinite
  body: by
  apply ProbabilityTheory.cond_isProbabilityMeasure
  simp [ne_eq, ← compl_mem_ae_iff, ae_toFiniteAux]

中文:
实例 [SFinite
  签名: μ] [NeZero μ] : 是概率测度 μ.toFinite
  定义体: by
  apply ProbabilityTheory.cond_isProbabilityMeasure
  simp [ne_eq, ← compl_mem_ae_iff, ae_toFiniteAux]

Depends on / 依赖: ProbabilityTheory, ProbabilityTheory.cond_isProbabilityMeasure, ae_toFiniteAux, compl_mem_ae_iff, cond_isProbabilityMeasure, ne_eq
-/
instance [SFinite μ] [NeZero μ] : IsProbabilityMeasure μ.toFinite := by
  apply ProbabilityTheory.cond_isProbabilityMeasure
  simp [ne_eq, ← compl_mem_ae_iff, ae_toFiniteAux]

/--
lemma `absolutelyContinuous_toFinite` / 引理 `absolutelyContinuous_toFinite`

English:
lemma absolutelyContinuous_toFinite
  given: (μ : Measure α) [SFinite μ]
  statement: μ ≪ μ.toFinite
  proof: Measure.ae_le_iff_absolutelyContinuous.mp ae_toFinite.ge

中文:
引理 absolutelyContinuous_toFinite
  条件: (μ : 测度 α) [SFinite μ]
  结论: μ ≪ μ.toFinite
  证明: Measure.ae_le_iff_absolutelyContinuous.mp ae_toFinite.ge

Depends on / 依赖: Measure, Measure.ae_le_iff_absolutelyContinuous.mp, ae_le_iff_absolutelyContinuous, ae_toFinite, ae_toFinite.ge
-/
lemma absolutelyContinuous_toFinite (μ : Measure α) [SFinite μ] : μ ≪ μ.toFinite :=
  Measure.ae_le_iff_absolutelyContinuous.mp ae_toFinite.ge

/--
lemma `sfiniteSeq_absolutelyContinuous_toFinite` / 引理 `sfiniteSeq_absolutelyContinuous_toFinite`

English:
lemma sfiniteSeq_absolutelyContinuous_toFinite
  given: (μ : Measure α) [SFinite μ] (n : Nat)
  proof: (sfiniteSeq_le μ n).absolutelyContinuous.trans (absolutelyContinuous_toFinite μ)

中文:
引理 sfiniteSeq_absolutelyContinuous_toFinite
  条件: (μ : 测度 α) [SFinite μ] (n : 自然数)
  证明: (sfiniteSeq_le μ n).absolutelyContinuous.trans (absolutelyContinuous_toFinite μ)

Depends on / 依赖: absolutelyContinuous, absolutelyContinuous.trans, absolutelyContinuous_toFinite, sfiniteSeq_le
-/
lemma sfiniteSeq_absolutelyContinuous_toFinite (μ : Measure α) [SFinite μ] (n : Nat) :
    sfiniteSeq μ n ≪ μ.toFinite :=
  (sfiniteSeq_le μ n).absolutelyContinuous.trans (absolutelyContinuous_toFinite μ)

/--
lemma `toFinite_absolutelyContinuous` / 引理 `toFinite_absolutelyContinuous`

English:
lemma toFinite_absolutelyContinuous
  given: (μ : Measure α) [SFinite μ]
  statement: μ.toFinite ≪ μ
  proof: Measure.ae_le_iff_absolutelyContinuous.mp ae_toFinite.le

中文:
引理 toFinite_absolutelyContinuous
  条件: (μ : 测度 α) [SFinite μ]
  结论: μ.toFinite ≪ μ
  证明: Measure.ae_le_iff_absolutelyContinuous.mp ae_toFinite.le

Depends on / 依赖: Measure, Measure.ae_le_iff_absolutelyContinuous.mp, ae_le_iff_absolutelyContinuous, ae_toFinite, ae_toFinite.le
-/
lemma toFinite_absolutelyContinuous (μ : Measure α) [SFinite μ] : μ.toFinite ≪ μ :=
  Measure.ae_le_iff_absolutelyContinuous.mp ae_toFinite.le

/--
lemma `restrict_compl_sigmaFiniteSet` / 引理 `restrict_compl_sigmaFiniteSet`

English:
lemma restrict_compl_sigmaFiniteSet
  given: [SFinite μ]
  proof: by
  rw [Measure.sigmaFiniteSet]; rw [restrict_compl_sigmaFiniteSetWRT (Measure.AbsolutelyContinuous.refl μ)]
  ext t ht
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Measure.restrict_apply ht]; rw [Measure.restrict_apply ht]
  by_cases hμt : μ (t inter (μ.sigmaFiniteSetWRT μ)ᶜ) = 0
  · rw [hμ

中文:
引理 restrict_compl_sigmaFiniteSet
  条件: [SFinite μ]
  证明: by
  rw [Measure.sigmaFiniteSet]; rw [restrict_compl_sigmaFiniteSetWRT (Measure.AbsolutelyContinuous.refl μ)]
  ext t ht
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Measure.restrict_apply ht]; rw [Measure.restrict_apply ht]
  by_cases hμt : μ (t inter (μ.sigmaFiniteSetWRT μ)ᶜ) = 0
  · rw [hμ

Depends on / 依赖: AbsolutelyContinuous, ENNReal, ENNReal.top_mul, Measure, Measure.AbsolutelyContinuous.refl, Measure.restrict_apply, Measure.sigmaFiniteSet, Measure.smul_apply, absolutelyContinuous_toFinite, restrict_apply, restrict_compl_sigmaFiniteSetWRT, sigmaFiniteSet, sigmaFiniteSetWRT, smul_apply, smul_eq_mul, toFinite_absolutelyContinuous, top_mul
-/
lemma restrict_compl_sigmaFiniteSet [SFinite μ] :
    μ.restrict μ.sigmaFiniteSetᶜ = ∞ • μ.toFinite.restrict μ.sigmaFiniteSetᶜ := by
  rw [Measure.sigmaFiniteSet]; rw [restrict_compl_sigmaFiniteSetWRT (Measure.AbsolutelyContinuous.refl μ)]
  ext t ht
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Measure.restrict_apply ht]; rw [Measure.restrict_apply ht]
  by_cases hμt : μ (t inter (μ.sigmaFiniteSetWRT μ)ᶜ) = 0
  · rw [hμt, toFinite_absolutelyContinuous μ hμt]
  · rw [ENNReal.top_mul hμt, ENNReal.top_mul]
    exact fun h => hμt (absolutelyContinuous_toFinite μ h)

end MeasureTheory
