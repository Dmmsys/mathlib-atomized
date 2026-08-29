/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Integrals with a measure derived from probability mass functions.

This file connects `PMF` with `integral`. The main result is that the integral (i.e. the expected
value) with regard to a measure derived from a `PMF` is a sum weighted by the `PMF`.

It also provides the expected value for specific probability mass functions.
-/

public section

namespace PMF

open MeasureTheory NNReal ENNReal TopologicalSpace

section General

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/--
theorem `integral_eq_tsum` / 定理 `integral_eq_tsum`

English:
theorem integral_eq_tsum
  given: (p : PMF α) (f : α -> E) (hf : Integrable f p.toMeasure)
  proof: calc
  _ = ∫ a in p.support, f a ∂(p.toMeasure) := by rw [restrict_toMeasure_support p]
  _ = ∑' (a : support p), (p.toMeasure {a.val}).toReal • f a := by
    apply setIntegral_countable f p.support_countable
    rwa [IntegrableOn, restrict_toMeasure_support p]
  _ = ∑' (a : support p), (p a).toReal

中文:
定理 integral_eq_tsum
  条件: (p : PMF α) (f : α -> E) (hf : 整数egrable f p.toMeasure)
  证明: calc
  _ = ∫ a in p.support, f a ∂(p.toMeasure) := by rw [restrict_toMeasure_support p]
  _ = ∑' (a : support p), (p.toMeasure {a.val}).toReal • f a := by
    apply setIntegral_countable f p.support_countable
    rwa [IntegrableOn, restrict_toMeasure_support p]
  _ = ∑' (a : support p), (p a).toReal
-/
theorem integral_eq_tsum (p : PMF α) (f : α -> E) (hf : Integrable f p.toMeasure) :
    ∫ a, f a ∂(p.toMeasure) = ∑' a, (p a).toReal • f a := calc
  _ = ∫ a in p.support, f a ∂(p.toMeasure) := by rw [restrict_toMeasure_support p]
  _ = ∑' (a : support p), (p.toMeasure {a.val}).toReal • f a := by
    apply setIntegral_countable f p.support_countable
    rwa [IntegrableOn, restrict_toMeasure_support p]
  _ = ∑' (a : support p), (p a).toReal • f a := by
    congr with x; congr 2
    apply PMF.toMeasure_apply_singleton p x (MeasurableSet.singleton _)
  _ = ∑' a, (p a).toReal • f a :=
tsum_subtype_eq_of_support_subset calc
      (fun a => (p a).toReal • f a).support subseteq (fun a => (p a).toReal).support :=
        Function.support_smul_subset_left _ _
      _ subseteq support p := fun x h1 h2 => h1 (by simp [h2])

/--
theorem `integral_eq_sum` / 定理 `integral_eq_sum`

English:
theorem integral_eq_sum
  given: [Fintype α] (p : PMF α) (f : α -> E)
  proof: by
  rw [integral_fintype .of_finite]
  congr with x
  rw [measureReal_def]
  congr 2
  exact PMF.toMeasure_apply_singleton p x (MeasurableSet.singleton _)

中文:
定理 integral_eq_sum
  条件: [Fintype α] (p : PMF α) (f : α -> E)
  证明: by
  rw [integral_fintype .of_finite]
  congr with x
  rw [measureReal_def]
  congr 2
  exact PMF.toMeasure_apply_singleton p x (MeasurableSet.singleton _)

Depends on / 依赖: MeasurableSet, MeasurableSet.singleton, PMF.toMeasure_apply_singleton, integral_fintype, measureReal_def, of_finite, singleton, toMeasure_apply_singleton
-/
theorem integral_eq_sum [Fintype α] (p : PMF α) (f : α -> E) :
    ∫ a, f a ∂(p.toMeasure) = ∑ a, (p a).toReal • f a := by
  rw [integral_fintype .of_finite]
  congr with x
  rw [measureReal_def]
  congr 2
  exact PMF.toMeasure_apply_singleton p x (MeasurableSet.singleton _)

end General

@[deprecated ProbabilityTheory.integral_bernoulliMeasure (since := "2026-04-07")]
/--
theorem `bernoulli_expectation` / 定理 `bernoulli_expectation`

English:
theorem bernoulli_expectation
  given: {p : Real>=0} (h : p <= 1)
  proof: by
  simp [integral_eq_sum, bernoulli_apply]

中文:
定理 bernoulli_expectation
  条件: {p : 实数>=0} (h : p <= 1)
  证明: by
  simp [integral_eq_sum, bernoulli_apply]

Depends on / 依赖: bernoulli_apply, integral_eq_sum
-/
theorem bernoulli_expectation {p : Real>=0} (h : p <= 1) :
    ∫ b, cond b 1 0 ∂((bernoulli p h).toMeasure) = p.toReal := by
  simp [integral_eq_sum, bernoulli_apply]

end PMF
