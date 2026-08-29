/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Decision.Risk.Defs
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Basic properties of the risk of an estimator

## Main statements

* `iSup_bayesRisk_le_minimaxRisk`: the maximal Bayes risk is less than or equal to the minimax risk.
* `bayesRisk_le_bayesRisk_comp`: data-processing inequality for the Bayes risk with respect to a
  prior: if we compose the data generating kernel `P` with a Markov kernel, then the Bayes risk
  increases.
* `bayesRisk_le_iInf`: for `P` a Markov kernel, the Bayes risk is less than `⨅ y, ∫⁻ θ, ℓ θ y ∂π`.

In several cases, there is no information in the data about the parameter and the Bayes risk takes
its maximal value.
* `bayesRisk_const`: if the data generating kernel is constant, then the Bayes risk is equal to
  `⨅ y, ∫⁻ θ, ℓ θ y ∂π`.
* `bayesRisk_of_subsingleton`: if the observation space is a subsingleton, then the Bayes risk is
  equal to `⨅ y, ∫⁻ θ, ℓ θ y ∂π`.

## TODO

In many cases, the maximal Bayes risk and the minimax risk are equal
(by a so-called minimax theorem).

-/

public section

open MeasureTheory Function
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Θ 𝓧 𝓧' 𝓨 : Type*} {mΘ : MeasurableSpace Θ}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓧' : MeasurableSpace 𝓧'} {m𝓨 : MeasurableSpace 𝓨}
  {ℓ : Θ -> 𝓨 -> Real>=0∞} {P : Kernel Θ 𝓧} {κ : Kernel 𝓧 𝓨} {π : Measure Θ}

section BayesRiskLeMinimaxRisk

/--
lemma `avgRisk_le_iSup_risk` / 引理 `avgRisk_le_iSup_risk`

English:
lemma avgRisk_le_iSup_risk
  statement: (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨)
  proof: lintegral_le_iSup _

中文:
引理 avgRisk_le_iSup_risk
  结论: (ℓ : Θ -> 𝓨 -> 实数>=0∞) (P : 核 Θ 𝓧) (κ : 核 𝓧 𝓨)
  证明: lintegral_le_iSup _

Depends on / 依赖: lintegral_le_iSup
-/
lemma avgRisk_le_iSup_risk (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨)
    (π : Measure Θ) [IsProbabilityMeasure π] :
    avgRisk ℓ P κ π <= ⨆ θ, ∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ) := lintegral_le_iSup _

/--
lemma `bayesRisk_le_avgRisk` / 引理 `bayesRisk_le_avgRisk`

English:
lemma bayesRisk_le_avgRisk
  statement: (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨)
  proof: iInf₂_le κ hκ

中文:
引理 bayesRisk_le_avgRisk
  结论: (ℓ : Θ -> 𝓨 -> 实数>=0∞) (P : 核 Θ 𝓧) (κ : 核 𝓧 𝓨)
  证明: iInf₂_le κ hκ
-/
lemma bayesRisk_le_avgRisk (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨)
    (π : Measure Θ) [hκ : IsMarkovKernel κ] :
    bayesRisk ℓ P π <= avgRisk ℓ P κ π := iInf₂_le κ hκ

/--
lemma `bayesRisk_le_minimaxRisk` / 引理 `bayesRisk_le_minimaxRisk`

English:
lemma bayesRisk_le_minimaxRisk
  statement: (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧)
  proof: iInf₂_mono fun _ _ => avgRisk_le_iSup_risk _ _ _ _

中文:
引理 bayesRisk_le_minimaxRisk
  结论: (ℓ : Θ -> 𝓨 -> 实数>=0∞) (P : 核 Θ 𝓧)
  证明: iInf₂_mono fun _ _ => avgRisk_le_iSup_risk _ _ _ _

Depends on / 依赖: avgRisk_le_iSup_risk
-/
lemma bayesRisk_le_minimaxRisk (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧)
    (π : Measure Θ) [IsProbabilityMeasure π] :
    bayesRisk ℓ P π <= minimaxRisk ℓ P := iInf₂_mono fun _ _ => avgRisk_le_iSup_risk _ _ _ _

/--
lemma `iSup_bayesRisk_le_minimaxRisk` / 引理 `iSup_bayesRisk_le_minimaxRisk`

English:
lemma iSup_bayesRisk_le_minimaxRisk
  given: (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧)
  proof: iSup₂_le fun _ _ => bayesRisk_le_minimaxRisk _ _ _

中文:
引理 iSup_bayesRisk_le_minimaxRisk
  条件: (ℓ : Θ -> 𝓨 -> 实数>=0∞) (P : 核 Θ 𝓧)
  证明: iSup₂_le fun _ _ => bayesRisk_le_minimaxRisk _ _ _

Depends on / 依赖: bayesRisk_le_minimaxRisk
-/
lemma iSup_bayesRisk_le_minimaxRisk (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) :
    ⨆ (π : Measure Θ) (_ : IsProbabilityMeasure π), bayesRisk ℓ P π
      <= minimaxRisk ℓ P := iSup₂_le fun _ _ => bayesRisk_le_minimaxRisk _ _ _

end BayesRiskLeMinimaxRisk

section Const

/--
lemma `avgRisk_const_left` / 引理 `avgRisk_const_left`

English:
lemma avgRisk_const_left
  given: (ℓ : Θ -> 𝓨 -> Real>=0∞) (μ : Measure 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ)
  proof: by
  simp [avgRisk]

中文:
引理 avgRisk_const_left
  条件: (ℓ : Θ -> 𝓨 -> 实数>=0∞) (μ : 测度 𝓧) (κ : 核 𝓧 𝓨) (π : 测度 Θ)
  证明: by
  simp [avgRisk]

Depends on / 依赖: avgRisk
-/
lemma avgRisk_const_left (ℓ : Θ -> 𝓨 -> Real>=0∞) (μ : Measure 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) :
    avgRisk ℓ (Kernel.const Θ μ) κ π = ∫⁻ θ, ∫⁻ y, ℓ θ y ∂(κ ∘ₘ μ) ∂π := by
  simp [avgRisk]

/--
lemma `avgRisk_const_left'` / 引理 `avgRisk_const_left'`

English:
lemma avgRisk_const_left'
  statement: (hl : Measurable (uncurry ℓ)) (μ : Measure 𝓧) [SFinite μ]
  proof: by
  rw [avgRisk_const_left]; rw [lintegral_lintegral_swap (by fun_prop)]

中文:
引理 avgRisk_const_left'
  结论: (hl : 可测 (uncurry ℓ)) (μ : 测度 𝓧) [SFinite μ]
  证明: by
  rw [avgRisk_const_left]; rw [lintegral_lintegral_swap (by fun_prop)]

Depends on / 依赖: avgRisk_const_left, fun_prop, lintegral_lintegral_swap
-/
lemma avgRisk_const_left' (hl : Measurable (uncurry ℓ)) (μ : Measure 𝓧) [SFinite μ]
    (κ : Kernel 𝓧 𝓨) [IsSFiniteKernel κ] (π : Measure Θ) [SFinite π] :
    avgRisk ℓ (Kernel.const Θ μ) κ π = ∫⁻ y, ∫⁻ θ, ℓ θ y ∂π ∂(κ ∘ₘ μ) := by
  rw [avgRisk_const_left]; rw [lintegral_lintegral_swap (by fun_prop)]

/--
lemma `avgRisk_const_right'` / 引理 `avgRisk_const_right'`

English:
lemma avgRisk_const_right'
  given: (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) (ν : Measure 𝓨) (π : Measure Θ)
  proof: by
  simp [avgRisk, Kernel.const_comp]

中文:
引理 avgRisk_const_right'
  条件: (ℓ : Θ -> 𝓨 -> 实数>=0∞) (P : 核 Θ 𝓧) (ν : 测度 𝓨) (π : 测度 Θ)
  证明: by
  simp [avgRisk, Kernel.const_comp]

Depends on / 依赖: Kernel, Kernel.const_comp, avgRisk, const_comp
-/
lemma avgRisk_const_right' (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) (ν : Measure 𝓨) (π : Measure Θ) :
    avgRisk ℓ P (Kernel.const 𝓧 ν) π = ∫⁻ θ, P θ .univ * ∫⁻ y, ℓ θ y ∂ν ∂π := by
  simp [avgRisk, Kernel.const_comp]

/--
lemma `avgRisk_const_right` / 引理 `avgRisk_const_right`

English:
lemma avgRisk_const_right
  statement: (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
  proof: by
  simp [avgRisk_const_right']

中文:
引理 avgRisk_const_right
  结论: (ℓ : Θ -> 𝓨 -> 实数>=0∞) (P : 核 Θ 𝓧) [是MarkovKernel P]
  证明: by
  simp [avgRisk_const_right']

Depends on / 依赖: avgRisk_const_right
-/
lemma avgRisk_const_right (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (ν : Measure 𝓨) (π : Measure Θ) :
    avgRisk ℓ P (Kernel.const 𝓧 ν) π = ∫⁻ θ, ∫⁻ y, ℓ θ y ∂ν ∂π := by
  simp [avgRisk_const_right']

/--
lemma `bayesRisk_le_iInf'` / 引理 `bayesRisk_le_iInf'`

English:
lemma bayesRisk_le_iInf'
  given: (hl : Measurable (uncurry ℓ)) (P : Kernel Θ 𝓧) (π : Measure Θ)
  proof: by
  simp_rw [le_iInf_iff, bayesRisk]
  refine fun y => iInf_le_of_le (Kernel.const _ (Measure.dirac y)) ?_
  simp only [iInf_pos, avgRisk_const_right', mul_comm]
  gcongr with θ
  rw [lintegral_dirac' _ (by fun_prop)]

中文:
引理 bayesRisk_le_iInf'
  条件: (hl : 可测 (uncurry ℓ)) (P : 核 Θ 𝓧) (π : 测度 Θ)
  证明: by
  simp_rw [le_iInf_iff, bayesRisk]
  refine fun y => iInf_le_of_le (Kernel.const _ (Measure.dirac y)) ?_
  simp only [iInf_pos, avgRisk_const_right', mul_comm]
  gcongr with θ
  rw [lintegral_dirac' _ (by fun_prop)]

Depends on / 依赖: Kernel, Kernel.const, Measure, Measure.dirac, avgRisk_const_right, bayesRisk, fun_prop, iInf_le_of_le, iInf_pos, le_iInf_iff, lintegral_dirac, mul_comm, simp_rw
-/
lemma bayesRisk_le_iInf' (hl : Measurable (uncurry ℓ)) (P : Kernel Θ 𝓧) (π : Measure Θ) :
    bayesRisk ℓ P π <= ⨅ y, ∫⁻ θ, ℓ θ y * P θ .univ ∂π := by
  simp_rw [le_iInf_iff, bayesRisk]
  refine fun y => iInf_le_of_le (Kernel.const _ (Measure.dirac y)) ?_
  simp only [iInf_pos, avgRisk_const_right', mul_comm]
  gcongr with θ
  rw [lintegral_dirac' _ (by fun_prop)]

/--
lemma `bayesRisk_le_iInf` / 引理 `bayesRisk_le_iInf`

English:
lemma bayesRisk_le_iInf
  statement: (hl : Measurable (uncurry ℓ)) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
  proof: (bayesRisk_le_iInf' hl P π).trans_eq (by simp)

中文:
引理 bayesRisk_le_iInf
  结论: (hl : 可测 (uncurry ℓ)) (P : 核 Θ 𝓧) [是MarkovKernel P]
  证明: (bayesRisk_le_iInf' hl P π).trans_eq (by simp)

Depends on / 依赖: bayesRisk_le_iInf, trans_eq
-/
lemma bayesRisk_le_iInf (hl : Measurable (uncurry ℓ)) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (π : Measure Θ) :
    bayesRisk ℓ P π <= ⨅ y, ∫⁻ θ, ℓ θ y ∂π :=
  (bayesRisk_le_iInf' hl P π).trans_eq (by simp)

/--
lemma `bayesRisk_const'` / 引理 `bayesRisk_const'`

English:
lemma bayesRisk_const'
  statement: (hl : Measurable (uncurry ℓ))
  proof: by
  refine le_antisymm ((bayesRisk_le_iInf' hl _ _).trans_eq (by simp)) ?_
  simp_rw [bayesRisk, le_iInf_iff]
  intro κ hκ
  rw [avgRisk_const_left' hl]
  refine le_trans ?_ (iInf_mul_le_lintegral (fun y => ∫⁻ θ, ℓ θ y ∂π))
  rw [Measure.comp_apply_univ]; rw [ENNReal.iInf_mul' hl_pos (fun hμ => h_zero (by simpa using hμ))]
  gcongr with y
  rw [lintegral_mul_const]
  fun_prop

中文:
引理 bayesRisk_const'
  结论: (hl : 可测 (uncurry ℓ))
  证明: by
  refine le_antisymm ((bayesRisk_le_iInf' hl _ _).trans_eq (by simp)) ?_
  simp_rw [bayesRisk, le_iInf_iff]
  intro κ hκ
  rw [avgRisk_const_left' hl]
  refine le_trans ?_ (iInf_mul_le_lintegral (fun y => ∫⁻ θ, ℓ θ y ∂π))
  rw [Measure.comp_apply_univ]; rw [ENNReal.iInf_mul' hl_pos (fun hμ => h_zero (by simpa using hμ))]
  gcongr with y
  rw [lintegral_mul_const]
  fun_prop

Depends on / 依赖: ENNReal, ENNReal.iInf_mul, Measure, Measure.comp_apply_univ, avgRisk_const_left, bayesRisk, bayesRisk_le_iInf, comp_apply_univ, fun_prop, h_zero, hl_pos, iInf_mul, iInf_mul_le_lintegral, le_antisymm, le_iInf_iff, le_trans, lintegral_mul_const, simp_rw, trans_eq
-/
lemma bayesRisk_const' (hl : Measurable (uncurry ℓ))
    (μ : Measure 𝓧) [SFinite μ] (π : Measure Θ) [SFinite π]
    (hl_pos : μ .univ = ∞ -> ⨅ y, ∫⁻ θ, ℓ θ y ∂π = 0 -> exists y, ∫⁻ θ, ℓ θ y ∂π = 0)
    (h_zero : μ = 0 -> Nonempty 𝓨) :
    bayesRisk ℓ (Kernel.const Θ μ) π = ⨅ y, ∫⁻ θ, ℓ θ y * μ .univ ∂π := by
  refine le_antisymm ((bayesRisk_le_iInf' hl _ _).trans_eq (by simp)) ?_
  simp_rw [bayesRisk, le_iInf_iff]
  intro κ hκ
  rw [avgRisk_const_left' hl]
  refine le_trans ?_ (iInf_mul_le_lintegral (fun y => ∫⁻ θ, ℓ θ y ∂π))
  rw [Measure.comp_apply_univ]; rw [ENNReal.iInf_mul' hl_pos (fun hμ => h_zero (by simpa using hμ))]
  gcongr with y
  rw [lintegral_mul_const]
  fun_prop

/--
lemma `bayesRisk_const_of_neZero` / 引理 `bayesRisk_const_of_neZero`

English:
lemma bayesRisk_const_of_neZero
  statement: (hl : Measurable (uncurry ℓ))
  proof: bayesRisk_const' hl μ π (by simp) (by simp [NeZero.out])

中文:
引理 bayesRisk_const_of_neZero
  结论: (hl : 可测 (uncurry ℓ))
  证明: bayesRisk_const' hl μ π (by simp) (by simp [NeZero.out])

Depends on / 依赖: NeZero, NeZero.out, bayesRisk_const
-/
lemma bayesRisk_const_of_neZero (hl : Measurable (uncurry ℓ))
    (μ : Measure 𝓧) [NeZero μ] [IsFiniteMeasure μ] (π : Measure Θ) [SFinite π] :
    bayesRisk ℓ (Kernel.const Θ μ) π = ⨅ y, ∫⁻ θ, ℓ θ y * μ .univ ∂π :=
  bayesRisk_const' hl μ π (by simp) (by simp [NeZero.out])

/--
lemma `bayesRisk_const_of_nonempty` / 引理 `bayesRisk_const_of_nonempty`

English:
lemma bayesRisk_const_of_nonempty
  statement: [Nonempty 𝓨] (hl : Measurable (uncurry ℓ))
  proof: bayesRisk_const' hl μ π (by simp) (fun _ => inferInstance)

中文:
引理 bayesRisk_const_of_nonempty
  结论: [非空 𝓨] (hl : 可测 (uncurry ℓ))
  证明: bayesRisk_const' hl μ π (by simp) (fun _ => inferInstance)

Depends on / 依赖: bayesRisk_const
-/
lemma bayesRisk_const_of_nonempty [Nonempty 𝓨] (hl : Measurable (uncurry ℓ))
    (μ : Measure 𝓧) [IsFiniteMeasure μ] (π : Measure Θ) [SFinite π] :
    bayesRisk ℓ (Kernel.const Θ μ) π = ⨅ y, ∫⁻ θ, ℓ θ y * μ .univ ∂π :=
  bayesRisk_const' hl μ π (by simp) (fun _ => inferInstance)

/--
lemma `bayesRisk_const` / 引理 `bayesRisk_const`

English:
lemma bayesRisk_const
  statement: (hl : Measurable (uncurry ℓ))
  proof: by
  simp [bayesRisk_const_of_neZero hl μ π]

中文:
引理 bayesRisk_const
  结论: (hl : 可测 (uncurry ℓ))
  证明: by
  simp [bayesRisk_const_of_neZero hl μ π]

Depends on / 依赖: bayesRisk_const_of_neZero
-/
lemma bayesRisk_const (hl : Measurable (uncurry ℓ))
    (μ : Measure 𝓧) [IsProbabilityMeasure μ] (π : Measure Θ) [SFinite π] :
    bayesRisk ℓ (Kernel.const Θ μ) π = ⨅ y, ∫⁻ θ, ℓ θ y ∂π := by
  simp [bayesRisk_const_of_neZero hl μ π]

end Const

section Bounds

/--
lemma `avgRisk_le_mul'` / 引理 `avgRisk_le_mul'`

English:
lemma avgRisk_le_mul'
  statement: (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ)
  proof: calc ∫⁻ θ, ∫⁻ y, ℓ θ y ∂(κ ∘ₖ P) θ ∂π
  _ <= ∫⁻ θ, ∫⁻ y, C ∂(κ ∘ₖ P) θ ∂π := by gcongr with θ y; exact hℓC θ y
  _ = ∫⁻ θ, C * ∫⁻ x, κ x .univ ∂P θ ∂π := by simp [Kernel.comp_apply' _ _ _ .univ]
  _ <= ∫⁻ θ, C * ∫⁻ x, κ.bound ∂P θ ∂π := by
    gcongr with θ x
    exact Kernel.measure_le_bound κ x Set.univ
  _ <= ∫⁻ θ, C * κ.bound * P.bound ∂π := by
    conv_lhs => simp only [lintegral_const, ← mul_assoc]
    gcongr with θ
    exact Kernel.measure_le_bound P θ Set.univ
  _ = C * κ.bound * P.bound * π Set.univ := by simp

中文:
引理 avgRisk_le_mul'
  结论: (P : 核 Θ 𝓧) (κ : 核 𝓧 𝓨) (π : 测度 Θ)
  证明: calc ∫⁻ θ, ∫⁻ y, ℓ θ y ∂(κ ∘ₖ P) θ ∂π
  _ <= ∫⁻ θ, ∫⁻ y, C ∂(κ ∘ₖ P) θ ∂π := by gcongr with θ y; exact hℓC θ y
  _ = ∫⁻ θ, C * ∫⁻ x, κ x .univ ∂P θ ∂π := by simp [Kernel.comp_apply' _ _ _ .univ]
  _ <= ∫⁻ θ, C * ∫⁻ x, κ.bound ∂P θ ∂π := by
    gcongr with θ x
    exact Kernel.measure_le_bound κ x Set.univ
  _ <= ∫⁻ θ, C * κ.bound * P.bound ∂π := by
    conv_lhs => simp only [lintegral_const, ← mul_assoc]
    gcongr with θ
    exact Kernel.measure_le_bound P θ Set.univ
  _ = C * κ.bound * P.bound * π Set.univ := by simp

Depends on / 依赖: Kernel, Kernel.comp_apply, Kernel.measure_le_bound, P.bound, Set.univ, comp_apply, conv_lhs, lintegral_const, measure_le_bound, mul_assoc
-/
lemma avgRisk_le_mul' (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ)
    {C : Real>=0} (hℓC : forall θ y, ℓ θ y <= C) :
    avgRisk ℓ P κ π <= C * κ.bound * P.bound * π Set.univ :=
  calc ∫⁻ θ, ∫⁻ y, ℓ θ y ∂(κ ∘ₖ P) θ ∂π
  _ <= ∫⁻ θ, ∫⁻ y, C ∂(κ ∘ₖ P) θ ∂π := by gcongr with θ y; exact hℓC θ y
  _ = ∫⁻ θ, C * ∫⁻ x, κ x .univ ∂P θ ∂π := by simp [Kernel.comp_apply' _ _ _ .univ]
  _ <= ∫⁻ θ, C * ∫⁻ x, κ.bound ∂P θ ∂π := by
    gcongr with θ x
    exact Kernel.measure_le_bound κ x Set.univ
  _ <= ∫⁻ θ, C * κ.bound * P.bound ∂π := by
    conv_lhs => simp only [lintegral_const, ← mul_assoc]
    gcongr with θ
    exact Kernel.measure_le_bound P θ Set.univ
  _ = C * κ.bound * P.bound * π Set.univ := by simp

/--
lemma `avgRisk_le_mul` / 引理 `avgRisk_le_mul`

English:
lemma avgRisk_le_mul
  statement: (P : Kernel Θ 𝓧) [IsMarkovKernel P] (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ]
  proof: by
  refine (avgRisk_le_mul' P κ π hℓC).trans ?_
  rcases isEmpty_or_nonempty Θ
  · simp
  · rcases isEmpty_or_nonempty 𝓧 <;> simp

中文:
引理 avgRisk_le_mul
  结论: (P : 核 Θ 𝓧) [是MarkovKernel P] (κ : 核 𝓧 𝓨) [是MarkovKernel κ]
  证明: by
  refine (avgRisk_le_mul' P κ π hℓC).trans ?_
  rcases isEmpty_or_nonempty Θ
  · simp
  · rcases isEmpty_or_nonempty 𝓧 <;> simp

Depends on / 依赖: avgRisk_le_mul, isEmpty_or_nonempty
-/
lemma avgRisk_le_mul (P : Kernel Θ 𝓧) [IsMarkovKernel P] (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ]
    (π : Measure Θ) [IsProbabilityMeasure π] {C : Real>=0} (hℓC : forall θ y, ℓ θ y <= C) :
    avgRisk ℓ P κ π <= C := by
  refine (avgRisk_le_mul' P κ π hℓC).trans ?_
  rcases isEmpty_or_nonempty Θ
  · simp
  · rcases isEmpty_or_nonempty 𝓧 <;> simp

/--
lemma `bayesRisk_le_mul'` / 引理 `bayesRisk_le_mul'`

English:
lemma bayesRisk_le_mul'
  statement: [h𝓨 : Nonempty 𝓨] (P : Kernel Θ 𝓧) (π : Measure Θ)
  proof: by
  refine (bayesRisk_le_avgRisk ℓ P (Kernel.const 𝓧 (Measure.dirac h𝓨.some)) π).trans ?_
  refine (avgRisk_le_mul' P (Kernel.const 𝓧 (Measure.dirac h𝓨.some)) π hℓC).trans ?_
  rcases isEmpty_or_nonempty 𝓧 <;> simp

中文:
引理 bayesRisk_le_mul'
  结论: [h𝓨 : 非空 𝓨] (P : 核 Θ 𝓧) (π : 测度 Θ)
  证明: by
  refine (bayesRisk_le_avgRisk ℓ P (Kernel.const 𝓧 (Measure.dirac h𝓨.some)) π).trans ?_
  refine (avgRisk_le_mul' P (Kernel.const 𝓧 (Measure.dirac h𝓨.some)) π hℓC).trans ?_
  rcases isEmpty_or_nonempty 𝓧 <;> simp

Depends on / 依赖: Kernel, Kernel.const, Measure, Measure.dirac, avgRisk_le_mul, bayesRisk_le_avgRisk, isEmpty_or_nonempty
-/
lemma bayesRisk_le_mul' [h𝓨 : Nonempty 𝓨] (P : Kernel Θ 𝓧) (π : Measure Θ)
    {C : Real>=0} (hℓC : forall θ y, ℓ θ y <= C) :
    bayesRisk ℓ P π <= C * P.bound * π Set.univ := by
  refine (bayesRisk_le_avgRisk ℓ P (Kernel.const 𝓧 (Measure.dirac h𝓨.some)) π).trans ?_
  refine (avgRisk_le_mul' P (Kernel.const 𝓧 (Measure.dirac h𝓨.some)) π hℓC).trans ?_
  rcases isEmpty_or_nonempty 𝓧 <;> simp

/--
lemma `bayesRisk_le_mul` / 引理 `bayesRisk_le_mul`

English:
lemma bayesRisk_le_mul
  statement: [Nonempty 𝓨] (P : Kernel Θ 𝓧) [IsMarkovKernel P]
  proof: by
  refine (bayesRisk_le_mul' P π hℓC).trans ?_
  rcases isEmpty_or_nonempty Θ <;> simp

中文:
引理 bayesRisk_le_mul
  结论: [非空 𝓨] (P : 核 Θ 𝓧) [是MarkovKernel P]
  证明: by
  refine (bayesRisk_le_mul' P π hℓC).trans ?_
  rcases isEmpty_or_nonempty Θ <;> simp

Depends on / 依赖: bayesRisk_le_mul, isEmpty_or_nonempty
-/
lemma bayesRisk_le_mul [Nonempty 𝓨] (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (π : Measure Θ) [IsProbabilityMeasure π] {C : Real>=0} (hℓC : forall θ y, ℓ θ y <= C) :
    bayesRisk ℓ P π <= C := by
  refine (bayesRisk_le_mul' P π hℓC).trans ?_
  rcases isEmpty_or_nonempty Θ <;> simp

/--
lemma `bayesRisk_lt_top` / 引理 `bayesRisk_lt_top`

English:
lemma bayesRisk_lt_top
  statement: [Nonempty 𝓨] (P : Kernel Θ 𝓧)
  proof: by
  refine (bayesRisk_le_mul' P π hℓC).trans_lt ?_
  simp [ENNReal.mul_lt_top_iff, P.bound_lt_top]

中文:
引理 bayesRisk_lt_top
  结论: [非空 𝓨] (P : 核 Θ 𝓧)
  证明: by
  refine (bayesRisk_le_mul' P π hℓC).trans_lt ?_
  simp [ENNReal.mul_lt_top_iff, P.bound_lt_top]

Depends on / 依赖: ENNReal, ENNReal.mul_lt_top_iff, P.bound_lt_top, bayesRisk_le_mul, bound_lt_top, mul_lt_top_iff, trans_lt
-/
lemma bayesRisk_lt_top [Nonempty 𝓨] (P : Kernel Θ 𝓧)
    [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π] {C : Real>=0} (hℓC : forall θ y, ℓ θ y <= C) :
    bayesRisk ℓ P π < ∞ := by
  refine (bayesRisk_le_mul' P π hℓC).trans_lt ?_
  simp [ENNReal.mul_lt_top_iff, P.bound_lt_top]

end Bounds

/--
lemma `bayesRisk_discard` / 引理 `bayesRisk_discard`

English:
lemma bayesRisk_discard
  given: (hl : Measurable (uncurry ℓ)) (π : Measure Θ) [SFinite π]
  proof: by
  rw [Kernel.discard_eq_const]; rw [bayesRisk_const hl]

中文:
引理 bayesRisk_discard
  条件: (hl : 可测 (uncurry ℓ)) (π : 测度 Θ) [SFinite π]
  证明: by
  rw [Kernel.discard_eq_const]; rw [bayesRisk_const hl]

Depends on / 依赖: Kernel, Kernel.discard_eq_const, bayesRisk_const, discard_eq_const
-/
lemma bayesRisk_discard (hl : Measurable (uncurry ℓ)) (π : Measure Θ) [SFinite π] :
    bayesRisk ℓ (Kernel.discard Θ) π = ⨅ y, ∫⁻ θ, ℓ θ y ∂π := by
  rw [Kernel.discard_eq_const]; rw [bayesRisk_const hl]

section Subsingleton

variable [Subsingleton 𝓧] [Nonempty 𝓨]

/--
lemma `bayesRisk_eq_iInf_measure_of_subsingleton` / 引理 `bayesRisk_eq_iInf_measure_of_subsingleton`

English:
lemma bayesRisk_eq_iInf_measure_of_subsingleton
  proof: by
  rcases isEmpty_or_nonempty 𝓧 with hX | hX
  · simp [iInf_subtype']
  obtain x := hX.some
  rw [bayesRisk]; rw [iInf_subtype']; rw [iInf_subtype']
  let e : {κ : Kernel 𝓧 𝓨 // IsMarkovKernel κ} ≃ {μ : Measure 𝓨 // IsProbabilityMeasure μ} :=
    { toFun κ := ⟨κ.1 x, κ.2.isProbabilityMeasure x⟩
      invFun μ := ⟨Kernel.const 𝓧 μ, ⟨fun _ => μ.2⟩⟩
      left_inv κ := by ext y; simp only [Kernel.const_apply, Subsingleton.elim x y]
      right_inv μ := by simp }
  rw [← Equiv.iInf_comp e.symm]
  rfl

中文:
引理 bayesRisk_eq_iInf_measure_of_subsingleton
  证明: by
  rcases isEmpty_or_nonempty 𝓧 with hX | hX
  · simp [iInf_subtype']
  obtain x := hX.some
  rw [bayesRisk]; rw [iInf_subtype']; rw [iInf_subtype']
  let e : {κ : Kernel 𝓧 𝓨 // IsMarkovKernel κ} ≃ {μ : Measure 𝓨 // IsProbabilityMeasure μ} :=
    { toFun κ := ⟨κ.1 x, κ.2.isProbabilityMeasure x⟩
      invFun μ := ⟨Kernel.const 𝓧 μ, ⟨fun _ => μ.2⟩⟩
      left_inv κ := by ext y; simp only [Kernel.const_apply, Subsingleton.elim x y]
      right_inv μ := by simp }
  rw [← Equiv.iInf_comp e.symm]
  rfl

Depends on / 依赖: Equiv.iInf_comp, IsMarkovKernel, IsProbabilityMeasure, Kernel, Kernel.const, Kernel.const_apply, Measure, Subsingleton, Subsingleton.elim, bayesRisk, const_apply, e.symm, hX.some, iInf_comp, iInf_subtype, invFun, isEmpty_or_nonempty, isProbabilityMeasure, left_inv, right_inv
-/
lemma bayesRisk_eq_iInf_measure_of_subsingleton :
    bayesRisk ℓ P π
      = ⨅ (μ : Measure 𝓨) (_ : IsProbabilityMeasure μ), avgRisk ℓ P (Kernel.const 𝓧 μ) π := by
  rcases isEmpty_or_nonempty 𝓧 with hX | hX
  · simp [iInf_subtype']
  obtain x := hX.some
  rw [bayesRisk]; rw [iInf_subtype']; rw [iInf_subtype']
  let e : {κ : Kernel 𝓧 𝓨 // IsMarkovKernel κ} ≃ {μ : Measure 𝓨 // IsProbabilityMeasure μ} :=
    { toFun κ := ⟨κ.1 x, κ.2.isProbabilityMeasure x⟩
      invFun μ := ⟨Kernel.const 𝓧 μ, ⟨fun _ => μ.2⟩⟩
      left_inv κ := by ext y; simp only [Kernel.const_apply, Subsingleton.elim x y]
      right_inv μ := by simp }
  rw [← Equiv.iInf_comp e.symm]
  rfl

/--
lemma `bayesRisk_of_subsingleton'` / 引理 `bayesRisk_of_subsingleton'`

English:
lemma bayesRisk_of_subsingleton'
  given: [SFinite π] (hl : Measurable (uncurry ℓ))
  proof: by
  refine le_antisymm (bayesRisk_le_iInf' hl _ _) ?_
  rw [bayesRisk_eq_iInf_measure_of_subsingleton]
  simp only [avgRisk_const_right', le_iInf_iff]
  refine fun μ hμ => (iInf_le_lintegral (μ := μ) _).trans_eq ?_
  rw [lintegral_lintegral_swap]
  · congr with θ
    rw [lintegral_mul_const _ (by fun_prop)]; rw [mul_comm]
  · have := P.measurable_coe .univ
    fun_prop

中文:
引理 bayesRisk_of_subsingleton'
  条件: [SFinite π] (hl : 可测 (uncurry ℓ))
  证明: by
  refine le_antisymm (bayesRisk_le_iInf' hl _ _) ?_
  rw [bayesRisk_eq_iInf_measure_of_subsingleton]
  simp only [avgRisk_const_right', le_iInf_iff]
  refine fun μ hμ => (iInf_le_lintegral (μ := μ) _).trans_eq ?_
  rw [lintegral_lintegral_swap]
  · congr with θ
    rw [lintegral_mul_const _ (by fun_prop)]; rw [mul_comm]
  · have := P.measurable_coe .univ
    fun_prop

Depends on / 依赖: P.measurable_coe, avgRisk_const_right, bayesRisk_eq_iInf_measure_of_subsingleton, bayesRisk_le_iInf, fun_prop, iInf_le_lintegral, le_antisymm, le_iInf_iff, lintegral_lintegral_swap, lintegral_mul_const, measurable_coe, mul_comm, trans_eq
-/
lemma bayesRisk_of_subsingleton' [SFinite π] (hl : Measurable (uncurry ℓ)) :
    bayesRisk ℓ P π = ⨅ y, ∫⁻ θ, ℓ θ y * P θ .univ ∂π := by
  refine le_antisymm (bayesRisk_le_iInf' hl _ _) ?_
  rw [bayesRisk_eq_iInf_measure_of_subsingleton]
  simp only [avgRisk_const_right', le_iInf_iff]
  refine fun μ hμ => (iInf_le_lintegral (μ := μ) _).trans_eq ?_
  rw [lintegral_lintegral_swap]
  · congr with θ
    rw [lintegral_mul_const _ (by fun_prop)]; rw [mul_comm]
  · have := P.measurable_coe .univ
    fun_prop

/--
lemma `bayesRisk_of_subsingleton` / 引理 `bayesRisk_of_subsingleton`

English:
lemma bayesRisk_of_subsingleton
  given: [IsMarkovKernel P] [SFinite π] (hl : Measurable (uncurry ℓ))
  proof: by
  simp [bayesRisk_of_subsingleton' hl]

中文:
引理 bayesRisk_of_subsingleton
  条件: [是MarkovKernel P] [SFinite π] (hl : 可测 (uncurry ℓ))
  证明: by
  simp [bayesRisk_of_subsingleton' hl]

Depends on / 依赖: bayesRisk_of_subsingleton
-/
lemma bayesRisk_of_subsingleton [IsMarkovKernel P] [SFinite π] (hl : Measurable (uncurry ℓ)) :
    bayesRisk ℓ P π = ⨅ y, ∫⁻ θ, ℓ θ y ∂π := by
  simp [bayesRisk_of_subsingleton' hl]

end Subsingleton

section Compositions

/--
lemma `bayesRisk_le_bayesRisk_comp` / 引理 `bayesRisk_le_bayesRisk_comp`

English:
lemma bayesRisk_le_bayesRisk_comp
  statement: (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧)
  proof: by
  simp only [bayesRisk, avgRisk, le_iInf_iff]
  intro κ hκ
  rw [← κ.comp_assoc η]
  exact iInf_le_of_le (κ ∘ₖ η) (iInf_le_of_le inferInstance le_rfl)

中文:
引理 bayesRisk_le_bayesRisk_comp
  结论: (ℓ : Θ -> 𝓨 -> 实数>=0∞) (P : 核 Θ 𝓧)
  证明: by
  simp only [bayesRisk, avgRisk, le_iInf_iff]
  intro κ hκ
  rw [← κ.comp_assoc η]
  exact iInf_le_of_le (κ ∘ₖ η) (iInf_le_of_le inferInstance le_rfl)

Depends on / 依赖: avgRisk, bayesRisk, comp_assoc, iInf_le_of_le, le_iInf_iff, le_rfl
-/
lemma bayesRisk_le_bayesRisk_comp (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧)
    (π : Measure Θ) (η : Kernel 𝓧 𝓧') [IsMarkovKernel η] :
    bayesRisk ℓ P π <= bayesRisk ℓ (η ∘ₖ P) π := by
  simp only [bayesRisk, avgRisk, le_iInf_iff]
  intro κ hκ
  rw [← κ.comp_assoc η]
  exact iInf_le_of_le (κ ∘ₖ η) (iInf_le_of_le inferInstance le_rfl)

/--
lemma `bayesRisk_le_bayesRisk_map` / 引理 `bayesRisk_le_bayesRisk_map`

English:
lemma bayesRisk_le_bayesRisk_map
  statement: (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧)
  proof: by
  rw [← Kernel.deterministic_comp_eq_map hf]
  exact bayesRisk_le_bayesRisk_comp _ _ _ _

中文:
引理 bayesRisk_le_bayesRisk_map
  结论: (ℓ : Θ -> 𝓨 -> 实数>=0∞) (P : 核 Θ 𝓧)
  证明: by
  rw [← Kernel.deterministic_comp_eq_map hf]
  exact bayesRisk_le_bayesRisk_comp _ _ _ _

Depends on / 依赖: Kernel, Kernel.deterministic_comp_eq_map, bayesRisk_le_bayesRisk_comp, deterministic_comp_eq_map
-/
lemma bayesRisk_le_bayesRisk_map (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧)
    (π : Measure Θ) {f : 𝓧 -> 𝓧'} (hf : Measurable f) :
    bayesRisk ℓ P π <= bayesRisk ℓ (P.map f) π := by
  rw [← Kernel.deterministic_comp_eq_map hf]
  exact bayesRisk_le_bayesRisk_comp _ _ _ _

/--
lemma `bayesRisk_compProd_le_bayesRisk` / 引理 `bayesRisk_compProd_le_bayesRisk`

English:
lemma bayesRisk_compProd_le_bayesRisk
  statement: (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧)
  proof: by
  have : P = (Kernel.deterministic Prod.fst (by fun_prop)) ∘ₖ (P otimesₖ η) := by
    rw [Kernel.deterministic_comp_eq_map]; rw [← Kernel.fst_eq]; rw [Kernel.fst_compProd]
  nth_rw 2 [this]
  exact bayesRisk_le_bayesRisk_comp _ _ _ _

中文:
引理 bayesRisk_compProd_le_bayesRisk
  结论: (ℓ : Θ -> 𝓨 -> 实数>=0∞) (P : 核 Θ 𝓧)
  证明: by
  have : P = (Kernel.deterministic Prod.fst (by fun_prop)) ∘ₖ (P otimesₖ η) := by
    rw [Kernel.deterministic_comp_eq_map]; rw [← Kernel.fst_eq]; rw [Kernel.fst_compProd]
  nth_rw 2 [this]
  exact bayesRisk_le_bayesRisk_comp _ _ _ _

Depends on / 依赖: Kernel, Kernel.deterministic, Kernel.deterministic_comp_eq_map, Kernel.fst_compProd, Kernel.fst_eq, Prod.fst, bayesRisk_le_bayesRisk_comp, deterministic, deterministic_comp_eq_map, fst_compProd, fst_eq, fun_prop, nth_rw
-/
lemma bayesRisk_compProd_le_bayesRisk (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧)
    [IsSFiniteKernel P] (π : Measure Θ) (η : Kernel (Θ × 𝓧) 𝓧') [IsMarkovKernel η] :
    bayesRisk ℓ (P otimesₖ η) π <= bayesRisk ℓ P π := by
  have : P = (Kernel.deterministic Prod.fst (by fun_prop)) ∘ₖ (P otimesₖ η) := by
    rw [Kernel.deterministic_comp_eq_map]; rw [← Kernel.fst_eq]; rw [Kernel.fst_compProd]
  nth_rw 2 [this]
  exact bayesRisk_le_bayesRisk_comp _ _ _ _

end Compositions

end ProbabilityTheory
