/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic

import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Independence.Process.HasIndepIncrements.IsGaussianProcess

/-!
# Brownian motion

In this file we define two predicates over stochastic processes `X : ℝ≥0 → Ω → ℝ` given
a probability measure `P : Measure Ω`. `IsPreBrownianReal X P` means that
`X` is a pre-Brownian motion. It means that it has the law of the Brownian motion, namely that
its finite dimensional distributions are given by `projectiveFamily`. Then
`IsBrownianReal X P` means that `X` is a Brownian motion, which means that it is a pre-Brownian
motion with almost surely continuous paths.

We prove that a centered Gaussian process `X` with covariances given by `cov[X s, X t; P] = min s t`
is a pre-Brownian motion and provide basic invariance properties. We also prove the
weak Markov property: if `B` is a pre-Brownian motion and `t₀ : ℝ≥0`, then the process
`t ↦ B (t + t₀) - B t₀` is a pre-Brownian motion independent from `(B t | t ≤ t₀)`.

## Main definitions

* `IsPreBrownianReal X P`: A stochastic process is called pre-Brownian if its finite-dimensional
  laws are those of the Brownian motion, see `projectiveFamily`.
* `IsBrownianReal X P`: A stochastic process is called Brownian if its finite-dimensional laws
  are those of the Brownian motion, see `IsPreBrownianReal`,
  and if it has almost-surely continuous paths.

## Main statements

* `IsGaussianProcess.isPreBrownianReal_of_covariance`: A centered Gaussian process with the right
  covariance is a pre-Brownian motion.
* `HasIndepIncrements.isPreBrownianReal_of_hasLaw`: A stochastic process `X` with independent
  increments and such that for all `t`, `X t` has law `gaussianReal 0 t` is a pre-Brownian motion.
* `IsPreBrownianReal.indepFun_shift`: The weak Markov property: If `B` is a pre-Brownian motion,
  then `B (t₀ + t) - B t₀` is a pre-Brownian motion which is independent from `(B t, t ≤ t₀)`.

## Tags

pre-Brownian motion, Brownian motion, Markov property

-/

@[expose] public section

open MeasureTheory ProbabilityTheory.BrownianReal
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B X : Real>=0 -> Ω -> Real} {P : Measure Ω}

namespace ProbabilityTheory

section IsPreBrownianReal

/-! ### Pre-Brownian motion -/

/--
Definition of `IsPreBrownianReal` / `IsPreBrownianReal` 的定义

English:
structure IsPreBrownianReal
  parameters: (X : Real>=0 -> Ω -> Real) (P : Measure Ω := by volume_tac)
  axioms and operations (2):
    - mk' : :
    - hasLaw : forall I : Finset Real>=0, HasLaw (fun ω => I.restrict (X · ω)) (projectiveFamily I) P

中文:
结构 IsPreBrownianReal
  参数: (X : 实数>=0 -> Ω -> 实数) (P : Measure Ω := by volume_tac)
  公理与运算 (2 个):
    - mk' : :
    - hasLaw : 对任意 I : Finset 实数>=0, HasLaw (fun ω => I.restrict (X · ω)) (projectiveFamily I) P

Depends on / 依赖: Finset, HasLaw, I.restrict, hasLaw, projectiveFamily, restrict, volume_tac
-/
structure IsPreBrownianReal (X : Real>=0 -> Ω -> Real) (P : Measure Ω := by volume_tac) : Prop where
  mk' ::
  hasLaw : forall I : Finset Real>=0, HasLaw (fun ω => I.restrict (X · ω)) (projectiveFamily I) P

/--
lemma `IsPreBrownianReal.congr` / 引理 `IsPreBrownianReal.congr`

English:
lemma IsPreBrownianReal.congr
  statement: {C : Real>=0 -> Ω -> Real} (hB : IsPreBrownianReal B P)
  proof: by
    refine (hB.hasLaw I).congr ?_
    have : forallᵐ ω ∂P, forall i : I, B i ω = C i ω := ae_all_iff.2 fun _ => h _
    filter_upwards [this] with ω hω using funext fun i => (hω i).symm

中文:
引理 IsPreBrownianReal.congr
  结论: {C : 实数>=0 -> Ω -> 实数} (hB : IsPreBrownian实数 B P)
  证明: by
    refine (hB.hasLaw I).congr ?_
    have : forallᵐ ω ∂P, forall i : I, B i ω = C i ω := ae_all_iff.2 fun _ => h _
    filter_upwards [this] with ω hω using funext fun i => (hω i).symm

Depends on / 依赖: ae_all_iff, filter_upwards, hB.hasLaw, hasLaw
-/
lemma IsPreBrownianReal.congr {C : Real>=0 -> Ω -> Real} (hB : IsPreBrownianReal B P)
    (h : forall t, B t =ᵐ[P] C t) :
    IsPreBrownianReal C P where
  hasLaw I := by
    refine (hB.hasLaw I).congr ?_
    have : forallᵐ ω ∂P, forall i : I, B i ω = C i ω := ae_all_iff.2 fun _ => h _
    filter_upwards [this] with ω hω using funext fun i => (hω i).symm

/--
lemma `IsPreBrownianReal.isGaussianProcess` / 引理 `IsPreBrownianReal.isGaussianProcess`

English:
lemma IsPreBrownianReal.isGaussianProcess
  given: (hB : IsPreBrownianReal B P)
  statement: IsGaussianProcess B P where
  proof: (hB.hasLaw I).hasGaussianLaw

中文:
引理 IsPreBrownianReal.isGaussianProcess
  条件: (hB : IsPreBrownian实数 B P)
  结论: IsGaussianProcess B P where
  证明: (hB.hasLaw I).hasGaussianLaw

Depends on / 依赖: hB.hasLaw, hasGaussianLaw, hasLaw
-/
lemma IsPreBrownianReal.isGaussianProcess (hB : IsPreBrownianReal B P) : IsGaussianProcess B P where
  hasGaussianLaw I := (hB.hasLaw I).hasGaussianLaw

/--
lemma `IsPreBrownianReal.aemeasurable` / 引理 `IsPreBrownianReal.aemeasurable`

English:
lemma IsPreBrownianReal.aemeasurable
  given: (hB : IsPreBrownianReal B P) (t : Real>=0)
  proof: HasGaussianLaw.aemeasurable (hB.isGaussianProcess.hasGaussianLaw_eval t)

中文:
引理 IsPreBrownianReal.aemeasurable
  条件: (hB : IsPreBrownian实数 B P) (t : 实数>=0)
  证明: HasGaussianLaw.aemeasurable (hB.isGaussianProcess.hasGaussianLaw_eval t)

Depends on / 依赖: HasGaussianLaw, HasGaussianLaw.aemeasurable, aemeasurable, hB.isGaussianProcess.hasGaussianLaw_eval, hasGaussianLaw_eval, isGaussianProcess
-/
lemma IsPreBrownianReal.aemeasurable (hB : IsPreBrownianReal B P) (t : Real>=0) :
    AEMeasurable (B t) P :=
  HasGaussianLaw.aemeasurable (hB.isGaussianProcess.hasGaussianLaw_eval t)

/--
lemma `IsPreBrownianReal.hasLaw_eval` / 引理 `IsPreBrownianReal.hasLaw_eval`

English:
lemma IsPreBrownianReal.hasLaw_eval
  given: (hB : IsPreBrownianReal B P) (t : Real>=0)
  proof: (measurePreserving_eval_projectiveFamily ⟨t, by simp⟩).hasLaw.comp (hB.hasLaw {t})

中文:
引理 IsPreBrownianReal.hasLaw_eval
  条件: (hB : IsPreBrownian实数 B P) (t : 实数>=0)
  证明: (measurePreserving_eval_projectiveFamily ⟨t, by simp⟩).hasLaw.comp (hB.hasLaw {t})

Depends on / 依赖: hB.hasLaw, hasLaw, hasLaw.comp, measurePreserving_eval_projectiveFamily
-/
lemma IsPreBrownianReal.hasLaw_eval (hB : IsPreBrownianReal B P) (t : Real>=0) :
    HasLaw (B t) (gaussianReal 0 t) P :=
  (measurePreserving_eval_projectiveFamily ⟨t, by simp⟩).hasLaw.comp (hB.hasLaw {t})

/--
lemma `IsPreBrownianReal.eval_zero_ae_eq_zero` / 引理 `IsPreBrownianReal.eval_zero_ae_eq_zero`

English:
lemma IsPreBrownianReal.eval_zero_ae_eq_zero
  given: (hB : IsPreBrownianReal B P)
  proof: by
  have := hB.hasLaw_eval 0
  rw [gaussianReal_zero_var] at this
  exact this.ae_eq_of_dirac

中文:
引理 IsPreBrownianReal.eval_zero_ae_eq_zero
  条件: (hB : IsPreBrownian实数 B P)
  证明: by
  have := hB.hasLaw_eval 0
  rw [gaussianReal_zero_var] at this
  exact this.ae_eq_of_dirac

Depends on / 依赖: ae_eq_of_dirac, gaussianReal_zero_var, hB.hasLaw_eval, hasLaw_eval, this.ae_eq_of_dirac
-/
lemma IsPreBrownianReal.eval_zero_ae_eq_zero (hB : IsPreBrownianReal B P) :
    forallᵐ ω ∂P, B 0 ω = 0 := by
  have := hB.hasLaw_eval 0
  rw [gaussianReal_zero_var] at this
  exact this.ae_eq_of_dirac

/--
lemma `IsPreBrownianReal.hasLaw_sub` / 引理 `IsPreBrownianReal.hasLaw_sub`

English:
lemma IsPreBrownianReal.hasLaw_sub
  given: (hB : IsPreBrownianReal B P) (s t : Real>=0)
  proof: (measurePreserving_eval_sub_eval_projectiveFamily
    {s, t} ⟨s, by simp⟩ ⟨t, by simp⟩).hasLaw.comp (hB.hasLaw _)

中文:
引理 IsPreBrownianReal.hasLaw_sub
  条件: (hB : IsPreBrownian实数 B P) (s t : 实数>=0)
  证明: (measurePreserving_eval_sub_eval_projectiveFamily
    {s, t} ⟨s, by simp⟩ ⟨t, by simp⟩).hasLaw.comp (hB.hasLaw _)

Depends on / 依赖: hB.hasLaw, hasLaw, hasLaw.comp, measurePreserving_eval_sub_eval_projectiveFamily
-/
lemma IsPreBrownianReal.hasLaw_sub (hB : IsPreBrownianReal B P) (s t : Real>=0) :
    HasLaw (B s - B t) (gaussianReal 0 (nndist s.1 t.1)) P :=
  (measurePreserving_eval_sub_eval_projectiveFamily
    {s, t} ⟨s, by simp⟩ ⟨t, by simp⟩).hasLaw.comp (hB.hasLaw _)

/--
lemma `IsPreBrownianReal.integral_eval` / 引理 `IsPreBrownianReal.integral_eval`

English:
lemma IsPreBrownianReal.integral_eval
  given: (hB : IsPreBrownianReal B P) (t : Real>=0)
  proof: by
  rw [(hB.hasLaw_eval t).integral_eq]; rw [integral_id_gaussianReal]

中文:
引理 IsPreBrownianReal.integral_eval
  条件: (hB : IsPreBrownian实数 B P) (t : 实数>=0)
  证明: by
  rw [(hB.hasLaw_eval t).integral_eq]; rw [integral_id_gaussianReal]

Depends on / 依赖: hB.hasLaw_eval, hasLaw_eval, integral_eq, integral_id_gaussianReal
-/
lemma IsPreBrownianReal.integral_eval (hB : IsPreBrownianReal B P) (t : Real>=0) :
    P[B t] = 0 := by
  rw [(hB.hasLaw_eval t).integral_eq]; rw [integral_id_gaussianReal]

/--
lemma `IsPreBrownianReal.integrable_eval` / 引理 `IsPreBrownianReal.integrable_eval`

English:
lemma IsPreBrownianReal.integrable_eval
  given: (hB : IsPreBrownianReal B P) (t : Real>=0)
  proof: (hB.isGaussianProcess.hasGaussianLaw_eval t).integrable

中文:
引理 IsPreBrownianReal.integrable_eval
  条件: (hB : IsPreBrownian实数 B P) (t : 实数>=0)
  证明: (hB.isGaussianProcess.hasGaussianLaw_eval t).integrable

Depends on / 依赖: hB.isGaussianProcess.hasGaussianLaw_eval, hasGaussianLaw_eval, integrable, isGaussianProcess
-/
lemma IsPreBrownianReal.integrable_eval (hB : IsPreBrownianReal B P) (t : Real>=0) :
    Integrable (B t) P := (hB.isGaussianProcess.hasGaussianLaw_eval t).integrable

/--
lemma `IsPreBrownianReal.covariance_eval` / 引理 `IsPreBrownianReal.covariance_eval`

English:
lemma IsPreBrownianReal.covariance_eval
  given: (hB : IsPreBrownianReal B P) (s t : Real>=0)
  proof: by
  convert (hB.hasLaw {s, t}).covariance_fun_comp
    (f := Function.eval ⟨s, by simp⟩) (g := fun x => x ⟨t, by simp⟩) ?_ ?_
  · simp
  · simp
  · rw [covariance_eval_projectiveFamily]
  all_goals exact Measurable.aemeasurable (by fun_prop)

中文:
引理 IsPreBrownianReal.covariance_eval
  条件: (hB : IsPreBrownian实数 B P) (s t : 实数>=0)
  证明: by
  convert (hB.hasLaw {s, t}).covariance_fun_comp
    (f := Function.eval ⟨s, by simp⟩) (g := fun x => x ⟨t, by simp⟩) ?_ ?_
  · simp
  · simp
  · rw [covariance_eval_projectiveFamily]
  all_goals exact Measurable.aemeasurable (by fun_prop)

Depends on / 依赖: Function, Function.eval, Measurable, Measurable.aemeasurable, aemeasurable, all_goals, convert, covariance_eval_projectiveFamily, covariance_fun_comp, fun_prop, hB.hasLaw, hasLaw
-/
lemma IsPreBrownianReal.covariance_eval (hB : IsPreBrownianReal B P) (s t : Real>=0) :
    cov[B s, B t; P] = min s t := by
  convert (hB.hasLaw {s, t}).covariance_fun_comp
    (f := Function.eval ⟨s, by simp⟩) (g := fun x => x ⟨t, by simp⟩) ?_ ?_
  · simp
  · simp
  · rw [covariance_eval_projectiveFamily]
  all_goals exact Measurable.aemeasurable (by fun_prop)

/--
lemma `IsPreBrownianReal.covariance_fun_eval` / 引理 `IsPreBrownianReal.covariance_fun_eval`

English:
lemma IsPreBrownianReal.covariance_fun_eval
  given: (hB : IsPreBrownianReal B P) (s t : Real>=0)
  proof: hB.covariance_eval s t

中文:
引理 IsPreBrownianReal.covariance_fun_eval
  条件: (hB : IsPreBrownian实数 B P) (s t : 实数>=0)
  证明: hB.covariance_eval s t

Depends on / 依赖: covariance_eval, hB.covariance_eval
-/
lemma IsPreBrownianReal.covariance_fun_eval (hB : IsPreBrownianReal B P) (s t : Real>=0) :
    cov[fun ω => B s ω, fun ω => B t ω; P] = min s t :=
  hB.covariance_eval s t

/--
theorem `IsGaussianProcess.isPreBrownianReal_of_covariance` / 定理 `IsGaussianProcess.isPreBrownianReal_of_covariance`

English:
theorem IsGaussianProcess.isPreBrownianReal_of_covariance
  statement: (h1 : IsGaussianProcess X P)
  proof: by
    refine ⟨aemeasurable_pi_lambda _ fun _ => h1.aemeasurable _, ?_⟩
    apply (MeasurableEquiv.toLp 2 (_ -> Real)).map_measurableEquiv_injective
    rw [MeasurableEquiv.coe_toLp]; rw [← PiLp.coe_symm_continuousLinearEquiv 2 Real]
    have := (h1.hasGaussianLaw I).isGaussian_map
    apply IsGauss

中文:
定理 IsGaussianProcess.isPreBrownianReal_of_covariance
  结论: (h1 : IsGaussianProcess X P)
  证明: by
    refine ⟨aemeasurable_pi_lambda _ fun _ => h1.aemeasurable _, ?_⟩
    apply (MeasurableEquiv.toLp 2 (_ -> Real)).map_measurableEquiv_injective
    rw [MeasurableEquiv.coe_toLp]; rw [← PiLp.coe_symm_continuousLinearEquiv 2 Real]
    have := (h1.hasGaussianLaw I).isGaussian_map
    apply IsGauss

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.integral_comp_comm, ContinuousLinearEquiv.integral_comp_id_comm, IsGaussian, IsGaussian.ext, MeasurableEquiv, MeasurableEquiv.coe_toLp, MeasurableEquiv.toLp, PiLp.coe_symm_continuousLinearEquiv, PiLp.continuousLinearEquiv_symm_apply, aemeasurable, aemeasurable_pi_lambda, coe_symm_continuousLinearEquiv, coe_toLp, continuousLinearEquiv_symm_apply, h1.aemeasurable, h1.hasGaussianLaw, hasGaussianLaw, id_eq, integral_comp_comm
-/
theorem IsGaussianProcess.isPreBrownianReal_of_covariance (h1 : IsGaussianProcess X P)
    (h2 : forall t, P[X t] = 0) (h3 : forall s t, s <= t -> cov[X s, X t; P] = s) :
    IsPreBrownianReal X P where
  hasLaw I := by
    refine ⟨aemeasurable_pi_lambda _ fun _ => h1.aemeasurable _, ?_⟩
    apply (MeasurableEquiv.toLp 2 (_ -> Real)).map_measurableEquiv_injective
    rw [MeasurableEquiv.coe_toLp]; rw [← PiLp.coe_symm_continuousLinearEquiv 2 Real]
    have := (h1.hasGaussianLaw I).isGaussian_map
    apply IsGaussian.ext
    · rw [integral_map, integral_map, integral_map]
      · simp only [id_eq]
        rw [ContinuousLinearEquiv.integral_comp_id_comm]; rw [ContinuousLinearEquiv.integral_comp_comm]
        simp only [PiLp.continuousLinearEquiv_symm_apply, integral_id_projectiveFamily,
          WithLp.toLp_zero, WithLp.toLp_eq_zero]
        congr with i
        rw [eval_integral]
        · simpa using h2 _
        · exact fun _ => (h1.hasGaussianLaw_eval _).integrable
      any_goals fun_prop
      exact aemeasurable_pi_lambda _ fun _ => h1.aemeasurable _
    · rw [← ContinuousLinearMap.toBilinForm_inj]
      refine LinearMap.BilinForm.ext_of_isSymm isPosSemidef_covarianceBilin.isSymm
        isPosSemidef_covarianceBilin.isSymm fun x => ?_
      simp only [ContinuousLinearMap.toBilinForm_apply]
      rw [PiLp.coe_symm_continuousLinearEquiv]; rw [covarianceBilin_apply_pi]; rw [covarianceBilin_apply_pi]
      · congrm ∑ i, ∑ j, _ * ?_
        rw [covariance_eval_projectiveFamily]; rw [covariance_map]
        · wlog hij : i.1 <= j.1 generalizing i j
          · rw [covariance_comm, this j i (by grind), min_comm]
          rw [min_eq_left hij]
          exact h3 i j hij
        any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
        exact aemeasurable_pi_lambda _ (fun _ => h1.aemeasurable _)
      · exact fun i => (IsGaussian.hasGaussianLaw_id.eval i).memLp_two
      · exact fun i => ((h1.hasGaussianLaw I).isGaussian_map.hasGaussianLaw_id.eval i).memLp_two

/--
lemma `IsPreBrownianReal.hasIndepIncrements` / 引理 `IsPreBrownianReal.hasIndepIncrements`

English:
lemma IsPreBrownianReal.hasIndepIncrements
  given: (hB : IsPreBrownianReal B P)
  proof: by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine fun n t ht => hB.isGaussianProcess.hasGaussianLaw_increments.iIndepFun_of_covariance_eq_zero
    fun i j hij => ?_
  rw [covariance_fun_sub_fun_sub]
  · simp_rw [hB.covariance_fun_eval]
    wlog h : i < j genera

中文:
引理 IsPreBrownianReal.hasIndepIncrements
  条件: (hB : IsPreBrownian实数 B P)
  证明: by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine fun n t ht => hB.isGaussianProcess.hasGaussianLaw_increments.iIndepFun_of_covariance_eq_zero
    fun i j hij => ?_
  rw [covariance_fun_sub_fun_sub]
  · simp_rw [hB.covariance_fun_eval]
    wlog h : i < j genera

Depends on / 依赖: Fin.le_of_lt, Fin.strictMono_succ, IsProbabilityMeasure, castSucc, covariance_fun_eval, covariance_fun_sub_fun_sub, generalizing, hB.covariance_fun_eval, hB.isGaussianProcess.hasGaussianLaw_increments.iIndepFun_of_covariance_eq_zero, hB.isGaussianProcess.isProbabilityMeasure, hasGaussianLaw_increments, hij.symm, i.castSucc, i.succ, iIndepFun_of_covariance_eq_zero, isGaussianProcess, isProbabilityMeasure, j.castSucc, j.succ, le_of_lt
-/
lemma IsPreBrownianReal.hasIndepIncrements (hB : IsPreBrownianReal B P) :
    HasIndepIncrements B P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine fun n t ht => hB.isGaussianProcess.hasGaussianLaw_increments.iIndepFun_of_covariance_eq_zero
    fun i j hij => ?_
  rw [covariance_fun_sub_fun_sub]
  · simp_rw [hB.covariance_fun_eval]
    wlog h : i < j generalizing i j
    · simp_rw [← this j i hij.symm (by grind), min_comm]
      grind
.le have h1 : i.succ <= j.succ := Fin.strictMono_succ h
    have h2 : i.castSucc <= j.succ := Fin.le_of_lt h1
    have h3 : i.castSucc <= j.castSucc := Fin.le_castSucc_iff.mpr h1
    rw [min_eq_left (ht h1)]; rw [min_eq_left (ht h)]; rw [min_eq_left (ht h2)]; rw [min_eq_left (ht h3)]
    simp
  all_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two

/--
theorem `HasIndepIncrements.isPreBrownianReal_of_hasLaw` / 定理 `HasIndepIncrements.isPreBrownianReal_of_hasLaw`

English:
theorem HasIndepIncrements.isPreBrownianReal_of_hasLaw
  proof: by
  have h0 : forallᵐ ω ∂P, X 0 ω = 0 := by
      apply HasLaw.ae_eq_of_dirac
      rw [← gaussianReal_zero_var]
      exact law 0
  refine IsGaussianProcess.isPreBrownianReal_of_covariance ?_ (fun t => ?_) (fun s t hst => ?_)
  · exact incr.isGaussianProcess (fun t => (law t).hasGaussianLaw) h0
  

中文:
定理 HasIndepIncrements.isPreBrownianReal_of_hasLaw
  证明: by
  have h0 : forallᵐ ω ∂P, X 0 ω = 0 := by
      apply HasLaw.ae_eq_of_dirac
      rw [← gaussianReal_zero_var]
      exact law 0
  refine IsGaussianProcess.isPreBrownianReal_of_covariance ?_ (fun t => ?_) (fun s t hst => ?_)
  · exact incr.isGaussianProcess (fun t => (law t).hasGaussianLaw) h0
  

Depends on / 依赖: HasLaw, HasLaw.ae_eq_of_dirac, IsGaussianProcess, IsGaussianProcess.isPreBrownianReal_of_covariance, ae_eq_of_dirac, covariance_add_right, gaussianReal_zero_var, h1.c, hasGaussianLaw, incr.indepFun_eval_sub, incr.isGaussianProcess, indepFun_eval_sub, integral_eq, integral_id_gaussianReal, isGaussianProcess, isPreBrownianReal_of_covariance, isProbabilityMeasure, zero_le
-/
theorem HasIndepIncrements.isPreBrownianReal_of_hasLaw
    (law : forall t, HasLaw (X t) (gaussianReal 0 t) P) (incr : HasIndepIncrements X P) :
    IsPreBrownianReal X P := by
  have h0 : forallᵐ ω ∂P, X 0 ω = 0 := by
      apply HasLaw.ae_eq_of_dirac
      rw [← gaussianReal_zero_var]
      exact law 0
  refine IsGaussianProcess.isPreBrownianReal_of_covariance ?_ (fun t => ?_) (fun s t hst => ?_)
  · exact incr.isGaussianProcess (fun t => (law t).hasGaussianLaw) h0
  · rw [(law t).integral_eq, integral_id_gaussianReal]
  have h1 := incr.indepFun_eval_sub zero_le hst h0
  have := (law 0).isProbabilityMeasure
  have h2 : X t = X t - X s + X s := by simp
  rw [h2]; rw [covariance_add_right]; rw [h1.covariance_eq_zero]; rw [covariance_self]; rw [(law s).variance_eq]; rw [variance_id_gaussianReal]
  · simp
  · exact (law s).aemeasurable
  · exact (law s).hasGaussianLaw.memLp_two
  · exact (law t).hasGaussianLaw.memLp_two.sub (law s).hasGaussianLaw.memLp_two
  · exact (law s).hasGaussianLaw.memLp_two
  · exact (law t).hasGaussianLaw.memLp_two.sub (law s).hasGaussianLaw.memLp_two
  · exact (law s).hasGaussianLaw.memLp_two

/--
lemma `IsPreBrownianReal.neg` / 引理 `IsPreBrownianReal.neg`

English:
lemma IsPreBrownianReal.neg
  given: (hB : IsPreBrownianReal B P)
  statement: IsPreBrownianReal (-B) P
  proof: by
  refine HasIndepIncrements.isPreBrownianReal_of_hasLaw (fun t => ?_) (fun n t ht => ?_)
  · simpa using gaussianReal_neg (hB.hasLaw_eval t)
  convert (hB.hasIndepIncrements n t ht).comp (fun _ x => -x) (by fun_prop)
  simp
  grind

中文:
引理 IsPreBrownianReal.neg
  条件: (hB : IsPreBrownian实数 B P)
  结论: IsPreBrownian实数 (-B) P
  证明: by
  refine HasIndepIncrements.isPreBrownianReal_of_hasLaw (fun t => ?_) (fun n t ht => ?_)
  · simpa using gaussianReal_neg (hB.hasLaw_eval t)
  convert (hB.hasIndepIncrements n t ht).comp (fun _ x => -x) (by fun_prop)
  simp
  grind

Depends on / 依赖: HasIndepIncrements, HasIndepIncrements.isPreBrownianReal_of_hasLaw, convert, fun_prop, gaussianReal_neg, hB.hasIndepIncrements, hB.hasLaw_eval, hasIndepIncrements, hasLaw_eval, isPreBrownianReal_of_hasLaw
-/
lemma IsPreBrownianReal.neg (hB : IsPreBrownianReal B P) : IsPreBrownianReal (-B) P := by
  refine HasIndepIncrements.isPreBrownianReal_of_hasLaw (fun t => ?_) (fun n t ht => ?_)
  · simpa using gaussianReal_neg (hB.hasLaw_eval t)
  convert (hB.hasIndepIncrements n t ht).comp (fun _ x => -x) (by fun_prop)
  simp
  grind

/--
lemma `IsPreBrownianReal.smul` / 引理 `IsPreBrownianReal.smul`

English:
lemma IsPreBrownianReal.smul
  given: (hB : IsPreBrownianReal B P) {c : Real>=0} (hc : c != 0)
  proof: by
  refine IsGaussianProcess.isPreBrownianReal_of_covariance ?_ (fun t => ?_) (fun s t hst => ?_)
  · have this t ω : (√c)⁻¹ * B (c * t) ω = (√c)⁻¹ • ((B ∘ (c * ·)) t ω) := rfl
    simp_rw [this]
    exact (hB.isGaussianProcess.comp_right _).smul _
  · rw [integral_const_mul, hB.integral_eval, mul_

中文:
引理 IsPreBrownianReal.smul
  条件: (hB : IsPreBrownian实数 B P) {c : 实数>=0} (hc : c != 0)
  证明: by
  refine IsGaussianProcess.isPreBrownianReal_of_covariance ?_ (fun t => ?_) (fun s t hst => ?_)
  · have this t ω : (√c)⁻¹ * B (c * t) ω = (√c)⁻¹ • ((B ∘ (c * ·)) t ω) := rfl
    simp_rw [this]
    exact (hB.isGaussianProcess.comp_right _).smul _
  · rw [integral_const_mul, hB.integral_eval, mul_

Depends on / 依赖: IsGaussianProcess, IsGaussianProcess.isPreBrownianReal_of_covariance, NonUnitalSubringClass, NonUnitalSubringClass.addSubgroupClass, addSubgroupClass, comp_right, covariance_const_mul_left, covariance_const_mul_right, covariance_eval, hB.covariance_eval, hB.integral_eval, hB.isGaussianProcess.comp_right, integral_const_mul, integral_eval, isGaussianProcess, isPreBrownianReal_of_covariance, min_eq_left, mul_le_mul_right, mul_zero, simp_rw
-/
lemma IsPreBrownianReal.smul (hB : IsPreBrownianReal B P) {c : Real>=0} (hc : c != 0) :
    IsPreBrownianReal (fun t ω => (√c)⁻¹ * B (c * t) ω) P := by
  refine IsGaussianProcess.isPreBrownianReal_of_covariance ?_ (fun t => ?_) (fun s t hst => ?_)
  · have this t ω : (√c)⁻¹ * B (c * t) ω = (√c)⁻¹ • ((B ∘ (c * ·)) t ω) := rfl
    simp_rw [this]
    exact (hB.isGaussianProcess.comp_right _).smul _
  · rw [integral_const_mul, hB.integral_eval, mul_zero]
  · rw [covariance_const_mul_left, covariance_const_mul_right, hB.covariance_eval, min_eq_left]
    · simp [field]
    · exact mul_le_mul_right hst c

/--
lemma `IsPreBrownianReal.shift` / 引理 `IsPreBrownianReal.shift`

English:
lemma IsPreBrownianReal.shift
  given: (hB : IsPreBrownianReal B P) (t₀ : Real>=0)
  proof: by
  refine (hB.isGaussianProcess.shift t₀).isPreBrownianReal_of_covariance
    (fun t => ?_) (fun s t hst => ?_)
  · rw [integral_sub, hB.integral_eval, hB.integral_eval, sub_zero]
    all_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).integrable
  · have := hB.isGaussianProcess.isProbabi

中文:
引理 IsPreBrownianReal.shift
  条件: (hB : IsPreBrownian实数 B P) (t₀ : 实数>=0)
  证明: by
  refine (hB.isGaussianProcess.shift t₀).isPreBrownianReal_of_covariance
    (fun t => ?_) (fun s t hst => ?_)
  · rw [integral_sub, hB.integral_eval, hB.integral_eval, sub_zero]
    all_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).integrable
  · have := hB.isGaussianProcess.isProbabi

Depends on / 依赖: NonUnitalNonAssocRing, add_, all_goals, covariance_eval, covariance_fun_sub_left, covariance_fun_sub_right, fast_instance, hB.covariance_eval, hB.integral_eval, hB.isGaussianProcess.hasGaussianLaw_eval, hB.isGaussianProcess.isProbabilityMeasure, hB.isGaussianProcess.shift, hasGaussianLaw_eval, integrable, integral_eval, integral_sub, isGaussianProcess, isPreBrownianReal_of_covariance, isProbabilityMeasure, sub_zero
-/
lemma IsPreBrownianReal.shift (hB : IsPreBrownianReal B P) (t₀ : Real>=0) :
    IsPreBrownianReal (fun t ω => B (t₀ + t) ω - B t₀ ω) P := by
  refine (hB.isGaussianProcess.shift t₀).isPreBrownianReal_of_covariance
    (fun t => ?_) (fun s t hst => ?_)
  · rw [integral_sub, hB.integral_eval, hB.integral_eval, sub_zero]
    all_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).integrable
  · have := hB.isGaussianProcess.isProbabilityMeasure
    rw [covariance_fun_sub_left]; rw [covariance_fun_sub_right]; rw [covariance_fun_sub_right]; rw [hB.covariance_eval]; rw [hB.covariance_eval]; rw [hB.covariance_eval]; rw [hB.covariance_eval]; rw [← add_min]; rw [min_eq_left hst]; rw [min_eq_right]; rw [min_eq_left]; rw [min_self]
    any_goals simp
    any_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
    exact hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two

/--
lemma `IsPreBrownianReal.indepFun_shift` / 引理 `IsPreBrownianReal.indepFun_shift`

English:
lemma IsPreBrownianReal.indepFun_shift
  given: (hB : IsPreBrownianReal B P) (t₀ : Real>=0)
  proof: by
  have mX t := hB.aemeasurable t
  apply IsGaussianProcess.indepFun_of_covariance_eq_zero
  · apply hB.isGaussianProcess.of_isGaussianProcess
    rintro (t | ⟨t, ht⟩)
    · exact ⟨{t₀, t₀ + t},
        { toFun x := x ⟨t₀ + t, by simp⟩ - x ⟨t₀, by simp⟩
          map_add' x y := by simp; abel
    

中文:
引理 IsPreBrownianReal.indepFun_shift
  条件: (hB : IsPreBrownian实数 B P) (t₀ : 实数>=0)
  证明: by
  have mX t := hB.aemeasurable t
  apply IsGaussianProcess.indepFun_of_covariance_eq_zero
  · apply hB.isGaussianProcess.of_isGaussianProcess
    rintro (t | ⟨t, ht⟩)
    · exact ⟨{t₀, t₀ + t},
        { toFun x := x ⟨t₀ + t, by simp⟩ - x ⟨t₀, by simp⟩
          map_add' x y := by simp; abel
    

Depends on / 依赖: IsGaussianProcess, IsGaussianProcess.indepFun_of_covariance_eq_zero, NonUnitalRing, SetLike, aemeasurable, any_goals, fun_prop, hB.aemeasurable, hB.isGaussianProcess.isProbability, hB.isGaussianProcess.of_isGaussianProcess, indepFun_of_covariance_eq_zero, isGaussianProcess, isProbability, map_add, map_smul, of_isGaussianProcess, toNonUnitalRing
-/
lemma IsPreBrownianReal.indepFun_shift (hB : IsPreBrownianReal B P) (t₀ : Real>=0) :
    IndepFun (fun ω t => B (t₀ + t) ω - B t₀ ω) (fun ω (t : Set.Iic t₀) => B t ω) P := by
  have mX t := hB.aemeasurable t
  apply IsGaussianProcess.indepFun_of_covariance_eq_zero
  · apply hB.isGaussianProcess.of_isGaussianProcess
    rintro (t | ⟨t, ht⟩)
    · exact ⟨{t₀, t₀ + t},
        { toFun x := x ⟨t₀ + t, by simp⟩ - x ⟨t₀, by simp⟩
          map_add' x y := by simp; abel
          map_smul' c x := by simp; ring }, by simp⟩
    · exact ⟨{t},
        { toFun x := x ⟨t, by simp⟩
          map_add' x y := by simp
          map_smul' c x := by simp }, by simp⟩
  any_goals fun_prop
  · rintro s ⟨t, ht : t <= t₀⟩
    have := hB.isGaussianProcess.isProbabilityMeasure
    rw [covariance_fun_sub_left]; rw [hB.covariance_eval]; rw [hB.covariance_eval]; rw [min_eq_right]; rw [min_eq_right]; rw [sub_self]
    · grind
    · simp [ht, le_add_right]
    all_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two

/--
lemma `IsPreBrownianReal.inv` / 引理 `IsPreBrownianReal.inv`

English:
lemma IsPreBrownianReal.inv
  given: (hB : IsPreBrownianReal B P)
  proof: by
  refine IsGaussianProcess.isPreBrownianReal_of_covariance ?_ (fun t => ?_) (fun s t hst => ?_)
  · exact (IsGaussianProcess.comp_right hB.isGaussianProcess _).smul _
  · rw [integral_const_mul, hB.integral_eval, mul_zero]
  · have := hB.isGaussianProcess.isProbabilityMeasure
    rw [covariance_c

中文:
引理 IsPreBrownianReal.inv
  条件: (hB : IsPreBrownian实数 B P)
  证明: by
  refine IsGaussianProcess.isPreBrownianReal_of_covariance ?_ (fun t => ?_) (fun s t hst => ?_)
  · exact (IsGaussianProcess.comp_right hB.isGaussianProcess _).smul _
  · rw [integral_const_mul, hB.integral_eval, mul_zero]
  · have := hB.isGaussianProcess.isProbabilityMeasure
    rw [covariance_c

Depends on / 依赖: IsGaussianProcess, IsGaussianProcess.comp_right, IsGaussianProcess.isPreBrownianReal_of_covariance, NonUnitalNonAssocCommRing, comp_right, covariance_const_mul_left, covariance_const_mul_right, covariance_eval, eq_or_ne, hB.covariance_eval, hB.integral_eval, hB.isGaussianProcess, hB.isGaussianProcess.isProbabilityMeasure, integral_const_mul, integral_eval, isGaussianProcess, isPreBrownianReal_of_covariance, isProbabilityMeasure, min_eq_right, mul_zero
-/
lemma IsPreBrownianReal.inv (hB : IsPreBrownianReal B P) :
    IsPreBrownianReal (fun t ω => t * (B (1 / t) ω)) P := by
  refine IsGaussianProcess.isPreBrownianReal_of_covariance ?_ (fun t => ?_) (fun s t hst => ?_)
  · exact (IsGaussianProcess.comp_right hB.isGaussianProcess _).smul _
  · rw [integral_const_mul, hB.integral_eval, mul_zero]
  · have := hB.isGaussianProcess.isProbabilityMeasure
    rw [covariance_const_mul_left]; rw [covariance_const_mul_right]; rw [hB.covariance_eval]
    obtain rfl | hs := eq_or_ne s 0
    · simp
    have : 0 < t := (pos_of_ne_zero hs).trans_le hst
    rw [min_eq_right]
    · norm_cast
      field_simp
    exact one_div_le_one_div_of_le (pos_of_ne_zero hs) hst

end IsPreBrownianReal

section IsBrownianReal

/-! ### Brownian motion -/

variable {B X : Real>=0 -> Ω -> Real}

/--
Definition of `IsBrownianReal` / `IsBrownianReal` 的定义

English:
structure IsBrownianReal
  parameters: (X : Real>=0 -> Ω -> Real) (P : Measure Ω := by volume_tac)
  extends: IsPreBrownianReal X P
  axioms and operations (1):
    - cont : forallᵐ ω ∂P, Continuous (X · ω)

中文:
结构 IsBrownianReal
  参数: (X : 实数>=0 -> Ω -> 实数) (P : Measure Ω := by volume_tac)
  继承: IsPreBrownianReal X P
  公理与运算 (1 个):
    - cont : 对任意ᵐ ω ∂P, Continuous (X · ω)

Depends on / 依赖: Continuous, IsPreBrownianReal, NonUnitalCommRing, SetLike, extends, toNonUnitalCommRing, volume_tac
-/
structure IsBrownianReal (X : Real>=0 -> Ω -> Real) (P : Measure Ω := by volume_tac) : Prop
    extends IsPreBrownianReal X P where
  cont : forallᵐ ω ∂P, Continuous (X · ω)

/--
lemma `IsBrownianReal.neg` / 引理 `IsBrownianReal.neg`

English:
lemma IsBrownianReal.neg
  given: (hB : IsBrownianReal B P)
  proof: hB.toIsPreBrownianReal.neg
  cont := hB.cont.mono (fun _ _ => by simpa [← Pi.neg_def, continuous_neg_iff])

中文:
引理 IsBrownianReal.neg
  条件: (hB : IsBrownian实数 B P)
  证明: hB.toIsPreBrownianReal.neg
  cont := hB.cont.mono (fun _ _ => by simpa [← Pi.neg_def, continuous_neg_iff])

Depends on / 依赖: hB.toIsPreBrownianReal.neg, toIsPreBrownianReal
-/
lemma IsBrownianReal.neg (hB : IsBrownianReal B P) :
    IsBrownianReal (-B) P where
  toIsPreBrownianReal := hB.toIsPreBrownianReal.neg
  cont := hB.cont.mono (fun _ _ => by simpa [← Pi.neg_def, continuous_neg_iff])

/--
lemma `IsBrownianReal.smul` / 引理 `IsBrownianReal.smul`

English:
lemma IsBrownianReal.smul
  given: (hB : IsBrownianReal B P) {c : Real>=0} (hc : c != 0)
  proof: hB.toIsPreBrownianReal.smul hc
  cont := by
    filter_upwards [hB.cont] with ω h
    fun_prop

中文:
引理 IsBrownianReal.smul
  条件: (hB : IsBrownian实数 B P) {c : 实数>=0} (hc : c != 0)
  证明: hB.toIsPreBrownianReal.smul hc
  cont := by
    filter_upwards [hB.cont] with ω h
    fun_prop

Depends on / 依赖: hB.toIsPreBrownianReal.smul, toIsPreBrownianReal
-/
lemma IsBrownianReal.smul (hB : IsBrownianReal B P) {c : Real>=0} (hc : c != 0) :
    IsBrownianReal (fun t ω => (√c)⁻¹ * B (c * t) ω) P where
  toIsPreBrownianReal := hB.toIsPreBrownianReal.smul hc
  cont := by
    filter_upwards [hB.cont] with ω h
    fun_prop

/--
lemma `IsBrownianReal.shift` / 引理 `IsBrownianReal.shift`

English:
lemma IsBrownianReal.shift
  given: (hB : IsBrownianReal B P) (t₀ : Real>=0)
  proof: hB.toIsPreBrownianReal.shift t₀
  cont := by
    filter_upwards [hB.cont] with ω h
    fun_prop

中文:
引理 IsBrownianReal.shift
  条件: (hB : IsBrownian实数 B P) (t₀ : 实数>=0)
  证明: hB.toIsPreBrownianReal.shift t₀
  cont := by
    filter_upwards [hB.cont] with ω h
    fun_prop

Depends on / 依赖: hB.toIsPreBrownianReal.shift, toIsPreBrownianReal
-/
lemma IsBrownianReal.shift (hB : IsBrownianReal B P) (t₀ : Real>=0) :
    IsBrownianReal (fun t ω => B (t₀ + t) ω - B t₀ ω) P where
  toIsPreBrownianReal := hB.toIsPreBrownianReal.shift t₀
  cont := by
    filter_upwards [hB.cont] with ω h
    fun_prop

/--
lemma `IsBrownianReal.tendsto_nhds_zero` / 引理 `IsBrownianReal.tendsto_nhds_zero`

English:
lemma IsBrownianReal.tendsto_nhds_zero
  given: (hB : IsBrownianReal B P)
  proof: by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω h1 h2
  convert h1.tendsto 0
  exact h2.symm

中文:
引理 IsBrownianReal.tendsto_nhds_zero
  条件: (hB : IsBrownian实数 B P)
  证明: by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω h1 h2
  convert h1.tendsto 0
  exact h2.symm

Depends on / 依赖: convert, eval_zero_ae_eq_zero, filter_upwards, h1.tendsto, h2.symm, hB.cont, hB.eval_zero_ae_eq_zero, tendsto
-/
lemma IsBrownianReal.tendsto_nhds_zero (hB : IsBrownianReal B P) :
    forallᵐ ω ∂P, Filter.Tendsto (B · ω) (𝓝 0) (𝓝 0) := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω h1 h2
  convert h1.tendsto 0
  exact h2.symm

end IsBrownianReal

end ProbabilityTheory
