/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic

import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!

# A stochastic process with independent increments and Gaussian marginals is Gaussian

We prove that a stochastic process with independent increments and Gaussian marginals is Gaussian.
To do so, we first define `I.orderEmbOfFinWithBot : Fin (#I + 1) → T`, which is
the map `(⊥, t₁, ..., tₙ)`, where `t₁ < ... < tₙ` are the elements of `I`
and `⊥` is the smallest element of `T`.

Assume then that `X` is a stochastic process with independent increments and Gaussian marginals,
and such that `X ⊥ = 0` almost surely. Then
`X tᵢ = ∑ j ≤ i-1, (X tⱼ₊₁ - X tⱼ)`. Therefore the vector `(X t₁, ..., X tₙ)` can be obtained
from the vector of the increments by a linear map. It remains to show that the vector of
the increments is Gaussian. Because increments are independent, it is enough to show that each
increment is Gaussian. This follows from the fact that `X tᵢ` and `X tᵢ₊₁` are Gaussian,
and `X tᵢ` and `X tᵢ₊₁ - X tᵢ` are independent (see `IndepFun.hasGaussianLaw_sub_of_sub`).

## Main statement

* `HasIndepIncrements.isGaussianProcess`: A stochastic process `X` with independent increments,
  such that `X t` is Gaussian for all `t` and such that `X ⊥ = 0` almost surely
  is a Gaussian process.

## Tags

independent increments, Gaussian process

-/

open MeasureTheory Finset

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [LinearOrder T]

namespace Finset

variable (I : Finset T)

section Bot

variable [Bot T]

/--
Definition of `orderEmbOfFinWithBot` / `orderEmbOfFinWithBot` 的定义

English:
definition orderEmbOfFinWithBot
  signature: (i : Fin (#I + 1))
  body: if h : i = 0
    then ⊥
    else I.orderEmbOfFin rfl (i.pred h)

@[simp]

中文:
定义 orderEmbOfFinWithBot
  签名: (i : Fin (#I + 1))
  定义体: if h : i = 0
    then ⊥
    else I.orderEmbOfFin rfl (i.pred h)

@[simp]

Depends on / 依赖: I.orderEmbOfFin, i.pred, orderEmbOfFin
-/
noncomputable def orderEmbOfFinWithBot (i : Fin (#I + 1)) : T :=
  if h : i = 0
    then ⊥
    else I.orderEmbOfFin rfl (i.pred h)

@[simp]
/--
lemma `orderEmbOfFinWithBot_zero` / 引理 `orderEmbOfFinWithBot_zero`

English:
lemma orderEmbOfFinWithBot_zero
  statement: I.orderEmbOfFinWithBot 0 = ⊥
  proof: rfl

中文:
引理 orderEmbOfFinWithBot_zero
  结论: I.orderEmbOfFinWithBot 0 = ⊥
  证明: rfl
-/
lemma orderEmbOfFinWithBot_zero : I.orderEmbOfFinWithBot 0 = ⊥ := rfl

/--
lemma `orderEmbOfFinWithBot_of_ne_zero` / 引理 `orderEmbOfFinWithBot_of_ne_zero`

English:
lemma orderEmbOfFinWithBot_of_ne_zero
  given: (i : Fin (#I + 1)) (hi : i != 0)
  proof: by
  rw [orderEmbOfFinWithBot]; rw [dif_neg hi]

@[simp]

中文:
引理 orderEmbOfFinWithBot_of_ne_zero
  条件: (i : Fin (#I + 1)) (hi : i != 0)
  证明: by
  rw [orderEmbOfFinWithBot]; rw [dif_neg hi]

@[simp]

Depends on / 依赖: dif_neg, orderEmbOfFinWithBot
-/
lemma orderEmbOfFinWithBot_of_ne_zero (i : Fin (#I + 1)) (hi : i != 0) :
    I.orderEmbOfFinWithBot i = I.orderEmbOfFin rfl (i.pred hi) := by
  rw [orderEmbOfFinWithBot]; rw [dif_neg hi]

@[simp]
/--
lemma `orderEmbOfFinWithBot_succ` / 引理 `orderEmbOfFinWithBot_succ`

English:
lemma orderEmbOfFinWithBot_succ
  given: (i : Fin #I)
  proof: by
  rw [orderEmbOfFinWithBot_of_ne_zero]; rw [Fin.pred_succ]
  simp

中文:
引理 orderEmbOfFinWithBot_succ
  条件: (i : Fin #I)
  证明: by
  rw [orderEmbOfFinWithBot_of_ne_zero]; rw [Fin.pred_succ]
  simp

Depends on / 依赖: Fin.pred_succ, orderEmbOfFinWithBot_of_ne_zero, pred_succ
-/
lemma orderEmbOfFinWithBot_succ (i : Fin #I) :
    I.orderEmbOfFinWithBot i.succ = I.orderEmbOfFin rfl i := by
  rw [orderEmbOfFinWithBot_of_ne_zero]; rw [Fin.pred_succ]
  simp

end Bot

/--
lemma `monotone_orderEmbOfFinWithBot` / 引理 `monotone_orderEmbOfFinWithBot`

English:
lemma monotone_orderEmbOfFinWithBot
  given: [OrderBot T]
  statement: Monotone (I.orderEmbOfFinWithBot)
  proof: by
  intro i j hij
  obtain rfl | hi := eq_or_ne i 0
  · simp
  rw [orderEmbOfFinWithBot_of_ne_zero I i hi]; rw [orderEmbOfFinWithBot_of_ne_zero I j (by grind)]
  exact OrderEmbedding.monotone _ (by simpa)

中文:
引理 monotone_orderEmbOfFinWithBot
  条件: [OrderBot T]
  结论: Monotone (I.orderEmbOfFinWithBot)
  证明: by
  intro i j hij
  obtain rfl | hi := eq_or_ne i 0
  · simp
  rw [orderEmbOfFinWithBot_of_ne_zero I i hi]; rw [orderEmbOfFinWithBot_of_ne_zero I j (by grind)]
  exact OrderEmbedding.monotone _ (by simpa)

Depends on / 依赖: OrderEmbedding, OrderEmbedding.monotone, eq_or_ne, monotone, orderEmbOfFinWithBot_of_ne_zero
-/
lemma monotone_orderEmbOfFinWithBot [OrderBot T] : Monotone (I.orderEmbOfFinWithBot) := by
  intro i j hij
  obtain rfl | hi := eq_or_ne i 0
  · simp
  rw [orderEmbOfFinWithBot_of_ne_zero I i hi]; rw [orderEmbOfFinWithBot_of_ne_zero I j (by grind)]
  exact OrderEmbedding.monotone _ (by simpa)

end Finset

namespace ProbabilityTheory

/--
Definition of `incrementsToRestrict` / `incrementsToRestrict` 的定义

English:
definition incrementsToRestrict
  signature: (R : Type*) [Semiring R] [AddCommMonoid E]
  body: { toFun x i := ∑ j <= (I.orderIsoOfFin rfl).symm i, x j
    map_add' x y := by ext; simp [sum_add_distrib]
    map_smul' m x := by ext; simp [smul_sum]
    cont := by fun_prop }

中文:
定义 incrementsToRestrict
  签名: (R : 类型) [Semiring R] [AddCommMonoid E]
  定义体: { toFun x i := ∑ j <= (I.orderIsoOfFin rfl).symm i, x j
    map_add' x y := by ext; simp [sum_add_distrib]
    map_smul' m x := by ext; simp [smul_sum]
    cont := by fun_prop }

Depends on / 依赖: I.orderIsoOfFin, fun_prop, map_add, map_smul, orderIsoOfFin, smul_sum, sum_add_distrib
-/
noncomputable def incrementsToRestrict (R : Type*) [Semiring R] [AddCommMonoid E]
    [Module R E] [TopologicalSpace E] [ContinuousAdd E] (I : Finset T) :
    (Fin #I -> E) ->L[R] (I -> E) :=
  { toFun x i := ∑ j <= (I.orderIsoOfFin rfl).symm i, x j
    map_add' x y := by ext; simp [sum_add_distrib]
    map_smul' m x := by ext; simp [smul_sum]
    cont := by fun_prop }

/--
lemma `incrementsToRestrict_increments_orderEmbOfFinWithBot_ae_eq_restrict` / 引理 `incrementsToRestrict_increments_orderEmbOfFinWithBot_ae_eq_restrict`

English:
lemma incrementsToRestrict_increments_orderEmbOfFinWithBot_ae_eq_restrict
  statement: [Bot T] (R : Type*)
  proof: by
  filter_upwards [h] with ω hω
  ext t
  simp only [restrict, incrementsToRestrict, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, Function.comp_apply]
  rw [Fin.sum_Iic_sub _ (fun j => X (I.orderEmbOfFinWithBot j) ω)]
  simp [hω, orderEmbOfFin]

中文:
引理 incrementsToRestrict_increments_orderEmbOfFinWithBot_ae_eq_restrict
  结论: [Bot T] (R : 类型)
  证明: by
  filter_upwards [h] with ω hω
  ext t
  simp only [restrict, incrementsToRestrict, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, Function.comp_apply]
  rw [Fin.sum_Iic_sub _ (fun j => X (I.orderEmbOfFinWithBot j) ω)]
  simp [hω, orderEmbOfFin]

Depends on / 依赖: AddHom, AddHom.coe_mk, ContinuousLinearMap, ContinuousLinearMap.coe_mk, Fin.sum_Iic_sub, Function, Function.comp_apply, I.orderEmbOfFinWithBot, LinearMap, LinearMap.coe_mk, coe_mk, comp_apply, filter_upwards, incrementsToRestrict, orderEmbOfFin, orderEmbOfFinWithBot, restrict, sum_Iic_sub
-/
lemma incrementsToRestrict_increments_orderEmbOfFinWithBot_ae_eq_restrict [Bot T] (R : Type*)
    [Semiring R] [AddCommGroup E] [Module R E] [TopologicalSpace E] [ContinuousAdd E]
    {X : T -> Ω -> E} (h : forallᵐ ω ∂P, X ⊥ ω = 0) (I : Finset T) :
    (fun ω => I.restrict (X · ω)) =ᵐ[P]
      (incrementsToRestrict R I) ∘
        (fun ω i => X (I.orderEmbOfFinWithBot i.succ) ω -
          X (I.orderEmbOfFinWithBot i.castSucc) ω) := by
  filter_upwards [h] with ω hω
  ext t
  simp only [restrict, incrementsToRestrict, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, Function.comp_apply]
  rw [Fin.sum_Iic_sub _ (fun j => X (I.orderEmbOfFinWithBot j) ω)]
  simp [hω, orderEmbOfFin]

/-- A stochastic process `X` with independent increments, such that `X t` is Gaussian for
all `t` and such that `X ⊥ = 0` almost surely is a Gaussian process. -/
public lemma HasIndepIncrements.isGaussianProcess [OrderBot T]
    [NormedAddCommGroup E] [NormedSpace Real E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E]
    {X : T -> Ω -> E} (law : forall t, HasGaussianLaw (X t) P) (h_bot : forallᵐ ω ∂P, X ⊥ ω = 0)
    (incr : HasIndepIncrements X P) :
    IsGaussianProcess X P where
  hasGaussianLaw I := by
    -- Label `t₁ < ... < tₙ` the elements of `I`.
    -- We want to show that `(X t₁, ..., X tₙ)` is Gaussian.
    have := (law ⊥).isProbabilityMeasure
    obtain rfl | hI := I.eq_empty_or_nonempty
    · -- If `I` is empty, there is nothing to say.
      exact .of_subsingleton
    -- Otherwise we know that `(X t₁, ..., X tₙ) = f (X t₁ - X ⊥, X t₂ - X t₁, ..., X tₙ - X tₙ₋₁)`
    -- almost surely (because `X ⊥ = 0` almost surely)
    -- for a certain continuous linear map `f` called here `incrementsToRestrict I`.
    have := incrementsToRestrict_increments_orderEmbOfFinWithBot_ae_eq_restrict Real h_bot I
    -- Therefore it is enough to show that `(X t₁ - X ⊥, X t₂ - X t₁, ..., X tₙ - X tₙ₋₁)` is
    -- Gaussian.
    refine .congr (.map ?_ _) this.symm
    -- Because they are independent, it is enough to show that each `X tᵢ₊₁ - X tᵢ` is Gaussian.
    refine (incr _ _ (monotone_orderEmbOfFinWithBot I)).hasGaussianLaw fun i => ?_
    -- Because `X tᵢ` and `X tᵢ₊₁` are Gaussian, it is enough to show that
    -- `X tᵢ` is independent from `X tᵢ₊₁ - X tᵢ`.
    refine IndepFun.hasGaussianLaw_sub_of_sub (law _) (law _) ?_
    -- This follows from the fact that `X` has independent increments and `X ⊥ = 0` almost surely.
    exact incr.indepFun_eval_sub bot_le
      (monotone_orderEmbOfFinWithBot I (Fin.castSucc_le_succ i)) h_bot

end ProbabilityTheory
