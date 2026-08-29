/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.InfinitePi

/-!
# Results about identically distributed random variables and independence

## Main statements

* `IdentDistrib.prodMk`: if `X` and `Y` are independent random variables on `Ω`, `Z` and `W` are
  independent random variables on `Ω'`, such that `X` and `Z` are identically distributed
  and `Y` and `W` are identically distributed, then the pairs `(X, Y)` and `(Z, W)` are
  identically distributed.
* `IdentDistrib.pi`: if `(X i)` and `(Y i)` are families of independent random variables indexed by
  a countable type `ι`, such that for each `i`, `X i` and `Y i` are identically distributed, then
  the products `X` and `Y` are identically distributed.

-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω Ω' ι E F : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {mE : MeasurableSpace E} {mF : MeasurableSpace F}
    {μ : Measure Ω} {ν : Measure Ω'}

/--
lemma `IdentDistrib.prodMk` / 引理 `IdentDistrib.prodMk`

English:
lemma IdentDistrib.prodMk
  statement: [IsFiniteMeasure μ]
  proof: hXZ.aemeasurable_fst.prodMk hYW.aemeasurable_fst
  aemeasurable_snd := hXZ.aemeasurable_snd.prodMk hYW.aemeasurable_snd
  map_eq := by
    have : IsFiniteMeasure ν := by
      have : IsFiniteMeasure (ν.map Z) := by rw [← hXZ.map_eq]; infer_instance
      exact Measure.isFiniteMeasure_of_map hXZ.aeme

中文:
引理 IdentDistrib.prodMk
  结论: [IsFiniteMeasure μ]
  证明: hXZ.aemeasurable_fst.prodMk hYW.aemeasurable_fst
  aemeasurable_snd := hXZ.aemeasurable_snd.prodMk hYW.aemeasurable_snd
  map_eq := by
    have : IsFiniteMeasure ν := by
      have : IsFiniteMeasure (ν.map Z) := by rw [← hXZ.map_eq]; infer_instance
      exact Measure.isFiniteMeasure_of_map hXZ.aeme

Depends on / 依赖: aemeasurable_fst, hXZ.aemeasurable_fst.prodMk, hYW.aemeasurable_fst, prodMk
-/
lemma IdentDistrib.prodMk [IsFiniteMeasure μ]
    {X : Ω -> E} {Y : Ω -> F} {Z : Ω' -> E} {W : Ω' -> F}
    (hXZ : IdentDistrib X Z μ ν) (hYW : IdentDistrib Y W μ ν)
    (hXY : X ⟂ᵢ[μ] Y) (hZW : Z ⟂ᵢ[ν] W) :
    IdentDistrib (fun ω => (X ω, Y ω)) (fun ω' => (Z ω', W ω')) μ ν where
  aemeasurable_fst := hXZ.aemeasurable_fst.prodMk hYW.aemeasurable_fst
  aemeasurable_snd := hXZ.aemeasurable_snd.prodMk hYW.aemeasurable_snd
  map_eq := by
    have : IsFiniteMeasure ν := by
      have : IsFiniteMeasure (ν.map Z) := by rw [← hXZ.map_eq]; infer_instance
      exact Measure.isFiniteMeasure_of_map hXZ.aemeasurable_snd
    rw [hXY.map_prod_eq_prod_map_map hXZ.aemeasurable_fst hYW.aemeasurable_fst]; rw [hZW.map_prod_eq_prod_map_map hXZ.aemeasurable_snd hYW.aemeasurable_snd]; rw [hXZ.map_eq]; rw [hYW.map_eq]

/--
lemma `IdentDistrib.pi` / 引理 `IdentDistrib.pi`

English:
lemma IdentDistrib.pi
  statement: [Countable ι] {E : ι -> Type*} {mE : forall i, MeasurableSpace (E i)}
  proof: aemeasurable_pi_lambda _ fun i => (h i).aemeasurable_fst
  aemeasurable_snd := aemeasurable_pi_lambda _ fun i => (h i).aemeasurable_snd
  map_eq := by
    have : IsProbabilityMeasure μ := hX_ind.isProbabilityMeasure
    have : IsProbabilityMeasure ν := hY_ind.isProbabilityMeasure
    rw [(iIndepFun_

中文:
引理 IdentDistrib.pi
  结论: [Countable ι] {E : ι -> 类型} {mE : 对任意 i, MeasurableSpace (E i)}
  证明: aemeasurable_pi_lambda _ fun i => (h i).aemeasurable_fst
  aemeasurable_snd := aemeasurable_pi_lambda _ fun i => (h i).aemeasurable_snd
  map_eq := by
    have : IsProbabilityMeasure μ := hX_ind.isProbabilityMeasure
    have : IsProbabilityMeasure ν := hY_ind.isProbabilityMeasure
    rw [(iIndepFun_

Depends on / 依赖: aemeasurable_fst, aemeasurable_pi_lambda
-/
lemma IdentDistrib.pi [Countable ι] {E : ι -> Type*} {mE : forall i, MeasurableSpace (E i)}
    {X : (i : ι) -> Ω -> E i} {Y : (i : ι) -> Ω' -> E i}
    (h : forall i, IdentDistrib (X i) (Y i) μ ν) (hX_ind : iIndepFun X μ) (hY_ind : iIndepFun Y ν) :
    IdentDistrib (fun ω => (X · ω)) (fun ω => (Y · ω)) μ ν where
  aemeasurable_fst := aemeasurable_pi_lambda _ fun i => (h i).aemeasurable_fst
  aemeasurable_snd := aemeasurable_pi_lambda _ fun i => (h i).aemeasurable_snd
  map_eq := by
    have : IsProbabilityMeasure μ := hX_ind.isProbabilityMeasure
    have : IsProbabilityMeasure ν := hY_ind.isProbabilityMeasure
    rw [(iIndepFun_iff_map_fun_eq_infinitePi_map₀' (fun i => (h i).aemeasurable_fst)).mp hX_ind]; rw [(iIndepFun_iff_map_fun_eq_infinitePi_map₀' (fun i => (h i).aemeasurable_snd)).mp hY_ind]
    congr with i
    rw [(h i).map_eq]

end ProbabilityTheory
