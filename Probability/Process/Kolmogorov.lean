/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Stochastic processes satisfying the Kolmogorov condition

A stochastic process `X : T → Ω → E` on an index space `T` and a measurable space `Ω`
with measure `P` is said to satisfy the Kolmogorov condition with exponents `p, q` and constant `M`
if for all `s, t : T`, the pair `(X s, X t)` is measurable for the Borel sigma-algebra on `E × E`
and the following condition holds:
`∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤ M * edist s t ^ q`.

This condition is the main assumption of the Kolmogorov-Chentsov theorem, which gives the existence
of a continuous modification of the process.

The measurability condition on pairs ensures that the distance `edist (X s ω) (X t ω)` is
measurable in `ω` for fixed `s, t`. In a space with second-countable topology, the measurability
of pairs can be obtained from measurability of each `X t`.

## Main definitions

* `IsKolmogorovProcess`: property of being a stochastic process that satisfies
  the Kolmogorov condition.
* `IsAEKolmogorovProcess`: a stochastic process satisfies `IsAEKolmogorovProcess` if it is
  a modification of a process satisfying the Kolmogorov condition.

## Main statements

* `IsKolmogorovProcess.mk_of_secondCountableTopology`: in a space with second-countable topology,
  a process is a Kolmogorov process if each `X t` is measurable and the Kolmogorov condition holds.

-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {T Ω E : Type*} [PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]
  {p q : Real} {M : Real>=0} {P : Measure Ω} {X : T -> Ω -> E}

/--
Definition of `IsKolmogorovProcess` / `IsKolmogorovProcess` 的定义

English:
structure IsKolmogorovProcess
  parameters: (X : T -> Ω -> E) (P : Measure Ω) (p q : Real) (M : Real>=0)
  axioms and operations (4):
    - measurablePair : forall s t : T, Measurable[_, borel (E × E)] fun ω => (X s ω, X t ω)
    - kolmogorovCondition : forall s t : T, ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P <= M * edist s t ^ q
    - p_pos : 0 < p
    - q_pos : 0 < q

中文:
结构 是KolmogorovProcess
  参数: (X : T -> Ω -> E) (P : 测度 Ω) (p q : 实数) (M : 实数>=0)
  公理与运算 (4 个):
    - measurablePair : 对任意 s t : T, 可测[_, borel (E × E)] fun ω => (X s ω, X t ω)
    - kolmogorovCondition : 对任意 s t : T, ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P <= M * edist s t ^ q
    - p_pos : 0 < p
    - q_pos : 0 < q
-/
structure IsKolmogorovProcess (X : T -> Ω -> E) (P : Measure Ω) (p q : Real) (M : Real>=0) : Prop where
  measurablePair : forall s t : T, Measurable[_, borel (E × E)] fun ω => (X s ω, X t ω)
  kolmogorovCondition : forall s t : T, ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P <= M * edist s t ^ q
  p_pos : 0 < p
  q_pos : 0 < q

/--
Definition of `IsAEKolmogorovProcess` / `IsAEKolmogorovProcess` 的定义

English:
definition IsAEKolmogorovProcess
  signature: (X : T -> Ω -> E) (P : Measure Ω) (p q : Real) (M : Real>=0)
  body: exists Y, IsKolmogorovProcess Y P p q M ∧ forall t, X t =ᵐ[P] Y t

中文:
定义 IsAEKolmogorovProcess
  签名: (X : T -> Ω -> E) (P : 测度 Ω) (p q : 实数) (M : 实数>=0)
  定义体: exists Y, IsKolmogorovProcess Y P p q M ∧ forall t, X t =ᵐ[P] Y t

Depends on / 依赖: IsKolmogorovProcess
-/
def IsAEKolmogorovProcess (X : T -> Ω -> E) (P : Measure Ω) (p q : Real) (M : Real>=0) : Prop :=
  exists Y, IsKolmogorovProcess Y P p q M ∧ forall t, X t =ᵐ[P] Y t

/--
lemma `IsKolmogorovProcess.IsAEKolmogorovProcess` / 引理 `IsKolmogorovProcess.IsAEKolmogorovProcess`

English:
lemma IsKolmogorovProcess.IsAEKolmogorovProcess
  given: (hX : IsKolmogorovProcess X P p q M)
  proof: ⟨X, hX, by simp⟩

中文:
引理 是KolmogorovProcess.IsAEKolmogorovProcess
  条件: (hX : 是KolmogorovProcess X P p q M)
  证明: ⟨X, hX, by simp⟩
-/
lemma IsKolmogorovProcess.IsAEKolmogorovProcess (hX : IsKolmogorovProcess X P p q M) :
    IsAEKolmogorovProcess X P p q M := ⟨X, hX, by simp⟩

namespace IsAEKolmogorovProcess

/-- A process with the property `IsKolmogorovProcess` such that `∀ t, X t =ᵐ[P] h.mk X t`. -/
protected noncomputable
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (X : T -> Ω -> E) (h : IsAEKolmogorovProcess X P p q M)
  body: Classical.choose h

中文:
定义 mk
  签名: (X : T -> Ω -> E) (h : IsAEKolmogorovProcess X P p q M)
  定义体: Classical.choose h

Depends on / 依赖: Classical, Classical.choose
-/
def mk (X : T -> Ω -> E) (h : IsAEKolmogorovProcess X P p q M) : T -> Ω -> E :=
  Classical.choose h

/--
lemma `IsKolmogorovProcess_mk` / 引理 `IsKolmogorovProcess_mk`

English:
lemma IsKolmogorovProcess_mk
  given: (h : IsAEKolmogorovProcess X P p q M)
  proof: (Classical.choose_spec h).1

中文:
引理 IsKolmogorovProcess_mk
  条件: (h : IsAEKolmogorovProcess X P p q M)
  证明: (Classical.choose_spec h).1

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec
-/
lemma IsKolmogorovProcess_mk (h : IsAEKolmogorovProcess X P p q M) :
    IsKolmogorovProcess (h.mk X) P p q M := (Classical.choose_spec h).1

/--
lemma `ae_eq_mk` / 引理 `ae_eq_mk`

English:
lemma ae_eq_mk
  given: (h : IsAEKolmogorovProcess X P p q M)
  statement: forall t, X t =ᵐ[P] h.mk X t
  proof: (Classical.choose_spec h).2

中文:
引理 ae_eq_mk
  条件: (h : IsAEKolmogorovProcess X P p q M)
  结论: 对任意 t, X t =ᵐ[P] h.mk X t
  证明: (Classical.choose_spec h).2

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec
-/
lemma ae_eq_mk (h : IsAEKolmogorovProcess X P p q M) : forall t, X t =ᵐ[P] h.mk X t :=
  (Classical.choose_spec h).2

/--
lemma `kolmogorovCondition` / 引理 `kolmogorovCondition`

English:
lemma kolmogorovCondition
  given: (hX : IsAEKolmogorovProcess X P p q M) (s t : T)
  proof: by
  convert! hX.IsKolmogorovProcess_mk.kolmogorovCondition s t using 1
  refine lintegral_congr_ae ?_
  filter_upwards [hX.ae_eq_mk s, hX.ae_eq_mk t] with ω hω₁ hω₂
  simp_rw [hω₁, hω₂]

中文:
引理 kolmogorovCondition
  条件: (hX : IsAEKolmogorovProcess X P p q M) (s t : T)
  证明: by
  convert! hX.IsKolmogorovProcess_mk.kolmogorovCondition s t using 1
  refine lintegral_congr_ae ?_
  filter_upwards [hX.ae_eq_mk s, hX.ae_eq_mk t] with ω hω₁ hω₂
  simp_rw [hω₁, hω₂]

Depends on / 依赖: IsKolmogorovProcess_mk, ae_eq_mk, convert, filter_upwards, hX.IsKolmogorovProcess_mk.kolmogorovCondition, hX.ae_eq_mk, kolmogorovCondition, lintegral_congr_ae, simp_rw
-/
lemma kolmogorovCondition (hX : IsAEKolmogorovProcess X P p q M) (s t : T) :
    ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P <= M * edist s t ^ q := by
  convert! hX.IsKolmogorovProcess_mk.kolmogorovCondition s t using 1
  refine lintegral_congr_ae ?_
  filter_upwards [hX.ae_eq_mk s, hX.ae_eq_mk t] with ω hω₁ hω₂
  simp_rw [hω₁, hω₂]

/--
lemma `p_pos` / 引理 `p_pos`

English:
lemma p_pos
  given: (hX : IsAEKolmogorovProcess X P p q M)
  statement: 0 < p
  proof: hX.IsKolmogorovProcess_mk.p_pos

中文:
引理 p_pos
  条件: (hX : IsAEKolmogorovProcess X P p q M)
  结论: 0 < p
  证明: hX.IsKolmogorovProcess_mk.p_pos

Depends on / 依赖: IsKolmogorovProcess_mk, hX.IsKolmogorovProcess_mk.p_pos, p_pos
-/
lemma p_pos (hX : IsAEKolmogorovProcess X P p q M) : 0 < p := hX.IsKolmogorovProcess_mk.p_pos

/--
lemma `q_pos` / 引理 `q_pos`

English:
lemma q_pos
  given: (hX : IsAEKolmogorovProcess X P p q M)
  statement: 0 < q
  proof: hX.IsKolmogorovProcess_mk.q_pos

中文:
引理 q_pos
  条件: (hX : IsAEKolmogorovProcess X P p q M)
  结论: 0 < q
  证明: hX.IsKolmogorovProcess_mk.q_pos

Depends on / 依赖: IsKolmogorovProcess_mk, hX.IsKolmogorovProcess_mk.q_pos, q_pos
-/
lemma q_pos (hX : IsAEKolmogorovProcess X P p q M) : 0 < q := hX.IsKolmogorovProcess_mk.q_pos

/--
lemma `congr` / 引理 `congr`

English:
lemma congr
  statement: {Y : T -> Ω -> E} (hX : IsAEKolmogorovProcess X P p q M)
  proof: by
  refine ⟨hX.mk X, hX.IsKolmogorovProcess_mk, fun t => ?_⟩
  filter_upwards [hX.ae_eq_mk t, h t] with ω hX hY using hY.symm.trans hX

中文:
引理 congr
  结论: {Y : T -> Ω -> E} (hX : IsAEKolmogorovProcess X P p q M)
  证明: by
  refine ⟨hX.mk X, hX.IsKolmogorovProcess_mk, fun t => ?_⟩
  filter_upwards [hX.ae_eq_mk t, h t] with ω hX hY using hY.symm.trans hX

Depends on / 依赖: IsKolmogorovProcess_mk, ae_eq_mk, filter_upwards, hX.IsKolmogorovProcess_mk, hX.ae_eq_mk, hX.mk, hY.symm.trans
-/
lemma congr {Y : T -> Ω -> E} (hX : IsAEKolmogorovProcess X P p q M)
    (h : forall t, X t =ᵐ[P] Y t) :
    IsAEKolmogorovProcess Y P p q M := by
  refine ⟨hX.mk X, hX.IsKolmogorovProcess_mk, fun t => ?_⟩
  filter_upwards [hX.ae_eq_mk t, h t] with ω hX hY using hY.symm.trans hX

end IsAEKolmogorovProcess

section Measurability

/--
lemma `IsKolmogorovProcess.stronglyMeasurable_edist` / 引理 `IsKolmogorovProcess.stronglyMeasurable_edist`

English:
lemma IsKolmogorovProcess.stronglyMeasurable_edist
  proof: by
  borelize (E × E)
  exact continuous_edist.stronglyMeasurable.comp_measurable (hX.measurablePair s t)

中文:
引理 是KolmogorovProcess.stronglyMeasurable_edist
  证明: by
  borelize (E × E)
  exact continuous_edist.stronglyMeasurable.comp_measurable (hX.measurablePair s t)

Depends on / 依赖: borelize, comp_measurable, continuous_edist, continuous_edist.stronglyMeasurable.comp_measurable, hX.measurablePair, measurablePair, stronglyMeasurable
-/
lemma IsKolmogorovProcess.stronglyMeasurable_edist
    (hX : IsKolmogorovProcess X P p q M) {s t : T} :
    StronglyMeasurable (fun ω => edist (X s ω) (X t ω)) := by
  borelize (E × E)
  exact continuous_edist.stronglyMeasurable.comp_measurable (hX.measurablePair s t)

/--
lemma `IsAEKolmogorovProcess.aestronglyMeasurable_edist` / 引理 `IsAEKolmogorovProcess.aestronglyMeasurable_edist`

English:
lemma IsAEKolmogorovProcess.aestronglyMeasurable_edist
  proof: by
  refine ⟨(fun ω => edist (hX.mk X s ω) (hX.mk X t ω)),
    hX.IsKolmogorovProcess_mk.stronglyMeasurable_edist, ?_⟩
  filter_upwards [hX.ae_eq_mk s, hX.ae_eq_mk t] with ω hω₁ hω₂ using by simp [hω₁, hω₂]

中文:
引理 IsAEKolmogorovProcess.aestronglyMeasurable_edist
  证明: by
  refine ⟨(fun ω => edist (hX.mk X s ω) (hX.mk X t ω)),
    hX.IsKolmogorovProcess_mk.stronglyMeasurable_edist, ?_⟩
  filter_upwards [hX.ae_eq_mk s, hX.ae_eq_mk t] with ω hω₁ hω₂ using by simp [hω₁, hω₂]

Depends on / 依赖: IsKolmogorovProcess_mk, ae_eq_mk, filter_upwards, hX.IsKolmogorovProcess_mk.stronglyMeasurable_edist, hX.ae_eq_mk, hX.mk, stronglyMeasurable_edist
-/
lemma IsAEKolmogorovProcess.aestronglyMeasurable_edist
    (hX : IsAEKolmogorovProcess X P p q M) {s t : T} :
    AEStronglyMeasurable (fun ω => edist (X s ω) (X t ω)) P := by
  refine ⟨(fun ω => edist (hX.mk X s ω) (hX.mk X t ω)),
    hX.IsKolmogorovProcess_mk.stronglyMeasurable_edist, ?_⟩
  filter_upwards [hX.ae_eq_mk s, hX.ae_eq_mk t] with ω hω₁ hω₂ using by simp [hω₁, hω₂]

/--
lemma `IsKolmogorovProcess.measurable_edist` / 引理 `IsKolmogorovProcess.measurable_edist`

English:
lemma IsKolmogorovProcess.measurable_edist
  given: (hX : IsKolmogorovProcess X P p q M) {s t : T}
  proof: hX.stronglyMeasurable_edist.measurable

中文:
引理 是KolmogorovProcess.measurable_edist
  条件: (hX : 是KolmogorovProcess X P p q M) {s t : T}
  证明: hX.stronglyMeasurable_edist.measurable

Depends on / 依赖: hX.stronglyMeasurable_edist.measurable, measurable, stronglyMeasurable_edist
-/
lemma IsKolmogorovProcess.measurable_edist (hX : IsKolmogorovProcess X P p q M) {s t : T} :
    Measurable (fun ω => edist (X s ω) (X t ω)) := hX.stronglyMeasurable_edist.measurable

/--
lemma `IsAEKolmogorovProcess.aemeasurable_edist` / 引理 `IsAEKolmogorovProcess.aemeasurable_edist`

English:
lemma IsAEKolmogorovProcess.aemeasurable_edist
  given: (hX : IsAEKolmogorovProcess X P p q M) {s t : T}
  proof: hX.aestronglyMeasurable_edist.aemeasurable

中文:
引理 IsAEKolmogorovProcess.aemeasurable_edist
  条件: (hX : IsAEKolmogorovProcess X P p q M) {s t : T}
  证明: hX.aestronglyMeasurable_edist.aemeasurable

Depends on / 依赖: aemeasurable, aestronglyMeasurable_edist, hX.aestronglyMeasurable_edist.aemeasurable
-/
lemma IsAEKolmogorovProcess.aemeasurable_edist (hX : IsAEKolmogorovProcess X P p q M) {s t : T} :
    AEMeasurable (fun ω => edist (X s ω) (X t ω)) P := hX.aestronglyMeasurable_edist.aemeasurable

variable [MeasurableSpace E] [BorelSpace E]

/--
lemma `IsKolmogorovProcess.measurable` / 引理 `IsKolmogorovProcess.measurable`

English:
lemma IsKolmogorovProcess.measurable
  given: (hX : IsKolmogorovProcess X P p q M) (s : T)
  proof: (measurable_fst.mono prod_le_borel_prod le_rfl).comp (hX.measurablePair s s)

中文:
引理 是KolmogorovProcess.measurable
  条件: (hX : 是KolmogorovProcess X P p q M) (s : T)
  证明: (measurable_fst.mono prod_le_borel_prod le_rfl).comp (hX.measurablePair s s)

Depends on / 依赖: hX.measurablePair, le_rfl, measurablePair, measurable_fst, measurable_fst.mono, prod_le_borel_prod
-/
lemma IsKolmogorovProcess.measurable (hX : IsKolmogorovProcess X P p q M) (s : T) :
    Measurable (X s) :=
  (measurable_fst.mono prod_le_borel_prod le_rfl).comp (hX.measurablePair s s)

/--
lemma `IsAEKolmogorovProcess.aemeasurable` / 引理 `IsAEKolmogorovProcess.aemeasurable`

English:
lemma IsAEKolmogorovProcess.aemeasurable
  given: (hX : IsAEKolmogorovProcess X P p q M) (s : T)
  proof: by
  refine ⟨hX.mk X s, hX.IsKolmogorovProcess_mk.measurable s, ?_⟩
  filter_upwards [hX.ae_eq_mk s] with ω hω using hω

中文:
引理 IsAEKolmogorovProcess.aemeasurable
  条件: (hX : IsAEKolmogorovProcess X P p q M) (s : T)
  证明: by
  refine ⟨hX.mk X s, hX.IsKolmogorovProcess_mk.measurable s, ?_⟩
  filter_upwards [hX.ae_eq_mk s] with ω hω using hω

Depends on / 依赖: IsKolmogorovProcess_mk, ae_eq_mk, filter_upwards, hX.IsKolmogorovProcess_mk.measurable, hX.ae_eq_mk, hX.mk, measurable
-/
lemma IsAEKolmogorovProcess.aemeasurable (hX : IsAEKolmogorovProcess X P p q M) (s : T) :
    AEMeasurable (X s) P := by
  refine ⟨hX.mk X s, hX.IsKolmogorovProcess_mk.measurable s, ?_⟩
  filter_upwards [hX.ae_eq_mk s] with ω hω using hω

/--
lemma `IsKolmogorovProcess.mk_of_secondCountableTopology` / 引理 `IsKolmogorovProcess.mk_of_secondCountableTopology`

English:
lemma IsKolmogorovProcess.mk_of_secondCountableTopology
  statement: [SecondCountableTopology E]
  proof: by
    suffices Measurable (fun ω => (X s ω, X t ω)) by
      rwa [Prod.borelSpace.measurable_eq] at this
    fun_prop
  kolmogorovCondition := h_kol
  p_pos := hp
  q_pos := hq

中文:
引理 是KolmogorovProcess.mk_of_secondCountableTopology
  结论: [第二可数拓扑 E]
  证明: by
    suffices Measurable (fun ω => (X s ω, X t ω)) by
      rwa [Prod.borelSpace.measurable_eq] at this
    fun_prop
  kolmogorovCondition := h_kol
  p_pos := hp
  q_pos := hq

Depends on / 依赖: Measurable, Prod.borelSpace.measurable_eq, borelSpace, fun_prop, h_kol, kolmogorovCondition, measurable_eq, p_pos, q_pos
-/
lemma IsKolmogorovProcess.mk_of_secondCountableTopology [SecondCountableTopology E]
    (h_meas : forall s, Measurable (X s))
    (h_kol : forall s t : T, ∫⁻ ω, (edist (X s ω) (X t ω)) ^ p ∂P <= M * edist s t ^ q)
    (hp : 0 < p) (hq : 0 < q) :
    IsKolmogorovProcess X P p q M where
  measurablePair s t := by
    suffices Measurable (fun ω => (X s ω, X t ω)) by
      rwa [Prod.borelSpace.measurable_eq] at this
    fun_prop
  kolmogorovCondition := h_kol
  p_pos := hp
  q_pos := hq

end Measurability

section ZeroDist

/--
lemma `IsAEKolmogorovProcess.edist_eq_zero` / 引理 `IsAEKolmogorovProcess.edist_eq_zero`

English:
lemma IsAEKolmogorovProcess.edist_eq_zero
  statement: (hX : IsAEKolmogorovProcess X P p q M)
  proof: by
  suffices (fun ω => edist (X s ω) (X t ω) ^ p) =ᵐ[P] 0 by
    filter_upwards [this] with ω hω
    simpa [hX.p_pos, not_lt_of_gt hX.p_pos] using hω
  rw [← lintegral_eq_zero_iff' (hX.aemeasurable_edist.pow_const p)]; rw [← nonpos_iff_eq_zero]
  calc ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P
  _ <= M * e

中文:
引理 IsAEKolmogorovProcess.edist_eq_zero
  结论: (hX : IsAEKolmogorovProcess X P p q M)
  证明: by
  suffices (fun ω => edist (X s ω) (X t ω) ^ p) =ᵐ[P] 0 by
    filter_upwards [this] with ω hω
    simpa [hX.p_pos, not_lt_of_gt hX.p_pos] using hω
  rw [← lintegral_eq_zero_iff' (hX.aemeasurable_edist.pow_const p)]; rw [← nonpos_iff_eq_zero]
  calc ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P
  _ <= M * e

Depends on / 依赖: aemeasurable_edist, filter_upwards, hX.aemeasurable_edist.pow_const, hX.kolmogorovCondition, hX.p_pos, hX.q_pos, kolmogorovCondition, lintegral_eq_zero_iff, nonpos_iff_eq_zero, not_lt_of_gt, p_pos, pow_const, q_pos
-/
lemma IsAEKolmogorovProcess.edist_eq_zero (hX : IsAEKolmogorovProcess X P p q M)
    {s t : T} (h : edist s t = 0) :
    forallᵐ ω ∂P, edist (X s ω) (X t ω) = 0 := by
  suffices (fun ω => edist (X s ω) (X t ω) ^ p) =ᵐ[P] 0 by
    filter_upwards [this] with ω hω
    simpa [hX.p_pos, not_lt_of_gt hX.p_pos] using hω
  rw [← lintegral_eq_zero_iff' (hX.aemeasurable_edist.pow_const p)]; rw [← nonpos_iff_eq_zero]
  calc ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P
  _ <= M * edist s t ^ q := hX.kolmogorovCondition s t
  _ = 0 := by simp [h, hX.q_pos]

/--
lemma `IsKolmogorovProcess.edist_eq_zero` / 引理 `IsKolmogorovProcess.edist_eq_zero`

English:
lemma IsKolmogorovProcess.edist_eq_zero
  statement: (hX : IsKolmogorovProcess X P p q M)
  proof: hX.IsAEKolmogorovProcess.edist_eq_zero h

中文:
引理 是KolmogorovProcess.edist_eq_zero
  结论: (hX : 是KolmogorovProcess X P p q M)
  证明: hX.IsAEKolmogorovProcess.edist_eq_zero h

Depends on / 依赖: IsAEKolmogorovProcess, edist_eq_zero, hX.IsAEKolmogorovProcess.edist_eq_zero
-/
lemma IsKolmogorovProcess.edist_eq_zero (hX : IsKolmogorovProcess X P p q M)
    {s t : T} (h : edist s t = 0) :
    forallᵐ ω ∂P, edist (X s ω) (X t ω) = 0 :=
  hX.IsAEKolmogorovProcess.edist_eq_zero h

/--
lemma `IsAEKolmogorovProcess.edist_eq_zero_of_const_eq_zero` / 引理 `IsAEKolmogorovProcess.edist_eq_zero_of_const_eq_zero`

English:
lemma IsAEKolmogorovProcess.edist_eq_zero_of_const_eq_zero
  statement: (hX : IsAEKolmogorovProcess X P p q 0)
  proof: by
  suffices (fun ω => edist (X s ω) (X t ω) ^ p) =ᵐ[P] 0 by
    filter_upwards [this] with ω hω
    simpa [hX.p_pos, not_lt_of_gt hX.p_pos] using hω
  rw [← lintegral_eq_zero_iff' (hX.aemeasurable_edist.pow_const p)]; rw [← nonpos_iff_eq_zero]
  calc ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P
  _ <= 0 * e

中文:
引理 IsAEKolmogorovProcess.edist_eq_zero_of_const_eq_zero
  结论: (hX : IsAEKolmogorovProcess X P p q 0)
  证明: by
  suffices (fun ω => edist (X s ω) (X t ω) ^ p) =ᵐ[P] 0 by
    filter_upwards [this] with ω hω
    simpa [hX.p_pos, not_lt_of_gt hX.p_pos] using hω
  rw [← lintegral_eq_zero_iff' (hX.aemeasurable_edist.pow_const p)]; rw [← nonpos_iff_eq_zero]
  calc ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P
  _ <= 0 * e

Depends on / 依赖: aemeasurable_edist, filter_upwards, hX.aemeasurable_edist.pow_const, hX.kolmogorovCondition, hX.p_pos, kolmogorovCondition, lintegral_eq_zero_iff, nonpos_iff_eq_zero, not_lt_of_gt, p_pos, pow_const
-/
lemma IsAEKolmogorovProcess.edist_eq_zero_of_const_eq_zero (hX : IsAEKolmogorovProcess X P p q 0)
    (s t : T) :
    forallᵐ ω ∂P, edist (X s ω) (X t ω) = 0 := by
  suffices (fun ω => edist (X s ω) (X t ω) ^ p) =ᵐ[P] 0 by
    filter_upwards [this] with ω hω
    simpa [hX.p_pos, not_lt_of_gt hX.p_pos] using hω
  rw [← lintegral_eq_zero_iff' (hX.aemeasurable_edist.pow_const p)]; rw [← nonpos_iff_eq_zero]
  calc ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P
  _ <= 0 * edist s t ^ q := hX.kolmogorovCondition s t
  _ = 0 := by simp

/--
lemma `IsKolmogorovProcess.edist_eq_zero_of_const_eq_zero` / 引理 `IsKolmogorovProcess.edist_eq_zero_of_const_eq_zero`

English:
lemma IsKolmogorovProcess.edist_eq_zero_of_const_eq_zero
  statement: (hX : IsKolmogorovProcess X P p q 0)
  proof: hX.IsAEKolmogorovProcess.edist_eq_zero_of_const_eq_zero s t

中文:
引理 是KolmogorovProcess.edist_eq_zero_of_const_eq_zero
  结论: (hX : 是KolmogorovProcess X P p q 0)
  证明: hX.IsAEKolmogorovProcess.edist_eq_zero_of_const_eq_zero s t

Depends on / 依赖: IsAEKolmogorovProcess, edist_eq_zero_of_const_eq_zero, hX.IsAEKolmogorovProcess.edist_eq_zero_of_const_eq_zero
-/
lemma IsKolmogorovProcess.edist_eq_zero_of_const_eq_zero (hX : IsKolmogorovProcess X P p q 0)
    (s t : T) :
    forallᵐ ω ∂P, edist (X s ω) (X t ω) = 0 :=
  hX.IsAEKolmogorovProcess.edist_eq_zero_of_const_eq_zero s t

end ZeroDist

end ProbabilityTheory
