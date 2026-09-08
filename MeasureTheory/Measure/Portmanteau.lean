/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Tight

import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Characterizations of weak convergence of finite measures and probability measures

This file will provide portmanteau characterizations of the weak convergence of finite measures
and of probability measures, i.e., the standard characterizations of convergence in distribution.

## Main definitions

The topologies of weak convergence on the types of finite measures and probability measures are
already defined in their corresponding files; no substantial new definitions are introduced here.

## Main results

The main result will be the portmanteau theorem providing various characterizations of the
weak convergence of measures (probability measures or finite measures). Given measures μs
and μ on a topological space Ω, the conditions that will be proven equivalent (under quite
general hypotheses) are:

  (T) The measures μs tend to the measure μ weakly.
  (C) For any closed set F, the limsup of the measures of F under μs is at most
      the measure of F under μ, i.e., limsupᵢ μsᵢ(F) ≤ μ(F).
  (O) For any open set G, the liminf of the measures of G under μs is at least
      the measure of G under μ, i.e., μ(G) ≤ liminfᵢ μsᵢ(G).
  (B) For any Borel set B whose boundary carries no mass under μ, i.e. μ(∂B) = 0,
      the measures of B under μs tend to the measure of B under μ, i.e., limᵢ μsᵢ(B) = μ(B).

The separate implications are:
* `MeasureTheory.FiniteMeasure.limsup_measure_closed_le_of_tendsto` is the implication (T) → (C).
* `MeasureTheory.limsup_measure_closed_le_iff_liminf_measure_open_ge` is the equivalence (C) ↔ (O).
* `MeasureTheory.tendsto_measure_of_null_frontier` is the implication (O) → (B).
* `MeasureTheory.limsup_measure_closed_le_of_forall_tendsto_measure` is the implication (B) → (C).
* `MeasureTheory.tendsto_of_forall_isOpen_le_liminf` gives the implication (O) → (T) for
    any sequence of Borel probability measures.
* `MeasureTheory.tendsto_of_limsup_measure_closed_le` gives the implication (C) → (T).

We also deduce a practical convergence criterion for probability measures, in
`IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem`.
Assume that, applied to all the elements of a π-system, a sequence of probability measures
converges to a limiting probability measure. Assume also that the π-system contains arbitrarily
small neighborhoods of any point. Then the sequence of probability measures converges for the
weak topology.

In case the set of measures is tight, (C) implies (T) even when 'closed' is replaced by 'compact'.
This is shown in `MeasureTheory.tendsto_of_forall_isCompact_of_isTightMeasureSet`.

## Implementation notes

Many of the characterizations of weak convergence hold for finite measures and are proven in that
generality and then specialized to probability measures. Some implications hold with slightly
more general assumptions than in the usual statement of portmanteau theorem. The full portmanteau
theorem, however, is most convenient for probability measures on pseudo-emetrizable spaces with
their Borel sigma algebras.

Some specific considerations on the assumptions in the different implications:
* `MeasureTheory.FiniteMeasure.limsup_measure_closed_le_of_tendsto`, i.e., implication (T) → (C),
  assumes that in the underlying topological space, indicator functions of closed sets have
  decreasing bounded continuous pointwise approximating sequences. The assumption is in the form
  of the type class `HasOuterApproxClosed`. Type class inference knows that for example the more
  common assumptions of metrizability or pseudo-emetrizability suffice.
* Where formulations are currently only provided for probability measures, one can obtain the
  finite measure formulations using the characterization of convergence of finite measures by
  their total masses and their probability-normalized versions, i.e., by
  `MeasureTheory.FiniteMeasure.tendsto_normalize_iff_tendsto`.

## References

* [Billingsley, *Convergence of probability measures*][billingsley1999]

## Tags

weak convergence of measures, convergence in distribution, convergence in law, finite measure,
probability measure

-/

public section


noncomputable section

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace MeasureTheory

section LimsupClosedLEAndLELiminfOpen

/-! ### Portmanteau: limsup condition for closed sets iff liminf condition for open sets

In this section we prove that for a sequence of Borel probability measures on a topological space
and its candidate limit measure, the following two conditions are equivalent:

  (C) For any closed set F, the limsup of the measures of F under μs is at most
      the measure of F under μ, i.e., limsupᵢ μsᵢ(F) ≤ μ(F);
  (O) For any open set G, the liminf of the measures of G under μs is at least
      the measure of G under μ, i.e., μ(G) ≤ liminfᵢ μsᵢ(G).

Either of these will later be shown to be equivalent to the weak convergence of the sequence
of measures.
-/

variable {Ω : Type*} [MeasurableSpace Ω]

/-
**MeasureTheory.le_measure_compl_liminf_of_limsup_measure_le** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
形式化陈述：le_measure_compl_liminf_of_limsup_measure_le {ι : Type*} {L : Filter ι} {μ
 : Measure Ω} {μs : ι -> Measure Ω} [IsProbabilityMeasure μ] [forall i, IsProbab
ilityMeasure (μs i)] {E : Set Ω} (E_mble : MeasurableSet E) (h : (L.limsup fun i
 => μs i E) <= μ E) : μ Eᶜ <= L.liminf fun i => μs i Eᶜ
参数：μs i；E_mble : MeasurableSet E；h : (L.limsup fun i => μs i E) <= μ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.liminf_bot`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLatti
ce α] (f : β → α), Filter.liminf f ⊥ = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `MeasureTheory.measure_compl`：measure_compl (h₁ : MeasurableSet s) (h_fin
 : μ s != ∞) : μ sᶜ = μ univ - μ s
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Antitone.map_limsup_of_continuousAt`：Antitone.map_limsup_of_continuousAt
 {f : R -> S} (f_decr : Antitone f) (a : ι -> R) (f_cont : ContinuousAt f (F.lim
sup a)) (bdd_above : F.Is…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `antitone_const_tsub`：antitone_const_tsub : Antitone fun x => c - x
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ENNReal.continuous_sub_left`：continuous_sub_left {a : Real>=0∞} (a_ne_to
p : a != ∞) : Continuous (a - ·)
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
-/
theorem le_measure_compl_liminf_of_limsup_measure_le {ι : Type*} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)] {E : Set Ω}
    (E_mble : MeasurableSet E) (h : (L.limsup fun i ↦ μs i E) ≤ μ E) :
    μ Eᶜ ≤ L.liminf fun i ↦ μs i Eᶜ := by
  rcases L.eq_or_neBot with rfl | hne
  · simp only [liminf_bot, le_top]
  have meas_Ec : μ Eᶜ = 1 - μ E := by
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top μ E).ne
  have meas_i_Ec : ∀ i, μs i Eᶜ = 1 - μs i E := by
    intro i
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top (μs i) E).ne
  simp_rw [meas_Ec, meas_i_Ec]
  rw [show (L.liminf fun i : ι ↦ 1 - μs i E) = L.liminf ((fun x ↦ 1 - x) ∘ fun i : ι ↦ μs i E)
      from rfl]
  have key := antitone_const_tsub.map_limsup_of_continuousAt (F := L)
    (fun i ↦ μs i E) (ENNReal.continuous_sub_left ENNReal.one_ne_top).continuousAt
  simpa [← key] using antitone_const_tsub h
/-
**MeasureTheory.le_measure_liminf_of_limsup_measure_compl_le** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
形式化陈述：le_measure_liminf_of_limsup_measure_compl_le {ι : Type*} {L : Filter ι} {μ
 : Measure Ω} {μs : ι -> Measure Ω} [IsProbabilityMeasure μ] [forall i, IsProbab
ilityMeasure (μs i)] {E : Set Ω} (E_mble : MeasurableSet E) (h : (L.limsup fun i
 => μs i Eᶜ) <= μ Eᶜ) : μ E <= L.liminf fun i => μs i E
参数：μs i；E_mble : MeasurableSet E；h : (L.limsup fun i => μs i Eᶜ) <= μ Eᶜ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.le_measure_compl_liminf_of_limsup_measure_le`：le_measure_c
ompl_liminf_of_limsup_measure_le {ι : Type*} {L : Filter ι} {μ : Measure Ω} {μs 
: ι -> Measure Ω} [IsProbabilityMeasure μ] [fora…
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
theorem le_measure_liminf_of_limsup_measure_compl_le {ι : Type*} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)] {E : Set Ω}
    (E_mble : MeasurableSet E) (h : (L.limsup fun i ↦ μs i Eᶜ) ≤ μ Eᶜ) :
    μ E ≤ L.liminf fun i ↦ μs i E :=
  compl_compl E ▸ le_measure_compl_liminf_of_limsup_measure_le (MeasurableSet.compl E_mble) h
/-
**MeasureTheory.limsup_measure_compl_le_of_le_liminf_measure** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
形式化陈述：limsup_measure_compl_le_of_le_liminf_measure {ι : Type*} {L : Filter ι} {μ
 : Measure Ω} {μs : ι -> Measure Ω} [IsProbabilityMeasure μ] [forall i, IsProbab
ilityMeasure (μs i)] {E : Set Ω} (E_mble : MeasurableSet E) (h : μ E <= L.liminf
 fun i => μs i E) : (L.limsup fun i => μs i Eᶜ) <= μ Eᶜ
参数：μs i；E_mble : MeasurableSet E；h : μ E <= L.liminf fun i => μs i E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.limsup_bot`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLatti
ce α] (f : β → α), Filter.limsup f ⊥ = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `MeasureTheory.measure_compl`：measure_compl (h₁ : MeasurableSet s) (h_fin
 : μ s != ∞) : μ sᶜ = μ univ - μ s
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Antitone.map_liminf_of_continuousAt`：Antitone.map_liminf_of_continuousAt
 {f : R -> S} (f_decr : Antitone f) (a : ι -> R) (f_cont : ContinuousAt f (F.lim
inf a)) (cobdd : F.IsCobo…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `antitone_const_tsub`：antitone_const_tsub : Antitone fun x => c - x
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ENNReal.continuous_sub_left`：continuous_sub_left {a : Real>=0∞} (a_ne_to
p : a != ∞) : Continuous (a - ·)
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
-/
theorem limsup_measure_compl_le_of_le_liminf_measure {ι : Type*} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)] {E : Set Ω}
    (E_mble : MeasurableSet E) (h : μ E ≤ L.liminf fun i ↦ μs i E) :
    (L.limsup fun i ↦ μs i Eᶜ) ≤ μ Eᶜ := by
  rcases L.eq_or_neBot with rfl | hne
  · simp only [limsup_bot, bot_le]
  have meas_Ec : μ Eᶜ = 1 - μ E := by
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top μ E).ne
  have meas_i_Ec : ∀ i, μs i Eᶜ = 1 - μs i E := by
    intro i
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top (μs i) E).ne
  simp_rw [meas_Ec, meas_i_Ec]
  rw [show (L.limsup fun i : ι ↦ 1 - μs i E) = L.limsup ((fun x ↦ 1 - x) ∘ fun i : ι ↦ μs i E)
      from rfl]
  have key := antitone_const_tsub.map_liminf_of_continuousAt (F := L)
    (fun i ↦ μs i E) (ENNReal.continuous_sub_left ENNReal.one_ne_top).continuousAt
  simpa [← key] using antitone_const_tsub h
/-
**MeasureTheory.limsup_measure_le_of_le_liminf_measure_compl** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
形式化陈述：limsup_measure_le_of_le_liminf_measure_compl {ι : Type*} {L : Filter ι} {μ
 : Measure Ω} {μs : ι -> Measure Ω} [IsProbabilityMeasure μ] [forall i, IsProbab
ilityMeasure (μs i)] {E : Set Ω} (E_mble : MeasurableSet E) (h : μ Eᶜ <= L.limin
f fun i => μs i Eᶜ) : (L.limsup fun i => μs i E) <= μ E
参数：μs i；E_mble : MeasurableSet E；h : μ Eᶜ <= L.liminf fun i => μs i Eᶜ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.limsup_measure_compl_le_of_le_liminf_measure`：limsup_measu
re_compl_le_of_le_liminf_measure {ι : Type*} {L : Filter ι} {μ : Measure Ω} {μs 
: ι -> Measure Ω} [IsProbabilityMeasure μ] [fora…
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
theorem limsup_measure_le_of_le_liminf_measure_compl {ι : Type*} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)] {E : Set Ω}
    (E_mble : MeasurableSet E) (h : μ Eᶜ ≤ L.liminf fun i ↦ μs i Eᶜ) :
    (L.limsup fun i ↦ μs i E) ≤ μ E :=
  compl_compl E ▸ limsup_measure_compl_le_of_le_liminf_measure (MeasurableSet.compl E_mble) h

variable [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/-- One pair of implications of the portmanteau theorem:
For a sequence of Borel probability measures, the following two are equivalent:

(C) The limsup of the measures of any closed set is at most the measure of the closed set
under a candidate limit measure.

(O) The liminf of the measures of any open set is at least the measure of the open set
under a candidate limit measure.
-/
/-
**MeasureTheory.limsup_measure_closed_le_iff_liminf_measure_open_ge** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：limsup_measure_closed_le_iff_liminf_measure_open_ge {ι : Type*} {L : Filte
r ι} {μ : Measure Ω} {μs : ι -> Measure Ω} [IsProbabilityMeasure μ] [forall i, I
sProbabilityMeasure (μs i)] : (forall F, IsClosed F -> (L.limsup fun i => μs i F
) <= μ F) ↔ forall G, IsOpen G -> μ G <= L.liminf fun i => μs i G
参数：μs i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.le_measure_liminf_of_limsup_measure_compl_le`：le_measure_l
iminf_of_limsup_measure_compl_le {ι : Type*} {L : Filter ι} {μ : Measure Ω} {μs 
: ι -> Measure Ω} [IsProbabilityMeasure μ] [fora…
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s
· 使用定理 `MeasureTheory.limsup_measure_le_of_le_liminf_measure_compl`：limsup_measu
re_le_of_le_liminf_measure_compl {ι : Type*} {L : Filter ι} {μ : Measure Ω} {μs 
: ι -> Measure Ω} [IsProbabilityMeasure μ] [fora…
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s

--- 原说明 ---
One pair of implications of the portmanteau theorem:
For a sequence of Borel probability measures, the following two are equivalent:

(C) The limsup of the measures of any closed set is at most the measure of the c
losed set
under a candidate limit measure.

(O) The liminf of the measures of any open set is at least the measure of the op
en set
under a candidate limit measure.
-/
theorem limsup_measure_closed_le_iff_liminf_measure_open_ge {ι : Type*} {L : Filter ι}
    {μ : Measure Ω} {μs : ι → Measure Ω} [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (μs i)] :
    (∀ F, IsClosed F → (L.limsup fun i ↦ μs i F) ≤ μ F) ↔
      ∀ G, IsOpen G → μ G ≤ L.liminf fun i ↦ μs i G := by
  constructor
  · intro h G G_open
    exact le_measure_liminf_of_limsup_measure_compl_le
      G_open.measurableSet (h Gᶜ (isClosed_compl_iff.mpr G_open))
  · intro h F F_closed
    exact limsup_measure_le_of_le_liminf_measure_compl
      F_closed.measurableSet (h Fᶜ (isOpen_compl_iff.mpr F_closed))

end LimsupClosedLEAndLELiminfOpen -- section

section TendstoOfNullFrontier

/-! ### Portmanteau: limit of measures of Borel sets whose boundary carries no mass in the limit

In this section we prove that for a sequence of Borel probability measures on a topological space
and its candidate limit measure, either of the following equivalent conditions:

  (C) For any closed set F, the limsup of the measures of F under μs is at most
      the measure of F under μ, i.e., limsupᵢ μsᵢ(F) ≤ μ(F);
  (O) For any open set G, the liminf of the measures of G under μs is at least
      the measure of G under μ, i.e., μ(G) ≤ liminfᵢ μsᵢ(G).

implies that

  (B) For any Borel set B whose boundary carries no mass under μ, i.e. μ(∂B) = 0,
      the measures of B under μs tend to the measure of B under μ, i.e., limᵢ μsᵢ(B) = μ(B).
-/


variable {Ω : Type*} [MeasurableSpace Ω]

/-
**MeasureTheory.tendsto_measure_of_le_liminf_measure_of_limsup_measure_le** 是 Ma
thlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_measure_of_le_liminf_measure_of_limsup_measure_le {ι : Type*} {L :
 Filter ι} {μ : Measure Ω} {μs : ι -> Measure Ω} {E₀ E E₁ : Set Ω} (E₀_subset : 
E₀ subseteq E) (subset_E₁ : E subseteq E₁) (nulldiff : μ (E₁ \ E₀) = 0) (h_E₀ : 
μ E₀ <= L.liminf fun i => μs i E₀) (h_E₁ : (L.limsup fun i => μs i E₁) <= μ E₁) 
: L.Tendsto (fun i => μs i E) (𝓝 (μ E))
参数：E₀_subset : E₀ subseteq E；subset_E₁ : E subseteq E₁；nulldiff : μ (E₁ \ E₀) = 
0；h_E₀ : μ E₀ <= L.liminf fun i => μs i E₀；h_E₁ : (L.limsup fun i => μs i E₁) <=
 μ E₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_of_le_liminf_of_limsup_le`：tendsto_of_le_liminf_of_limsup_le {f 
: Filter β} {u : β -> α} {a : α} (hinf : a <= liminf u f) (hsup : limsup u f <= 
a) (h : f.IsBoundedUnde…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyLE.antisymm`：∀ {α : Type u} {β : Type v} [inst : Partia
lOrder β] {l : Filter α} {f g : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] f → f =ᶠ[l] g
· 使用定理 `LE.le.eventuallyLE`：LE.le.eventuallyLE {α} {l : Filter α} {s t : Set α} 
(h : s subseteq t) : s <=ᶠ[l] t
· 使用定理 `Filter.EventuallyLE.trans`：∀ {α : Type u} {β : Type v} [inst : Preorder 
β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_le_set`：ae_le_set : s <=ᵐ[μ] t ↔ μ (s \ t) = 0
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Filter.liminf_le_liminf`：liminf_le_liminf {α : Type*} [ConditionallyComp
leteLattice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a <= v a) (h
u : f.IsBound…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.limsup_le_limsup`：limsup_le_limsup {α : Type*} [ConditionallyComp
leteLattice β] {f : Filter α} {u v : α -> β} (h : u <=ᶠ[f] v) (hu : f.IsCobounde
dUnder (· <= …
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
-/
theorem tendsto_measure_of_le_liminf_measure_of_limsup_measure_le {ι : Type*} {L : Filter ι}
    {μ : Measure Ω} {μs : ι → Measure Ω} {E₀ E E₁ : Set Ω} (E₀_subset : E₀ ⊆ E) (subset_E₁ : E ⊆ E₁)
    (nulldiff : μ (E₁ \ E₀) = 0) (h_E₀ : μ E₀ ≤ L.liminf fun i ↦ μs i E₀)
    (h_E₁ : (L.limsup fun i ↦ μs i E₁) ≤ μ E₁) : L.Tendsto (fun i ↦ μs i E) (𝓝 (μ E)) := by
  apply tendsto_of_le_liminf_of_limsup_le
  · have E₀_ae_eq_E : E₀ =ᵐ[μ] E :=
      EventuallyLE.antisymm E₀_subset.eventuallyLE
        (subset_E₁.eventuallyLE.trans (ae_le_set.mpr nulldiff))
    calc
      μ E = μ E₀ := measure_congr E₀_ae_eq_E.symm
      _ ≤ L.liminf fun i ↦ μs i E₀ := h_E₀
      _ ≤ L.liminf fun i ↦ μs i E :=
        liminf_le_liminf (.of_forall fun _ ↦ measure_mono E₀_subset)
  · have E_ae_eq_E₁ : E =ᵐ[μ] E₁ :=
      EventuallyLE.antisymm subset_E₁.eventuallyLE
        ((ae_le_set.mpr nulldiff).trans E₀_subset.eventuallyLE)
    calc
      (L.limsup fun i ↦ μs i E) ≤ L.limsup fun i ↦ μs i E₁ :=
        limsup_le_limsup (.of_forall fun _ ↦ measure_mono subset_E₁)
      _ ≤ μ E₁ := h_E₁
      _ = μ E := measure_congr E_ae_eq_E₁.symm
  · infer_param
  · infer_param

variable [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/-- One implication of the portmanteau theorem:
For a sequence of Borel probability measures, if the liminf of the measures of any open set is at
least the measure of the open set under a candidate limit measure, then for any set whose
boundary carries no probability mass under the candidate limit measure, then its measures under the
sequence converge to its measure under the candidate limit measure.
-/
/-
**MeasureTheory.tendsto_measure_of_null_frontier** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：tendsto_measure_of_null_frontier {ι : Type*} {L : Filter ι} {μ : Measure Ω
} {μs : ι -> Measure Ω} [IsProbabilityMeasure μ] [forall i, IsProbabilityMeasure
 (μs i)] (h_opens : forall G, IsOpen G -> μ G <= L.liminf fun i => μs i G) {E : 
Set Ω} (E_nullbdry : μ (frontier E) = 0) : L.Tendsto (fun i => μs i E) (𝓝 (μ E))
参数：μs i；h_opens : forall G, IsOpen G -> μ G <= L.liminf fun i => μs i G；E_nullbd
ry : μ (frontier E) = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tendsto_measure_of_le_liminf_measure_of_limsup_measure_le`
：tendsto_measure_of_le_liminf_measure_of_limsup_measure_le {ι : Type*} {L : Filt
er ι} {μ : Measure Ω} {μs : ι -> Measure Ω} {E₀ E E₁ : Set Ω}…
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.limsup_measure_closed_le_iff_liminf_measure_open_ge`：limsu
p_measure_closed_le_iff_liminf_measure_open_ge {ι : Type*} {L : Filter ι} {μ : M
easure Ω} {μs : ι -> Measure Ω} [IsProbabilityMeasure μ…
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)

--- 原说明 ---
One implication of the portmanteau theorem:
For a sequence of Borel probability measures, if the liminf of the measures of a
ny open set is at
least the measure of the open set under a candidate limit measure, then for any 
set whose
boundary carries no probability mass under the candidate limit measure, then its
 measures under the
sequence converge to its measure under the candidate limit measure.
-/
theorem tendsto_measure_of_null_frontier {ι : Type*} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)]
    (h_opens : ∀ G, IsOpen G → μ G ≤ L.liminf fun i ↦ μs i G) {E : Set Ω}
    (E_nullbdry : μ (frontier E) = 0) : L.Tendsto (fun i ↦ μs i E) (𝓝 (μ E)) :=
  haveI h_closeds : ∀ F, IsClosed F → (L.limsup fun i ↦ μs i F) ≤ μ F :=
    limsup_measure_closed_le_iff_liminf_measure_open_ge.mpr h_opens
  tendsto_measure_of_le_liminf_measure_of_limsup_measure_le interior_subset subset_closure
    E_nullbdry (h_opens _ isOpen_interior) (h_closeds _ isClosed_closure)

end TendstoOfNullFrontier --section

section ConvergenceImpliesLimsupClosedLE

/-! ### Portmanteau implication: weak convergence implies a limsup condition for closed sets

In this section we prove, under the assumption that the underlying topological space `Ω` is
pseudo-emetrizable, that

  (T) The measures μs tend to the measure μ weakly

implies

  (C) For any closed set F, the limsup of the measures of F under μs is at most
      the measure of F under μ, i.e., limsupᵢ μsᵢ(F) ≤ μ(F).

Combining with earlier proven implications, we get that (T) implies also both

  (O) For any open set G, the liminf of the measures of G under μs is at least
      the measure of G under μ, i.e., μ(G) ≤ liminfᵢ μsᵢ(G);
  (B) For any Borel set B whose boundary carries no mass under μ, i.e. μ(∂B) = 0,
      the measures of B under μs tend to the measure of B under μ, i.e., limᵢ μsᵢ(B) = μ(B).
-/


/-- One implication of the portmanteau theorem:
Weak convergence of finite measures implies that the limsup of the measures of any closed set is
at most the measure of the closed set under the limit measure.
-/
/-
**MeasureTheory.FiniteMeasure.limsup_measure_closed_le_of_tendsto** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.FiniteMeasure`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {L : Filter ι} [inst : MeasurableSpace Ω] 
[inst_1 : TopologicalSpace Ω]   [HasOuterApproxClosed Ω] [inst_3 : OpensMeasurab
leSpace Ω] {μ : MeasureTheory.FiniteMeasure Ω}   {μs : ι → MeasureTheory.FiniteM
easure Ω},   Filter.Tendsto μs L (nhds μ) → ∀ {F : Set Ω}, IsClosed F → Filter.l
imsup (fun i => ↑(μs i) F) L ≤ ↑μ F
参数：nhds μ；fun i => ↑(μs i) F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.limsup_bot`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLatti
ce α] (f : β → α), Filter.limsup f ⊥ = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.le_of_forall_pos_le_add`：le_of_forall_pos_le_add (h : forall ε :
 Real>=0, 0 < ε -> b < ∞ -> a <= b + ε) : a <= b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ENNReal.half_pos`：∀ {a : ENNReal}, a ≠ 0 → 0 < a / 2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_ne_zero`：coe_ne_zero : (r : Real>=0∞) != 0 ↔ r != 0
· 使用引理 `HasOuterApproxClosed.tendsto_lintegral_apprSeq`：tendsto_lintegral_apprSe
q [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure 
μ] : Tendsto (fun n => ∫⁻ x, hF.appr…
· 使用定理 `ENNReal.lt_add_right`：lt_add_right (ha : a != ∞) (hb : b != 0) : a < a +
 b
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.eventually_lt_const`：∀ {α : Type u} {γ : Type w} [inst : 
TopologicalSpace α] [inst_1 : LinearOrder α] [ClosedIciTopology α] {l : Filter γ
}   {f : γ → α} {u v : α…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `MeasureTheory.FiniteMeasure.tendsto_iff_forall_lintegral_tendsto`：tendst
o_iff_forall_lintegral_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> FiniteMeasu
re Ω} {μ : FiniteMeasure Ω} : Tendsto μs F (𝓝 μ) ↔ for…
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
One implication of the portmanteau theorem:
Weak convergence of finite measures implies that the limsup of the measures of a
ny closed set is
at most the measure of the closed set under the limit measure.
-/
theorem FiniteMeasure.limsup_measure_closed_le_of_tendsto {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [HasOuterApproxClosed Ω]
    [OpensMeasurableSpace Ω] {μ : FiniteMeasure Ω}
    {μs : ι → FiniteMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ)) {F : Set Ω} (F_closed : IsClosed F) :
    (L.limsup fun i ↦ (μs i : Measure Ω) F) ≤ (μ : Measure Ω) F := by
  rcases L.eq_or_neBot with rfl | hne
  · simp only [limsup_bot, bot_le]
  apply ENNReal.le_of_forall_pos_le_add
  intro ε ε_pos _
  have ε_pos' := (ENNReal.half_pos (ENNReal.coe_ne_zero.mpr ε_pos.ne.symm)).ne.symm
  let fs := F_closed.apprSeq
  have key₁ : Tendsto (fun n ↦ ∫⁻ ω, (fs n ω : ℝ≥0∞) ∂μ) atTop (𝓝 ((μ : Measure Ω) F)) :=
    HasOuterApproxClosed.tendsto_lintegral_apprSeq F_closed (μ : Measure Ω)
  have room₁ : (μ : Measure Ω) F < (μ : Measure Ω) F + ε / 2 :=
    ENNReal.lt_add_right (measure_lt_top (μ : Measure Ω) F).ne ε_pos'
  obtain ⟨M, hM⟩ := eventually_atTop.mp <| key₁.eventually_lt_const room₁
  have key₂ := FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mp μs_lim (fs M)
  have room₂ :
    (lintegral (μ : Measure Ω) fun a ↦ fs M a) <
      (lintegral (μ : Measure Ω) fun a ↦ fs M a) + ε / 2 :=
    ENNReal.lt_add_right (ne_of_lt ((fs M).lintegral_lt_top_of_nnreal _)) ε_pos'
  have ev_near := key₂.eventually_le_const room₂
  have ev_near' := ev_near.mono
    (fun n ↦ le_trans (HasOuterApproxClosed.measure_le_lintegral F_closed (μs n) M))
  apply (Filter.limsup_le_limsup ev_near').trans
  rw [limsup_const]
  apply le_trans (add_le_add (hM M rfl.le).le (le_refl (ε / 2 : ℝ≥0∞)))
  simp only [add_assoc, ENNReal.add_halves, le_refl]

/-- One implication of the portmanteau theorem:
Weak convergence of probability measures implies that the limsup of the measures of any closed
set is at most the measure of the closed set under the limit probability measure.
-/
/-
**MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_tendsto** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {L : Filter ι} [inst : MeasurableSpace Ω] 
[inst_1 : TopologicalSpace Ω]   [inst_2 : OpensMeasurableSpace Ω] [HasOuterAppro
xClosed Ω] {μ : MeasureTheory.ProbabilityMeasure Ω}   {μs : ι → MeasureTheory.Pr
obabilityMeasure Ω},   Filter.Tendsto μs L (nhds μ) → ∀ {F : Set Ω}, IsClosed F 
→ Filter.limsup (fun i => ↑(μs i) F) L ≤ ↑μ F
参数：nhds μ；fun i => ↑(μs i) F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.FiniteMeasure.limsup_measure_closed_le_of_tendsto`：∀ {Ω : 
Type u_1} {ι : Type u_2} {L : Filter ι} [inst : MeasurableSpace Ω] [inst_1 : Top
ologicalSpace Ω]   [HasOuterApproxClosed Ω] [inst_3 :…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendst
o_nhds`：tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds {δ : Type*} (F : Filter δ)
 {μs : δ -> ProbabilityMeasure Ω} {μ₀ : ProbabilityMeasure Ω} : Tend…

--- 原说明 ---
One implication of the portmanteau theorem:
Weak convergence of probability measures implies that the limsup of the measures
 of any closed
set is at most the measure of the closed set under the limit probability measure
.
-/
theorem ProbabilityMeasure.limsup_measure_closed_le_of_tendsto {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ))
    {F : Set Ω} (F_closed : IsClosed F) :
    (L.limsup fun i ↦ (μs i : Measure Ω) F) ≤ (μ : Measure Ω) F := by
  apply FiniteMeasure.limsup_measure_closed_le_of_tendsto
    ((tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds L).mp μs_lim) F_closed

/-- One implication of the portmanteau theorem:
Weak convergence of probability measures implies that the liminf of the measures of any open set
is at least the measure of the open set under the limit probability measure.
-/
/-
**MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {L : Filter ι} [inst : MeasurableSpace Ω] 
[inst_1 : TopologicalSpace Ω]   [inst_2 : OpensMeasurableSpace Ω] [HasOuterAppro
xClosed Ω] {μ : MeasureTheory.ProbabilityMeasure Ω}   {μs : ι → MeasureTheory.Pr
obabilityMeasure Ω},   Filter.Tendsto μs L (nhds μ) → ∀ {G : Set Ω}, IsOpen G → 
↑μ G ≤ Filter.liminf (fun i => ↑(μs i) G) L
参数：nhds μ；fun i => ↑(μs i) G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.le_measure_liminf_of_limsup_measure_compl_le`：le_measure_l
iminf_of_limsup_measure_compl_le {ι : Type*} {L : Filter ι} {μ : Measure Ω} {μs 
: ι -> Measure Ω} [IsProbabilityMeasure μ] [fora…
· 使用定理 `MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure`：∀ {Ω
 : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.ProbabilityMeasure Ω)
,   MeasureTheory.IsProbabilityMeasure ↑μ
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`：∀ 
{Ω : Type u_1} {ι : Type u_2} {L : Filter ι} [inst : MeasurableSpace Ω] [inst_1 
: TopologicalSpace Ω]   [inst_2 : OpensMeasurableSpace Ω] …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s

--- 原说明 ---
One implication of the portmanteau theorem:
Weak convergence of probability measures implies that the liminf of the measures
 of any open set
is at least the measure of the open set under the limit probability measure.
-/
theorem ProbabilityMeasure.le_liminf_measure_open_of_tendsto {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ))
    {G : Set Ω} (G_open : IsOpen G) :
    (μ : Measure Ω) G ≤ L.liminf fun i ↦ (μs i : Measure Ω) G :=
  haveI h_closeds : ∀ F, IsClosed F → (L.limsup fun i ↦ (μs i : Measure Ω) F) ≤ (μ : Measure Ω) F :=
    fun _ F_closed ↦ limsup_measure_closed_le_of_tendsto μs_lim F_closed
  le_measure_liminf_of_limsup_measure_compl_le G_open.measurableSet
    (h_closeds _ (isClosed_compl_iff.mpr G_open))
/-
**MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'*
* 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {L : Filter ι} [inst : MeasurableSpace Ω] 
[inst_1 : TopologicalSpace Ω]   [inst_2 : OpensMeasurableSpace Ω] [HasOuterAppro
xClosed Ω] {μ : MeasureTheory.ProbabilityMeasure Ω}   {μs : ι → MeasureTheory.Pr
obabilityMeasure Ω},   Filter.Tendsto μs L (nhds μ) →     ∀ {E : Set Ω}, ↑μ (fro
ntier E) = 0 → Filter.Tendsto (fun i => ↑(μs i) E) L (nhds (↑μ E))
参数：nhds μ；frontier E；fun i => ↑(μs i) E；nhds (↑μ E)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tendsto_measure_of_null_frontier`：tendsto_measure_of_null_
frontier {ι : Type*} {L : Filter ι} {μ : Measure Ω} {μs : ι -> Measure Ω} [IsPro
babilityMeasure μ] [forall i, IsProb…
· 使用定理 `MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure`：∀ {Ω
 : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.ProbabilityMeasure Ω)
,   MeasureTheory.IsProbabilityMeasure ↑μ
· 使用定理 `MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto`：∀ {Ω
 : Type u_1} {ι : Type u_2} {L : Filter ι} [inst : MeasurableSpace Ω] [inst_1 : 
TopologicalSpace Ω]   [inst_2 : OpensMeasurableSpace Ω] …
-/
theorem ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' {Ω ι : Type*}
    {L : Filter ι} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    [HasOuterApproxClosed Ω] {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω}
    (μs_lim : Tendsto μs L (𝓝 μ)) {E : Set Ω} (E_nullbdry : (μ : Measure Ω) (frontier E) = 0) :
    Tendsto (fun i ↦ (μs i : Measure Ω) E) L (𝓝 ((μ : Measure Ω) E)) :=
  haveI h_opens : ∀ G, IsOpen G → (μ : Measure Ω) G ≤ L.liminf fun i ↦ (μs i : Measure Ω) G :=
    fun _ G_open ↦ le_liminf_measure_open_of_tendsto μs_lim G_open
  tendsto_measure_of_null_frontier h_opens E_nullbdry

/-- One implication of the portmanteau theorem:
Weak convergence of probability measures implies that if the boundary of a Borel set
carries no probability mass under the limit measure, then the limit of the measures of the set
equals the measure of the set under the limit probability measure.

A version with coercions to ordinary `ℝ≥0∞`-valued measures is
`MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'`.
-/
/-
**MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto**
 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {L : Filter ι} [inst : MeasurableSpace Ω] 
[inst_1 : TopologicalSpace Ω]   [inst_2 : OpensMeasurableSpace Ω] [HasOuterAppro
xClosed Ω] {μ : MeasureTheory.ProbabilityMeasure Ω}   {μs : ι → MeasureTheory.Pr
obabilityMeasure Ω},   Filter.Tendsto μs L (nhds μ) → ∀ {E : Set Ω}, μ (frontier
 E) = 0 → Filter.Tendsto (fun i => (μs i) E) L (nhds (μ E))
参数：nhds μ；frontier E；fun i => (μs i) E；nhds (μ E)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_ten
dsto'`：∀ {Ω : Type u_1} {ι : Type u_2} {L : Filter ι} [inst : MeasurableSpace Ω]
 [inst_1 : TopologicalSpace Ω]   [inst_2 : OpensMeasurableSpace Ω] …
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ENNReal.tendsto_toNNReal`：tendsto_toNNReal {a : Real>=0∞} (ha : a != ∞) 
: Tendsto ENNReal.toNNReal (𝓝 a) (𝓝 a.toNNReal)
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure`：∀ {Ω
 : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.ProbabilityMeasure Ω)
,   MeasureTheory.IsProbabilityMeasure ↑μ

--- 原说明 ---
One implication of the portmanteau theorem:
Weak convergence of probability measures implies that if the boundary of a Borel
 set
carries no probability mass under the limit measure, then the limit of the measu
res of the set
equals the measure of the set under the limit probability measure.

A version with coercions to ordinary `ℝ≥0∞`-valued measures is
`MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'`.
-/
theorem ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ))
    {E : Set Ω} (E_nullbdry : μ (frontier E) = 0) : Tendsto (fun i ↦ μs i E) L (𝓝 (μ E)) := by
  have key := tendsto_measure_of_null_frontier_of_tendsto' μs_lim (by simpa using E_nullbdry)
  exact (ENNReal.tendsto_toNNReal (measure_ne_top (↑μ) E)).comp key

/-- One implication of the portmanteau theorem:
Weak convergence of probability measures implies that if a set is clopen, then the limit of the
measures of the set equals the measure of the set under the limit probability measure.
-/
/-
**MeasureTheory.ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto** 是 Ma
thlib 中的一个定理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {L : Filter ι} [inst : MeasurableSpace Ω] 
[inst_1 : TopologicalSpace Ω]   [inst_2 : OpensMeasurableSpace Ω] [HasOuterAppro
xClosed Ω] {μ : MeasureTheory.ProbabilityMeasure Ω}   {μs : ι → MeasureTheory.Pr
obabilityMeasure Ω},   Filter.Tendsto μs L (nhds μ) → ∀ {E : Set Ω}, IsClopen E 
→ Filter.Tendsto (fun i => (μs i) E) L (nhds (μ E))
参数：nhds μ；fun i => (μs i) E；nhds (μ E)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_ten
dsto`：∀ {Ω : Type u_1} {ι : Type u_2} {L : Filter ι} [inst : MeasurableSpace Ω] 
[inst_1 : TopologicalSpace Ω]   [inst_2 : OpensMeasurableSpace Ω] …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClopen.frontier_eq`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Se
t X}, IsClopen s → frontier s = ∅
· 使用定理 `MeasureTheory.ProbabilityMeasure.coeFn_empty`：coeFn_empty (ν : Probabili
tyMeasure Ω) : ν ∅ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
One implication of the portmanteau theorem:
Weak convergence of probability measures implies that if a set is clopen, then t
he limit of the
measures of the set equals the measure of the set under the limit probability me
asure.
-/
theorem ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ))
    {E : Set Ω} (hE : IsClopen E) : Tendsto (fun i ↦ μs i E) L (𝓝 (μ E)) :=
  ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto μs_lim (by simp [hE])

end ConvergenceImpliesLimsupClosedLE --section

section LimitBorelImpliesLimsupClosedLE

/-! ### Portmanteau implication: limit condition for Borel sets implies limsup for closed sets


In this section we prove, under the assumption that the underlying topological space `Ω` is
pseudo-emetrizable, that

  (B) For any Borel set B whose boundary carries no mass under μ, i.e. μ(∂B) = 0,
      the measures of B under μs tend to the measure of B under μ, i.e., limᵢ μsᵢ(B) = μ(B)

implies

  (C) For any closed set F, the limsup of the measures of F under μs is at most
      the measure of F under μ, i.e., limsupᵢ μsᵢ(F) ≤ μ(F).

Combining with earlier proven implications, we get that (B) implies also

  (O) For any open set G, the liminf of the measures of G under μs is at least
      the measure of G under μ, i.e., μ(G) ≤ liminfᵢ μsᵢ(G).

-/

open ENNReal

section PseudoMetricSpace

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

/-
**MeasureTheory.exists_null_frontier_thickening** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：exists_null_frontier_thickening (μ : Measure Ω) [SFinite μ] (s : Set Ω) {a
 b : Real} (hab : a < b) : exists r in Ioo a b, μ (frontier (Metric.thickening r
 s)) = 0
参数：μ : Measure Ω；s : Set Ω；hab : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `isClosed_frontier`：isClosed_frontier : IsClosed (frontier s)
· 使用定理 `Metric.frontier_thickening_disjoint`：frontier_thickening_disjoint (A : S
et α) : Pairwise (Disjoint on fun r : Real => frontier (thickening r A))
· 使用定理 `MeasureTheory.Measure.countable_meas_pos_of_disjoint_iUnion`：countable_m
eas_pos_of_disjoint_iUnion {ι : Type*} {_ : MeasurableSpace α} {μ : Measure α} [
SFinite μ] {As : ι -> Set α} (As_mble : forall i …
· 使用定理 `MeasureTheory.measure_sdiff_null`：measure_sdiff_null (ht : μ t = 0) : μ 
(s \ t) = μ s
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.Countable.measure_zero`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {s
 : Set α},   s.Countable → ∀ (μ : MeasureTheory.Measure α) [MeasureTheory.NullSi
ngletonClass μ],…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.nonempty_of_measure_ne_zero`：nonempty_of_measure_ne_zero (
h : μ s != 0) : s.Nonempty
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.volume_Ioo`：volume_Ioo {a b : Real} : volume (Ioo a b) = ofReal (b 
- a)
-/
theorem exists_null_frontier_thickening (μ : Measure Ω) [SFinite μ] (s : Set Ω) {a b : ℝ}
    (hab : a < b) : ∃ r ∈ Ioo a b, μ (frontier (Metric.thickening r s)) = 0 := by
  have mbles : ∀ r : ℝ, MeasurableSet (frontier (Metric.thickening r s)) :=
    fun r ↦ isClosed_frontier.measurableSet
  have disjs := Metric.frontier_thickening_disjoint s
  have key := Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ) mbles disjs
  have aux := measure_sdiff_null (s := Ioo a b) (Set.Countable.measure_zero key volume)
  have len_pos : 0 < ENNReal.ofReal (b - a) := by simp only [hab, ENNReal.ofReal_pos, sub_pos]
  rw [← Real.volume_Ioo, ← aux] at len_pos
  simpa [Set.Nonempty] using nonempty_of_measure_ne_zero len_pos.ne'
/-
**MeasureTheory.exists_null_frontiers_thickening** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：exists_null_frontiers_thickening (μ : Measure Ω) [SFinite μ] (s : Set Ω) :
 exists rs : Nat -> Real, Tendsto rs atTop (𝓝 0) ∧ forall n, 0 < rs n ∧ μ (front
ier (Metric.thickening (rs n) s)) = 0
参数：μ : Measure Ω；s : Set Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_seq_strictAnti_tendsto`：exists_seq_strictAnti_tendsto [DenselyOrd
ered α] [NoMaxOrder α] [FirstCountableTopology α] (x : α) : exists u : Nat -> α,
 StrictAnti u ∧ (fo…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.exists_null_frontier_thickening`：exists_null_frontier_thic
kening (μ : Measure Ω) [SFinite μ] (s : Set Ω) {a b : Real} (hab : a < b) : exis
ts r in Ioo a b, μ (frontier (Metri…
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le`：tendsto_of_tendsto_of_tendsto
_of_le_of_le [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : Ten
dsto g b (𝓝 a)) (hh : Tendsto h…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem exists_null_frontiers_thickening (μ : Measure Ω) [SFinite μ] (s : Set Ω) :
    ∃ rs : ℕ → ℝ,
      Tendsto rs atTop (𝓝 0) ∧ ∀ n, 0 < rs n ∧ μ (frontier (Metric.thickening (rs n) s)) = 0 := by
  rcases exists_seq_strictAnti_tendsto (0 : ℝ) with ⟨Rs, ⟨_, ⟨Rs_pos, Rs_lim⟩⟩⟩
  have obs := fun n : ℕ => exists_null_frontier_thickening μ s (Rs_pos n)
  refine ⟨fun n : ℕ => (obs n).choose, ⟨?_, ?_⟩⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds Rs_lim
      (fun n ↦ (obs n).choose_spec.1.1.le) fun n ↦ (obs n).choose_spec.1.2.le
  · exact fun n ↦ ⟨(obs n).choose_spec.1.1, (obs n).choose_spec.2⟩

end PseudoMetricSpace

open TopologicalSpace

/-- One implication of the portmanteau theorem:
Assuming that for all Borel sets E whose boundary ∂E carries no probability mass under a
candidate limit probability measure μ we have convergence of the measures μsᵢ(E) to μ(E),
then for all closed sets F we have the limsup condition limsup μsᵢ(F) ≤ μ(F). -/
/-
**MeasureTheory.limsup_measure_closed_le_of_forall_tendsto_measure** 是 Mathlib 中
的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：limsup_measure_closed_le_of_forall_tendsto_measure {Ω ι : Type*} {L : Filt
er ι} [MeasurableSpace Ω] [TopologicalSpace Ω] [PseudoMetrizableSpace Ω] [OpensM
easurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {μs : ι -> Measure Ω} (h :
 forall {E : Set Ω}, MeasurableSet E -> μ (frontier E) = 0 -> Tendsto (fun i => 
μs i E) L (𝓝 (μ E))) (F : Set Ω) (F_closed : IsClosed F) : L.limsup (fun i => μs
 i F) <= μ F
参数：h : forall {E : Set Ω}, MeasurableSet E -> μ (frontier E) = 0 -> Tendsto (fun
 i => μs i E) L (𝓝 (μ E))；F : Set Ω；F_closed : IsClosed F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.limsup_bot`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLatti
ce α] (f : β → α), Filter.limsup f ⊥ = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.exists_null_frontiers_thickening`：exists_null_frontiers_th
ickening (μ : Measure Ω) [SFinite μ] (s : Set Ω) : exists rs : Nat -> Real, Tend
sto rs atTop (𝓝 0) ∧ forall n, 0 < r…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Metric.isOpen_thickening`：isOpen_thickening {δ : Real} {E : Set α} : IsO
pen (thickening δ E)
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `ENNReal.le_of_forall_pos_le_add`：le_of_forall_pos_le_add (h : forall ε :
 Real>=0, 0 < ε -> b < ∞ -> a <= b + ε) : a <= b
· 使用定理 `tendsto_measure_cthickening_of_isClosed`：tendsto_measure_cthickening_of_
isClosed {μ : Measure α} {s : Set α} (hs : exists R > 0, μ (cthickening R s) != 
∞) (h's : IsClosed s) : Tends…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `Iio_mem_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Iio a ∈ nhds b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.lt_add_right`：lt_add_right (ha : a != ∞) (hb : b != 0) : a < a +
 b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
One implication of the portmanteau theorem:
Assuming that for all Borel sets E whose boundary ∂E carries no probability mass
 under a
candidate limit probability measure μ we have convergence of the measures μsᵢ(E)
 to μ(E),
then for all closed sets F we have the limsup condition limsup μsᵢ(F) ≤ μ(F).
-/
lemma limsup_measure_closed_le_of_forall_tendsto_measure
    {Ω ι : Type*} {L : Filter ι} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [PseudoMetrizableSpace Ω] [OpensMeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {μs : ι → Measure Ω}
    (h : ∀ {E : Set Ω}, MeasurableSet E → μ (frontier E) = 0 →
            Tendsto (fun i ↦ μs i E) L (𝓝 (μ E)))
    (F : Set Ω) (F_closed : IsClosed F) :
    L.limsup (fun i ↦ μs i F) ≤ μ F := by
  let : PseudoMetricSpace Ω := TopologicalSpace.pseudoMetrizableSpacePseudoMetric Ω
  rcases L.eq_or_neBot with rfl | _
  · simp only [limsup_bot, bot_eq_zero', zero_le]
  have ex := exists_null_frontiers_thickening μ F
  let rs := Classical.choose ex
  have rs_lim : Tendsto rs atTop (𝓝 0) := (Classical.choose_spec ex).1
  have rs_pos : ∀ n, 0 < rs n := fun n ↦ ((Classical.choose_spec ex).2 n).1
  have rs_null : ∀ n, μ (frontier (Metric.thickening (rs n) F)) = 0 :=
    fun n ↦ ((Classical.choose_spec ex).2 n).2
  have Fthicks_open : ∀ n, IsOpen (Metric.thickening (rs n) F) :=
    fun n ↦ Metric.isOpen_thickening
  have key := fun (n : ℕ) ↦ h (Fthicks_open n).measurableSet (rs_null n)
  apply ENNReal.le_of_forall_pos_le_add
  intro ε ε_pos μF_finite
  have keyB := tendsto_measure_cthickening_of_isClosed (μ := μ) (s := F)
                ⟨1, ⟨by simp only [gt_iff_lt, zero_lt_one], measure_ne_top _ _⟩⟩ F_closed
  have nhds : Iio (μ F + ε) ∈ 𝓝 (μ F) :=
    Iio_mem_nhds <| ENNReal.lt_add_right μF_finite.ne (ENNReal.coe_pos.mpr ε_pos).ne'
  specialize rs_lim (keyB nhds)
  simp only [mem_map, mem_atTop_sets, mem_preimage, mem_Iio] at rs_lim
  obtain ⟨m, hm⟩ := rs_lim
  have aux : (fun i ↦ (μs i F)) ≤ᶠ[L] (fun i ↦ μs i (Metric.thickening (rs m) F)) :=
    .of_forall <| fun i ↦ measure_mono (Metric.self_subset_thickening (rs_pos m) F)
  refine (limsup_le_limsup aux).trans ?_
  rw [Tendsto.limsup_eq (key m)]
  apply (measure_mono (Metric.thickening_subset_cthickening (rs m) F)).trans (hm m rfl.le).le

/-- One implication of the portmanteau theorem:
Assuming that for all Borel sets E whose boundary ∂E carries no probability mass under a
candidate limit probability measure μ we have convergence of the measures μsᵢ(E) to μ(E),
then for all open sets G we have the limsup condition μ(G) ≤ liminf μsᵢ(G). -/
/-
**MeasureTheory.le_liminf_measure_open_of_forall_tendsto_measure** 是 Mathlib 中的一
个引理，位于命名空间 `MeasureTheory`。
形式化陈述：le_liminf_measure_open_of_forall_tendsto_measure {Ω ι : Type*} {L : Filter
 ι} [MeasurableSpace Ω] [TopologicalSpace Ω] [PseudoMetrizableSpace Ω] [OpensMea
surableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {μs : ι -> Measure Ω} [
forall i, IsProbabilityMeasure (μs i)] (h : forall {E}, MeasurableSet E -> μ (fr
ontier E) = 0 -> Tendsto (fun i => μs i E) L (𝓝 (μ E))) (G : Set Ω) (G_open : Is
Open G) : μ G <= L.liminf (fun i => μs i G)
参数：μs i；h : forall {E}, MeasurableSet E -> μ (frontier E) = 0 -> Tendsto (fun i 
=> μs i E) L (𝓝 (μ E))；G : Set Ω；G_open : IsOpen G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.le_measure_liminf_of_limsup_measure_compl_le`：le_measure_l
iminf_of_limsup_measure_compl_le {ι : Type*} {L : Filter ι} {μ : Measure Ω} {μs 
: ι -> Measure Ω} [IsProbabilityMeasure μ] [fora…
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用引理 `MeasureTheory.limsup_measure_closed_le_of_forall_tendsto_measure`：limsup
_measure_closed_le_of_forall_tendsto_measure {Ω ι : Type*} {L : Filter ι} [Measu
rableSpace Ω] [TopologicalSpace Ω] [PseudoMetrizableSp…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s

--- 原说明 ---
One implication of the portmanteau theorem:
Assuming that for all Borel sets E whose boundary ∂E carries no probability mass
 under a
candidate limit probability measure μ we have convergence of the measures μsᵢ(E)
 to μ(E),
then for all open sets G we have the limsup condition μ(G) ≤ liminf μsᵢ(G).
-/
lemma le_liminf_measure_open_of_forall_tendsto_measure
    {Ω ι : Type*} {L : Filter ι} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [PseudoMetrizableSpace Ω] [OpensMeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μs : ι → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]
    (h : ∀ {E}, MeasurableSet E → μ (frontier E) = 0 → Tendsto (fun i ↦ μs i E) L (𝓝 (μ E)))
    (G : Set Ω) (G_open : IsOpen G) :
    μ G ≤ L.liminf (fun i ↦ μs i G) := by
  apply le_measure_liminf_of_limsup_measure_compl_le G_open.measurableSet
  exact limsup_measure_closed_le_of_forall_tendsto_measure h _ (isClosed_compl_iff.mpr G_open)

end LimitBorelImpliesLimsupClosedLE --section

section le_liminf_open_implies_convergence

/-! ### Portmanteau implication: liminf condition for open sets implies weak convergence


In this section we prove for a sequence (μsₙ)ₙ Borel probability measures that

  (O) For any open set G, the liminf of the measures of G under μsₙ is at least
      the measure of G under μ, i.e., μ(G) ≤ liminfₙ μsₙ(G).

implies

  (T) The measures μsₙ converge weakly to the measure μ.

-/

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/-
**MeasureTheory.lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf
_measure** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure {
μ : Measure Ω} {μs : Nat -> Measure Ω} {f : Ω -> Real} (f_cont : Continuous f) (
f_nn : 0 <= f) (h_opens : forall G, IsOpen G -> μ G <= atTop.liminf (fun i => μs
 i G)) : ∫⁻ x, ENNReal.ofReal (f x) ∂μ <= atTop.liminf (fun i => ∫⁻ x, ENNReal.o
fReal (f x) ∂(μs i))
参数：f_cont : Continuous f；f_nn : 0 <= f；h_opens : forall G, IsOpen G -> μ G <= at
Top.liminf (fun i => μs i G)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_eq_lintegral_meas_lt`：lintegral_eq_lintegral_mea
s_lt (μ : Measure α) (f_nn : 0 <=ᵐ[μ] f) (f_mble : AEMeasurable f μ) : ∫⁻ ω, ENN
Real.ofReal (f ω) ∂μ = ∫⁻ t in Ioi…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Continuous.aemeasurable`：Continuous.aemeasurable {f : α -> γ} (h : Conti
nuous f) {μ : Measure α} : AEMeasurable f μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_def`：continuous_def {_ : TopologicalSpace X} {_ : Topological
Space Y} {f : X -> Y} : Continuous f ↔ forall s, IsOpen s -> IsOpen (f ⁻¹' s)
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.lintegral_liminf_le`：lintegral_liminf_le {ι : Type*} {f : 
ι -> α -> Real>=0∞} {u : Filter ι} [IsCountablyGenerated u] (h_meas : forall i, 
Measurable (f i)) : ∫⁻ …
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Antitone.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Topological
Space α] {mα : MeasurableSpace α} [BorelSpace α]   [inst_2 : TopologicalSpace β]
 {mβ : Me…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
-/
lemma lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    {μ : Measure Ω} {μs : ℕ → Measure Ω} {f : Ω → ℝ} (f_cont : Continuous f) (f_nn : 0 ≤ f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫⁻ x, ENNReal.ofReal (f x) ∂(μs i)) := by
  simp_rw [lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall f_nn) f_cont.aemeasurable]
  calc ∫⁻ (t : ℝ) in Set.Ioi 0, μ {a | t < f a}
      ≤ ∫⁻ (t : ℝ) in Set.Ioi 0, atTop.liminf (fun i ↦ (μs i) {a | t < f a}) := ?_ -- (i)
    _ ≤ atTop.liminf (fun i ↦ ∫⁻ (t : ℝ) in Set.Ioi 0, (μs i) {a | t < f a}) := ?_ -- (ii)
  · -- (i)
    exact (lintegral_mono (fun t ↦ h_opens _ (continuous_def.mp f_cont _ isOpen_Ioi))).trans
            (le_refl _)
  · -- (ii)
    exact lintegral_liminf_le (fun n ↦ Antitone.measurable (fun s t hst ↦
            measure_mono (fun ω hω ↦ lt_of_le_of_lt hst hω)))
/-
**MeasureTheory.integral_le_liminf_integral_of_forall_isOpen_measure_le_liminf_m
easure** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_le_liminf_integral_of_forall_isOpen_measure_le_liminf_measure {μ 
: Measure Ω} {μs : Nat -> Measure Ω} [forall i, IsProbabilityMeasure (μs i)] {f 
: Ω ->ᵇ Real} (f_nn : 0 <= f) (h_opens : forall G, IsOpen G -> μ G <= atTop.limi
nf (fun i => μs i G)) : ∫ x, (f x) ∂μ <= atTop.liminf (fun i => ∫ x, (f x) ∂(μs 
i))
参数：μs i；f_nn : 0 <= f；h_opens : forall G, IsOpen G -> μ G <= atTop.liminf (fun i
 => μs i G)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_
liminf_measure`：lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf
_measure {μ : Measure Ω} {μs : Nat -> Measure Ω} {f : Ω -> Real} (f_cont : C…
· 使用定理 `BoundedContinuousFunction.continuous`：∀ {α : Type u} {β : Type v} [inst 
: TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (f : BoundedContinuousFun
ction α β), Continuous ⇑f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_lintegral_of_nonneg_ae`：integral_eq_lintegral_
of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfm : AEStronglyMeasurable f μ) 
: ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.lipschitzWith_toNNReal`：LipschitzWith 1 Real.toNNReal
· 使用定理 `coe_nnreal_ennreal_nndist`：coe_nnreal_ennreal_nndist (x y : α) : ↑(nndis
t x y) = edist x y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `BoundedContinuousFunction.lintegral_le_edist_mul`：lintegral_le_edist_mul
 (f : X ->ᵇ Real>=0) (μ : Measure X) : (∫⁻ x, f x ∂μ) <= edist 0 f * (μ Set.univ
)
· 使用引理 `ENNReal.liminf_toReal_eq`：liminf_toReal_eq [NeBot f] {b : Real>=0∞} (b_n
e_top : b != ∞) (le_b : forallᶠ i in f, u i <= b) : f.liminf (fun i => (u i).toR
eal) = (f.limi…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `BoundedContinuousFunction.lintegral_nnnorm_le`：lintegral_nnnorm_le (f : 
X ->ᵇ E) : ∫⁻ x, ‖f x‖₊ ∂μ <= ‖f‖₊ * (μ Set.univ)
（共 42 条，此处仅展示前 30 条）
-/
lemma integral_le_liminf_integral_of_forall_isOpen_measure_le_liminf_measure
    {μ : Measure Ω} {μs : ℕ → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]
    {f : Ω →ᵇ ℝ} (f_nn : 0 ≤ f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    ∫ x, (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫ x, (f x) ∂(μs i)) := by
  have same := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
                  f.continuous f_nn h_opens
  rw [@integral_eq_lintegral_of_nonneg_ae Ω _ μ f (Eventually.of_forall f_nn)
        f.continuous.measurable.aestronglyMeasurable]
  convert! ENNReal.toReal_mono ?_ same
  · simp only [fun i ↦ @integral_eq_lintegral_of_nonneg_ae Ω _ (μs i) f (Eventually.of_forall f_nn)
                        f.continuous.measurable.aestronglyMeasurable]
    let g := BoundedContinuousFunction.comp _ Real.lipschitzWith_toNNReal f
    have bound : ∀ i, ∫⁻ x, ENNReal.ofReal (f x) ∂(μs i) ≤ nndist 0 g := fun i ↦ by
      simpa only [coe_nnreal_ennreal_nndist, measure_univ, mul_one, ge_iff_le] using!
            BoundedContinuousFunction.lintegral_le_edist_mul (μ := μs i) g
    apply ENNReal.liminf_toReal_eq ENNReal.coe_ne_top (Eventually.of_forall bound)
  · apply ne_of_lt
    have obs := fun (i : ℕ) ↦ @BoundedContinuousFunction.lintegral_nnnorm_le Ω _ _ (μs i) ℝ _ f
    simp only [measure_univ, mul_one] at obs
    apply lt_of_le_of_lt _ (show (‖f‖₊ : ℝ≥0∞) < ∞ from ENNReal.coe_lt_top)
    apply liminf_le_of_le
    · refine ⟨0, .of_forall (by simp)⟩
    · intro x hx
      obtain ⟨i, hi⟩ := hx.exists
      apply le_trans hi
      convert! obs i with x
      have aux := ENNReal.ofReal_eq_coe_nnreal (f_nn x)
      simp only [ContinuousMap.toFun_eq_coe, BoundedContinuousFunction.coe_toContinuousMap] at aux
      rw [aux]
      congr
      exact (Real.norm_of_nonneg (f_nn x)).symm
/-
**MeasureTheory.tendsto_of_forall_isOpen_le_liminf_nat'** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：tendsto_of_forall_isOpen_le_liminf_nat' {μ : ProbabilityMeasure Ω} {μs : N
at -> ProbabilityMeasure Ω} (h_opens : forall G, IsOpen G -> (μ : Measure Ω) G <
= liminf (fun i => (μs i : Measure Ω) G) atTop) : atTop.Tendsto (fun i => μs i) 
(𝓝 μ)
参数：h_opens : forall G, IsOpen G -> (μ : Measure Ω) G <= liminf (fun i => (μs i :
 Measure Ω) G) atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`：te
ndsto_iff_forall_integral_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> Probabil
ityMeasure Ω} {μ : ProbabilityMeasure Ω} : Tendsto μs F (𝓝…
· 使用引理 `BoundedContinuousFunction.tendsto_integral_of_forall_integral_le_liminf_
integral`：tendsto_integral_of_forall_integral_le_liminf_integral {ι : Type*} {L 
: Filter ι} {μ : Measure X} [IsProbabilityMeasure μ] {μs : ι -> Measur…
· 使用定理 `MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure`：∀ {Ω
 : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.ProbabilityMeasure Ω)
,   MeasureTheory.IsProbabilityMeasure ↑μ
· 使用引理 `MeasureTheory.integral_le_liminf_integral_of_forall_isOpen_measure_le_li
minf_measure`：integral_le_liminf_integral_of_forall_isOpen_measure_le_liminf_mea
sure {μ : Measure Ω} {μs : Nat -> Measure Ω} [forall i, IsProbabilityMeasu…
-/
theorem tendsto_of_forall_isOpen_le_liminf_nat' {μ : ProbabilityMeasure Ω}
    {μs : ℕ → ProbabilityMeasure Ω}
    (h_opens : ∀ G, IsOpen G → (μ : Measure Ω) G ≤ liminf (fun i ↦ (μs i : Measure Ω) G) atTop) :
    atTop.Tendsto (fun i ↦ μs i) (𝓝 μ) := by
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr ?_
  refine tendsto_integral_of_forall_integral_le_liminf_integral fun f f_nn ↦ ?_
  exact integral_le_liminf_integral_of_forall_isOpen_measure_le_liminf_measure f_nn h_opens

/-- One implication of the portmanteau theorem: if for all open sets `G` we have the liminf
condition `μ(G) ≤ liminf μsₙ(G)`, then the measures `μsₙ` converge weakly to the measure `μ`.
Superseded by `tendsto_of_forall_isOpen_le_liminf` which works for all countably
generated filters. -/
/-
**MeasureTheory.tendsto_of_forall_isOpen_le_liminf_nat** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：tendsto_of_forall_isOpen_le_liminf_nat {μ : ProbabilityMeasure Ω} {μs : Na
t -> ProbabilityMeasure Ω} (h_opens : forall G, IsOpen G -> μ G <= atTop.liminf 
(fun i => μs i G)) : atTop.Tendsto (fun i => μs i) (𝓝 μ)
参数：h_opens : forall G, IsOpen G -> μ G <= atTop.liminf (fun i => μs i G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tendsto_of_forall_isOpen_le_liminf_nat'`：tendsto_of_forall
_isOpen_le_liminf_nat' {μ : ProbabilityMeasure Ω} {μs : Nat -> ProbabilityMeasur
e Ω} (h_opens : forall G, IsOpen G -> (μ : …
· 使用定理 `Monotone.map_liminf_of_continuousAt`：Monotone.map_liminf_of_continuousAt
 {f : R -> S} (f_incr : Monotone f) (a : ι -> R) (f_cont : ContinuousAt f (F.lim
inf a)) (cobdd : F.IsCobo…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.coe_mono`：coe_mono : Monotone ofNNReal
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ENNReal.continuous_coe`：continuous_coe : Continuous ((↑) : Real>=0 -> Re
al>=0∞)
· 使用定理 `Filter.IsBoundedUnder.isCoboundedUnder_ge`：∀ {α : Type u_1} {γ : Type u_
3} {u : γ → α} {l : Filter γ} [inst : Preorder α] [l.NeBot],   Filter.IsBoundedU
nder (fun x1 x2 => x1 ≤ x2) l u…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure`：ennre
al_coeFn_eq_coeFn_toMeasure (ν : ProbabilityMeasure Ω) (s : Set Ω) : (ν s : Real
>=0∞) = (ν : Measure Ω) s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂

--- 原说明 ---
One implication of the portmanteau theorem: if for all open sets `G` we have the
 liminf
condition `μ(G) ≤ liminf μsₙ(G)`, then the measures `μsₙ` converge weakly to the
 measure `μ`.
Superseded by `tendsto_of_forall_isOpen_le_liminf` which works for all countably
generated filters.
-/
theorem tendsto_of_forall_isOpen_le_liminf_nat {μ : ProbabilityMeasure Ω}
    {μs : ℕ → ProbabilityMeasure Ω}
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    atTop.Tendsto (fun i ↦ μs i) (𝓝 μ) := by
  refine tendsto_of_forall_isOpen_le_liminf_nat' fun G G_open ↦ ?_
  specialize h_opens G G_open
  have aux : ENNReal.ofNNReal (liminf (fun i ↦ μs i G) atTop) =
          liminf (ENNReal.ofNNReal ∘ fun i ↦ μs i G) atTop := by
    refine Monotone.map_liminf_of_continuousAt (F := atTop) ENNReal.coe_mono (μs · G) ?_ ?_ ?_
    · exact ENNReal.continuous_coe.continuousAt
    · exact IsBoundedUnder.isCoboundedUnder_ge ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  have obs := ENNReal.coe_mono h_opens
  simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, aux] at obs
  convert! obs
  simp only [Function.comp_apply, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]

/-- One implication of the portmanteau theorem: if for all open sets `G` we have the liminf
condition `μ(G) ≤ liminf μsₙ(G)`, then the measures `μsₙ` converge weakly to the measure `μ`.

This lemma uses a coercion from `ProbabilityMeasure` to `Measure` in the hypothesis.
See `tendsto_of_forall_isOpen_le_liminf` for the version without coercion. -/
/-
**MeasureTheory.tendsto_of_forall_isOpen_le_liminf'** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：tendsto_of_forall_isOpen_le_liminf' {ι : Type*} {μ : ProbabilityMeasure Ω}
 {μs : ι -> ProbabilityMeasure Ω} {L : Filter ι} [L.IsCountablyGenerated] (h_ope
ns : forall G, IsOpen G -> (μ : Measure Ω) G <= L.liminf (fun i => (μs i : Measu
re Ω) G)) : L.Tendsto (fun i => μs i) (𝓝 μ)
参数：h_opens : forall G, IsOpen G -> (μ : Measure Ω) G <= L.liminf (fun i => (μs i
 : Measure Ω) G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_of_seq_tendsto`：tendsto_of_seq_tendsto {f : α -> β} {k : 
Filter α} {l : Filter β} [k.IsCountablyGenerated] : (forall x : Nat -> α, Tendst
o x atTop k -> Tend…
· 使用定理 `MeasureTheory.tendsto_of_forall_isOpen_le_liminf_nat'`：tendsto_of_forall
_isOpen_le_liminf_nat' {μ : ProbabilityMeasure Ω} {μs : Nat -> ProbabilityMeasur
e Ω} (h_opens : forall G, IsOpen G -> (μ : …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.liminf_le_liminf_of_le`：liminf_le_liminf_of_le {α β} [Conditional
lyCompleteLattice β] {f g : Filter α} (h : g <= f) {u : α -> β} (hf : f.IsBounde
dUnder (· >= ·) u
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f

--- 原说明 ---
One implication of the portmanteau theorem: if for all open sets `G` we have the
 liminf
condition `μ(G) ≤ liminf μsₙ(G)`, then the measures `μsₙ` converge weakly to the
 measure `μ`.

This lemma uses a coercion from `ProbabilityMeasure` to `Measure` in the hypothe
sis.
See `tendsto_of_forall_isOpen_le_liminf` for the version without coercion.
-/
theorem tendsto_of_forall_isOpen_le_liminf' {ι : Type*} {μ : ProbabilityMeasure Ω}
    {μs : ι → ProbabilityMeasure Ω} {L : Filter ι} [L.IsCountablyGenerated]
    (h_opens : ∀ G, IsOpen G → (μ : Measure Ω) G ≤ L.liminf (fun i ↦ (μs i : Measure Ω) G)) :
    L.Tendsto (fun i ↦ μs i) (𝓝 μ) := by
  apply Filter.tendsto_of_seq_tendsto fun u hu ↦ ?_
  apply tendsto_of_forall_isOpen_le_liminf_nat' fun G hG ↦ ?_
  exact (h_opens G hG).trans (liminf_le_liminf_of_le hu)

/-- One implication of the portmanteau theorem: if for all open sets `G` we have the liminf
condition `μ(G) ≤ liminf μsₙ(G)`, then the measures `μsₙ` converge weakly to the measure `μ`.
Formulated here for countably generated filters. -/
/-
**MeasureTheory.tendsto_of_forall_isOpen_le_liminf** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：tendsto_of_forall_isOpen_le_liminf {ι : Type*} {μ : ProbabilityMeasure Ω} 
{μs : ι -> ProbabilityMeasure Ω} {L : Filter ι} [L.IsCountablyGenerated] (h_open
s : forall G, IsOpen G -> μ G <= L.liminf (fun i => μs i G)) : L.Tendsto (fun i 
=> μs i) (𝓝 μ)
参数：h_opens : forall G, IsOpen G -> μ G <= L.liminf (fun i => μs i G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_of_seq_tendsto`：tendsto_of_seq_tendsto {f : α -> β} {k : 
Filter α} {l : Filter β} [k.IsCountablyGenerated] : (forall x : Nat -> α, Tendst
o x atTop k -> Tend…
· 使用定理 `MeasureTheory.tendsto_of_forall_isOpen_le_liminf_nat`：tendsto_of_forall_
isOpen_le_liminf_nat {μ : ProbabilityMeasure Ω} {μs : Nat -> ProbabilityMeasure 
Ω} (h_opens : forall G, IsOpen G -> μ G <=…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.liminf_comp`：liminf_comp (u : β -> α) (v : γ -> β) (f : Filter γ)
 : liminf (u ∘ v) f = liminf u (map v f)
· 使用定理 `Filter.liminf_le_liminf_of_le`：liminf_le_liminf_of_le {α β} [Conditional
lyCompleteLattice β] {f g : Filter α} (h : g <= f) {u : α -> β} (hf : f.IsBounde
dUnder (· >= ·) u
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.IsBoundedUnder.isCoboundedUnder_ge`：∀ {α : Type u_1} {γ : Type u_
3} {u : γ → α} {l : Filter γ} [inst : Preorder α] [l.NeBot],   Filter.IsBoundedU
nder (fun x1 x2 => x1 ≤ x2) l u…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.isBoundedUnder_of`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → P
rop} {f : Filter β} {u : β → α},   (∃ b, ∀ (x : β), r (u x) b) → Filter.IsBounde
dUnder r f u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
One implication of the portmanteau theorem: if for all open sets `G` we have the
 liminf
condition `μ(G) ≤ liminf μsₙ(G)`, then the measures `μsₙ` converge weakly to the
 measure `μ`.
Formulated here for countably generated filters.
-/
theorem tendsto_of_forall_isOpen_le_liminf {ι : Type*} {μ : ProbabilityMeasure Ω}
    {μs : ι → ProbabilityMeasure Ω} {L : Filter ι} [L.IsCountablyGenerated]
    (h_opens : ∀ G, IsOpen G → μ G ≤ L.liminf (fun i ↦ μs i G)) :
    L.Tendsto (fun i ↦ μs i) (𝓝 μ) := by
  apply Filter.tendsto_of_seq_tendsto fun u hu ↦ ?_
  apply tendsto_of_forall_isOpen_le_liminf_nat fun G hG ↦ (h_opens G hG).trans ?_
  change _ ≤ atTop.liminf ((fun i ↦ μs i G) ∘ u)
  rw [liminf_comp]
  refine liminf_le_liminf_of_le hu (by isBoundedDefault) ?_
  exact isBoundedUnder_of ⟨1, by simp⟩ |>.isCoboundedUnder_ge

end le_liminf_open_implies_convergence

section Closed

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω}
    {L : Filter ι} [L.IsCountablyGenerated]

/-- One implication of the portmanteau theorem: if for all closed sets `F` we have the limsup
condition `limsup μsₙ(F) ≤ μ(F)`, then the measures `μsₙ` converge weakly to the measure `μ`.
Formulated here for countably generated filters.

This lemma uses a coercion from `ProbabilityMeasure` to `Measure` in the hypothesis.
See `tendsto_of_forall_isClosed_limsup_le` for the version without coercion. -/
/-
**MeasureTheory.tendsto_of_forall_isClosed_limsup_le'** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory`。
形式化陈述：tendsto_of_forall_isClosed_limsup_le' (h : forall F : Set Ω, IsClosed F ->
 limsup (fun i => (μs i : Measure Ω) F) L <= (μ : Measure Ω) F) : Tendsto μs L (
𝓝 μ)
参数：h : forall F : Set Ω, IsClosed F -> limsup (fun i => (μs i : Measure Ω) F) L 
<= (μ : Measure Ω) F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tendsto_of_forall_isOpen_le_liminf'`：tendsto_of_forall_isO
pen_le_liminf' {ι : Type*} {μ : ProbabilityMeasure Ω} {μs : ι -> ProbabilityMeas
ure Ω} {L : Filter ι} [L.IsCountablyGen…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.limsup_measure_closed_le_iff_liminf_measure_open_ge`：limsu
p_measure_closed_le_iff_liminf_measure_open_ge {ι : Type*} {L : Filter ι} {μ : M
easure Ω} {μs : ι -> Measure Ω} [IsProbabilityMeasure μ…
· 使用定理 `MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure`：∀ {Ω
 : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.ProbabilityMeasure Ω)
,   MeasureTheory.IsProbabilityMeasure ↑μ

--- 原说明 ---
One implication of the portmanteau theorem: if for all closed sets `F` we have t
he limsup
condition `limsup μsₙ(F) ≤ μ(F)`, then the measures `μsₙ` converge weakly to the
 measure `μ`.
Formulated here for countably generated filters.

This lemma uses a coercion from `ProbabilityMeasure` to `Measure` in the hypothe
sis.
See `tendsto_of_forall_isClosed_limsup_le` for the version without coercion.
-/
lemma tendsto_of_forall_isClosed_limsup_le'
    (h : ∀ F : Set Ω, IsClosed F → limsup (fun i ↦ (μs i : Measure Ω) F) L ≤ (μ : Measure Ω) F) :
    Tendsto μs L (𝓝 μ) := by
  refine tendsto_of_forall_isOpen_le_liminf' ?_
  rwa [← limsup_measure_closed_le_iff_liminf_measure_open_ge]
/-
**MeasureTheory.tendsto_of_forall_isClosed_limsup_le_nat** 是 Mathlib 中的一个引理，位于命名
空间 `MeasureTheory`。
形式化陈述：tendsto_of_forall_isClosed_limsup_le_nat {μs : Nat -> ProbabilityMeasure Ω
} (h : forall F : Set Ω, IsClosed F -> limsup (fun i => μs i F) atTop <= μ F) : 
Tendsto μs atTop (𝓝 μ)
参数：h : forall F : Set Ω, IsClosed F -> limsup (fun i => μs i F) atTop <= μ F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.tendsto_of_forall_isClosed_limsup_le'`：tendsto_of_forall_i
sClosed_limsup_le' (h : forall F : Set Ω, IsClosed F -> limsup (fun i => (μs i :
 Measure Ω) F) L <= (μ : Measure Ω) F) : …
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Monotone.map_limsup_of_continuousAt`：Monotone.map_limsup_of_continuousAt
 {f : R -> S} (f_incr : Monotone f) (a : ι -> R) (f_cont : ContinuousAt f (F.lim
sup a)) (bdd_above : F.Is…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.coe_mono`：coe_mono : Monotone ofNNReal
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ENNReal.continuous_coe`：continuous_coe : Continuous ((↑) : Real>=0 -> Re
al>=0∞)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure`：ennre
al_coeFn_eq_coeFn_toMeasure (ν : ProbabilityMeasure Ω) (s : Set Ω) : (ν s : Real
>=0∞) = (ν : Measure Ω) s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 31 条，此处仅展示前 30 条）
-/
lemma tendsto_of_forall_isClosed_limsup_le_nat {μs : ℕ → ProbabilityMeasure Ω}
    (h : ∀ F : Set Ω, IsClosed F → limsup (fun i ↦ μs i F) atTop ≤ μ F) :
    Tendsto μs atTop (𝓝 μ) := by
  refine tendsto_of_forall_isClosed_limsup_le' fun F hF_closed ↦ ?_
  specialize h F hF_closed
  have aux : ENNReal.ofNNReal (limsup (fun i ↦ μs i F) atTop) =
      limsup (ENNReal.ofNNReal ∘ fun i ↦ μs i F) atTop :=
    Monotone.map_limsup_of_continuousAt (F := atTop) ENNReal.coe_mono (μs · F) (by fun_prop)
      ⟨1, by simp⟩ ⟨0, by simp⟩
  have obs := ENNReal.coe_mono h
  simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, aux] at obs
  convert! obs
  simp

/-- One implication of the portmanteau theorem: if for all closed sets `F` we have the limsup
condition `limsup μsₙ(F) ≤ μ(F)`, then the measures `μsₙ` converge weakly to the measure `μ`.
Formulated here for countably generated filters. -/
/-
**MeasureTheory.tendsto_of_forall_isClosed_limsup_le** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：tendsto_of_forall_isClosed_limsup_le (h : forall F : Set Ω, IsClosed F -> 
limsup (fun i => μs i F) L <= μ F) : Tendsto μs L (𝓝 μ)
参数：h : forall F : Set Ω, IsClosed F -> limsup (fun i => μs i F) L <= μ F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_of_seq_tendsto`：tendsto_of_seq_tendsto {f : α -> β} {k : 
Filter α} {l : Filter β} [k.IsCountablyGenerated] : (forall x : Nat -> α, Tendst
o x atTop k -> Tend…
· 使用引理 `MeasureTheory.tendsto_of_forall_isClosed_limsup_le_nat`：tendsto_of_foral
l_isClosed_limsup_le_nat {μs : Nat -> ProbabilityMeasure Ω} (h : forall F : Set 
Ω, IsClosed F -> limsup (fun i => μs i F) at…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用引理 `Filter.limsup_comp`：limsup_comp (u : β -> α) (v : γ -> β) (f : Filter γ)
 : limsup (u ∘ v) f = limsup u (map v f)
· 使用定理 `Filter.limsup_le_limsup_of_le`：limsup_le_limsup_of_le {α β} [Conditional
lyCompleteLattice β] {f g : Filter α} (h : f <= g) {u : α -> β} (hf : f.IsCoboun
dedUnder (· <= ·) u
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
One implication of the portmanteau theorem: if for all closed sets `F` we have t
he limsup
condition `limsup μsₙ(F) ≤ μ(F)`, then the measures `μsₙ` converge weakly to the
 measure `μ`.
Formulated here for countably generated filters.
-/
theorem tendsto_of_forall_isClosed_limsup_le
    (h : ∀ F : Set Ω, IsClosed F → limsup (fun i ↦ μs i F) L ≤ μ F) :
    Tendsto μs L (𝓝 μ) := by
  apply Filter.tendsto_of_seq_tendsto fun u hu ↦ ?_
  apply tendsto_of_forall_isClosed_limsup_le_nat fun F hF ↦ le_trans ?_ (h F hF)
  exact (limsup_comp (fun i ↦ μs i F) u _).trans_le
    (limsup_le_limsup_of_le hu (by isBoundedDefault) ⟨1, by simp⟩)
/-
**MeasureTheory.tendsto_of_forall_isClosed_limsup_real_le'** 是 Mathlib 中的一个引理，位于
命名空间 `MeasureTheory`。
形式化陈述：tendsto_of_forall_isClosed_limsup_real_le' {L : Filter ι} [L.IsCountablyGe
nerated] (h : forall F : Set Ω, IsClosed F -> limsup (fun i => (μs i : Measure Ω
).real F) L <= (μ : Measure Ω).real F) : Tendsto μs L (𝓝 μ)
参数：h : forall F : Set Ω, IsClosed F -> limsup (fun i => (μs i : Measure Ω).real 
F) L <= (μ : Measure Ω).real F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tendsto_of_forall_isClosed_limsup_le`：tendsto_of_forall_is
Closed_limsup_le (h : forall F : Set Ω, IsClosed F -> limsup (fun i => μs i F) L
 <= μ F) : Tendsto μs L (𝓝 μ)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.ProbabilityMeasure.measureReal_eq_coe_coeFn`：∀ {Ω : Type u
_1} [inst : MeasurableSpace Ω] (ν : MeasureTheory.ProbabilityMeasure Ω) (s : Set
 Ω), (↑ν).real s = ↑(ν s)
· 使用引理 `NNReal.toReal_limsup`：toReal_limsup : limsup (fun i => (u i : Real)) f =
 limsup u f
-/
lemma tendsto_of_forall_isClosed_limsup_real_le' {L : Filter ι} [L.IsCountablyGenerated]
    (h : ∀ F : Set Ω, IsClosed F →
      limsup (fun i ↦ (μs i : Measure Ω).real F) L ≤ (μ : Measure Ω).real F) :
    Tendsto μs L (𝓝 μ) := tendsto_of_forall_isClosed_limsup_le (by simpa using h)

/-- A different version of the (C) → (T) implication of the portmanteau theorem:
If the set of measures is tight, a `limsup` inequality for compact sets implies weak convergence. -/
/-
**MeasureTheory.tendsto_of_forall_isCompact_of_isTightMeasureSet** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_of_forall_isCompact_of_isTightMeasureSet (h₁ : IsTightMeasureSet (
range (ProbabilityMeasure.toMeasure ∘ μs))) (h₂ : forall F, IsCompact F -> limsu
p (μs · F) L <= μ F) : Tendsto μs L (𝓝 μ)
参数：h₁ : IsTightMeasureSet (range (ProbabilityMeasure.toMeasure ∘ μs))；h₂ : foral
l F, IsCompact F -> limsup (μs · F) L <= μ F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.tendsto_of_forall_isClosed_limsup_le`：tendsto_of_forall_is
Closed_limsup_le (h : forall F : Set Ω, IsClosed F -> limsup (fun i => μs i F) L
 <= μ F) : Tendsto μs L (𝓝 μ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用引理 `ENNReal.ofNNReal_limsup`：ofNNReal_limsup {u : ι -> Real>=0} (hf : f.IsBo
undedUnder (· <= ·) u) : limsup u f = limsup (fun i => (u i : Real>=0∞)) f
· 使用引理 `Filter.isBoundedUnder_of_eventually_le`：isBoundedUnder_of_eventually_le 
{a : α} (h : forallᶠ x in f, u x <= a) : IsBoundedUnder (· <= ·) f u
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.le_of_forall_pos_le_add`：le_of_forall_pos_le_add (h : forall ε :
 Real>=0, 0 < ε -> b < ∞ -> a <= b + ε) : a <= b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le`：i
sTightMeasureSet_iff_exists_isCompact_measure_compl_le : IsTightMeasureSet S ↔ f
orall ε, 0 < ε -> exists K : Set 𝓧, IsCompact K ∧ forall μ …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Filter.limsup_le_limsup`：limsup_le_limsup {α : Type*} [ConditionallyComp
leteLattice β] {f : Filter α} {u v : α -> β} (h : u <=ᶠ[f] v) (hu : f.IsCobounde
dUnder (· <= …
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure`：ennre
al_coeFn_eq_coeFn_toMeasure (ν : ProbabilityMeasure Ω) (s : Set Ω) : (ν s : Real
>=0∞) = (ν : Measure Ω) s
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_union_sdiff`：inter_union_sdiff (s t : Set α) : s inter t union
 s \ t = s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
A different version of the (C) → (T) implication of the portmanteau theorem:
If the set of measures is tight, a `limsup` inequality for compact sets implies 
weak convergence.
-/
theorem tendsto_of_forall_isCompact_of_isTightMeasureSet
    (h₁ : IsTightMeasureSet (range (ProbabilityMeasure.toMeasure ∘ μs)))
    (h₂ : ∀ F, IsCompact F → limsup (μs · F) L ≤ μ F) :
    Tendsto μs L (𝓝 μ) := by
  obtain rfl | _ := L.eq_or_neBot
  · simp
  refine tendsto_of_forall_isClosed_limsup_le <| fun F hF_closed ↦ ?_
  rw [← ENNReal.coe_le_coe, ENNReal.ofNNReal_limsup <|
      isBoundedUnder_of_eventually_le (a := 1) (by simp)]
  refine ENNReal.le_of_forall_pos_le_add <| fun ε hε _ ↦ ?_
  obtain ⟨K, hKc, hK_le⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    h₁ ε (by positivity)
  grw [limsup_le_limsup (v := fun i ↦ μs i (F ∩ K) + (ε : ENNReal))]
  · rw [limsup_add_const _ _ _ (by isBoundedDefault) (by isBoundedDefault)]
    apply add_le_add _ (by simp)
    specialize h₂ (F ∩ K) <| hKc.inter_left hF_closed
    rw [← ENNReal.coe_le_coe, ENNReal.ofNNReal_limsup <|
      isBoundedUnder_of_eventually_le (a := 1) (by simp)] at h₂
    grw [h₂]
    simp [measure_mono]
  · refine .of_forall (fun i ↦ ?_)
    simp_rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    grw [measure_mono (t := (F ∩ K) ∪ F \ K) (by simp), measure_union_le]
    gcongr
    exact le_trans (measure_mono (by simp)) <| hK_le (μs i) <| by simp

end Closed

section Lipschitz

/-- Weak convergence of probability measures is equivalent to the property that the integrals of
every bounded Lipschitz function converge to the integral of the function against
the limit measure. -/
/-
**MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_iff_forall_lipschitz_integral_tendsto {γ Ω : Type*} {mΩ : Measurab
leSpace Ω} [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] {F : Filter γ} [F.IsC
ountablyGenerated] {μs : γ -> ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} :
 Tendsto μs F (𝓝 μ) ↔ forall f : Ω -> Real, (exists (C : Real), forall x y, dist
 (f x) (f y) <= C) -> (exists L, LipschitzWith L f) -> Tendsto (fun i => ∫ ω, f 
ω ∂(μs i)) F (𝓝 (∫ ω, f ω ∂μ))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.tendsto_of_forall_isClosed_limsup_real_le'`：tendsto_of_for
all_isClosed_limsup_real_le' {L : Filter ι} [L.IsCountablyGenerated] (h : forall
 F : Set Ω, IsClosed F -> limsup (fun i => (μs…
· 使用定理 `le_of_forall_pos_le_add`：∀ {α : Type u} [inst : LinearOrder α] [DenselyO
rdered α] [inst_2 : AddMonoid α] [ExistsAddOfLE α] [AddLeftReflectLT α]   {a b :
 α}, (∀ (ε : …
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用引理 `MeasureTheory.tendsto_integral_thickenedIndicator_of_isClosed`：tendsto_i
ntegral_thickenedIndicator_of_isClosed {Ω : Type*} {mΩ : MeasurableSpace Ω} [Pse
udoEMetricSpace Ω] [OpensMeasurableSpace Ω] (μ : Me…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure`：∀ {Ω
 : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.ProbabilityMeasure Ω)
,   MeasureTheory.IsProbabilityMeasure ↑μ
· 使用定理 `tendsto_one_div_add_atTop_nhds_zero_nat`：tendsto_one_div_add_atTop_nhds_
zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜] [TopologicalSpace 𝕜] [Con
tinuousSMul Rat>=0 𝕜] : Tends…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
（共 108 条，此处仅展示前 30 条）

--- 原说明 ---
Weak convergence of probability measures is equivalent to the property that the 
integrals of
every bounded Lipschitz function converge to the integral of the function agains
t
the limit measure.
-/
theorem tendsto_iff_forall_lipschitz_integral_tendsto {γ Ω : Type*} {mΩ : MeasurableSpace Ω}
    [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] {F : Filter γ} [F.IsCountablyGenerated]
    {μs : γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : Ω → ℝ, (∃ (C : ℝ), ∀ x y, dist (f x) (f y) ≤ C) → (∃ L, LipschitzWith L f) →
        Tendsto (fun i ↦ ∫ ω, f ω ∂(μs i)) F (𝓝 (∫ ω, f ω ∂μ)) := by
  constructor
  · -- A bounded Lipschitz function is in particular a bounded continuous function, and we already
    -- know that weak convergence implies convergence of their integrals
    intro h f hf_bounded hf_lip
    simp_rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at h
    let f' : BoundedContinuousFunction Ω ℝ :=
    { toFun := f
      continuous_toFun := hf_lip.choose_spec.continuous
      map_bounded' := hf_bounded }
    simpa using! h f'
  -- To prove the other direction, we prove convergence of the measure of closed sets.
  -- We approximate the indicator function of a closed set by bounded Lipschitz functions.
  rcases F.eq_or_neBot with rfl | hne
  · simp
  refine fun h ↦ tendsto_of_forall_isClosed_limsup_real_le' fun s hs ↦ ?_
  refine le_of_forall_pos_le_add fun ε ε_pos ↦ ?_
  let fs : ℕ → Ω → ℝ := fun n ω ↦ thickenedIndicator (δ := (1 : ℝ) / (n + 1)) (by positivity) s ω
  have key₁ : Tendsto (fun n ↦ ∫ ω, fs n ω ∂μ) atTop (𝓝 ((μ : Measure Ω).real s)) :=
    tendsto_integral_thickenedIndicator_of_isClosed μ hs (δs := fun n ↦ (1 : ℝ) / (n + 1))
      (fun _ ↦ by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
  have room₁ : (μ : Measure Ω).real s < (μ : Measure Ω).real s + ε / 2 := by simp [ε_pos]
  obtain ⟨M, hM⟩ := eventually_atTop.mp <| key₁.eventually_lt_const room₁
  have key₂ : Tendsto (fun i ↦ ∫ ω, fs M ω ∂(μs i)) F (𝓝 (∫ ω, fs M ω ∂μ)) :=
    h (fs M) ⟨1, fun x y ↦ ?_⟩
      ⟨_, lipschitzWith_thickenedIndicator (δ := (1 : ℝ) / (M + 1)) (by positivity) s⟩
  swap
  · simp only [Real.dist_eq, abs_le]
    have h1 x : fs M x ≤ 1 := thickenedIndicator_le_one _ _ _
    have h2 x : 0 ≤ fs M x := by simp [fs]
    grind
  have room₂ : ∫ a, fs M a ∂μ < ∫ a, fs M a ∂μ + ε / 2 := by simp [ε_pos]
  have ev_near : ∀ᶠ x in F, (μs x : Measure Ω).real s ≤ ∫ a, fs M a ∂μ + ε / 2 := by
    refine (key₂.eventually_le_const room₂).mono fun x hx ↦ le_trans ?_ hx
    rw [← integral_indicator_one hs.measurableSet]
    refine integral_mono ?_ (integrable_thickenedIndicator _ _) ?_
    · exact (integrable_indicator_iff hs.measurableSet).mpr (integrable_const _).integrableOn
    · have h : _ ≤ fs M :=
        indicator_le_thickenedIndicator (δ := (1 : ℝ) / (M + 1)) (by positivity) s
      simpa using! h
  apply (Filter.limsup_le_of_le ?_ ev_near).trans
  · apply (add_le_add (hM M rfl.le).le (le_refl (ε / 2))).trans_eq
    ring
  · exact isCoboundedUnder_le_of_le F (x := 0) (by simp)

end Lipschitz

section convergenceCriterion

open scoped Finset

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-- Given a π-system, if a sequence of measures converges along all elements of the π-system, then
it also converges along finite unions of elements of the π-system. -/
/-
**MeasureTheory._root_.IsPiSystem.tendsto_measureReal_biUnion** 是 Mathlib 中的一个引理
，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a π-system, if a sequence of measures converges along all elements of the 
π-system, then
it also converges along finite unions of elements of the π-system.
-/
lemma _root_.IsPiSystem.tendsto_measureReal_biUnion
    {S : Set (Set Ω)} (hS : IsPiSystem S) {μ : ι → Measure Ω} {ν : Measure Ω} {l : Filter ι}
    {t : Finset (Set Ω)} (ht : ∀ s ∈ t, s ∈ S)
    (hmeas : ∀ s ∈ S, MeasurableSet s)
    (h : ∀ s ∈ S, Tendsto (fun i ↦ (μ i).real s) l (𝓝 (ν.real s)))
    (hν : ∀ s ∈ S, ν s ≠ ∞ := by finiteness)
    (hμ : ∀ s ∈ S, ∀ i, μ i s ≠ ∞ := by finiteness) :
    Tendsto (fun i ↦ (μ i).real (⋃ s ∈ t, s)) l (𝓝 (ν.real (⋃ s ∈ t, s))) := by
  /- This statement is not completely obvious, as `⋃ s ∈ t, s` does not belong to the π-system `S`.
  However, thanks to the inclusion-exclusion formula one may express its measure in terms of
  measures of elements of `S`, from which the result follows. -/
  have A (i) : (μ i).real (⋃ s ∈ t, s) = ∑ u ∈ t.powerset with u.Nonempty,
      (-1 : ℝ) ^ (#u + 1) * (μ i).real (⋂ s ∈ u, s) :=
    measureReal_biUnion_eq_sum_powerset (fun s hs ↦ hmeas _ (ht _ hs))
      (fun s hs ↦ hμ _ (ht _ hs) i)
  simp_rw [A, measureReal_biUnion_eq_sum_powerset (fun s hs ↦ hmeas _ (ht _ hs))
    (fun s hs ↦ hν _ (ht _ hs))]
  refine tendsto_finsetSum _ (fun u hu ↦ ?_)
  simp only [Finset.mem_filter, Finset.mem_powerset] at hu
  apply Filter.Tendsto.const_mul
  rcases eq_empty_or_nonempty (⋂ s ∈ u, s) with h'u | h'u
  · simpa [h'u] using tendsto_const_nhds
  apply h
  exact hS.biInter_mem hu.2 (fun s hs ↦ ht _ (hu.1 hs)) h'u

/-- Given a π-system, if a sequence of probability measures converges along all elements of
the π-system, then it also converges along finite unions of elements of the π-system. -/
/-
**MeasureTheory._root_.IsPiSystem.tendsto_probabilityMeasure_biUnion** 是 Mathlib
 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a π-system, if a sequence of probability measures converges along all elem
ents of
the π-system, then it also converges along finite unions of elements of the π-sy
stem.
-/
lemma _root_.IsPiSystem.tendsto_probabilityMeasure_biUnion
    {S : Set (Set Ω)} (hS : IsPiSystem S) {μ : ι → ProbabilityMeasure Ω} {ν : ProbabilityMeasure Ω}
    {l : Filter ι} {t : Finset (Set Ω)} (ht : ∀ s ∈ t, s ∈ S) (hmeas : ∀ s ∈ S, MeasurableSet s)
    (h : ∀ s ∈ S, Tendsto (fun i ↦ μ i s) l (𝓝 (ν s))) :
    Tendsto (fun i ↦ μ i (⋃ s ∈ t, s)) l (𝓝 (ν (⋃ s ∈ t, s))) := by
  have : Tendsto (fun i ↦ (μ i : Measure Ω).real (⋃ s ∈ t, s)) l
      (𝓝 ((ν : Measure Ω).real (⋃ s ∈ t, s))) := by
    apply hS.tendsto_measureReal_biUnion ht hmeas
    simpa using h
  simpa using this

/-- Consider a set of sets `S` containing arbitrarily small neighborhoods of any point, and a
probability measure. Then any open set can be approximated arbitrarily well in measure from inside
by a finite union of elements of `S`.

This is a technical lemma for `IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem`, which is
why it is formulated for a `ProbabilityMeasure`. If needed, this could be generalized to finite
measures or to general measures.
-/
/-
**MeasureTheory.ProbabilityMeasure.exists_lt_measure_biUnion_of_isOpen** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] [inst_1 : TopologicalSpace Ω] 
[SecondCountableTopology Ω] {S : Set (Set Ω)}   (ν : MeasureTheory.ProbabilityMe
asure Ω),   (∀ (u : Set Ω), IsOpen u → ∀ x ∈ u, ∃ s ∈ S, s ∈ nhds x ∧ s ⊆ u) →  
   ∀ {G : Set Ω}, IsOpen G → ∀ {r : NNReal}, r < ν G → ∃ T, (∀ t ∈ T, t ∈ S) ∧ r
 < ν (⋃ t ∈ T, t) ∧ ⋃ t ∈ T, t ⊆ G
参数：Set Ω；ν : MeasureTheory.ProbabilityMeasure Ω；∀ (u : Set Ω), IsOpen u → ∀ x ∈ 
u, ∃ s ∈ S, s ∈ nhds x ∧ s ⊆ u；∀ t ∈ T, t ∈ S；⋃ t ∈ T, t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `TopologicalSpace.isOpen_iUnion_countable`：isOpen_iUnion_countable [Secon
dCountableTopology α] {ι} (s : ι -> Set α) (H : forall i, IsOpen (s i)) : exists
 T : Set ι, T.Countable ∧ ⋃ i …
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_image`：biUnion_image : ⋃ x in f '' s, g x = ⋃ y in s, g (f y
)
· 使用定理 `Set.iUnion₂_mono`：iUnion₂_mono {s t : forall i, κ i -> Set α} (h : foral
l i j, s i j subseteq t i j) : ⋃ (i) (j), s i j subseteq ⋃ (i) (j), t i j
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
Consider a set of sets `S` containing arbitrarily small neighborhoods of any poi
nt, and a
probability measure. Then any open set can be approximated arbitrarily well in m
easure from inside
by a finite union of elements of `S`.

This is a technical lemma for `IsPiSystem.tendsto_probabilityMeasure_of_tendsto_
of_mem`, which is
why it is formulated for a `ProbabilityMeasure`. If needed, this could be genera
lized to finite
measures or to general measures.
-/
lemma ProbabilityMeasure.exists_lt_measure_biUnion_of_isOpen
    [TopologicalSpace Ω] [SecondCountableTopology Ω]
    {S : Set (Set Ω)} (ν : ProbabilityMeasure Ω)
    (h : ∀ (u : Set Ω), IsOpen u → ∀ x ∈ u, ∃ s ∈ S, s ∈ 𝓝 x ∧ s ⊆ u)
    {G : Set Ω} (hG : IsOpen G) {r : ℝ≥0} (hr : r < ν G) :
    ∃ T : Finset (Set Ω), (∀ t ∈ T, t ∈ S) ∧ (r < ν (⋃ t ∈ T, t)) ∧ (⋃ t ∈ T, t) ⊆ G := by
  obtain ⟨T, TS, T_count, hT⟩ : ∃ T : Set (Set Ω), T ⊆ S ∧ T.Countable ∧ ⋃ t ∈ T, t = G := by
    have : ∀ (x : G), ∃ s ∈ S, s ∈ 𝓝 (x : Ω) ∧ s ⊆ G := fun x ↦ h G hG x x.2
    choose! s hsS hs_nhds hsG using this
    rcases TopologicalSpace.isOpen_iUnion_countable (fun i ↦ interior (s i))
      (fun i ↦ isOpen_interior) with ⟨T₀, T₀_count, hT₀⟩
    refine ⟨s '' T₀, by grind, T₀_count.image s, ?_⟩
    refine Subset.antisymm (by simp; grind) ?_
    have : G ⊆ ⋃ i, interior (s i) := by
      intro y hy
      simpa using ⟨y, hy, mem_interior_iff_mem_nhds.2 (hs_nhds ⟨y, hy⟩)⟩
    apply this.trans
    rw [← hT₀, biUnion_image]
    exact iUnion₂_mono fun i j ↦ interior_subset
  have : T.Nonempty := by
    contrapose! hr
    simp [← hT, hr]
  rcases T_count.exists_eq_range this with ⟨f, hf⟩
  have G_eq : G = ⋃ n, f n := by simp [← hT, hf]
  have : Tendsto (fun i ↦ ν (accumulate f i)) atTop (𝓝 (ν (⋃ i, f i))) :=
    (ENNReal.tendsto_toNNReal_iff (by simp) (by simp)).2 tendsto_measure_iUnion_accumulate
  rw [← G_eq] at this
  rcases ((tendsto_order.1 this).1 r hr).exists with ⟨n, hn⟩
  refine ⟨(Finset.range (n + 1)).image f, by grind, ?_, ?_⟩
  · convert! hn
    simp [accumulate_def]
  · simpa [G_eq] using fun i _ ↦ subset_iUnion f i

/-- Assume that, applied to all the elements of a π-system, a sequence of probability measures
converges to a limiting probability measure. Assume also that the π-system contains arbitrarily
small neighborhoods of any point. Then the sequence of probability measures converges for the
weak topology. -/
/-
**MeasureTheory._root_.IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem**
 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assume that, applied to all the elements of a π-system, a sequence of probabilit
y measures
converges to a limiting probability measure. Assume also that the π-system conta
ins arbitrarily
small neighborhoods of any point. Then the sequence of probability measures conv
erges for the
weak topology.
-/
lemma _root_.IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem
    [TopologicalSpace Ω] [SecondCountableTopology Ω] [OpensMeasurableSpace Ω]
    {S : Set (Set Ω)} (hS : IsPiSystem S) {μ : ι → ProbabilityMeasure Ω} {ν : ProbabilityMeasure Ω}
    {l : Filter ι} [l.IsCountablyGenerated]
    (hmeas : ∀ s ∈ S, MeasurableSet s)
    (h : ∀ (u : Set Ω), IsOpen u → ∀ x ∈ u, ∃ s ∈ S, s ∈ 𝓝 x ∧ s ⊆ u)
    (h' : ∀ s ∈ S, Tendsto (fun i ↦ μ i s) l (𝓝 (ν s))) :
    Tendsto μ l (𝓝 ν) := by
  /- We apply the portmanteau theorem: it suffices to show that, given an open set `G`
  and `r < ν G`, then for large `i` one has `r < μᵢ G`. For this, we approximate `G` from inside by
  a finite union `G'` of elements of `S`, still with measure `> r`, by Lemma
  `ProbabilityMeasure.exists_lt_measure_biUnion_of_isOpen`. If we have `μᵢ G' → ν G'`,
  then we deduce `r < μᵢ G'` for large `i`, and therefore `r < μᵢ G`.

  Our assumption does not give directly `μᵢ G' → ν G'`, as `G'` does not belong to the π-system `S`.
  However, the inclusion-exclusion formula makes it possible to express `μᵢ G'` and `ν G'` in terms
  of the measures of intersections of elements of `S`, for which we have the convergence. It follows
  that `μᵢ G' → ν G'` holds, concluding the proof. This second step is already formalized in the
  lemma `IsPiSystem.tendsto_probabilityMeasure_biUnion`. -/
  rcases l.eq_or_neBot with rfl | hl
  · simp
  apply tendsto_of_forall_isOpen_le_liminf
  intro G hG
  refine (le_liminf_iff (isCoboundedUnder_ge_of_le (x := 1) l (by simp)) (by isBoundedDefault)).2
    (fun r hr ↦ ?_)
  obtain ⟨T, TS, T_meas, TG⟩ :
      ∃ T : Finset (Set Ω), (∀ t ∈ T, t ∈ S) ∧ (r < ν (⋃ t ∈ T, t)) ∧ (⋃ t ∈ T, t) ⊆ G :=
    ν.exists_lt_measure_biUnion_of_isOpen h hG hr
  have : Tendsto (fun i ↦ μ i (⋃ t ∈ T, t)) l (𝓝 (ν (⋃ t ∈ T, t))) :=
    hS.tendsto_probabilityMeasure_biUnion TS hmeas h'
  filter_upwards [(tendsto_order.1 this).1 r T_meas] with i hi
  exact hi.trans_le <| ProbabilityMeasure.apply_mono _ TG

end convergenceCriterion

end MeasureTheory --namespace

