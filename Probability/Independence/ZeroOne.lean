/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Conditional

/-!
# Kolmogorov's 0-1 law

Let `s : ι → MeasurableSpace Ω` be an independent sequence of sub-σ-algebras. Then any set which
is measurable with respect to the tail σ-algebra `limsup s atTop` has probability 0 or 1.

## Main statements

* `measure_zero_or_one_of_measurableSet_limsup_atTop`: Kolmogorov's 0-1 law. Any set which is
  measurable with respect to the tail σ-algebra `limsup s atTop` of an independent sequence of
  σ-algebras `s` has probability 0 or 1.
-/

public section

open MeasureTheory MeasurableSpace

open scoped MeasureTheory ENNReal

namespace ProbabilityTheory

variable {α Ω ι : Type*} {_mα : MeasurableSpace α} {s : ι -> MeasurableSpace Ω}
  {m m0 : MeasurableSpace Ω} {κ : Kernel α Ω} {μα : Measure α} {μ : Measure Ω}

/--
theorem `Kernel.measure_eq_zero_or_one_or_top_of_indepSet_self` / 定理 `Kernel.measure_eq_zero_or_one_or_top_of_indepSet_self`

English:
theorem Kernel.measure_eq_zero_or_one_or_top_of_indepSet_self
  statement: {t : Set Ω}
  proof: by
  specialize h_indep t t (measurableSet_generateFrom (Set.mem_singleton t))
    (measurableSet_generateFrom (Set.mem_singleton t))
  filter_upwards [h_indep] with a ha
  by_cases h0 : κ a t = 0
  · exact Or.inl h0
  by_cases h_top : κ a t = ∞
  · exact Or.inr (Or.inr h_top)
  rw [← one_mul (κ a (

中文:
定理 Kernel.measure_eq_zero_or_one_or_top_of_indepSet_self
  结论: {t : Set Ω}
  证明: by
  specialize h_indep t t (measurableSet_generateFrom (Set.mem_singleton t))
    (measurableSet_generateFrom (Set.mem_singleton t))
  filter_upwards [h_indep] with a ha
  by_cases h0 : κ a t = 0
  · exact Or.inl h0
  by_cases h_top : κ a t = ∞
  · exact Or.inr (Or.inr h_top)
  rw [← one_mul (κ a (

Depends on / 依赖: ENNReal, ENNReal.mul_left_inj, Or.inl, Or.inr, Set.inter_self, Set.mem_singleton, filter_upwards, h_indep, h_top, ha.symm, inter_self, measurableSet_generateFrom, mem_singleton, mul_left_inj, one_mul, specialize
-/
theorem Kernel.measure_eq_zero_or_one_or_top_of_indepSet_self {t : Set Ω}
    (h_indep : Kernel.IndepSet t t κ μα) :
    forallᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 ∨ κ a t = ∞ := by
  specialize h_indep t t (measurableSet_generateFrom (Set.mem_singleton t))
    (measurableSet_generateFrom (Set.mem_singleton t))
  filter_upwards [h_indep] with a ha
  by_cases h0 : κ a t = 0
  · exact Or.inl h0
  by_cases h_top : κ a t = ∞
  · exact Or.inr (Or.inr h_top)
  rw [← one_mul (κ a (t inter t))]; rw [Set.inter_self]; rw [ENNReal.mul_left_inj h0 h_top] at ha
  exact Or.inr (Or.inl ha.symm)

/--
theorem `measure_eq_zero_or_one_or_top_of_indepSet_self` / 定理 `measure_eq_zero_or_one_or_top_of_indepSet_self`

English:
theorem measure_eq_zero_or_one_or_top_of_indepSet_self
  statement: {t : Set Ω}
  proof: by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using! Kernel.measure_eq_zero_or_one_or_top_of_indepSet_self h_indep

中文:
定理 measure_eq_zero_or_one_or_top_of_indepSet_self
  结论: {t : Set Ω}
  证明: by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using! Kernel.measure_eq_zero_or_one_or_top_of_indepSet_self h_indep

Depends on / 依赖: Filter, Filter.eventually_pure, Kernel, Kernel.measure_eq_zero_or_one_or_top_of_indepSet_self, ae_dirac_eq, eventually_pure, h_indep, measure_eq_zero_or_one_or_top_of_indepSet_self
-/
theorem measure_eq_zero_or_one_or_top_of_indepSet_self {t : Set Ω}
    (h_indep : IndepSet t t μ) : μ t = 0 ∨ μ t = 1 ∨ μ t = ∞ := by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using! Kernel.measure_eq_zero_or_one_or_top_of_indepSet_self h_indep

/--
theorem `Kernel.measure_eq_zero_or_one_of_indepSet_self'` / 定理 `Kernel.measure_eq_zero_or_one_of_indepSet_self'`

English:
theorem Kernel.measure_eq_zero_or_one_of_indepSet_self'
  statement: (h : forallᵐ a ∂μα, IsFiniteMeasure (κ a))
  proof: by
  filter_upwards [measure_eq_zero_or_one_or_top_of_indepSet_self h_indep, h] with a h_0_1_top h'
  simpa only [measure_ne_top (κ a), or_false] using h_0_1_top

中文:
定理 Kernel.measure_eq_zero_or_one_of_indepSet_self'
  结论: (h : 对任意ᵐ a ∂μα, IsFiniteMeasure (κ a))
  证明: by
  filter_upwards [measure_eq_zero_or_one_or_top_of_indepSet_self h_indep, h] with a h_0_1_top h'
  simpa only [measure_ne_top (κ a), or_false] using h_0_1_top

Depends on / 依赖: filter_upwards, h_0_1_top, h_indep, measure_eq_zero_or_one_or_top_of_indepSet_self, measure_ne_top, or_false
-/
theorem Kernel.measure_eq_zero_or_one_of_indepSet_self' (h : forallᵐ a ∂μα, IsFiniteMeasure (κ a))
    {t : Set Ω} (h_indep : IndepSet t t κ μα) :
    forallᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 := by
  filter_upwards [measure_eq_zero_or_one_or_top_of_indepSet_self h_indep, h] with a h_0_1_top h'
  simpa only [measure_ne_top (κ a), or_false] using h_0_1_top

/--
theorem `Kernel.measure_eq_zero_or_one_of_indepSet_self` / 定理 `Kernel.measure_eq_zero_or_one_of_indepSet_self`

English:
theorem Kernel.measure_eq_zero_or_one_of_indepSet_self
  statement: [h : forall a, IsFiniteMeasure (κ a)] {t : Set Ω}
  proof: Kernel.measure_eq_zero_or_one_of_indepSet_self' (ae_of_all μα h) h_indep

中文:
定理 Kernel.measure_eq_zero_or_one_of_indepSet_self
  结论: [h : 对任意 a, IsFiniteMeasure (κ a)] {t : Set Ω}
  证明: Kernel.measure_eq_zero_or_one_of_indepSet_self' (ae_of_all μα h) h_indep

Depends on / 依赖: Kernel, Kernel.measure_eq_zero_or_one_of_indepSet_self, ae_of_all, h_indep, measure_eq_zero_or_one_of_indepSet_self
-/
theorem Kernel.measure_eq_zero_or_one_of_indepSet_self [h : forall a, IsFiniteMeasure (κ a)] {t : Set Ω}
    (h_indep : IndepSet t t κ μα) :
    forallᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 :=
  Kernel.measure_eq_zero_or_one_of_indepSet_self' (ae_of_all μα h) h_indep

/--
lemma `Kernel.measure_eq_zero_or_one_of_indep_self` / 引理 `Kernel.measure_eq_zero_or_one_of_indep_self`

English:
lemma Kernel.measure_eq_zero_or_one_of_indep_self
  statement: [h : forall a, IsFiniteMeasure (κ a)]
  proof: measure_eq_zero_or_one_of_indepSet_self
    (indep_of_indep_of_le hm (generateFrom_singleton_le ht) (generateFrom_singleton_le ht))

中文:
引理 Kernel.measure_eq_zero_or_one_of_indep_self
  结论: [h : 对任意 a, IsFiniteMeasure (κ a)]
  证明: measure_eq_zero_or_one_of_indepSet_self
    (indep_of_indep_of_le hm (generateFrom_singleton_le ht) (generateFrom_singleton_le ht))

Depends on / 依赖: generateFrom_singleton_le, indep_of_indep_of_le, measure_eq_zero_or_one_of_indepSet_self
-/
lemma Kernel.measure_eq_zero_or_one_of_indep_self [h : forall a, IsFiniteMeasure (κ a)]
    (hm : Indep m m κ μα) {t : Set Ω} (ht : MeasurableSet[m] t) :
    forallᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 :=
  measure_eq_zero_or_one_of_indepSet_self
    (indep_of_indep_of_le hm (generateFrom_singleton_le ht) (generateFrom_singleton_le ht))

/--
theorem `measure_eq_zero_or_one_of_indepSet_self` / 定理 `measure_eq_zero_or_one_of_indepSet_self`

English:
theorem measure_eq_zero_or_one_of_indepSet_self
  statement: [IsFiniteMeasure μ] {t : Set Ω}
  proof: by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using! Kernel.measure_eq_zero_or_one_of_indepSet_self h_indep

中文:
定理 measure_eq_zero_or_one_of_indepSet_self
  结论: [IsFiniteMeasure μ] {t : Set Ω}
  证明: by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using! Kernel.measure_eq_zero_or_one_of_indepSet_self h_indep

Depends on / 依赖: Filter, Filter.eventually_pure, Kernel, Kernel.measure_eq_zero_or_one_of_indepSet_self, ae_dirac_eq, eventually_pure, h_indep, measure_eq_zero_or_one_of_indepSet_self
-/
theorem measure_eq_zero_or_one_of_indepSet_self [IsFiniteMeasure μ] {t : Set Ω}
    (h_indep : IndepSet t t μ) : μ t = 0 ∨ μ t = 1 := by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using! Kernel.measure_eq_zero_or_one_of_indepSet_self h_indep

/--
lemma `measure_eq_zero_or_one_of_indep_self` / 引理 `measure_eq_zero_or_one_of_indep_self`

English:
lemma measure_eq_zero_or_one_of_indep_self
  statement: [IsFiniteMeasure μ] (hm : Indep m m μ)
  proof: by
  simpa using Kernel.measure_eq_zero_or_one_of_indep_self hm ht

中文:
引理 measure_eq_zero_or_one_of_indep_self
  结论: [IsFiniteMeasure μ] (hm : Indep m m μ)
  证明: by
  simpa using Kernel.measure_eq_zero_or_one_of_indep_self hm ht

Depends on / 依赖: Kernel, Kernel.measure_eq_zero_or_one_of_indep_self, measure_eq_zero_or_one_of_indep_self
-/
lemma measure_eq_zero_or_one_of_indep_self [IsFiniteMeasure μ] (hm : Indep m m μ)
    {t : Set Ω} (ht : MeasurableSet[m] t) :
    μ t = 0 ∨ μ t = 1 := by
  simpa using Kernel.measure_eq_zero_or_one_of_indep_self hm ht

/--
theorem `condExp_eq_zero_or_one_of_condIndepSet_self` / 定理 `condExp_eq_zero_or_one_of_condIndepSet_self`

English:
theorem condExp_eq_zero_or_one_of_condIndepSet_self
  proof: by
  -- TODO: Why is not inferred?
  have (a : _) : IsFiniteMeasure (condExpKernel μ m a) := inferInstance
  have h := ae_of_ae_trim hm (Kernel.measure_eq_zero_or_one_of_indepSet_self h_indep)
  filter_upwards [condExpKernel_ae_eq_condExp hm ht, h] with ω hω_eq hω
  rwa [← hω_eq, measureReal_eq_zero

中文:
定理 condExp_eq_zero_or_one_of_condIndepSet_self
  证明: by
  -- TODO: Why is not inferred?
  have (a : _) : IsFiniteMeasure (condExpKernel μ m a) := inferInstance
  have h := ae_of_ae_trim hm (Kernel.measure_eq_zero_or_one_of_indepSet_self h_indep)
  filter_upwards [condExpKernel_ae_eq_condExp hm ht, h] with ω hω_eq hω
  rwa [← hω_eq, measureReal_eq_zero
-/
theorem condExp_eq_zero_or_one_of_condIndepSet_self
    [StandardBorelSpace Ω]
    (hm : m <= m0) [hμ : IsFiniteMeasure μ] {t : Set Ω} (ht : MeasurableSet t)
    (h_indep : CondIndepSet m hm t t μ) :
    forallᵐ ω ∂μ, (μ⟦t | m⟧) ω = 0 ∨ (μ⟦t | m⟧) ω = 1 := by
  -- TODO: Why is not inferred?
  have (a : _) : IsFiniteMeasure (condExpKernel μ m a) := inferInstance
  have h := ae_of_ae_trim hm (Kernel.measure_eq_zero_or_one_of_indepSet_self h_indep)
  filter_upwards [condExpKernel_ae_eq_condExp hm ht, h] with ω hω_eq hω
  rwa [← hω_eq, measureReal_eq_zero_iff, measureReal_def, ENNReal.toReal_eq_one_iff]

open Filter

/--
theorem `Kernel.indep_biSup_compl` / 定理 `Kernel.indep_biSup_compl`

English:
theorem Kernel.indep_biSup_compl
  given: (h_le : forall n, s n <= m0) (h_indep : iIndep s κ μα) (t : Set ι)
  proof: indep_iSup_of_disjoint h_le h_indep disjoint_compl_right

中文:
定理 Kernel.indep_biSup_compl
  条件: (h_le : 对任意 n, s n <= m0) (h_indep : iIndep s κ μα) (t : Set ι)
  证明: indep_iSup_of_disjoint h_le h_indep disjoint_compl_right

Depends on / 依赖: disjoint_compl_right, h_indep, h_le, indep_iSup_of_disjoint
-/
theorem Kernel.indep_biSup_compl (h_le : forall n, s n <= m0) (h_indep : iIndep s κ μα) (t : Set ι) :
    Indep (⨆ n in t, s n) (⨆ n in tᶜ, s n) κ μα :=
  indep_iSup_of_disjoint h_le h_indep disjoint_compl_right

/--
theorem `indep_biSup_compl` / 定理 `indep_biSup_compl`

English:
theorem indep_biSup_compl
  given: (h_le : forall n, s n <= m0) (h_indep : iIndep s μ) (t : Set ι)
  proof: Kernel.indep_biSup_compl h_le h_indep t

中文:
定理 indep_biSup_compl
  条件: (h_le : 对任意 n, s n <= m0) (h_indep : iIndep s μ) (t : Set ι)
  证明: Kernel.indep_biSup_compl h_le h_indep t

Depends on / 依赖: Kernel, Kernel.indep_biSup_compl, h_indep, h_le, indep_biSup_compl
-/
theorem indep_biSup_compl (h_le : forall n, s n <= m0) (h_indep : iIndep s μ) (t : Set ι) :
    Indep (⨆ n in t, s n) (⨆ n in tᶜ, s n) μ :=
  Kernel.indep_biSup_compl h_le h_indep t

/--
theorem `condIndep_biSup_compl` / 定理 `condIndep_biSup_compl`

English:
theorem condIndep_biSup_compl
  statement: [StandardBorelSpace Ω]
  proof: Kernel.indep_biSup_compl h_le h_indep t

中文:
定理 condIndep_biSup_compl
  结论: [StandardBorelSpace Ω]
  证明: Kernel.indep_biSup_compl h_le h_indep t

Depends on / 依赖: Kernel, Kernel.indep_biSup_compl, h_indep, h_le, indep_biSup_compl
-/
theorem condIndep_biSup_compl [StandardBorelSpace Ω]
    (hm : m <= m0) [IsFiniteMeasure μ]
    (h_le : forall n, s n <= m0) (h_indep : iCondIndep m hm s μ) (t : Set ι) :
    CondIndep m (⨆ n in t, s n) (⨆ n in tᶜ, s n) hm μ :=
  Kernel.indep_biSup_compl h_le h_indep t

section Abstract

variable {β : Type*} {p : Set ι -> Prop} {f : Filter ι} {ns : β -> Set ι}


/--
theorem `Kernel.indep_biSup_limsup` / 定理 `Kernel.indep_biSup_limsup`

English:
theorem Kernel.indep_biSup_limsup
  statement: (h_le : forall n, s n <= m0) (h_indep : iIndep s κ μα)
  proof: by
  refine indep_of_indep_of_le_right (indep_biSup_compl h_le h_indep t) ?_
  refine limsSup_le_of_le (by isBoundedDefault) ?_
  simp only [Set.mem_compl_iff, eventually_map]
  exact eventually_of_mem (hf t ht) le_iSup₂

中文:
定理 Kernel.indep_biSup_limsup
  结论: (h_le : 对任意 n, s n <= m0) (h_indep : iIndep s κ μα)
  证明: by
  refine indep_of_indep_of_le_right (indep_biSup_compl h_le h_indep t) ?_
  refine limsSup_le_of_le (by isBoundedDefault) ?_
  simp only [Set.mem_compl_iff, eventually_map]
  exact eventually_of_mem (hf t ht) le_iSup₂

Depends on / 依赖: Set.mem_compl_iff, eventually_map, eventually_of_mem, h_indep, h_le, indep_biSup_compl, indep_of_indep_of_le_right, isBoundedDefault, limsSup_le_of_le, mem_compl_iff
-/
theorem Kernel.indep_biSup_limsup (h_le : forall n, s n <= m0) (h_indep : iIndep s κ μα)
    (hf : forall t, p t -> tᶜ in f) {t : Set ι} (ht : p t) :
    Indep (⨆ n in t, s n) (limsup s f) κ μα := by
  refine indep_of_indep_of_le_right (indep_biSup_compl h_le h_indep t) ?_
  refine limsSup_le_of_le (by isBoundedDefault) ?_
  simp only [Set.mem_compl_iff, eventually_map]
  exact eventually_of_mem (hf t ht) le_iSup₂

/--
theorem `indep_biSup_limsup` / 定理 `indep_biSup_limsup`

English:
theorem indep_biSup_limsup
  proof: Kernel.indep_biSup_limsup h_le h_indep hf ht

中文:
定理 indep_biSup_limsup
  证明: Kernel.indep_biSup_limsup h_le h_indep hf ht

Depends on / 依赖: Kernel, Kernel.indep_biSup_limsup, h_indep, h_le, indep_biSup_limsup
-/
theorem indep_biSup_limsup
    (h_le : forall n, s n <= m0) (h_indep : iIndep s μ) (hf : forall t, p t -> tᶜ in f)
    {t : Set ι} (ht : p t) :
    Indep (⨆ n in t, s n) (limsup s f) μ :=
  Kernel.indep_biSup_limsup h_le h_indep hf ht

/--
theorem `condIndep_biSup_limsup` / 定理 `condIndep_biSup_limsup`

English:
theorem condIndep_biSup_limsup
  statement: [StandardBorelSpace Ω]
  proof: Kernel.indep_biSup_limsup h_le h_indep hf ht

中文:
定理 condIndep_biSup_limsup
  结论: [StandardBorelSpace Ω]
  证明: Kernel.indep_biSup_limsup h_le h_indep hf ht

Depends on / 依赖: Kernel, Kernel.indep_biSup_limsup, h_indep, h_le, indep_biSup_limsup
-/
theorem condIndep_biSup_limsup [StandardBorelSpace Ω]
    (hm : m <= m0) [IsFiniteMeasure μ]
    (h_le : forall n, s n <= m0) (h_indep : iCondIndep m hm s μ) (hf : forall t, p t -> tᶜ in f)
    {t : Set ι} (ht : p t) :
    CondIndep m (⨆ n in t, s n) (limsup s f) hm μ :=
  Kernel.indep_biSup_limsup h_le h_indep hf ht

/--
theorem `Kernel.indep_iSup_directed_limsup` / 定理 `Kernel.indep_iSup_directed_limsup`

English:
theorem Kernel.indep_iSup_directed_limsup
  statement: (h_le : forall n, s n <= m0) (h_indep : iIndep s κ μα)
  proof: by
  rcases eq_or_ne μα 0 with rfl | hμ
  · simp
  obtain ⟨η, η_eq, hη⟩ : exists (η : Kernel α Ω), κ =ᵐ[μα] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel h_indep.ae_isProbabilityMeasure hμ
  replace h_indep := h_indep.congr η_eq
  apply Indep.congr (Filter.EventuallyEq.symm η_eq)
  apply i

中文:
定理 Kernel.indep_iSup_directed_limsup
  结论: (h_le : 对任意 n, s n <= m0) (h_indep : iIndep s κ μα)
  证明: by
  rcases eq_or_ne μα 0 with rfl | hμ
  · simp
  obtain ⟨η, η_eq, hη⟩ : exists (η : Kernel α Ω), κ =ᵐ[μα] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel h_indep.ae_isProbabilityMeasure hμ
  replace h_indep := h_indep.congr η_eq
  apply Indep.congr (Filter.EventuallyEq.symm η_eq)
  apply i

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.symm, Indep.congr, IsMarkovKernel, Kernel, ae_isProbabilityMeasure, eq_or_ne, exists_ae_eq_isMarkovKernel, h_indep, h_indep.ae_isProbabilityMeasure, h_indep.congr, h_le, iSup_le, indep_biSup_limsup, indep_iSup_of_directed_le, limsup_le_iSup, limsup_le_iSup.trans, replace
-/
theorem Kernel.indep_iSup_directed_limsup (h_le : forall n, s n <= m0) (h_indep : iIndep s κ μα)
    (hf : forall t, p t -> tᶜ in f) (hns : Directed (· <= ·) ns) (hnsp : forall a, p (ns a)) :
    Indep (⨆ a, ⨆ n in ns a, s n) (limsup s f) κ μα := by
  rcases eq_or_ne μα 0 with rfl | hμ
  · simp
  obtain ⟨η, η_eq, hη⟩ : exists (η : Kernel α Ω), κ =ᵐ[μα] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel h_indep.ae_isProbabilityMeasure hμ
  replace h_indep := h_indep.congr η_eq
  apply Indep.congr (Filter.EventuallyEq.symm η_eq)
  apply indep_iSup_of_directed_le
  · exact fun a => indep_biSup_limsup h_le h_indep hf (hnsp a)
  · exact fun a => iSup₂_le fun n _ => h_le n
  · exact limsup_le_iSup.trans (iSup_le h_le)
  · intro a b
    obtain ⟨c, hc⟩ := hns a b
    refine ⟨c, ?_, ?_⟩ <;> refine iSup_mono fun n => iSup_mono' fun hn => ⟨?_, le_rfl⟩
    · exact hc.1 hn
    · exact hc.2 hn

/--
theorem `indep_iSup_directed_limsup` / 定理 `indep_iSup_directed_limsup`

English:
theorem indep_iSup_directed_limsup
  proof: Kernel.indep_iSup_directed_limsup h_le h_indep hf hns hnsp

中文:
定理 indep_iSup_directed_limsup
  证明: Kernel.indep_iSup_directed_limsup h_le h_indep hf hns hnsp

Depends on / 依赖: Kernel, Kernel.indep_iSup_directed_limsup, h_indep, h_le, indep_iSup_directed_limsup
-/
theorem indep_iSup_directed_limsup
    (h_le : forall n, s n <= m0) (h_indep : iIndep s μ)
    (hf : forall t, p t -> tᶜ in f) (hns : Directed (· <= ·) ns) (hnsp : forall a, p (ns a)) :
    Indep (⨆ a, ⨆ n in ns a, s n) (limsup s f) μ :=
  Kernel.indep_iSup_directed_limsup h_le h_indep hf hns hnsp

/--
theorem `condIndep_iSup_directed_limsup` / 定理 `condIndep_iSup_directed_limsup`

English:
theorem condIndep_iSup_directed_limsup
  statement: [StandardBorelSpace Ω]
  proof: Kernel.indep_iSup_directed_limsup h_le h_indep hf hns hnsp

中文:
定理 condIndep_iSup_directed_limsup
  结论: [StandardBorelSpace Ω]
  证明: Kernel.indep_iSup_directed_limsup h_le h_indep hf hns hnsp

Depends on / 依赖: Kernel, Kernel.indep_iSup_directed_limsup, h_indep, h_le, indep_iSup_directed_limsup
-/
theorem condIndep_iSup_directed_limsup [StandardBorelSpace Ω]
    (hm : m <= m0) [IsFiniteMeasure μ]
    (h_le : forall n, s n <= m0) (h_indep : iCondIndep m hm s μ)
    (hf : forall t, p t -> tᶜ in f) (hns : Directed (· <= ·) ns) (hnsp : forall a, p (ns a)) :
    CondIndep m (⨆ a, ⨆ n in ns a, s n) (limsup s f) hm μ :=
  Kernel.indep_iSup_directed_limsup h_le h_indep hf hns hnsp

/--
theorem `Kernel.indep_iSup_limsup` / 定理 `Kernel.indep_iSup_limsup`

English:
theorem Kernel.indep_iSup_limsup
  statement: (h_le : forall n, s n <= m0) (h_indep : iIndep s κ μα)
  proof: by
  suffices (⨆ a, ⨆ n in ns a, s n) = ⨆ n, s n by
    rw [← this]
    exact indep_iSup_directed_limsup h_le h_indep hf hns hnsp
  rw [iSup_comm]
  refine iSup_congr fun n => ?_
  have h : ⨆ (i : β) (_ : n in ns i), s n = ⨆ _ : exists i, n in ns i, s n := by rw [iSup_exists]
  have : Nonempty (exis

中文:
定理 Kernel.indep_iSup_limsup
  结论: (h_le : 对任意 n, s n <= m0) (h_indep : iIndep s κ μα)
  证明: by
  suffices (⨆ a, ⨆ n in ns a, s n) = ⨆ n, s n by
    rw [← this]
    exact indep_iSup_directed_limsup h_le h_indep hf hns hnsp
  rw [iSup_comm]
  refine iSup_congr fun n => ?_
  have h : ⨆ (i : β) (_ : n in ns i), s n = ⨆ _ : exists i, n in ns i, s n := by rw [iSup_exists]
  have : Nonempty (exis

Depends on / 依赖: Nonempty, h_indep, h_le, hns_univ, iSup_comm, iSup_congr, iSup_const, iSup_exists, indep_iSup_directed_limsup
-/
theorem Kernel.indep_iSup_limsup (h_le : forall n, s n <= m0) (h_indep : iIndep s κ μα)
    (hf : forall t, p t -> tᶜ in f)
    (hns : Directed (· <= ·) ns) (hnsp : forall a, p (ns a)) (hns_univ : forall n, exists a, n in ns a) :
    Indep (⨆ n, s n) (limsup s f) κ μα := by
  suffices (⨆ a, ⨆ n in ns a, s n) = ⨆ n, s n by
    rw [← this]
    exact indep_iSup_directed_limsup h_le h_indep hf hns hnsp
  rw [iSup_comm]
  refine iSup_congr fun n => ?_
  have h : ⨆ (i : β) (_ : n in ns i), s n = ⨆ _ : exists i, n in ns i, s n := by rw [iSup_exists]
  have : Nonempty (exists i : β, n in ns i) := ⟨hns_univ n⟩
  rw [h]; rw [iSup_const]

/--
theorem `indep_iSup_limsup` / 定理 `indep_iSup_limsup`

English:
theorem indep_iSup_limsup
  proof: Kernel.indep_iSup_limsup h_le h_indep hf hns hnsp hns_univ

中文:
定理 indep_iSup_limsup
  证明: Kernel.indep_iSup_limsup h_le h_indep hf hns hnsp hns_univ

Depends on / 依赖: Kernel, Kernel.indep_iSup_limsup, h_indep, h_le, hns_univ, indep_iSup_limsup
-/
theorem indep_iSup_limsup
    (h_le : forall n, s n <= m0) (h_indep : iIndep s μ) (hf : forall t, p t -> tᶜ in f)
    (hns : Directed (· <= ·) ns) (hnsp : forall a, p (ns a)) (hns_univ : forall n, exists a, n in ns a) :
    Indep (⨆ n, s n) (limsup s f) μ :=
  Kernel.indep_iSup_limsup h_le h_indep hf hns hnsp hns_univ

/--
theorem `condIndep_iSup_limsup` / 定理 `condIndep_iSup_limsup`

English:
theorem condIndep_iSup_limsup
  statement: [StandardBorelSpace Ω]
  proof: Kernel.indep_iSup_limsup h_le h_indep hf hns hnsp hns_univ

中文:
定理 condIndep_iSup_limsup
  结论: [StandardBorelSpace Ω]
  证明: Kernel.indep_iSup_limsup h_le h_indep hf hns hnsp hns_univ

Depends on / 依赖: Kernel, Kernel.indep_iSup_limsup, h_indep, h_le, hns_univ, indep_iSup_limsup
-/
theorem condIndep_iSup_limsup [StandardBorelSpace Ω]
    (hm : m <= m0) [IsFiniteMeasure μ]
    (h_le : forall n, s n <= m0) (h_indep : iCondIndep m hm s μ) (hf : forall t, p t -> tᶜ in f)
    (hns : Directed (· <= ·) ns) (hnsp : forall a, p (ns a)) (hns_univ : forall n, exists a, n in ns a) :
    CondIndep m (⨆ n, s n) (limsup s f) hm μ :=
  Kernel.indep_iSup_limsup h_le h_indep hf hns hnsp hns_univ

/--
theorem `Kernel.indep_limsup_self` / 定理 `Kernel.indep_limsup_self`

English:
theorem Kernel.indep_limsup_self
  statement: (h_le : forall n, s n <= m0) (h_indep : iIndep s κ μα)
  proof: indep_of_indep_of_le_left (indep_iSup_limsup h_le h_indep hf hns hnsp hns_univ) limsup_le_iSup

中文:
定理 Kernel.indep_limsup_self
  结论: (h_le : 对任意 n, s n <= m0) (h_indep : iIndep s κ μα)
  证明: indep_of_indep_of_le_left (indep_iSup_limsup h_le h_indep hf hns hnsp hns_univ) limsup_le_iSup

Depends on / 依赖: h_indep, h_le, hns_univ, indep_iSup_limsup, indep_of_indep_of_le_left, limsup_le_iSup
-/
theorem Kernel.indep_limsup_self (h_le : forall n, s n <= m0) (h_indep : iIndep s κ μα)
    (hf : forall t, p t -> tᶜ in f)
    (hns : Directed (· <= ·) ns) (hnsp : forall a, p (ns a)) (hns_univ : forall n, exists a, n in ns a) :
    Indep (limsup s f) (limsup s f) κ μα :=
  indep_of_indep_of_le_left (indep_iSup_limsup h_le h_indep hf hns hnsp hns_univ) limsup_le_iSup

/--
theorem `indep_limsup_self` / 定理 `indep_limsup_self`

English:
theorem indep_limsup_self
  proof: Kernel.indep_limsup_self h_le h_indep hf hns hnsp hns_univ

中文:
定理 indep_limsup_self
  证明: Kernel.indep_limsup_self h_le h_indep hf hns hnsp hns_univ

Depends on / 依赖: Kernel, Kernel.indep_limsup_self, h_indep, h_le, hns_univ, indep_limsup_self
-/
theorem indep_limsup_self
    (h_le : forall n, s n <= m0) (h_indep : iIndep s μ) (hf : forall t, p t -> tᶜ in f)
    (hns : Directed (· <= ·) ns) (hnsp : forall a, p (ns a)) (hns_univ : forall n, exists a, n in ns a) :
    Indep (limsup s f) (limsup s f) μ :=
  Kernel.indep_limsup_self h_le h_indep hf hns hnsp hns_univ

/--
theorem `condIndep_limsup_self` / 定理 `condIndep_limsup_self`

English:
theorem condIndep_limsup_self
  statement: [StandardBorelSpace Ω]
  proof: Kernel.indep_limsup_self h_le h_indep hf hns hnsp hns_univ

中文:
定理 condIndep_limsup_self
  结论: [StandardBorelSpace Ω]
  证明: Kernel.indep_limsup_self h_le h_indep hf hns hnsp hns_univ

Depends on / 依赖: Kernel, Kernel.indep_limsup_self, h_indep, h_le, hns_univ, indep_limsup_self
-/
theorem condIndep_limsup_self [StandardBorelSpace Ω]
    (hm : m <= m0) [IsFiniteMeasure μ]
    (h_le : forall n, s n <= m0) (h_indep : iCondIndep m hm s μ) (hf : forall t, p t -> tᶜ in f)
    (hns : Directed (· <= ·) ns) (hnsp : forall a, p (ns a)) (hns_univ : forall n, exists a, n in ns a) :
    CondIndep m (limsup s f) (limsup s f) hm μ :=
  Kernel.indep_limsup_self h_le h_indep hf hns hnsp hns_univ

/--
theorem `Kernel.measure_zero_or_one_of_measurableSet_limsup` / 定理 `Kernel.measure_zero_or_one_of_measurableSet_limsup`

English:
theorem Kernel.measure_zero_or_one_of_measurableSet_limsup
  statement: (h_le : forall n, s n <= m0)
  proof: by
  apply measure_eq_zero_or_one_of_indepSet_self' ?_
    ((indep_limsup_self h_le h_indep hf hns hnsp hns_univ).indepSet_of_measurableSet ht_tail
      ht_tail)
  filter_upwards [h_indep.ae_isProbabilityMeasure] with a ha using by infer_instance

中文:
定理 Kernel.measure_zero_or_one_of_measurableSet_limsup
  结论: (h_le : 对任意 n, s n <= m0)
  证明: by
  apply measure_eq_zero_or_one_of_indepSet_self' ?_
    ((indep_limsup_self h_le h_indep hf hns hnsp hns_univ).indepSet_of_measurableSet ht_tail
      ht_tail)
  filter_upwards [h_indep.ae_isProbabilityMeasure] with a ha using by infer_instance

Depends on / 依赖: ae_isProbabilityMeasure, filter_upwards, h_indep, h_indep.ae_isProbabilityMeasure, h_le, hns_univ, ht_tail, indepSet_of_measurableSet, indep_limsup_self, infer_instance, measure_eq_zero_or_one_of_indepSet_self
-/
theorem Kernel.measure_zero_or_one_of_measurableSet_limsup (h_le : forall n, s n <= m0)
    (h_indep : iIndep s κ μα)
    (hf : forall t, p t -> tᶜ in f) (hns : Directed (· <= ·) ns) (hnsp : forall a, p (ns a))
    (hns_univ : forall n, exists a, n in ns a) {t : Set Ω} (ht_tail : MeasurableSet[limsup s f] t) :
    forallᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 := by
  apply measure_eq_zero_or_one_of_indepSet_self' ?_
    ((indep_limsup_self h_le h_indep hf hns hnsp hns_univ).indepSet_of_measurableSet ht_tail
      ht_tail)
  filter_upwards [h_indep.ae_isProbabilityMeasure] with a ha using by infer_instance

/--
theorem `measure_zero_or_one_of_measurableSet_limsup` / 定理 `measure_zero_or_one_of_measurableSet_limsup`

English:
theorem measure_zero_or_one_of_measurableSet_limsup
  proof: by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using! Kernel.measure_zero_or_one_of_measurableSet_limsup h_le h_indep hf hns hnsp hns_univ
      ht_tail

中文:
定理 measure_zero_or_one_of_measurableSet_limsup
  证明: by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using! Kernel.measure_zero_or_one_of_measurableSet_limsup h_le h_indep hf hns hnsp hns_univ
      ht_tail

Depends on / 依赖: Filter, Filter.eventually_pure, Kernel, Kernel.measure_zero_or_one_of_measurableSet_limsup, ae_dirac_eq, eventually_pure, h_indep, h_le, hns_univ, ht_tail, measure_zero_or_one_of_measurableSet_limsup
-/
theorem measure_zero_or_one_of_measurableSet_limsup
    (h_le : forall n, s n <= m0) (h_indep : iIndep s μ)
    (hf : forall t, p t -> tᶜ in f) (hns : Directed (· <= ·) ns) (hnsp : forall a, p (ns a))
    (hns_univ : forall n, exists a, n in ns a) {t : Set Ω} (ht_tail : MeasurableSet[limsup s f] t) :
    μ t = 0 ∨ μ t = 1 := by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using! Kernel.measure_zero_or_one_of_measurableSet_limsup h_le h_indep hf hns hnsp hns_univ
      ht_tail

/--
theorem `condExp_zero_or_one_of_measurableSet_limsup` / 定理 `condExp_zero_or_one_of_measurableSet_limsup`

English:
theorem condExp_zero_or_one_of_measurableSet_limsup
  statement: [StandardBorelSpace Ω]
  proof: by
  have h := ae_of_ae_trim hm
    (Kernel.measure_zero_or_one_of_measurableSet_limsup h_le h_indep hf hns hnsp hns_univ ht_tail)
  have ht : MeasurableSet t := limsup_le_iSup.trans (iSup_le h_le) t ht_tail
  filter_upwards [condExpKernel_ae_eq_condExp hm ht, h] with ω hω_eq hω
  rwa [← hω_eq, meas

中文:
定理 condExp_zero_or_one_of_measurableSet_limsup
  结论: [StandardBorelSpace Ω]
  证明: by
  have h := ae_of_ae_trim hm
    (Kernel.measure_zero_or_one_of_measurableSet_limsup h_le h_indep hf hns hnsp hns_univ ht_tail)
  have ht : MeasurableSet t := limsup_le_iSup.trans (iSup_le h_le) t ht_tail
  filter_upwards [condExpKernel_ae_eq_condExp hm ht, h] with ω hω_eq hω
  rwa [← hω_eq, meas

Depends on / 依赖: ENNReal, ENNReal.toReal_eq_one_iff, Kernel, Kernel.measure_zero_or_one_of_measurableSet_limsup, MeasurableSet, ae_of_ae_trim, condExpKernel_ae_eq_condExp, filter_upwards, h_indep, h_le, hns_univ, ht_tail, iSup_le, limsup_le_iSup, limsup_le_iSup.trans, measureReal_def, measureReal_eq_zero_iff, measure_zero_or_one_of_measurableSet_limsup, toReal_eq_one_iff
-/
theorem condExp_zero_or_one_of_measurableSet_limsup [StandardBorelSpace Ω]
    (hm : m <= m0) [IsFiniteMeasure μ]
    (h_le : forall n, s n <= m0) (h_indep : iCondIndep m hm s μ)
    (hf : forall t, p t -> tᶜ in f) (hns : Directed (· <= ·) ns) (hnsp : forall a, p (ns a))
    (hns_univ : forall n, exists a, n in ns a) {t : Set Ω} (ht_tail : MeasurableSet[limsup s f] t) :
    forallᵐ ω ∂μ, (μ⟦t | m⟧) ω = 0 ∨ (μ⟦t | m⟧) ω = 1 := by
  have h := ae_of_ae_trim hm
    (Kernel.measure_zero_or_one_of_measurableSet_limsup h_le h_indep hf hns hnsp hns_univ ht_tail)
  have ht : MeasurableSet t := limsup_le_iSup.trans (iSup_le h_le) t ht_tail
  filter_upwards [condExpKernel_ae_eq_condExp hm ht, h] with ω hω_eq hω
  rwa [← hω_eq, measureReal_eq_zero_iff, measureReal_def, ENNReal.toReal_eq_one_iff]

end Abstract

section AtTop

variable [SemilatticeSup ι] [NoMaxOrder ι] [Nonempty ι]

/--
theorem `Kernel.indep_limsup_atTop_self` / 定理 `Kernel.indep_limsup_atTop_self`

English:
theorem Kernel.indep_limsup_atTop_self
  given: (h_le : forall n, s n <= m0) (h_indep : iIndep s κ μα)
  proof: by
  let ns : ι -> Set ι := Set.Iic
  have hnsp : forall i, BddAbove (ns i) := fun i => bddAbove_Iic
  refine indep_limsup_self h_le h_indep ?_ ?_ hnsp ?_
  · simp only [mem_atTop_sets, Set.mem_compl_iff, BddAbove, upperBounds, Set.Nonempty]
    rintro t ⟨a, ha⟩
    obtain ⟨b, hb⟩ : exists b, a < b 

中文:
定理 Kernel.indep_limsup_atTop_self
  条件: (h_le : 对任意 n, s n <= m0) (h_indep : iIndep s κ μα)
  证明: by
  let ns : ι -> Set ι := Set.Iic
  have hnsp : forall i, BddAbove (ns i) := fun i => bddAbove_Iic
  refine indep_limsup_self h_le h_indep ?_ ?_ hnsp ?_
  · simp only [mem_atTop_sets, Set.mem_compl_iff, BddAbove, upperBounds, Set.Nonempty]
    rintro t ⟨a, ha⟩
    obtain ⟨b, hb⟩ : exists b, a < b 

Depends on / 依赖: BddAbove, Monotone, Monotone.directed_le, Nonempty, Set.Iic, Set.Nonempty, Set.mem_compl_iff, bddAbove_Iic, directed_le, exists_gt, h_indep, h_le, hb.trans_le, indep_limsup_self, le_trans, lt_irrefl, mem_atTop_sets, mem_compl_iff, trans_le, trans_lt
-/
theorem Kernel.indep_limsup_atTop_self (h_le : forall n, s n <= m0) (h_indep : iIndep s κ μα) :
    Indep (limsup s atTop) (limsup s atTop) κ μα := by
  let ns : ι -> Set ι := Set.Iic
  have hnsp : forall i, BddAbove (ns i) := fun i => bddAbove_Iic
  refine indep_limsup_self h_le h_indep ?_ ?_ hnsp ?_
  · simp only [mem_atTop_sets, Set.mem_compl_iff, BddAbove, upperBounds, Set.Nonempty]
    rintro t ⟨a, ha⟩
    obtain ⟨b, hb⟩ : exists b, a < b := exists_gt a
    refine ⟨b, fun c hc hct => ?_⟩
    suffices forall i in t, i < c from lt_irrefl c (this c hct)
    exact fun i hi => (ha hi).trans_lt (hb.trans_le hc)
  · exact Monotone.directed_le fun i j hij k hki => le_trans hki hij
  · exact fun n => ⟨n, le_rfl⟩

/--
theorem `indep_limsup_atTop_self` / 定理 `indep_limsup_atTop_self`

English:
theorem indep_limsup_atTop_self
  given: (h_le : forall n, s n <= m0) (h_indep : iIndep s μ)
  proof: Kernel.indep_limsup_atTop_self h_le h_indep

中文:
定理 indep_limsup_atTop_self
  条件: (h_le : 对任意 n, s n <= m0) (h_indep : iIndep s μ)
  证明: Kernel.indep_limsup_atTop_self h_le h_indep

Depends on / 依赖: Kernel, Kernel.indep_limsup_atTop_self, h_indep, h_le, indep_limsup_atTop_self
-/
theorem indep_limsup_atTop_self (h_le : forall n, s n <= m0) (h_indep : iIndep s μ) :
    Indep (limsup s atTop) (limsup s atTop) μ :=
  Kernel.indep_limsup_atTop_self h_le h_indep

/--
theorem `condIndep_limsup_atTop_self` / 定理 `condIndep_limsup_atTop_self`

English:
theorem condIndep_limsup_atTop_self
  statement: [StandardBorelSpace Ω]
  proof: Kernel.indep_limsup_atTop_self h_le h_indep

中文:
定理 condIndep_limsup_atTop_self
  结论: [StandardBorelSpace Ω]
  证明: Kernel.indep_limsup_atTop_self h_le h_indep

Depends on / 依赖: Kernel, Kernel.indep_limsup_atTop_self, h_indep, h_le, indep_limsup_atTop_self
-/
theorem condIndep_limsup_atTop_self [StandardBorelSpace Ω]
    (hm : m <= m0) [IsFiniteMeasure μ]
    (h_le : forall n, s n <= m0) (h_indep : iCondIndep m hm s μ) :
    CondIndep m (limsup s atTop) (limsup s atTop) hm μ :=
  Kernel.indep_limsup_atTop_self h_le h_indep

/--
theorem `Kernel.measure_zero_or_one_of_measurableSet_limsup_atTop` / 定理 `Kernel.measure_zero_or_one_of_measurableSet_limsup_atTop`

English:
theorem Kernel.measure_zero_or_one_of_measurableSet_limsup_atTop
  statement: (h_le : forall n, s n <= m0)
  proof: by
  apply measure_eq_zero_or_one_of_indepSet_self' ?_
    ((indep_limsup_atTop_self h_le h_indep).indepSet_of_measurableSet ht_tail ht_tail)
  filter_upwards [h_indep.ae_isProbabilityMeasure] with a ha using by infer_instance

中文:
定理 Kernel.measure_zero_or_one_of_measurableSet_limsup_atTop
  结论: (h_le : 对任意 n, s n <= m0)
  证明: by
  apply measure_eq_zero_or_one_of_indepSet_self' ?_
    ((indep_limsup_atTop_self h_le h_indep).indepSet_of_measurableSet ht_tail ht_tail)
  filter_upwards [h_indep.ae_isProbabilityMeasure] with a ha using by infer_instance

Depends on / 依赖: AlgHom, AlgHom.id, Subalgebra, Subalgebra.inclusion, _eq_of_diagram, ae_isProbabilityMeasure, filter_upwards, h_indep, h_indep.ae_isProbabilityMeasure, h_le, ht_tail, inclusion, indepSet_of_measurableSet, indep_limsup_atTop_self, infer_instance, measure_eq_zero_or_one_of_indepSet_self
-/
theorem Kernel.measure_zero_or_one_of_measurableSet_limsup_atTop (h_le : forall n, s n <= m0)
    (h_indep : iIndep s κ μα) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atTop] t) :
    forallᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 := by
  apply measure_eq_zero_or_one_of_indepSet_self' ?_
    ((indep_limsup_atTop_self h_le h_indep).indepSet_of_measurableSet ht_tail ht_tail)
  filter_upwards [h_indep.ae_isProbabilityMeasure] with a ha using by infer_instance

/--
theorem `measure_zero_or_one_of_measurableSet_limsup_atTop` / 定理 `measure_zero_or_one_of_measurableSet_limsup_atTop`

English:
theorem measure_zero_or_one_of_measurableSet_limsup_atTop
  proof: by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using! Kernel.measure_zero_or_one_of_measurableSet_limsup_atTop h_le h_indep ht_tail

中文:
定理 measure_zero_or_one_of_measurableSet_limsup_atTop
  证明: by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using! Kernel.measure_zero_or_one_of_measurableSet_limsup_atTop h_le h_indep ht_tail

Depends on / 依赖: Filter, Filter.eventually_pure, Kernel, Kernel.measure_zero_or_one_of_measurableSet_limsup_atTop, ae_dirac_eq, eventually_pure, h_indep, h_le, ht_tail, measure_zero_or_one_of_measurableSet_limsup_atTop
-/
theorem measure_zero_or_one_of_measurableSet_limsup_atTop
    (h_le : forall n, s n <= m0)
    (h_indep : iIndep s μ) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atTop] t) :
    μ t = 0 ∨ μ t = 1 := by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using! Kernel.measure_zero_or_one_of_measurableSet_limsup_atTop h_le h_indep ht_tail

/--
theorem `condExp_zero_or_one_of_measurableSet_limsup_atTop` / 定理 `condExp_zero_or_one_of_measurableSet_limsup_atTop`

English:
theorem condExp_zero_or_one_of_measurableSet_limsup_atTop
  statement: [StandardBorelSpace Ω]
  proof: condExp_eq_zero_or_one_of_condIndepSet_self hm (limsup_le_iSup.trans (iSup_le h_le) t ht_tail)
    ((condIndep_limsup_atTop_self hm h_le h_indep).condIndepSet_of_measurableSet ht_tail ht_tail)

中文:
定理 condExp_zero_or_one_of_measurableSet_limsup_atTop
  结论: [StandardBorelSpace Ω]
  证明: condExp_eq_zero_or_one_of_condIndepSet_self hm (limsup_le_iSup.trans (iSup_le h_le) t ht_tail)
    ((condIndep_limsup_atTop_self hm h_le h_indep).condIndepSet_of_measurableSet ht_tail ht_tail)

Depends on / 依赖: condExp_eq_zero_or_one_of_condIndepSet_self, condIndepSet_of_measurableSet, condIndep_limsup_atTop_self, h_indep, h_le, ht_tail, iSup_le, limsup_le_iSup, limsup_le_iSup.trans
-/
theorem condExp_zero_or_one_of_measurableSet_limsup_atTop [StandardBorelSpace Ω]
    (hm : m <= m0) [IsFiniteMeasure μ] (h_le : forall n, s n <= m0)
    (h_indep : iCondIndep m hm s μ) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atTop] t) :
    forallᵐ ω ∂μ, (μ⟦t | m⟧) ω = 0 ∨ (μ⟦t | m⟧) ω = 1 :=
  condExp_eq_zero_or_one_of_condIndepSet_self hm (limsup_le_iSup.trans (iSup_le h_le) t ht_tail)
    ((condIndep_limsup_atTop_self hm h_le h_indep).condIndepSet_of_measurableSet ht_tail ht_tail)

end AtTop

section AtBot

variable [SemilatticeInf ι] [NoMinOrder ι] [Nonempty ι]

/--
theorem `Kernel.indep_limsup_atBot_self` / 定理 `Kernel.indep_limsup_atBot_self`

English:
theorem Kernel.indep_limsup_atBot_self
  given: (h_le : forall n, s n <= m0) (h_indep : iIndep s κ μα)
  proof: by
  let ns : ι -> Set ι := Set.Ici
  have hnsp : forall i, BddBelow (ns i) := fun i => bddBelow_Ici
  refine indep_limsup_self h_le h_indep ?_ ?_ hnsp ?_
  · simp only [mem_atBot_sets, Set.mem_compl_iff, BddBelow, lowerBounds, Set.Nonempty]
    rintro t ⟨a, ha⟩
    obtain ⟨b, hb⟩ : exists b, b < a 

中文:
定理 Kernel.indep_limsup_atBot_self
  条件: (h_le : 对任意 n, s n <= m0) (h_indep : iIndep s κ μα)
  证明: by
  let ns : ι -> Set ι := Set.Ici
  have hnsp : forall i, BddBelow (ns i) := fun i => bddBelow_Ici
  refine indep_limsup_self h_le h_indep ?_ ?_ hnsp ?_
  · simp only [mem_atBot_sets, Set.mem_compl_iff, BddBelow, lowerBounds, Set.Nonempty]
    rintro t ⟨a, ha⟩
    obtain ⟨b, hb⟩ : exists b, b < a 

Depends on / 依赖: Antitone, Antitone.directed_le, BddBelow, Ici_subset_Ici, Nonempty, Set.Ici, Set.Ici_subset_Ici, Set.Nonempty, Set.mem_compl_iff, bddBelow_Ici, directed_le, exists_lt, h_indep, h_le, hb.trans_le, hc.trans_lt, indep_limsup_self, lowerBounds, lt_irrefl, mem_atBot_sets
-/
theorem Kernel.indep_limsup_atBot_self (h_le : forall n, s n <= m0) (h_indep : iIndep s κ μα) :
    Indep (limsup s atBot) (limsup s atBot) κ μα := by
  let ns : ι -> Set ι := Set.Ici
  have hnsp : forall i, BddBelow (ns i) := fun i => bddBelow_Ici
  refine indep_limsup_self h_le h_indep ?_ ?_ hnsp ?_
  · simp only [mem_atBot_sets, Set.mem_compl_iff, BddBelow, lowerBounds, Set.Nonempty]
    rintro t ⟨a, ha⟩
    obtain ⟨b, hb⟩ : exists b, b < a := exists_lt a
    refine ⟨b, fun c hc hct => ?_⟩
    suffices forall i in t, c < i from lt_irrefl c (this c hct)
    exact fun i hi => hc.trans_lt (hb.trans_le (ha hi))
  · exact Antitone.directed_le fun _ _ => Set.Ici_subset_Ici.2
  · exact fun n => ⟨n, le_rfl⟩

/--
theorem `indep_limsup_atBot_self` / 定理 `indep_limsup_atBot_self`

English:
theorem indep_limsup_atBot_self
  proof: Kernel.indep_limsup_atBot_self h_le h_indep

中文:
定理 indep_limsup_atBot_self
  证明: Kernel.indep_limsup_atBot_self h_le h_indep

Depends on / 依赖: Kernel, Kernel.indep_limsup_atBot_self, h_indep, h_le, indep_limsup_atBot_self
-/
theorem indep_limsup_atBot_self
    (h_le : forall n, s n <= m0) (h_indep : iIndep s μ) :
    Indep (limsup s atBot) (limsup s atBot) μ :=
  Kernel.indep_limsup_atBot_self h_le h_indep

/--
theorem `condIndep_limsup_atBot_self` / 定理 `condIndep_limsup_atBot_self`

English:
theorem condIndep_limsup_atBot_self
  statement: [StandardBorelSpace Ω]
  proof: Kernel.indep_limsup_atBot_self h_le h_indep

中文:
定理 condIndep_limsup_atBot_self
  结论: [StandardBorelSpace Ω]
  证明: Kernel.indep_limsup_atBot_self h_le h_indep

Depends on / 依赖: Kernel, Kernel.indep_limsup_atBot_self, h_indep, h_le, indep_limsup_atBot_self
-/
theorem condIndep_limsup_atBot_self [StandardBorelSpace Ω]
    (hm : m <= m0) [IsFiniteMeasure μ]
    (h_le : forall n, s n <= m0) (h_indep : iCondIndep m hm s μ) :
    CondIndep m (limsup s atBot) (limsup s atBot) hm μ :=
  Kernel.indep_limsup_atBot_self h_le h_indep

/--
theorem `Kernel.measure_zero_or_one_of_measurableSet_limsup_atBot` / 定理 `Kernel.measure_zero_or_one_of_measurableSet_limsup_atBot`

English:
theorem Kernel.measure_zero_or_one_of_measurableSet_limsup_atBot
  statement: (h_le : forall n, s n <= m0)
  proof: by
  apply measure_eq_zero_or_one_of_indepSet_self' ?_
    ((indep_limsup_atBot_self h_le h_indep).indepSet_of_measurableSet ht_tail ht_tail)
  filter_upwards [h_indep.ae_isProbabilityMeasure] with a ha using by infer_instance

中文:
定理 Kernel.measure_zero_or_one_of_measurableSet_limsup_atBot
  结论: (h_le : 对任意 n, s n <= m0)
  证明: by
  apply measure_eq_zero_or_one_of_indepSet_self' ?_
    ((indep_limsup_atBot_self h_le h_indep).indepSet_of_measurableSet ht_tail ht_tail)
  filter_upwards [h_indep.ae_isProbabilityMeasure] with a ha using by infer_instance

Depends on / 依赖: ae_isProbabilityMeasure, filter_upwards, h_indep, h_indep.ae_isProbabilityMeasure, h_le, ht_tail, indepSet_of_measurableSet, indep_limsup_atBot_self, infer_instance, measure_eq_zero_or_one_of_indepSet_self
-/
theorem Kernel.measure_zero_or_one_of_measurableSet_limsup_atBot (h_le : forall n, s n <= m0)
    (h_indep : iIndep s κ μα) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atBot] t) :
    forallᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 := by
  apply measure_eq_zero_or_one_of_indepSet_self' ?_
    ((indep_limsup_atBot_self h_le h_indep).indepSet_of_measurableSet ht_tail ht_tail)
  filter_upwards [h_indep.ae_isProbabilityMeasure] with a ha using by infer_instance

/--
theorem `measure_zero_or_one_of_measurableSet_limsup_atBot` / 定理 `measure_zero_or_one_of_measurableSet_limsup_atBot`

English:
theorem measure_zero_or_one_of_measurableSet_limsup_atBot
  proof: by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using! Kernel.measure_zero_or_one_of_measurableSet_limsup_atBot h_le h_indep ht_tail

中文:
定理 measure_zero_or_one_of_measurableSet_limsup_atBot
  证明: by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using! Kernel.measure_zero_or_one_of_measurableSet_limsup_atBot h_le h_indep ht_tail

Depends on / 依赖: Filter, Filter.eventually_pure, Kernel, Kernel.measure_zero_or_one_of_measurableSet_limsup_atBot, ae_dirac_eq, congr_arg, eventually_pure, f.isCompat_apply, f.toFun_eq_rTensor_, h_indep, h_le, ha.symm, ht_tail, isCompat_apply, measure_zero_or_one_of_measurableSet_limsup_atBot
-/
theorem measure_zero_or_one_of_measurableSet_limsup_atBot
    (h_le : forall n, s n <= m0) (h_indep : iIndep s μ) {t : Set Ω}
    (ht_tail : MeasurableSet[limsup s atBot] t) :
    μ t = 0 ∨ μ t = 1 := by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using! Kernel.measure_zero_or_one_of_measurableSet_limsup_atBot h_le h_indep ht_tail

/--
theorem `condExp_zero_or_one_of_measurableSet_limsup_atBot` / 定理 `condExp_zero_or_one_of_measurableSet_limsup_atBot`

English:
theorem condExp_zero_or_one_of_measurableSet_limsup_atBot
  statement: [StandardBorelSpace Ω]
  proof: condExp_eq_zero_or_one_of_condIndepSet_self hm (limsup_le_iSup.trans (iSup_le h_le) t ht_tail)
    ((condIndep_limsup_atBot_self hm h_le h_indep).condIndepSet_of_measurableSet ht_tail ht_tail)

中文:
定理 condExp_zero_or_one_of_measurableSet_limsup_atBot
  结论: [StandardBorelSpace Ω]
  证明: condExp_eq_zero_or_one_of_condIndepSet_self hm (limsup_le_iSup.trans (iSup_le h_le) t ht_tail)
    ((condIndep_limsup_atBot_self hm h_le h_indep).condIndepSet_of_measurableSet ht_tail ht_tail)

Depends on / 依赖: condExp_eq_zero_or_one_of_condIndepSet_self, condIndepSet_of_measurableSet, condIndep_limsup_atBot_self, h_indep, h_le, ht_tail, iSup_le, limsup_le_iSup, limsup_le_iSup.trans
-/
theorem condExp_zero_or_one_of_measurableSet_limsup_atBot [StandardBorelSpace Ω]
    (hm : m <= m0) [IsFiniteMeasure μ] (h_le : forall n, s n <= m0)
    (h_indep : iCondIndep m hm s μ) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atBot] t) :
    forallᵐ ω ∂μ, (μ⟦t | m⟧) ω = 0 ∨ (μ⟦t | m⟧) ω = 1 :=
  condExp_eq_zero_or_one_of_condIndepSet_self hm (limsup_le_iSup.trans (iSup_le h_le) t ht_tail)
    ((condIndep_limsup_atBot_self hm h_le h_indep).condIndepSet_of_measurableSet ht_tail ht_tail)

end AtBot

end ProbabilityTheory
