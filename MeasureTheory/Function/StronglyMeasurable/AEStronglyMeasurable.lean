/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Strongly measurable and finitely strongly measurable functions

A function `f` is said to be almost everywhere strongly measurable if `f` is almost everywhere
equal to a strongly measurable function, i.e. the sequential limit of simple functions.
It is said to be almost everywhere finitely strongly measurable with respect to a measure `μ`
if the supports of those simple functions have finite measure.

Almost everywhere strongly measurable functions form the largest class of functions that can be
integrated using the Bochner integral.

## Main definitions
* `AEStronglyMeasurable f μ`: `f` is almost everywhere equal to a `StronglyMeasurable` function.
* `AEFinStronglyMeasurable f μ`: `f` is almost everywhere equal to a `FinStronglyMeasurable`
  function.

* `AEFinStronglyMeasurable.sigmaFiniteSet`: a measurable set `t` such that
  `f =ᵐ[μ.restrict tᶜ] 0` and `μ.restrict t` is sigma-finite.

## Main statements

* `AEFinStronglyMeasurable.exists_set_sigmaFinite`: there exists a measurable set `t` such that
  `f =ᵐ[μ.restrict tᶜ] 0` and `μ.restrict t` is sigma-finite.

We provide a solid API for almost everywhere strongly
measurable functions, as a basis for the Bochner integral.

## References

* [Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
  Springer, 2016.][Hytonen_VanNeerven_Veraar_Wies_2016]

-/

@[expose] public section

open MeasureTheory Filter TopologicalSpace Function Set MeasureTheory.Measure

open ENNReal Topology MeasureTheory NNReal

variable {α β γ ι : Type*} [Countable ι]

namespace MeasureTheory

local infixr:25 " ->ₛ " => SimpleFunc

section Definitions

variable [TopologicalSpace β]

/-- A function is `AEStronglyMeasurable` with respect to a measure `μ` if it is almost everywhere
equal to the limit of a sequence of simple functions.

One can specify the sigma-algebra according to which simple functions are taken using the
`AEStronglyMeasurable[m]` notation in the `MeasureTheory` scope. -/
@[fun_prop]
/--
Definition of `AEStronglyMeasurable` / `AEStronglyMeasurable` 的定义

English:
definition AEStronglyMeasurable
  signature: [m : MeasurableSpace α] {m₀ : MeasurableSpace α} (f : α -> β)
  body: exists g : α -> β, StronglyMeasurable[m] g ∧ f =ᵐ[μ] g

add_aesop_rules safe tactic
  (rule_sets := [Measurable])
  (index := [target @AEStronglyMeasurable ..])
  (by fun_prop (disch := measurability))

中文:
定义 AEStronglyMeasurable
  签名: [m : 可测空间 α] {m₀ : 可测空间 α} (f : α -> β)
  定义体: exists g : α -> β, StronglyMeasurable[m] g ∧ f =ᵐ[μ] g

add_aesop_rules safe tactic
  (rule_sets := [Measurable])
  (index := [target @AEStronglyMeasurable ..])
  (by fun_prop (disch := measurability))

Depends on / 依赖: StronglyMeasurable, volume_tac
-/
def AEStronglyMeasurable [m : MeasurableSpace α] {m₀ : MeasurableSpace α} (f : α -> β)
    (μ : Measure[m₀] α := by volume_tac) : Prop :=
  exists g : α -> β, StronglyMeasurable[m] g ∧ f =ᵐ[μ] g

add_aesop_rules safe tactic
  (rule_sets := [Measurable])
  (index := [target @AEStronglyMeasurable ..])
  (by fun_prop (disch := measurability))

/-- A function is `m`-`AEStronglyMeasurable` with respect to a measure `μ` if it is almost
everywhere equal to the limit of a sequence of `m`-simple functions. -/
scoped notation "AEStronglyMeasurable[" m "]" => @MeasureTheory.AEStronglyMeasurable _ _ _ m

/--
Definition of `AEFinStronglyMeasurable` / `AEFinStronglyMeasurable` 的定义

English:
definition AEFinStronglyMeasurable
  body: exists g, FinStronglyMeasurable g μ ∧ f =ᵐ[μ] g

中文:
定义 AEFinStronglyMeasurable
  定义体: exists g, FinStronglyMeasurable g μ ∧ f =ᵐ[μ] g

Depends on / 依赖: FinStronglyMeasurable, volume_tac
-/
def AEFinStronglyMeasurable
    [Zero β] {_ : MeasurableSpace α} (f : α -> β) (μ : Measure α := by volume_tac) : Prop :=
  exists g, FinStronglyMeasurable g μ ∧ f =ᵐ[μ] g

end Definitions

namespace FinStronglyMeasurable

variable {m0 : MeasurableSpace α} {μ : Measure α} {f g : α -> β}

/--
theorem `aefinStronglyMeasurable` / 定理 `aefinStronglyMeasurable`

English:
theorem aefinStronglyMeasurable
  given: [Zero β] [TopologicalSpace β] (hf : FinStronglyMeasurable f μ)
  proof: ⟨f, hf, ae_eq_refl f⟩

中文:
定理 aefinStronglyMeasurable
  条件: [零 β] [拓扑空间 β] (hf : FinStronglyMeasurable f μ)
  证明: ⟨f, hf, ae_eq_refl f⟩

Depends on / 依赖: ae_eq_refl
-/
theorem aefinStronglyMeasurable [Zero β] [TopologicalSpace β] (hf : FinStronglyMeasurable f μ) :
    AEFinStronglyMeasurable f μ :=
  ⟨f, hf, ae_eq_refl f⟩

end FinStronglyMeasurable

/--
theorem `aefinStronglyMeasurable_zero` / 定理 `aefinStronglyMeasurable_zero`

English:
theorem aefinStronglyMeasurable_zero
  statement: {α β} {_ : MeasurableSpace α} (μ : Measure α) [Zero β]
  proof: ⟨0, finStronglyMeasurable_zero, EventuallyEq.rfl⟩

中文:
定理 aefinStronglyMeasurable_zero
  结论: {α β} {_ : 可测空间 α} (μ : 测度 α) [零 β]
  证明: ⟨0, finStronglyMeasurable_zero, EventuallyEq.rfl⟩

Depends on / 依赖: EventuallyEq, EventuallyEq.rfl, finStronglyMeasurable_zero
-/
theorem aefinStronglyMeasurable_zero {α β} {_ : MeasurableSpace α} (μ : Measure α) [Zero β]
    [TopologicalSpace β] : AEFinStronglyMeasurable (0 : α -> β) μ :=
  ⟨0, finStronglyMeasurable_zero, EventuallyEq.rfl⟩

/-! ## Almost everywhere strongly measurable functions -/

section AEStronglyMeasurable
variable [TopologicalSpace β] [TopologicalSpace γ] {m m₀ : MeasurableSpace α} {μ ν : Measure[m₀] α}
  {f g : α -> β}

@[fun_prop]
/--
theorem `StronglyMeasurable.aestronglyMeasurable` / 定理 `StronglyMeasurable.aestronglyMeasurable`

English:
theorem StronglyMeasurable.aestronglyMeasurable
  given: (hf : StronglyMeasurable[m] f)
  proof: ⟨f, hf, EventuallyEq.refl _ _⟩

@[fun_prop]

中文:
定理 StronglyMeasurable.aestronglyMeasurable
  条件: (hf : StronglyMeasurable[m] f)
  证明: ⟨f, hf, EventuallyEq.refl _ _⟩

@[fun_prop]
-/
protected theorem StronglyMeasurable.aestronglyMeasurable (hf : StronglyMeasurable[m] f) :
    AEStronglyMeasurable[m] f μ := ⟨f, hf, EventuallyEq.refl _ _⟩

@[fun_prop]
/--
theorem `aestronglyMeasurable_const` / 定理 `aestronglyMeasurable_const`

English:
theorem aestronglyMeasurable_const
  given: {b : β}
  statement: AEStronglyMeasurable[m] (fun _ : α => b) μ
  proof: stronglyMeasurable_const.aestronglyMeasurable

@[to_additive (attr := fun_prop)]

中文:
定理 aestronglyMeasurable_const
  条件: {b : β}
  结论: AEStronglyMeasurable[m] (fun _ : α => b) μ
  证明: stronglyMeasurable_const.aestronglyMeasurable

@[to_additive (attr := fun_prop)]

Depends on / 依赖: aestronglyMeasurable, stronglyMeasurable_const, stronglyMeasurable_const.aestronglyMeasurable
-/
theorem aestronglyMeasurable_const {b : β} : AEStronglyMeasurable[m] (fun _ : α => b) μ :=
  stronglyMeasurable_const.aestronglyMeasurable

@[to_additive (attr := fun_prop)]
/--
theorem `aestronglyMeasurable_one` / 定理 `aestronglyMeasurable_one`

English:
theorem aestronglyMeasurable_one
  given: [One β]
  statement: AEStronglyMeasurable[m] (1 : α -> β) μ
  proof: stronglyMeasurable_one.aestronglyMeasurable

@[simp, nontriviality]

中文:
定理 aestronglyMeasurable_one
  条件: [幺 β]
  结论: AEStronglyMeasurable[m] (1 : α -> β) μ
  证明: stronglyMeasurable_one.aestronglyMeasurable

@[simp, nontriviality]

Depends on / 依赖: aestronglyMeasurable, stronglyMeasurable_one, stronglyMeasurable_one.aestronglyMeasurable
-/
theorem aestronglyMeasurable_one [One β] : AEStronglyMeasurable[m] (1 : α -> β) μ :=
  stronglyMeasurable_one.aestronglyMeasurable

@[simp, nontriviality]
/--
lemma `AEStronglyMeasurable.of_subsingleton_dom` / 引理 `AEStronglyMeasurable.of_subsingleton_dom`

English:
lemma AEStronglyMeasurable.of_subsingleton_dom
  given: [Subsingleton α]
  statement: AEStronglyMeasurable[m] f μ
  proof: StronglyMeasurable.of_subsingleton_dom.aestronglyMeasurable

@[simp, nontriviality]

中文:
引理 AEStronglyMeasurable.of_subsingleton_dom
  条件: [子单例 α]
  结论: AEStronglyMeasurable[m] f μ
  证明: StronglyMeasurable.of_subsingleton_dom.aestronglyMeasurable

@[simp, nontriviality]

Depends on / 依赖: StronglyMeasurable, StronglyMeasurable.of_subsingleton_dom.aestronglyMeasurable, aestronglyMeasurable, of_subsingleton_dom
-/
lemma AEStronglyMeasurable.of_subsingleton_dom [Subsingleton α] : AEStronglyMeasurable[m] f μ :=
  StronglyMeasurable.of_subsingleton_dom.aestronglyMeasurable

@[simp, nontriviality]
/--
lemma `AEStronglyMeasurable.of_subsingleton_cod` / 引理 `AEStronglyMeasurable.of_subsingleton_cod`

English:
lemma AEStronglyMeasurable.of_subsingleton_cod
  given: [Subsingleton β]
  statement: AEStronglyMeasurable[m] f μ
  proof: StronglyMeasurable.of_subsingleton_cod.aestronglyMeasurable

@[fun_prop, simp]

中文:
引理 AEStronglyMeasurable.of_subsingleton_cod
  条件: [子单例 β]
  结论: AEStronglyMeasurable[m] f μ
  证明: StronglyMeasurable.of_subsingleton_cod.aestronglyMeasurable

@[fun_prop, simp]

Depends on / 依赖: StronglyMeasurable, StronglyMeasurable.of_subsingleton_cod.aestronglyMeasurable, aestronglyMeasurable, of_subsingleton_cod
-/
lemma AEStronglyMeasurable.of_subsingleton_cod [Subsingleton β] : AEStronglyMeasurable[m] f μ :=
  StronglyMeasurable.of_subsingleton_cod.aestronglyMeasurable

@[fun_prop, simp]
/--
theorem `aestronglyMeasurable_zero_measure` / 定理 `aestronglyMeasurable_zero_measure`

English:
theorem aestronglyMeasurable_zero_measure
  given: (f : α -> β)
  proof: by
  nontriviality α
  inhabit α
  exact ⟨fun _ => f default, stronglyMeasurable_const, rfl⟩

@[fun_prop]

中文:
定理 aestronglyMeasurable_zero_measure
  条件: (f : α -> β)
  证明: by
  nontriviality α
  inhabit α
  exact ⟨fun _ => f default, stronglyMeasurable_const, rfl⟩

@[fun_prop]

Depends on / 依赖: inhabit, nontriviality, stronglyMeasurable_const
-/
theorem aestronglyMeasurable_zero_measure (f : α -> β) :
    AEStronglyMeasurable[m] f (0 : Measure[m₀] α) := by
  nontriviality α
  inhabit α
  exact ⟨fun _ => f default, stronglyMeasurable_const, rfl⟩

@[fun_prop]
/--
theorem `SimpleFunc.aestronglyMeasurable` / 定理 `SimpleFunc.aestronglyMeasurable`

English:
theorem SimpleFunc.aestronglyMeasurable
  given: (f : α ->ₛ β)
  statement: AEStronglyMeasurable f μ
  proof: f.stronglyMeasurable.aestronglyMeasurable

中文:
定理 SimpleFunc.aestronglyMeasurable
  条件: (f : α ->ₛ β)
  结论: AEStronglyMeasurable f μ
  证明: f.stronglyMeasurable.aestronglyMeasurable

Depends on / 依赖: aestronglyMeasurable, f.stronglyMeasurable.aestronglyMeasurable, stronglyMeasurable
-/
theorem SimpleFunc.aestronglyMeasurable (f : α ->ₛ β) : AEStronglyMeasurable f μ :=
  f.stronglyMeasurable.aestronglyMeasurable

/--
lemma `aestronglyMeasurable_id_of_isSeparable` / 引理 `aestronglyMeasurable_id_of_isSeparable`

English:
lemma aestronglyMeasurable_id_of_isSeparable
  statement: [TopologicalSpace α]
  proof: by
  nontriviality α
  obtain ⟨a, -⟩ := exists_pair_ne α
  classical
  refine ⟨(closure s).piecewise id (fun _ => a), ?_,
    Filter.mem_of_superset h2 (fun x hx => by simp [subset_closure hx])⟩
  have h : StronglyMeasurable ((↑) : closure s -> α) := by
    have := h1.closure.secondCountableTopology

中文:
引理 aestronglyMeasurable_id_of_isSeparable
  结论: [拓扑空间 α]
  证明: by
  nontriviality α
  obtain ⟨a, -⟩ := exists_pair_ne α
  classical
  refine ⟨(closure s).piecewise id (fun _ => a), ?_,
    Filter.mem_of_superset h2 (fun x hx => by simp [subset_closure hx])⟩
  have h : StronglyMeasurable ((↑) : closure s -> α) := by
    have := h1.closure.secondCountableTopology

Depends on / 依赖: Filter, Filter.mem_of_superset, Functio, StronglyMeasurable, classical, closure, continuous_subtype_val, continuous_subtype_val.stronglyMeasurable, exists_pair_ne, extend, h1.closure.secondCountableTopology, mem_of_superset, nontriviality, piecewise, secondCountableTopology, stronglyMeasurable, subset_closure
-/
lemma aestronglyMeasurable_id_of_isSeparable [TopologicalSpace α]
    [TopologicalSpace.PseudoMetrizableSpace α] [OpensMeasurableSpace α]
    {s : Set α} (h1 : TopologicalSpace.IsSeparable s) (h2 : μ sᶜ = 0) :
    AEStronglyMeasurable id μ := by
  nontriviality α
  obtain ⟨a, -⟩ := exists_pair_ne α
  classical
  refine ⟨(closure s).piecewise id (fun _ => a), ?_,
    Filter.mem_of_superset h2 (fun x hx => by simp [subset_closure hx])⟩
  have h : StronglyMeasurable ((↑) : closure s -> α) := by
    have := h1.closure.secondCountableTopology
    exact continuous_subtype_val.stronglyMeasurable
  have : (closure s).piecewise id (fun _ => a) =
      ((↑) : closure s -> α).extend ((↑) : closure s -> α) (fun _ => a) := by
    ext x
    by_cases hx : x in closure s
    · simp [Function.extend_val_apply, hx]
    · simp [hx]
  rw [this]
  exact (MeasurableEmbedding.subtype_coe isClosed_closure.measurableSet).stronglyMeasurable_extend
    h stronglyMeasurable_const

namespace AEStronglyMeasurable

@[fun_prop]
/--
lemma `of_discrete` / 引理 `of_discrete`

English:
lemma of_discrete
  given: [Countable α] [MeasurableSingletonClass α]
  statement: AEStronglyMeasurable f μ
  proof: StronglyMeasurable.of_discrete.aestronglyMeasurable

中文:
引理 of_discrete
  条件: [可数 α] [MeasurableSingleton类 α]
  结论: AEStronglyMeasurable f μ
  证明: StronglyMeasurable.of_discrete.aestronglyMeasurable

Depends on / 依赖: StronglyMeasurable, StronglyMeasurable.of_discrete.aestronglyMeasurable, aestronglyMeasurable, of_discrete
-/
lemma of_discrete [Countable α] [MeasurableSingletonClass α] : AEStronglyMeasurable f μ :=
  StronglyMeasurable.of_discrete.aestronglyMeasurable

section Mk

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def mk (f : α -> β) (hf : AEStronglyMeasurable[m] f μ)
  body: hf.choose

@[fun_prop]

中文:
定义 noncomputable
  签名: def mk (f : α -> β) (hf : AEStronglyMeasurable[m] f μ)
  定义体: hf.choose

@[fun_prop]
-/
protected noncomputable def mk (f : α -> β) (hf : AEStronglyMeasurable[m] f μ) : α -> β :=
  hf.choose

@[fun_prop]
/--
lemma `stronglyMeasurable_mk` / 引理 `stronglyMeasurable_mk`

English:
lemma stronglyMeasurable_mk
  given: (hf : AEStronglyMeasurable[m] f μ)
  statement: StronglyMeasurable[m] (hf.mk f)
  proof: hf.choose_spec.1

@[fun_prop]

中文:
引理 stronglyMeasurable_mk
  条件: (hf : AEStronglyMeasurable[m] f μ)
  结论: StronglyMeasurable[m] (hf.mk f)
  证明: hf.choose_spec.1

@[fun_prop]

Depends on / 依赖: choose_spec, hf.choose_spec
-/
lemma stronglyMeasurable_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f) :=
  hf.choose_spec.1

@[fun_prop]
/--
theorem `measurable_mk` / 定理 `measurable_mk`

English:
theorem measurable_mk
  statement: [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
  proof: hf.stronglyMeasurable_mk.measurable

中文:
定理 measurable_mk
  结论: [PseudoMetrizable空间 β] [可测空间 β] [Borel空间 β]
  证明: hf.stronglyMeasurable_mk.measurable

Depends on / 依赖: hf.stronglyMeasurable_mk.measurable, measurable, stronglyMeasurable_mk
-/
theorem measurable_mk [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (hf : AEStronglyMeasurable[m] f μ) : Measurable[m] (hf.mk f) :=
  hf.stronglyMeasurable_mk.measurable

/--
theorem `ae_eq_mk` / 定理 `ae_eq_mk`

English:
theorem ae_eq_mk
  given: (hf : AEStronglyMeasurable[m] f μ)
  statement: f =ᵐ[μ] hf.mk f
  proof: hf.choose_spec.2

@[fun_prop]

中文:
定理 ae_eq_mk
  条件: (hf : AEStronglyMeasurable[m] f μ)
  结论: f =ᵐ[μ] hf.mk f
  证明: hf.choose_spec.2

@[fun_prop]

Depends on / 依赖: choose_spec, hf.choose_spec
-/
theorem ae_eq_mk (hf : AEStronglyMeasurable[m] f μ) : f =ᵐ[μ] hf.mk f :=
  hf.choose_spec.2

@[fun_prop]
/--
theorem `aemeasurable` / 定理 `aemeasurable`

English:
theorem aemeasurable
  statement: {β} [MeasurableSpace β] [TopologicalSpace β]
  proof: ⟨hf.mk f, hf.stronglyMeasurable_mk.measurable, hf.ae_eq_mk⟩

中文:
定理 aemeasurable
  结论: {β} [可测空间 β] [拓扑空间 β]
  证明: ⟨hf.mk f, hf.stronglyMeasurable_mk.measurable, hf.ae_eq_mk⟩
-/
protected theorem aemeasurable {β} [MeasurableSpace β] [TopologicalSpace β]
    [PseudoMetrizableSpace β] [BorelSpace β] {f : α -> β} (hf : AEStronglyMeasurable f μ) :
    AEMeasurable f μ :=
  ⟨hf.mk f, hf.stronglyMeasurable_mk.measurable, hf.ae_eq_mk⟩

end Mk

/--
theorem `congr` / 定理 `congr`

English:
theorem congr
  given: (hf : AEStronglyMeasurable[m] f μ) (h : f =ᵐ[μ] g)
  statement: AEStronglyMeasurable[m] g μ
  proof: ⟨hf.mk f, hf.stronglyMeasurable_mk, h.symm.trans hf.ae_eq_mk⟩

中文:
定理 congr
  条件: (hf : AEStronglyMeasurable[m] f μ) (h : f =ᵐ[μ] g)
  结论: AEStronglyMeasurable[m] g μ
  证明: ⟨hf.mk f, hf.stronglyMeasurable_mk, h.symm.trans hf.ae_eq_mk⟩

Depends on / 依赖: ae_eq_mk, h.symm.trans, hf.ae_eq_mk, hf.mk, hf.stronglyMeasurable_mk, stronglyMeasurable_mk
-/
theorem congr (hf : AEStronglyMeasurable[m] f μ) (h : f =ᵐ[μ] g) : AEStronglyMeasurable[m] g μ :=
  ⟨hf.mk f, hf.stronglyMeasurable_mk, h.symm.trans hf.ae_eq_mk⟩

/--
theorem `_root_.aestronglyMeasurable_congr` / 定理 `_root_.aestronglyMeasurable_congr`

English:
theorem _root_.aestronglyMeasurable_congr
  given: (h : f =ᵐ[μ] g)
  proof: ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩

中文:
定理 _root_.aestronglyMeasurable_congr
  条件: (h : f =ᵐ[μ] g)
  证明: ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩

Depends on / 依赖: h.symm, hf.congr, hg.congr
-/
theorem _root_.aestronglyMeasurable_congr (h : f =ᵐ[μ] g) :
    AEStronglyMeasurable[m] f μ ↔ AEStronglyMeasurable[m] g μ :=
  ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩

/--
theorem `mono_measure` / 定理 `mono_measure`

English:
theorem mono_measure
  given: {ν : Measure α} (hf : AEStronglyMeasurable[m] f μ) (h : ν <= μ)
  proof: ⟨hf.mk f, hf.stronglyMeasurable_mk, Eventually.filter_mono (ae_mono h) hf.ae_eq_mk⟩

中文:
定理 mono_measure
  条件: {ν : 测度 α} (hf : AEStronglyMeasurable[m] f μ) (h : ν <= μ)
  证明: ⟨hf.mk f, hf.stronglyMeasurable_mk, Eventually.filter_mono (ae_mono h) hf.ae_eq_mk⟩

Depends on / 依赖: Eventually, Eventually.filter_mono, ae_eq_mk, ae_mono, filter_mono, hf.ae_eq_mk, hf.mk, hf.stronglyMeasurable_mk, stronglyMeasurable_mk
-/
theorem mono_measure {ν : Measure α} (hf : AEStronglyMeasurable[m] f μ) (h : ν <= μ) :
    AEStronglyMeasurable[m] f ν :=
  ⟨hf.mk f, hf.stronglyMeasurable_mk, Eventually.filter_mono (ae_mono h) hf.ae_eq_mk⟩

/--
lemma `mono_ac` / 引理 `mono_ac`

English:
lemma mono_ac
  given: (h : ν ≪ μ) (hμ : AEStronglyMeasurable[m] f μ)
  proof: let ⟨g, hg, hg'⟩ := hμ; ⟨g, hg, h.ae_eq hg'⟩

中文:
引理 mono_ac
  条件: (h : ν ≪ μ) (hμ : AEStronglyMeasurable[m] f μ)
  证明: let ⟨g, hg, hg'⟩ := hμ; ⟨g, hg, h.ae_eq hg'⟩
-/
protected lemma mono_ac (h : ν ≪ μ) (hμ : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] f ν := let ⟨g, hg, hg'⟩ := hμ; ⟨g, hg, h.ae_eq hg'⟩

/--
theorem `mono_set` / 定理 `mono_set`

English:
theorem mono_set
  given: {s t} (h : s subseteq t) (ht : AEStronglyMeasurable[m] f (μ.restrict t))
  proof: ht.mono_measure (restrict_mono h le_rfl)

中文:
定理 mono_set
  条件: {s t} (h : s subseteq t) (ht : AEStronglyMeasurable[m] f (μ.restrict t))
  证明: ht.mono_measure (restrict_mono h le_rfl)

Depends on / 依赖: ht.mono_measure, le_rfl, mono_measure, restrict_mono
-/
theorem mono_set {s t} (h : s subseteq t) (ht : AEStronglyMeasurable[m] f (μ.restrict t)) :
    AEStronglyMeasurable[m] f (μ.restrict s) :=
  ht.mono_measure (restrict_mono h le_rfl)

/--
lemma `mono` / 引理 `mono`

English:
lemma mono
  given: {m'} (hm : m <= m') (hf : AEStronglyMeasurable[m] f μ)
  statement: AEStronglyMeasurable[m'] f μ
  proof: let ⟨f', hf'_meas, hff'⟩ := hf; ⟨f', hf'_meas.mono hm, hff'⟩

中文:
引理 mono
  条件: {m'} (hm : m <= m') (hf : AEStronglyMeasurable[m] f μ)
  结论: AEStronglyMeasurable[m'] f μ
  证明: let ⟨f', hf'_meas, hff'⟩ := hf; ⟨f', hf'_meas.mono hm, hff'⟩

Depends on / 依赖: _meas, _meas.mono
-/
lemma mono {m'} (hm : m <= m') (hf : AEStronglyMeasurable[m] f μ) : AEStronglyMeasurable[m'] f μ :=
  let ⟨f', hf'_meas, hff'⟩ := hf; ⟨f', hf'_meas.mono hm, hff'⟩

/--
lemma `of_trim` / 引理 `of_trim`

English:
lemma of_trim
  statement: {m₀' : MeasurableSpace α} (hm₀ : m₀' <= m₀)
  proof: by
  obtain ⟨g, hg_meas, hfg⟩ := hf; exact ⟨g, hg_meas, ae_eq_of_ae_eq_trim hfg⟩

@[fun_prop]

中文:
引理 of_trim
  结论: {m₀' : 可测空间 α} (hm₀ : m₀' <= m₀)
  证明: by
  obtain ⟨g, hg_meas, hfg⟩ := hf; exact ⟨g, hg_meas, ae_eq_of_ae_eq_trim hfg⟩

@[fun_prop]

Depends on / 依赖: ae_eq_of_ae_eq_trim, hg_meas
-/
lemma of_trim {m₀' : MeasurableSpace α} (hm₀ : m₀' <= m₀)
    (hf : AEStronglyMeasurable[m] f (μ.trim hm₀)) : AEStronglyMeasurable[m] f μ := by
  obtain ⟨g, hg_meas, hfg⟩ := hf; exact ⟨g, hg_meas, ae_eq_of_ae_eq_trim hfg⟩

@[fun_prop]
/--
theorem `restrict` / 定理 `restrict`

English:
theorem restrict
  given: (hfm : AEStronglyMeasurable[m] f μ) {s}
  proof: hfm.mono_measure Measure.restrict_le_self

中文:
定理 restrict
  条件: (hfm : AEStronglyMeasurable[m] f μ) {s}
  证明: hfm.mono_measure Measure.restrict_le_self
-/
protected theorem restrict (hfm : AEStronglyMeasurable[m] f μ) {s} :
    AEStronglyMeasurable[m] f (μ.restrict s) :=
  hfm.mono_measure Measure.restrict_le_self

/--
theorem `ae_mem_imp_eq_mk` / 定理 `ae_mem_imp_eq_mk`

English:
theorem ae_mem_imp_eq_mk
  given: {s} (h : AEStronglyMeasurable[m] f (μ.restrict s))
  proof: ae_imp_of_ae_restrict h.ae_eq_mk

中文:
定理 ae_mem_imp_eq_mk
  条件: {s} (h : AEStronglyMeasurable[m] f (μ.restrict s))
  证明: ae_imp_of_ae_restrict h.ae_eq_mk

Depends on / 依赖: ae_eq_mk, ae_imp_of_ae_restrict, h.ae_eq_mk
-/
theorem ae_mem_imp_eq_mk {s} (h : AEStronglyMeasurable[m] f (μ.restrict s)) :
    forallᵐ x ∂μ, x in s -> f x = h.mk f x :=
  ae_imp_of_ae_restrict h.ae_eq_mk

/-- The composition of a continuous function and an ae strongly measurable function is ae strongly
measurable. -/
@[fun_prop]
/--
theorem `_root_.Continuous.comp_aestronglyMeasurable` / 定理 `_root_.Continuous.comp_aestronglyMeasurable`

English:
theorem _root_.Continuous.comp_aestronglyMeasurable
  statement: {g : β -> γ} {f : α -> β} (hg : Continuous g)
  proof: ⟨_, hg.comp_stronglyMeasurable hf.stronglyMeasurable_mk, EventuallyEq.fun_comp hf.ae_eq_mk g⟩

中文:
定理 _root_.连续.comp_aestronglyMeasurable
  结论: {g : β -> γ} {f : α -> β} (hg : 连续 g)
  证明: ⟨_, hg.comp_stronglyMeasurable hf.stronglyMeasurable_mk, EventuallyEq.fun_comp hf.ae_eq_mk g⟩

Depends on / 依赖: EventuallyEq, EventuallyEq.fun_comp, ae_eq_mk, comp_stronglyMeasurable, fun_comp, hf.ae_eq_mk, hf.stronglyMeasurable_mk, hg.comp_stronglyMeasurable, stronglyMeasurable_mk
-/
theorem _root_.Continuous.comp_aestronglyMeasurable {g : β -> γ} {f : α -> β} (hg : Continuous g)
    (hf : AEStronglyMeasurable[m] f μ) : AEStronglyMeasurable[m] (fun x => g (f x)) μ :=
  ⟨_, hg.comp_stronglyMeasurable hf.stronglyMeasurable_mk, EventuallyEq.fun_comp hf.ae_eq_mk g⟩

/-- A continuous function from `α` to `β` is ae strongly measurable when one of the two spaces is
second countable. -/
@[fun_prop]
/--
theorem `_root_.Continuous.aestronglyMeasurable` / 定理 `_root_.Continuous.aestronglyMeasurable`

English:
theorem _root_.Continuous.aestronglyMeasurable
  statement: [TopologicalSpace α] [OpensMeasurableSpace α]
  proof: hf.stronglyMeasurable.aestronglyMeasurable

@[fun_prop]

中文:
定理 _root_.连续.aestronglyMeasurable
  结论: [拓扑空间 α] [OpensMeasurable空间 α]
  证明: hf.stronglyMeasurable.aestronglyMeasurable

@[fun_prop]

Depends on / 依赖: aestronglyMeasurable, hf.stronglyMeasurable.aestronglyMeasurable, stronglyMeasurable
-/
theorem _root_.Continuous.aestronglyMeasurable [TopologicalSpace α] [OpensMeasurableSpace α]
    [PseudoMetrizableSpace β] [SecondCountableTopologyEither α β] (hf : Continuous f) :
    AEStronglyMeasurable f μ :=
  hf.stronglyMeasurable.aestronglyMeasurable

@[fun_prop]
/--
theorem `fst` / 定理 `fst`

English:
theorem fst
  given: {f : α -> β × γ} (hf : AEStronglyMeasurable[m] f μ)
  proof: continuous_fst.comp_aestronglyMeasurable hf

@[fun_prop]

中文:
定理 fst
  条件: {f : α -> β × γ} (hf : AEStronglyMeasurable[m] f μ)
  证明: continuous_fst.comp_aestronglyMeasurable hf

@[fun_prop]
-/
protected theorem fst {f : α -> β × γ} (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] (fun x => (f x).1) μ :=
  continuous_fst.comp_aestronglyMeasurable hf

@[fun_prop]
/--
theorem `snd` / 定理 `snd`

English:
theorem snd
  given: {f : α -> β × γ} (hf : AEStronglyMeasurable[m] f μ)
  proof: continuous_snd.comp_aestronglyMeasurable hf

@[fun_prop]

中文:
定理 snd
  条件: {f : α -> β × γ} (hf : AEStronglyMeasurable[m] f μ)
  证明: continuous_snd.comp_aestronglyMeasurable hf

@[fun_prop]
-/
protected theorem snd {f : α -> β × γ} (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] (fun x => (f x).2) μ :=
  continuous_snd.comp_aestronglyMeasurable hf

@[fun_prop]
/--
theorem `prodMk` / 定理 `prodMk`

English:
theorem prodMk
  statement: {f : α -> β} {g : α -> γ} (hf : AEStronglyMeasurable[m] f μ)
  proof: ⟨fun x => (hf.mk f x, hg.mk g x), hf.stronglyMeasurable_mk.prodMk hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.prodMk hg.ae_eq_mk⟩

中文:
定理 prodMk
  结论: {f : α -> β} {g : α -> γ} (hf : AEStronglyMeasurable[m] f μ)
  证明: ⟨fun x => (hf.mk f x, hg.mk g x), hf.stronglyMeasurable_mk.prodMk hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.prodMk hg.ae_eq_mk⟩
-/
protected theorem prodMk {f : α -> β} {g : α -> γ} (hf : AEStronglyMeasurable[m] f μ)
    (hg : AEStronglyMeasurable[m] g μ) : AEStronglyMeasurable[m] (fun x => (f x, g x)) μ :=
  ⟨fun x => (hf.mk f x, hg.mk g x), hf.stronglyMeasurable_mk.prodMk hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.prodMk hg.ae_eq_mk⟩

/--
theorem `_root_.Continuous.comp_aestronglyMeasurable₂` / 定理 `_root_.Continuous.comp_aestronglyMeasurable₂`

English:
theorem _root_.Continuous.comp_aestronglyMeasurable₂
  proof: hg.comp_aestronglyMeasurable (hf.prodMk h'f)

中文:
定理 _root_.连续.comp_aestronglyMeasurable₂
  证明: hg.comp_aestronglyMeasurable (hf.prodMk h'f)

Depends on / 依赖: comp_aestronglyMeasurable, hf.prodMk, hg.comp_aestronglyMeasurable, prodMk
-/
theorem _root_.Continuous.comp_aestronglyMeasurable₂
    {β' : Type*} [TopologicalSpace β']
    {g : β -> β' -> γ} {f : α -> β} {f' : α -> β'} (hg : Continuous g.uncurry)
    (hf : AEStronglyMeasurable[m] f μ) (h'f : AEStronglyMeasurable[m] f' μ) :
    AEStronglyMeasurable[m] (fun x => g (f x) (f' x)) μ :=
  hg.comp_aestronglyMeasurable (hf.prodMk h'f)

/-- In a space with second countable topology, measurable implies ae strongly measurable. -/
@[fun_prop]
/--
theorem `_root_.Measurable.aestronglyMeasurable` / 定理 `_root_.Measurable.aestronglyMeasurable`

English:
theorem _root_.Measurable.aestronglyMeasurable
  proof: hf.stronglyMeasurable.aestronglyMeasurable

中文:
定理 _root_.可测.aestronglyMeasurable
  证明: hf.stronglyMeasurable.aestronglyMeasurable

Depends on / 依赖: aestronglyMeasurable, hf.stronglyMeasurable.aestronglyMeasurable, stronglyMeasurable
-/
theorem _root_.Measurable.aestronglyMeasurable
    [MeasurableSpace β] [PseudoMetrizableSpace β] [SecondCountableTopology β]
    [OpensMeasurableSpace β] (hf : Measurable[m] f) : AEStronglyMeasurable[m] f μ :=
  hf.stronglyMeasurable.aestronglyMeasurable

/--
lemma `of_measurableSpace_le_on` / 引理 `of_measurableSpace_le_on`

English:
lemma of_measurableSpace_le_on
  statement: {m' m₀ : MeasurableSpace α} {μ : Measure[m₀] α} [Zero β]
  proof: by
  have h_ind_eq : s.indicator (hf.mk f) =ᵐ[μ] f := by
refine Filter.EventuallyEq.trans ?_
      indicator_ae_eq_of_restrict_compl_ae_eq_zero (hm _ hs_m) hf_zero
    filter_upwards [hf.ae_eq_mk] with x hx
    by_cases hxs : x in s
    · simp [hxs, hx]
    · simp [hxs]
  suffices StronglyMeasurable

中文:
引理 of_measurableSpace_le_on
  结论: {m' m₀ : 可测空间 α} {μ : 测度[m₀] α} [零 β]
  证明: by
  have h_ind_eq : s.indicator (hf.mk f) =ᵐ[μ] f := by
refine Filter.EventuallyEq.trans ?_
      indicator_ae_eq_of_restrict_compl_ae_eq_zero (hm _ hs_m) hf_zero
    filter_upwards [hf.ae_eq_mk] with x hx
    by_cases hxs : x in s
    · simp [hxs, hx]
    · simp [hxs]
  suffices StronglyMeasurable

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.trans, Set.indicator_of_notMem, StronglyMeasurable, ae_eq_mk, aestronglyMeasurable, filter_upwards, h_ind_eq, hf.ae_eq_mk, hf.mk, hf.stronglyMeasurable_mk.indicator, hf_zero, hs_m, indicator, indicator_ae_eq_of_restrict_compl_ae_eq_zero, indicator_of_notMem, s.indicator, stronglyMeasurable_mk, stronglyMeasurable_of_measurableSpace_le_on
-/
lemma of_measurableSpace_le_on {m' m₀ : MeasurableSpace α} {μ : Measure[m₀] α} [Zero β]
    (hm : m <= m₀) {s : Set α} (hs_m : MeasurableSet[m] s)
    (hs : forall t, MeasurableSet[m] (s inter t) -> MeasurableSet[m'] (s inter t))
    (hf : AEStronglyMeasurable[m] f μ) (hf_zero : f =ᵐ[μ.restrict sᶜ] 0) :
    AEStronglyMeasurable[m'] f μ := by
  have h_ind_eq : s.indicator (hf.mk f) =ᵐ[μ] f := by
refine Filter.EventuallyEq.trans ?_
      indicator_ae_eq_of_restrict_compl_ae_eq_zero (hm _ hs_m) hf_zero
    filter_upwards [hf.ae_eq_mk] with x hx
    by_cases hxs : x in s
    · simp [hxs, hx]
    · simp [hxs]
  suffices StronglyMeasurable[m'] (s.indicator (hf.mk f)) from
    this.aestronglyMeasurable.congr h_ind_eq
  exact (hf.stronglyMeasurable_mk.indicator hs_m).stronglyMeasurable_of_measurableSpace_le_on hs_m
    hs fun x hxs => Set.indicator_of_notMem hxs _

section Arithmetic

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  statement: [Mul β] [ContinuousMul β] (hf : AEStronglyMeasurable[m] f μ)
  proof: ⟨hf.mk f * hg.mk g, by fun_prop, hf.ae_eq_mk.mul hg.ae_eq_mk⟩

@[to_additive (attr := fun_prop)]

中文:
定理 mul
  结论: [乘法 β] [连续乘法 β] (hf : AEStronglyMeasurable[m] f μ)
  证明: ⟨hf.mk f * hg.mk g, by fun_prop, hf.ae_eq_mk.mul hg.ae_eq_mk⟩

@[to_additive (attr := fun_prop)]
-/
protected theorem mul [Mul β] [ContinuousMul β] (hf : AEStronglyMeasurable[m] f μ)
    (hg : AEStronglyMeasurable[m] g μ) : AEStronglyMeasurable[m] (f * g) μ :=
  ⟨hf.mk f * hg.mk g, by fun_prop, hf.ae_eq_mk.mul hg.ae_eq_mk⟩

@[to_additive (attr := fun_prop)]
/--
theorem `mul_const` / 定理 `mul_const`

English:
theorem mul_const
  given: [Mul β] [ContinuousMul β] (hf : AEStronglyMeasurable[m] f μ) (c : β)
  proof: hf.mul aestronglyMeasurable_const

@[to_additive (attr := fun_prop)]

中文:
定理 mul_const
  条件: [乘法 β] [连续乘法 β] (hf : AEStronglyMeasurable[m] f μ) (c : β)
  证明: hf.mul aestronglyMeasurable_const

@[to_additive (attr := fun_prop)]
-/
protected theorem mul_const [Mul β] [ContinuousMul β] (hf : AEStronglyMeasurable[m] f μ) (c : β) :
    AEStronglyMeasurable[m] (fun x => f x * c) μ :=
  hf.mul aestronglyMeasurable_const

@[to_additive (attr := fun_prop)]
/--
theorem `const_mul` / 定理 `const_mul`

English:
theorem const_mul
  given: [Mul β] [ContinuousMul β] (hf : AEStronglyMeasurable[m] f μ) (c : β)
  proof: aestronglyMeasurable_const.mul hf

@[to_fun (attr := to_additive (attr := fun_prop))]

中文:
定理 const_mul
  条件: [乘法 β] [连续乘法 β] (hf : AEStronglyMeasurable[m] f μ) (c : β)
  证明: aestronglyMeasurable_const.mul hf

@[to_fun (attr := to_additive (attr := fun_prop))]
-/
protected theorem const_mul [Mul β] [ContinuousMul β] (hf : AEStronglyMeasurable[m] f μ) (c : β) :
    AEStronglyMeasurable[m] (fun x => c * f x) μ :=
  aestronglyMeasurable_const.mul hf

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `inv` / 定理 `inv`

English:
theorem inv
  given: [Inv β] [ContinuousInv β] (hf : AEStronglyMeasurable[m] f μ)
  proof: ⟨(hf.mk f)⁻¹, hf.stronglyMeasurable_mk.inv, hf.ae_eq_mk.inv⟩

@[to_fun (attr := fun_prop)]

中文:
定理 inv
  条件: [取逆 β] [连续取逆 β] (hf : AEStronglyMeasurable[m] f μ)
  证明: ⟨(hf.mk f)⁻¹, hf.stronglyMeasurable_mk.inv, hf.ae_eq_mk.inv⟩

@[to_fun (attr := fun_prop)]
-/
protected theorem inv [Inv β] [ContinuousInv β] (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] f⁻¹ μ :=
  ⟨(hf.mk f)⁻¹, hf.stronglyMeasurable_mk.inv, hf.ae_eq_mk.inv⟩

@[to_fun (attr := fun_prop)]
/--
theorem `inv₀` / 定理 `inv₀`

English:
theorem inv₀
  statement: [GroupWithZero β] [ContinuousInv₀ β] [MetrizableSpace β]
  proof: ⟨(hf.mk f)⁻¹, hf.stronglyMeasurable_mk.inv₀, hf.ae_eq_mk.inv⟩

@[to_fun (attr := to_additive (attr := fun_prop))]

中文:
定理 inv₀
  结论: [带零群 β] [余ntinuousInv₀ β] [Metrizable空间 β]
  证明: ⟨(hf.mk f)⁻¹, hf.stronglyMeasurable_mk.inv₀, hf.ae_eq_mk.inv⟩

@[to_fun (attr := to_additive (attr := fun_prop))]

Depends on / 依赖: ae_eq_mk, hf.ae_eq_mk.inv, hf.mk, hf.stronglyMeasurable_mk.inv, stronglyMeasurable_mk
-/
theorem inv₀ [GroupWithZero β] [ContinuousInv₀ β] [MetrizableSpace β]
    (hf : AEStronglyMeasurable[m] f μ) : AEStronglyMeasurable[m] f⁻¹ μ :=
  ⟨(hf.mk f)⁻¹, hf.stronglyMeasurable_mk.inv₀, hf.ae_eq_mk.inv⟩

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `div` / 定理 `div`

English:
theorem div
  statement: [Group β] [IsTopologicalGroup β] (hf : AEStronglyMeasurable[m] f μ)
  proof: ⟨hf.mk f / hg.mk g, hf.stronglyMeasurable_mk.div' hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.div hg.ae_eq_mk⟩

@[fun_prop]

中文:
定理 div
  结论: [群 β] [是拓扑群 β] (hf : AEStronglyMeasurable[m] f μ)
  证明: ⟨hf.mk f / hg.mk g, hf.stronglyMeasurable_mk.div' hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.div hg.ae_eq_mk⟩

@[fun_prop]
-/
protected theorem div [Group β] [IsTopologicalGroup β] (hf : AEStronglyMeasurable[m] f μ)
    (hg : AEStronglyMeasurable[m] g μ) : AEStronglyMeasurable[m] (f / g) μ :=
  ⟨hf.mk f / hg.mk g, hf.stronglyMeasurable_mk.div' hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.div hg.ae_eq_mk⟩

@[fun_prop]
/--
theorem `div₀` / 定理 `div₀`

English:
theorem div₀
  statement: [GroupWithZero β] [ContinuousMul β] [ContinuousInv₀ β] [MetrizableSpace β]
  proof: ⟨hf.mk f / hg.mk g, hf.stronglyMeasurable_mk.div hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.div hg.ae_eq_mk⟩

@[to_additive]

中文:
定理 div₀
  结论: [带零群 β] [连续乘法 β] [余ntinuousInv₀ β] [Metrizable空间 β]
  证明: ⟨hf.mk f / hg.mk g, hf.stronglyMeasurable_mk.div hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.div hg.ae_eq_mk⟩

@[to_additive]

Depends on / 依赖: ae_eq_mk, hf.ae_eq_mk.div, hf.mk, hf.stronglyMeasurable_mk.div, hg.ae_eq_mk, hg.mk, hg.stronglyMeasurable_mk, stronglyMeasurable_mk
-/
theorem div₀ [GroupWithZero β] [ContinuousMul β] [ContinuousInv₀ β] [MetrizableSpace β]
    (hf : AEStronglyMeasurable[m] f μ) (hg : AEStronglyMeasurable[m] g μ) :
    AEStronglyMeasurable[m] (f / g) μ :=
  ⟨hf.mk f / hg.mk g, hf.stronglyMeasurable_mk.div hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.div hg.ae_eq_mk⟩

@[to_additive]
/--
theorem `mul_iff_right` / 定理 `mul_iff_right`

English:
theorem mul_iff_right
  given: [CommGroup β] [IsTopologicalGroup β] (hf : AEStronglyMeasurable[m] f μ)
  proof: ⟨fun h => show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h => hf.mul h⟩

@[to_additive]

中文:
定理 mul_iff_right
  条件: [交换群 β] [是拓扑群 β] (hf : AEStronglyMeasurable[m] f μ)
  证明: ⟨fun h => show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h => hf.mul h⟩

@[to_additive]

Depends on / 依赖: h.mul, hf.inv, hf.mul, mul_inv_cancel_comm
-/
theorem mul_iff_right [CommGroup β] [IsTopologicalGroup β] (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] (f * g) μ ↔ AEStronglyMeasurable[m] g μ :=
  ⟨fun h => show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h => hf.mul h⟩

@[to_additive]
/--
theorem `mul_iff_left` / 定理 `mul_iff_left`

English:
theorem mul_iff_left
  given: [CommGroup β] [IsTopologicalGroup β] (hf : AEStronglyMeasurable[m] f μ)
  proof: mul_comm g f ▸ AEStronglyMeasurable.mul_iff_right hf

@[to_fun (attr := to_additive (attr := fun_prop))]

中文:
定理 mul_iff_left
  条件: [交换群 β] [是拓扑群 β] (hf : AEStronglyMeasurable[m] f μ)
  证明: mul_comm g f ▸ AEStronglyMeasurable.mul_iff_right hf

@[to_fun (attr := to_additive (attr := fun_prop))]

Depends on / 依赖: AEStronglyMeasurable, AEStronglyMeasurable.mul_iff_right, mul_comm, mul_iff_right
-/
theorem mul_iff_left [CommGroup β] [IsTopologicalGroup β] (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] (g * f) μ ↔ AEStronglyMeasurable[m] g μ :=
  mul_comm g f ▸ AEStronglyMeasurable.mul_iff_right hf

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  statement: {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α -> 𝕜}
  proof: continuous_smul.comp_aestronglyMeasurable (hf.prodMk hg)

@[to_additive (attr := to_fun (attr := fun_prop)) const_nsmul]

中文:
定理 smul
  结论: {𝕜} [拓扑空间 𝕜] [标量乘法 𝕜 β] [连续标量乘法 𝕜 β] {f : α -> 𝕜}
  证明: continuous_smul.comp_aestronglyMeasurable (hf.prodMk hg)

@[to_additive (attr := to_fun (attr := fun_prop)) const_nsmul]
-/
protected theorem smul {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α -> 𝕜}
    {g : α -> β} (hf : AEStronglyMeasurable[m] f μ) (hg : AEStronglyMeasurable[m] g μ) :
    AEStronglyMeasurable[m] (f • g) μ :=
  continuous_smul.comp_aestronglyMeasurable (hf.prodMk hg)

@[to_additive (attr := to_fun (attr := fun_prop)) const_nsmul]
/--
theorem `pow` / 定理 `pow`

English:
theorem pow
  given: [Monoid β] [ContinuousMul β] (hf : AEStronglyMeasurable[m] f μ) (n : Nat)
  proof: ⟨hf.mk f ^ n, hf.stronglyMeasurable_mk.pow _, hf.ae_eq_mk.pow_const _⟩

@[to_additive (attr := to_fun (attr := fun_prop))]

中文:
定理 pow
  条件: [幺半群 β] [连续乘法 β] (hf : AEStronglyMeasurable[m] f μ) (n : 自然数)
  证明: ⟨hf.mk f ^ n, hf.stronglyMeasurable_mk.pow _, hf.ae_eq_mk.pow_const _⟩

@[to_additive (attr := to_fun (attr := fun_prop))]
-/
protected theorem pow [Monoid β] [ContinuousMul β] (hf : AEStronglyMeasurable[m] f μ) (n : Nat) :
    AEStronglyMeasurable[m] (f ^ n) μ :=
  ⟨hf.mk f ^ n, hf.stronglyMeasurable_mk.pow _, hf.ae_eq_mk.pow_const _⟩

@[to_additive (attr := to_fun (attr := fun_prop))]
/--
theorem `const_smul` / 定理 `const_smul`

English:
theorem const_smul
  statement: {𝕜} [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β]
  proof: ⟨c • hf.mk f, hf.stronglyMeasurable_mk.const_smul c, hf.ae_eq_mk.const_smul c⟩

@[deprecated (since := "2026-06-26")]
alias const_smul' := AEStronglyMeasurable.fun_const_smul

@[deprecated (since := "2026-06-26")]
alias const_vadd' := AEStronglyMeasurable.fun_const_vadd

@[to_additive (attr := fun_p

中文:
定理 const_smul
  结论: {𝕜} [标量乘法 𝕜 β] [连续常数标量乘法 𝕜 β]
  证明: ⟨c • hf.mk f, hf.stronglyMeasurable_mk.const_smul c, hf.ae_eq_mk.const_smul c⟩

@[deprecated (since := "2026-06-26")]
alias const_smul' := AEStronglyMeasurable.fun_const_smul

@[deprecated (since := "2026-06-26")]
alias const_vadd' := AEStronglyMeasurable.fun_const_vadd

@[to_additive (attr := fun_p
-/
protected theorem const_smul {𝕜} [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β]
    (hf : AEStronglyMeasurable[m] f μ) (c : 𝕜) : AEStronglyMeasurable[m] (c • f) μ :=
  ⟨c • hf.mk f, hf.stronglyMeasurable_mk.const_smul c, hf.ae_eq_mk.const_smul c⟩

@[deprecated (since := "2026-06-26")]
alias const_smul' := AEStronglyMeasurable.fun_const_smul

@[deprecated (since := "2026-06-26")]
alias const_vadd' := AEStronglyMeasurable.fun_const_vadd

@[to_additive (attr := fun_prop)]
/--
theorem `smul_const` / 定理 `smul_const`

English:
theorem smul_const
  statement: {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α -> 𝕜}
  proof: continuous_smul.comp_aestronglyMeasurable (hf.prodMk aestronglyMeasurable_const)

中文:
定理 smul_const
  结论: {𝕜} [拓扑空间 𝕜] [标量乘法 𝕜 β] [连续标量乘法 𝕜 β] {f : α -> 𝕜}
  证明: continuous_smul.comp_aestronglyMeasurable (hf.prodMk aestronglyMeasurable_const)
-/
protected theorem smul_const {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α -> 𝕜}
    (hf : AEStronglyMeasurable[m] f μ) (c : β) : AEStronglyMeasurable[m] (fun x => f x • c) μ :=
  continuous_smul.comp_aestronglyMeasurable (hf.prodMk aestronglyMeasurable_const)

end Arithmetic

section Star

@[fun_prop]
/--
theorem `star` / 定理 `star`

English:
theorem star
  statement: {R : Type*} [TopologicalSpace R] [Star R] [ContinuousStar R] {f : α -> R}
  proof: ⟨star (hf.mk f), hf.stronglyMeasurable_mk.star, hf.ae_eq_mk.star⟩

中文:
定理 star
  结论: {R : 类型} [拓扑空间 R] [对合 R] [余ntinuousStar R] {f : α -> R}
  证明: ⟨star (hf.mk f), hf.stronglyMeasurable_mk.star, hf.ae_eq_mk.star⟩
-/
protected theorem star {R : Type*} [TopologicalSpace R] [Star R] [ContinuousStar R] {f : α -> R}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (star f) μ :=
  ⟨star (hf.mk f), hf.stronglyMeasurable_mk.star, hf.ae_eq_mk.star⟩

end Star

section Order

@[to_fun (attr := fun_prop)]
/--
theorem `sup` / 定理 `sup`

English:
theorem sup
  statement: [SemilatticeSup β] [ContinuousSup β] (hf : AEStronglyMeasurable f μ)
  proof: ⟨hf.mk f ⊔ hg.mk g, hf.stronglyMeasurable_mk.sup hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.sup hg.ae_eq_mk⟩

@[to_fun (attr := fun_prop)]

中文:
定理 上确界
  结论: [SemilatticeSup β] [余ntinuousSup β] (hf : AEStronglyMeasurable f μ)
  证明: ⟨hf.mk f ⊔ hg.mk g, hf.stronglyMeasurable_mk.sup hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.sup hg.ae_eq_mk⟩

@[to_fun (attr := fun_prop)]
-/
protected theorem sup [SemilatticeSup β] [ContinuousSup β] (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) : AEStronglyMeasurable (f ⊔ g) μ :=
  ⟨hf.mk f ⊔ hg.mk g, hf.stronglyMeasurable_mk.sup hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.sup hg.ae_eq_mk⟩

@[to_fun (attr := fun_prop)]
/--
theorem `inf` / 定理 `inf`

English:
theorem inf
  statement: [SemilatticeInf β] [ContinuousInf β] (hf : AEStronglyMeasurable f μ)
  proof: ⟨hf.mk f ⊓ hg.mk g, hf.stronglyMeasurable_mk.inf hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.inf hg.ae_eq_mk⟩

@[to_additive (attr := fun_prop)]

中文:
定理 下确界
  结论: [SemilatticeInf β] [余ntinuousInf β] (hf : AEStronglyMeasurable f μ)
  证明: ⟨hf.mk f ⊓ hg.mk g, hf.stronglyMeasurable_mk.inf hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.inf hg.ae_eq_mk⟩

@[to_additive (attr := fun_prop)]
-/
protected theorem inf [SemilatticeInf β] [ContinuousInf β] (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) : AEStronglyMeasurable (f ⊓ g) μ :=
  ⟨hf.mk f ⊓ hg.mk g, hf.stronglyMeasurable_mk.inf hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.inf hg.ae_eq_mk⟩

@[to_additive (attr := fun_prop)]
/--
theorem `oneLePart` / 定理 `oneLePart`

English:
theorem oneLePart
  statement: [Group β] [Lattice β] [ContinuousSup β]
  proof: hf.sup aestronglyMeasurable_const

@[to_additive (attr := fun_prop)]

中文:
定理 oneLePart
  结论: [群 β] [格 β] [余ntinuousSup β]
  证明: hf.sup aestronglyMeasurable_const

@[to_additive (attr := fun_prop)]
-/
protected theorem oneLePart [Group β] [Lattice β] [ContinuousSup β]
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => oneLePart (f x)) μ :=
  hf.sup aestronglyMeasurable_const

@[to_additive (attr := fun_prop)]
/--
theorem `leOnePart` / 定理 `leOnePart`

English:
theorem leOnePart
  statement: [Group β] [Lattice β] [ContinuousSup β] [ContinuousInv β]
  proof: hf.inv.sup aestronglyMeasurable_const

中文:
定理 leOnePart
  结论: [群 β] [格 β] [余ntinuousSup β] [连续取逆 β]
  证明: hf.inv.sup aestronglyMeasurable_const
-/
protected theorem leOnePart [Group β] [Lattice β] [ContinuousSup β] [ContinuousInv β]
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => leOnePart (f x)) μ :=
  hf.inv.sup aestronglyMeasurable_const

end Order

/-!
### Big operators: `∏` and `∑`
-/


section Monoid

variable {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M]

-- TODO: `fun_prop` cannot use lemmas with a condition quantifying over the function
@[to_additive (attr := fun_prop)]
/--
theorem `_root_.List.aestronglyMeasurable_prod` / 定理 `_root_.List.aestronglyMeasurable_prod`

English:
theorem _root_.List.aestronglyMeasurable_prod
  statement: (l : List (α -> M))
  proof: by
  induction l with
  | nil => exact aestronglyMeasurable_one
  | cons f l ihl =>
    rw [List.forall_mem_cons] at hl
    rw [List.prod_cons]
    exact hl.1.mul (ihl hl.2)

@[to_additive (attr := fun_prop)]

中文:
定理 _root_.列表.aestronglyMeasurable_prod
  结论: (l : 列表 (α -> M))
  证明: by
  induction l with
  | nil => exact aestronglyMeasurable_one
  | cons f l ihl =>
    rw [List.forall_mem_cons] at hl
    rw [List.prod_cons]
    exact hl.1.mul (ihl hl.2)

@[to_additive (attr := fun_prop)]

Depends on / 依赖: List.forall_mem_cons, List.prod_cons, aestronglyMeasurable_one, forall_mem_cons, prod_cons
-/
theorem _root_.List.aestronglyMeasurable_prod (l : List (α -> M))
    (hl : forall f in l, AEStronglyMeasurable f μ) : AEStronglyMeasurable l.prod μ := by
  induction l with
  | nil => exact aestronglyMeasurable_one
  | cons f l ihl =>
    rw [List.forall_mem_cons] at hl
    rw [List.prod_cons]
    exact hl.1.mul (ihl hl.2)

@[to_additive (attr := fun_prop)]
/--
theorem `_root_.List.aestronglyMeasurable_fun_prod` / 定理 `_root_.List.aestronglyMeasurable_fun_prod`

English:
theorem _root_.List.aestronglyMeasurable_fun_prod
  proof: by
  simpa only [← Pi.list_prod_apply] using l.aestronglyMeasurable_prod hl

中文:
定理 _root_.列表.aestronglyMeasurable_fun_prod
  证明: by
  simpa only [← Pi.list_prod_apply] using l.aestronglyMeasurable_prod hl

Depends on / 依赖: Pi.list_prod_apply, aestronglyMeasurable_prod, l.aestronglyMeasurable_prod, list_prod_apply
-/
theorem _root_.List.aestronglyMeasurable_fun_prod
    (l : List (α -> M)) (hl : forall f in l, AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => (l.map fun f : α -> M => f x).prod) μ := by
  simpa only [← Pi.list_prod_apply] using l.aestronglyMeasurable_prod hl

end Monoid

section CommMonoid

variable {M : Type*} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]

@[to_additive (attr := fun_prop)]
/--
theorem `_root_.Multiset.aestronglyMeasurable_prod` / 定理 `_root_.Multiset.aestronglyMeasurable_prod`

English:
theorem _root_.Multiset.aestronglyMeasurable_prod
  statement: (l : Multiset (α -> M))
  proof: by
  rcases l with ⟨l⟩
  simpa using l.aestronglyMeasurable_prod (by simpa using hl)

@[to_additive (attr := fun_prop)]

中文:
定理 _root_.Multiset.aestronglyMeasurable_prod
  结论: (l : Multiset (α -> M))
  证明: by
  rcases l with ⟨l⟩
  simpa using l.aestronglyMeasurable_prod (by simpa using hl)

@[to_additive (attr := fun_prop)]

Depends on / 依赖: aestronglyMeasurable_prod, l.aestronglyMeasurable_prod
-/
theorem _root_.Multiset.aestronglyMeasurable_prod (l : Multiset (α -> M))
    (hl : forall f in l, AEStronglyMeasurable f μ) : AEStronglyMeasurable l.prod μ := by
  rcases l with ⟨l⟩
  simpa using l.aestronglyMeasurable_prod (by simpa using hl)

@[to_additive (attr := fun_prop)]
/--
theorem `_root_.Multiset.aestronglyMeasurable_fun_prod` / 定理 `_root_.Multiset.aestronglyMeasurable_fun_prod`

English:
theorem _root_.Multiset.aestronglyMeasurable_fun_prod
  statement: (s : Multiset (α -> M))
  proof: by
  simpa only [← Pi.multiset_prod_apply] using s.aestronglyMeasurable_prod hs

@[to_additive (attr := fun_prop)]

中文:
定理 _root_.Multiset.aestronglyMeasurable_fun_prod
  结论: (s : Multiset (α -> M))
  证明: by
  simpa only [← Pi.multiset_prod_apply] using s.aestronglyMeasurable_prod hs

@[to_additive (attr := fun_prop)]

Depends on / 依赖: Pi.multiset_prod_apply, aestronglyMeasurable_prod, multiset_prod_apply, s.aestronglyMeasurable_prod
-/
theorem _root_.Multiset.aestronglyMeasurable_fun_prod (s : Multiset (α -> M))
    (hs : forall f in s, AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => (s.map fun f : α -> M => f x).prod) μ := by
  simpa only [← Pi.multiset_prod_apply] using s.aestronglyMeasurable_prod hs

@[to_additive (attr := fun_prop)]
/--
theorem `_root_.Finset.aestronglyMeasurable_prod` / 定理 `_root_.Finset.aestronglyMeasurable_prod`

English:
theorem _root_.Finset.aestronglyMeasurable_prod
  statement: {ι : Type*} {f : ι -> α -> M} (s : Finset ι)
  proof: Multiset.aestronglyMeasurable_prod _ fun _g hg =>
    let ⟨_i, hi, hg⟩ := Multiset.mem_map.1 hg
    hg ▸ hf _ hi

@[to_additive (attr := fun_prop)]

中文:
定理 _root_.有限集.aestronglyMeasurable_prod
  结论: {ι : 类型} {f : ι -> α -> M} (s : 有限集 ι)
  证明: Multiset.aestronglyMeasurable_prod _ fun _g hg =>
    let ⟨_i, hi, hg⟩ := Multiset.mem_map.1 hg
    hg ▸ hf _ hi

@[to_additive (attr := fun_prop)]

Depends on / 依赖: Multiset, Multiset.aestronglyMeasurable_prod, Multiset.mem_map, aestronglyMeasurable_prod, mem_map
-/
theorem _root_.Finset.aestronglyMeasurable_prod {ι : Type*} {f : ι -> α -> M} (s : Finset ι)
    (hf : forall i in s, AEStronglyMeasurable (f i) μ) : AEStronglyMeasurable (∏ i in s, f i) μ :=
  Multiset.aestronglyMeasurable_prod _ fun _g hg =>
    let ⟨_i, hi, hg⟩ := Multiset.mem_map.1 hg
    hg ▸ hf _ hi

@[to_additive (attr := fun_prop)]
/--
theorem `_root_.Finset.aestronglyMeasurable_fun_prod` / 定理 `_root_.Finset.aestronglyMeasurable_fun_prod`

English:
theorem _root_.Finset.aestronglyMeasurable_fun_prod
  statement: {ι : Type*} {f : ι -> α -> M} (s : Finset ι)
  proof: by
  simpa only [← Finset.prod_apply] using s.aestronglyMeasurable_prod hf

中文:
定理 _root_.有限集.aestronglyMeasurable_fun_prod
  结论: {ι : 类型} {f : ι -> α -> M} (s : 有限集 ι)
  证明: by
  simpa only [← Finset.prod_apply] using s.aestronglyMeasurable_prod hf

Depends on / 依赖: Finset, Finset.prod_apply, aestronglyMeasurable_prod, prod_apply, s.aestronglyMeasurable_prod
-/
theorem _root_.Finset.aestronglyMeasurable_fun_prod {ι : Type*} {f : ι -> α -> M} (s : Finset ι)
    (hf : forall i in s, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun a => ∏ i in s, f i a) μ := by
  simpa only [← Finset.prod_apply] using s.aestronglyMeasurable_prod hf

end CommMonoid

section SecondCountableAEStronglyMeasurable

variable [MeasurableSpace β]

/-- In a space with second countable topology, measurable implies strongly measurable. -/
@[fun_prop]
/--
theorem `_root_.AEMeasurable.aestronglyMeasurable` / 定理 `_root_.AEMeasurable.aestronglyMeasurable`

English:
theorem _root_.AEMeasurable.aestronglyMeasurable
  statement: [PseudoMetrizableSpace β] [OpensMeasurableSpace β]
  proof: ⟨hf.mk f, hf.measurable_mk.stronglyMeasurable, hf.ae_eq_mk⟩

@[fun_prop]

中文:
定理 _root_.几乎处处可测.aestronglyMeasurable
  结论: [PseudoMetrizable空间 β] [OpensMeasurable空间 β]
  证明: ⟨hf.mk f, hf.measurable_mk.stronglyMeasurable, hf.ae_eq_mk⟩

@[fun_prop]

Depends on / 依赖: ae_eq_mk, hf.ae_eq_mk, hf.measurable_mk.stronglyMeasurable, hf.mk, measurable_mk, stronglyMeasurable
-/
theorem _root_.AEMeasurable.aestronglyMeasurable [PseudoMetrizableSpace β] [OpensMeasurableSpace β]
    [SecondCountableTopology β] (hf : AEMeasurable f μ) : AEStronglyMeasurable f μ :=
  ⟨hf.mk f, hf.measurable_mk.stronglyMeasurable, hf.ae_eq_mk⟩

@[fun_prop]
/--
theorem `_root_.aestronglyMeasurable_id` / 定理 `_root_.aestronglyMeasurable_id`

English:
theorem _root_.aestronglyMeasurable_id
  statement: {α : Type*} [TopologicalSpace α] [PseudoMetrizableSpace α]
  proof: aemeasurable_id.aestronglyMeasurable

中文:
定理 _root_.aestronglyMeasurable_id
  结论: {α : 类型} [拓扑空间 α] [PseudoMetrizable空间 α]
  证明: aemeasurable_id.aestronglyMeasurable

Depends on / 依赖: aemeasurable_id, aemeasurable_id.aestronglyMeasurable, aestronglyMeasurable
-/
theorem _root_.aestronglyMeasurable_id {α : Type*} [TopologicalSpace α] [PseudoMetrizableSpace α]
    {_ : MeasurableSpace α} [OpensMeasurableSpace α] [SecondCountableTopology α] {μ : Measure α} :
    AEStronglyMeasurable (id : α -> α) μ :=
  aemeasurable_id.aestronglyMeasurable

/--
theorem `_root_.aestronglyMeasurable_iff_aemeasurable` / 定理 `_root_.aestronglyMeasurable_iff_aemeasurable`

English:
theorem _root_.aestronglyMeasurable_iff_aemeasurable
  statement: [PseudoMetrizableSpace β] [BorelSpace β]
  proof: ⟨fun h => h.aemeasurable, fun h => h.aestronglyMeasurable⟩

中文:
定理 _root_.aestronglyMeasurable_iff_aemeasurable
  结论: [PseudoMetrizable空间 β] [Borel空间 β]
  证明: ⟨fun h => h.aemeasurable, fun h => h.aestronglyMeasurable⟩

Depends on / 依赖: aemeasurable, aestronglyMeasurable, h.aemeasurable, h.aestronglyMeasurable
-/
theorem _root_.aestronglyMeasurable_iff_aemeasurable [PseudoMetrizableSpace β] [BorelSpace β]
    [SecondCountableTopology β] : AEStronglyMeasurable f μ ↔ AEMeasurable f μ :=
  ⟨fun h => h.aemeasurable, fun h => h.aestronglyMeasurable⟩

end SecondCountableAEStronglyMeasurable

@[fun_prop]
/--
theorem `dist` / 定理 `dist`

English:
theorem dist
  statement: {β : Type*} [PseudoMetricSpace β] {f g : α -> β}
  proof: continuous_dist.comp_aestronglyMeasurable (hf.prodMk hg)

@[fun_prop]

中文:
定理 dist
  结论: {β : 类型} [伪度量空间 β] {f g : α -> β}
  证明: continuous_dist.comp_aestronglyMeasurable (hf.prodMk hg)

@[fun_prop]
-/
protected theorem dist {β : Type*} [PseudoMetricSpace β] {f g : α -> β}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun x => dist (f x) (g x)) μ :=
  continuous_dist.comp_aestronglyMeasurable (hf.prodMk hg)

@[fun_prop]
/--
theorem `norm` / 定理 `norm`

English:
theorem norm
  statement: {β : Type*} [SeminormedAddCommGroup β] {f : α -> β}
  proof: continuous_norm.comp_aestronglyMeasurable hf

@[fun_prop]

中文:
定理 norm
  结论: {β : 类型} [SeminormedAddComm群 β] {f : α -> β}
  证明: continuous_norm.comp_aestronglyMeasurable hf

@[fun_prop]
-/
protected theorem norm {β : Type*} [SeminormedAddCommGroup β] {f : α -> β}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun x => ‖f x‖) μ :=
  continuous_norm.comp_aestronglyMeasurable hf

@[fun_prop]
/--
theorem `nnnorm` / 定理 `nnnorm`

English:
theorem nnnorm
  statement: {β : Type*} [SeminormedAddCommGroup β] {f : α -> β}
  proof: continuous_nnnorm.comp_aestronglyMeasurable hf

中文:
定理 nnnorm
  结论: {β : 类型} [SeminormedAddComm群 β] {f : α -> β}
  证明: continuous_nnnorm.comp_aestronglyMeasurable hf
-/
protected theorem nnnorm {β : Type*} [SeminormedAddCommGroup β] {f : α -> β}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun x => ‖f x‖₊) μ :=
  continuous_nnnorm.comp_aestronglyMeasurable hf

/-- The `enorm` of a strongly a.e. measurable function is a.e. measurable.

Note that unlike `AEStronglyMeasurable.norm` and `AEStronglyMeasurable.nnnorm`, this lemma proves
a.e. measurability, **not** a.e. strong measurability. This is an intentional decision:
for functions taking values in `ℝ≥0∞`, a.e. measurability is much more useful than
a.e. strong measurability. -/
@[fun_prop]
/--
theorem `enorm` / 定理 `enorm`

English:
theorem enorm
  statement: {β : Type*} [TopologicalSpace β] [ContinuousENorm β] {f : α -> β}
  proof: (continuous_enorm.comp_aestronglyMeasurable hf).aemeasurable

中文:
定理 enorm
  结论: {β : 类型} [拓扑空间 β] [余ntinuousE范数 β] {f : α -> β}
  证明: (continuous_enorm.comp_aestronglyMeasurable hf).aemeasurable
-/
protected theorem enorm {β : Type*} [TopologicalSpace β] [ContinuousENorm β] {f : α -> β}
    (hf : AEStronglyMeasurable f μ) : AEMeasurable (‖f ·‖ₑ) μ :=
  (continuous_enorm.comp_aestronglyMeasurable hf).aemeasurable

/-- Given a.e. strongly measurable functions `f` and `g`, `edist f g` is measurable.

Note that this lemma proves a.e. measurability, **not** a.e. strong measurability.
This is an intentional decision: for functions taking values in ℝ≥0∞,
a.e. measurability is much more useful than a.e. strong measurability. -/
@[fun_prop]
/--
theorem `edist` / 定理 `edist`

English:
theorem edist
  statement: {β : Type*} [PseudoMetricSpace β] {f g : α -> β}
  proof: (continuous_edist.comp_aestronglyMeasurable (hf.prodMk hg)).aemeasurable

@[fun_prop]

中文:
定理 edist
  结论: {β : 类型} [伪度量空间 β] {f g : α -> β}
  证明: (continuous_edist.comp_aestronglyMeasurable (hf.prodMk hg)).aemeasurable

@[fun_prop]
-/
protected theorem edist {β : Type*} [PseudoMetricSpace β] {f g : α -> β}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEMeasurable (fun a => edist (f a) (g a)) μ :=
  (continuous_edist.comp_aestronglyMeasurable (hf.prodMk hg)).aemeasurable

@[fun_prop]
/--
theorem `real_toNNReal` / 定理 `real_toNNReal`

English:
theorem real_toNNReal
  given: {f : α -> Real} (hf : AEStronglyMeasurable f μ)
  proof: continuous_real_toNNReal.comp_aestronglyMeasurable hf

中文:
定理 real_toNN实数
  条件: {f : α -> 实数} (hf : AEStronglyMeasurable f μ)
  证明: continuous_real_toNNReal.comp_aestronglyMeasurable hf
-/
protected theorem real_toNNReal {f : α -> Real} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => (f x).toNNReal) μ :=
  continuous_real_toNNReal.comp_aestronglyMeasurable hf

/--
theorem `_root_.aestronglyMeasurable_indicator_iff` / 定理 `_root_.aestronglyMeasurable_indicator_iff`

English:
theorem _root_.aestronglyMeasurable_indicator_iff
  given: [Zero β] {s : Set α} (hs : MeasurableSet s)
  proof: by
  constructor
  · intro h
    exact (h.mono_measure Measure.restrict_le_self).congr (indicator_ae_eq_restrict hs)
  · intro h
    refine ⟨indicator s (h.mk f), h.stronglyMeasurable_mk.indicator hs, ?_⟩
    have A : s.indicator f =ᵐ[μ.restrict s] s.indicator (h.mk f) :=
      (indicator_ae_eq_rest

中文:
定理 _root_.aestronglyMeasurable_indicator_iff
  条件: [零 β] {s : 集合 α} (hs : 可测集 s)
  证明: by
  constructor
  · intro h
    exact (h.mono_measure Measure.restrict_le_self).congr (indicator_ae_eq_restrict hs)
  · intro h
    refine ⟨indicator s (h.mk f), h.stronglyMeasurable_mk.indicator hs, ?_⟩
    have A : s.indicator f =ᵐ[μ.restrict s] s.indicator (h.mk f) :=
      (indicator_ae_eq_rest

Depends on / 依赖: Measure, Measure.restrict_le_self, ae_eq_mk, h.ae_eq_mk.trans, h.mk, h.mono_measure, h.stronglyMeasurable_mk.indicator, indicator, indicator_ae_eq_restrict, indicator_ae_eq_restrict_compl, mono_measure, restrict, restrict_le_self, s.indicator, stronglyMeasurable_mk
-/
theorem _root_.aestronglyMeasurable_indicator_iff [Zero β] {s : Set α} (hs : MeasurableSet s) :
    AEStronglyMeasurable (indicator s f) μ ↔ AEStronglyMeasurable f (μ.restrict s) := by
  constructor
  · intro h
    exact (h.mono_measure Measure.restrict_le_self).congr (indicator_ae_eq_restrict hs)
  · intro h
    refine ⟨indicator s (h.mk f), h.stronglyMeasurable_mk.indicator hs, ?_⟩
    have A : s.indicator f =ᵐ[μ.restrict s] s.indicator (h.mk f) :=
      (indicator_ae_eq_restrict hs).trans (h.ae_eq_mk.trans <| (indicator_ae_eq_restrict hs).symm)
    have B : s.indicator f =ᵐ[μ.restrict sᶜ] s.indicator (h.mk f) :=
      (indicator_ae_eq_restrict_compl hs).trans (indicator_ae_eq_restrict_compl hs).symm
    exact ae_of_ae_restrict_of_ae_restrict_compl _ A B

/--
theorem `_root_.aestronglyMeasurable_indicator_iff₀` / 定理 `_root_.aestronglyMeasurable_indicator_iff₀`

English:
theorem _root_.aestronglyMeasurable_indicator_iff₀
  proof: by
  rw [← aestronglyMeasurable_congr (indicator_ae_eq_of_ae_eq_set hs.toMeasurable_ae_eq)]; rw [aestronglyMeasurable_indicator_iff (measurableSet_toMeasurable ..)]; rw [restrict_congr_set hs.toMeasurable_ae_eq]

@[fun_prop]

中文:
定理 _root_.aestronglyMeasurable_indicator_iff₀
  证明: by
  rw [← aestronglyMeasurable_congr (indicator_ae_eq_of_ae_eq_set hs.toMeasurable_ae_eq)]; rw [aestronglyMeasurable_indicator_iff (measurableSet_toMeasurable ..)]; rw [restrict_congr_set hs.toMeasurable_ae_eq]

@[fun_prop]

Depends on / 依赖: aestronglyMeasurable_congr, aestronglyMeasurable_indicator_iff, hs.toMeasurable_ae_eq, indicator_ae_eq_of_ae_eq_set, measurableSet_toMeasurable, restrict_congr_set, toMeasurable_ae_eq
-/
theorem _root_.aestronglyMeasurable_indicator_iff₀
    [Zero β] {s : Set α} (hs : NullMeasurableSet s μ) :
    AEStronglyMeasurable (indicator s f) μ ↔ AEStronglyMeasurable f (μ.restrict s) := by
  rw [← aestronglyMeasurable_congr (indicator_ae_eq_of_ae_eq_set hs.toMeasurable_ae_eq)]; rw [aestronglyMeasurable_indicator_iff (measurableSet_toMeasurable ..)]; rw [restrict_congr_set hs.toMeasurable_ae_eq]

@[fun_prop]
/--
theorem `indicator` / 定理 `indicator`

English:
theorem indicator
  statement: [Zero β] (hfm : AEStronglyMeasurable f μ) {s : Set α}
  proof: (aestronglyMeasurable_indicator_iff hs).mpr hfm.restrict

@[fun_prop]

中文:
定理 indicator
  结论: [零 β] (hfm : AEStronglyMeasurable f μ) {s : 集合 α}
  证明: (aestronglyMeasurable_indicator_iff hs).mpr hfm.restrict

@[fun_prop]
-/
protected theorem indicator [Zero β] (hfm : AEStronglyMeasurable f μ) {s : Set α}
    (hs : MeasurableSet s) : AEStronglyMeasurable (s.indicator f) μ :=
  (aestronglyMeasurable_indicator_iff hs).mpr hfm.restrict

@[fun_prop]
/--
theorem `indicator₀` / 定理 `indicator₀`

English:
theorem indicator₀
  statement: [Zero β] (hfm : AEStronglyMeasurable f μ) {s : Set α}
  proof: (aestronglyMeasurable_indicator_iff₀ hs).2 hfm.restrict

中文:
定理 indicator₀
  结论: [零 β] (hfm : AEStronglyMeasurable f μ) {s : 集合 α}
  证明: (aestronglyMeasurable_indicator_iff₀ hs).2 hfm.restrict
-/
protected theorem indicator₀ [Zero β] (hfm : AEStronglyMeasurable f μ) {s : Set α}
    (hs : NullMeasurableSet s μ) : AEStronglyMeasurable (s.indicator f) μ :=
  (aestronglyMeasurable_indicator_iff₀ hs).2 hfm.restrict

/--
theorem `nullMeasurableSet_eq_fun` / 定理 `nullMeasurableSet_eq_fun`

English:
theorem nullMeasurableSet_eq_fun
  statement: {E} [TopologicalSpace E] [MetrizableSpace E] {f g : α -> E}
  proof: by
  apply
    (hf.stronglyMeasurable_mk.measurableSet_eq_fun
          hg.stronglyMeasurable_mk).nullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
  change (hf.mk f x = hg.mk g x) = (f x = g x)
  simp only [hfx, hgx]

@[to_additive]

中文:
定理 nullMeasurableSet_eq_fun
  结论: {E} [拓扑空间 E] [Metrizable空间 E] {f g : α -> E}
  证明: by
  apply
    (hf.stronglyMeasurable_mk.measurableSet_eq_fun
          hg.stronglyMeasurable_mk).nullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
  change (hf.mk f x = hg.mk g x) = (f x = g x)
  simp only [hfx, hgx]

@[to_additive]

Depends on / 依赖: ae_eq_mk, filter_upwards, hf.ae_eq_mk, hf.mk, hf.stronglyMeasurable_mk.measurableSet_eq_fun, hg.ae_eq_mk, hg.mk, hg.stronglyMeasurable_mk, measurableSet_eq_fun, nullMeasurableSet, nullMeasurableSet.congr, stronglyMeasurable_mk
-/
theorem nullMeasurableSet_eq_fun {E} [TopologicalSpace E] [MetrizableSpace E] {f g : α -> E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    NullMeasurableSet { x | f x = g x } μ := by
  apply
    (hf.stronglyMeasurable_mk.measurableSet_eq_fun
          hg.stronglyMeasurable_mk).nullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
  change (hf.mk f x = hg.mk g x) = (f x = g x)
  simp only [hfx, hgx]

@[to_additive]
/--
lemma `nullMeasurableSet_mulSupport` / 引理 `nullMeasurableSet_mulSupport`

English:
lemma nullMeasurableSet_mulSupport
  statement: {E} [TopologicalSpace E] [MetrizableSpace E] [One E] {f : α -> E}
  proof: (hf.nullMeasurableSet_eq_fun stronglyMeasurable_const.aestronglyMeasurable).compl

中文:
引理 nullMeasurableSet_mulSupport
  结论: {E} [拓扑空间 E] [Metrizable空间 E] [幺 E] {f : α -> E}
  证明: (hf.nullMeasurableSet_eq_fun stronglyMeasurable_const.aestronglyMeasurable).compl

Depends on / 依赖: aestronglyMeasurable, hf.nullMeasurableSet_eq_fun, nullMeasurableSet_eq_fun, stronglyMeasurable_const, stronglyMeasurable_const.aestronglyMeasurable
-/
lemma nullMeasurableSet_mulSupport {E} [TopologicalSpace E] [MetrizableSpace E] [One E] {f : α -> E}
    (hf : AEStronglyMeasurable f μ) : NullMeasurableSet (mulSupport f) μ :=
  (hf.nullMeasurableSet_eq_fun stronglyMeasurable_const.aestronglyMeasurable).compl

/--
theorem `nullMeasurableSet_lt` / 定理 `nullMeasurableSet_lt`

English:
theorem nullMeasurableSet_lt
  statement: [Preorder β] [OrderClosedTopology β] [PseudoMetrizableSpace β]
  proof: by
  apply
    (hf.stronglyMeasurable_mk.measurableSet_lt hg.stronglyMeasurable_mk).nullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
  change (hf.mk f x < hg.mk g x) = (f x < g x)
  simp only [hfx, hgx]

中文:
定理 nullMeasurableSet_lt
  结论: [预序 β] [OrderClosed拓扑 β] [PseudoMetrizable空间 β]
  证明: by
  apply
    (hf.stronglyMeasurable_mk.measurableSet_lt hg.stronglyMeasurable_mk).nullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
  change (hf.mk f x < hg.mk g x) = (f x < g x)
  simp only [hfx, hgx]

Depends on / 依赖: ae_eq_mk, filter_upwards, hf.ae_eq_mk, hf.mk, hf.stronglyMeasurable_mk.measurableSet_lt, hg.ae_eq_mk, hg.mk, hg.stronglyMeasurable_mk, measurableSet_lt, nullMeasurableSet, nullMeasurableSet.congr, stronglyMeasurable_mk
-/
theorem nullMeasurableSet_lt [Preorder β] [OrderClosedTopology β] [PseudoMetrizableSpace β]
    {f g : α -> β} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    NullMeasurableSet { a | f a < g a } μ := by
  apply
    (hf.stronglyMeasurable_mk.measurableSet_lt hg.stronglyMeasurable_mk).nullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
  change (hf.mk f x < hg.mk g x) = (f x < g x)
  simp only [hfx, hgx]

/--
theorem `nullMeasurableSet_le` / 定理 `nullMeasurableSet_le`

English:
theorem nullMeasurableSet_le
  statement: [Preorder β] [OrderClosedTopology β] [PseudoMetrizableSpace β]
  proof: by
  apply
    (hf.stronglyMeasurable_mk.measurableSet_le hg.stronglyMeasurable_mk).nullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
  change (hf.mk f x <= hg.mk g x) = (f x <= g x)
  simp only [hfx, hgx]

中文:
定理 nullMeasurableSet_le
  结论: [预序 β] [OrderClosed拓扑 β] [PseudoMetrizable空间 β]
  证明: by
  apply
    (hf.stronglyMeasurable_mk.measurableSet_le hg.stronglyMeasurable_mk).nullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
  change (hf.mk f x <= hg.mk g x) = (f x <= g x)
  simp only [hfx, hgx]

Depends on / 依赖: ae_eq_mk, filter_upwards, hf.ae_eq_mk, hf.mk, hf.stronglyMeasurable_mk.measurableSet_le, hg.ae_eq_mk, hg.mk, hg.stronglyMeasurable_mk, measurableSet_le, nullMeasurableSet, nullMeasurableSet.congr, stronglyMeasurable_mk
-/
theorem nullMeasurableSet_le [Preorder β] [OrderClosedTopology β] [PseudoMetrizableSpace β]
    {f g : α -> β} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    NullMeasurableSet { a | f a <= g a } μ := by
  apply
    (hf.stronglyMeasurable_mk.measurableSet_le hg.stronglyMeasurable_mk).nullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
  change (hf.mk f x <= hg.mk g x) = (f x <= g x)
  simp only [hfx, hgx]

/--
theorem `_root_.aestronglyMeasurable_of_aestronglyMeasurable_trim` / 定理 `_root_.aestronglyMeasurable_of_aestronglyMeasurable_trim`

English:
theorem _root_.aestronglyMeasurable_of_aestronglyMeasurable_trim
  statement: {α} {m m0 : MeasurableSpace α}
  proof: ⟨hf.mk f, StronglyMeasurable.mono hf.stronglyMeasurable_mk hm, ae_eq_of_ae_eq_trim hf.ae_eq_mk⟩

中文:
定理 _root_.aestronglyMeasurable_of_aestronglyMeasurable_trim
  结论: {α} {m m0 : 可测空间 α}
  证明: ⟨hf.mk f, StronglyMeasurable.mono hf.stronglyMeasurable_mk hm, ae_eq_of_ae_eq_trim hf.ae_eq_mk⟩

Depends on / 依赖: StronglyMeasurable, StronglyMeasurable.mono, ae_eq_mk, ae_eq_of_ae_eq_trim, hf.ae_eq_mk, hf.mk, hf.stronglyMeasurable_mk, stronglyMeasurable_mk
-/
theorem _root_.aestronglyMeasurable_of_aestronglyMeasurable_trim {α} {m m0 : MeasurableSpace α}
    {μ : Measure α} (hm : m <= m0) {f : α -> β} (hf : AEStronglyMeasurable[m] f (μ.trim hm)) :
    AEStronglyMeasurable f μ :=
  ⟨hf.mk f, StronglyMeasurable.mono hf.stronglyMeasurable_mk hm, ae_eq_of_ae_eq_trim hf.ae_eq_mk⟩

/--
theorem `comp_aemeasurable` / 定理 `comp_aemeasurable`

English:
theorem comp_aemeasurable
  statement: {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ -> α}
  proof: ⟨hg.mk g ∘ hf.mk f, hg.stronglyMeasurable_mk.comp_measurable hf.measurable_mk,
    (ae_eq_comp hf hg.ae_eq_mk).trans (hf.ae_eq_mk.fun_comp (hg.mk g))⟩

中文:
定理 comp_aemeasurable
  结论: {γ : 类型} {_ : 可测空间 γ} {_ : 可测空间 α} {f : γ -> α}
  证明: ⟨hg.mk g ∘ hf.mk f, hg.stronglyMeasurable_mk.comp_measurable hf.measurable_mk,
    (ae_eq_comp hf hg.ae_eq_mk).trans (hf.ae_eq_mk.fun_comp (hg.mk g))⟩

Depends on / 依赖: ae_eq_comp, ae_eq_mk, comp_measurable, fun_comp, hf.ae_eq_mk.fun_comp, hf.measurable_mk, hf.mk, hg.ae_eq_mk, hg.mk, hg.stronglyMeasurable_mk.comp_measurable, measurable_mk, stronglyMeasurable_mk
-/
theorem comp_aemeasurable {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ -> α}
    {μ : Measure γ} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) :
    AEStronglyMeasurable (g ∘ f) μ :=
  ⟨hg.mk g ∘ hf.mk f, hg.stronglyMeasurable_mk.comp_measurable hf.measurable_mk,
    (ae_eq_comp hf hg.ae_eq_mk).trans (hf.ae_eq_mk.fun_comp (hg.mk g))⟩

/--
theorem `comp_measurable` / 定理 `comp_measurable`

English:
theorem comp_measurable
  statement: {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ -> α}
  proof: hg.comp_aemeasurable hf.aemeasurable

中文:
定理 comp_measurable
  结论: {γ : 类型} {_ : 可测空间 γ} {_ : 可测空间 α} {f : γ -> α}
  证明: hg.comp_aemeasurable hf.aemeasurable

Depends on / 依赖: aemeasurable, comp_aemeasurable, hf.aemeasurable, hg.comp_aemeasurable
-/
theorem comp_measurable {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ -> α}
    {μ : Measure γ} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : Measurable f) :
    AEStronglyMeasurable (g ∘ f) μ :=
  hg.comp_aemeasurable hf.aemeasurable

/--
theorem `comp_quasiMeasurePreserving` / 定理 `comp_quasiMeasurePreserving`

English:
theorem comp_quasiMeasurePreserving
  statement: {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α}
  proof: (hg.mono_ac hf.absolutelyContinuous).comp_measurable hf.measurable

中文:
定理 comp_quasiMeasurePreserving
  结论: {γ : 类型} {_ : 可测空间 γ} {_ : 可测空间 α}
  证明: (hg.mono_ac hf.absolutelyContinuous).comp_measurable hf.measurable

Depends on / 依赖: absolutelyContinuous, comp_measurable, hf.absolutelyContinuous, hf.measurable, hg.mono_ac, measurable, mono_ac
-/
theorem comp_quasiMeasurePreserving {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α}
    {f : γ -> α} {μ : Measure γ} {ν : Measure α} (hg : AEStronglyMeasurable g ν)
    (hf : QuasiMeasurePreserving f μ ν) : AEStronglyMeasurable (g ∘ f) μ :=
  (hg.mono_ac hf.absolutelyContinuous).comp_measurable hf.measurable

/--
theorem `isSeparable_ae_range` / 定理 `isSeparable_ae_range`

English:
theorem isSeparable_ae_range
  given: (hf : AEStronglyMeasurable f μ)
  proof: by
  refine ⟨range (hf.mk f), hf.stronglyMeasurable_mk.isSeparable_range, ?_⟩
  filter_upwards [hf.ae_eq_mk] with x hx
  simp [hx]

中文:
定理 isSeparable_ae_range
  条件: (hf : AEStronglyMeasurable f μ)
  证明: by
  refine ⟨range (hf.mk f), hf.stronglyMeasurable_mk.isSeparable_range, ?_⟩
  filter_upwards [hf.ae_eq_mk] with x hx
  simp [hx]

Depends on / 依赖: ae_eq_mk, filter_upwards, hf.ae_eq_mk, hf.mk, hf.stronglyMeasurable_mk.isSeparable_range, isSeparable_range, stronglyMeasurable_mk
-/
theorem isSeparable_ae_range (hf : AEStronglyMeasurable f μ) :
    exists t : Set β, IsSeparable t ∧ forallᵐ x ∂μ, f x in t := by
  refine ⟨range (hf.mk f), hf.stronglyMeasurable_mk.isSeparable_range, ?_⟩
  filter_upwards [hf.ae_eq_mk] with x hx
  simp [hx]

/--
lemma `aestronglyMeasurable_id_map` / 引理 `aestronglyMeasurable_id_map`

English:
lemma aestronglyMeasurable_id_map
  statement: {mβ : MeasurableSpace β}
  proof: by
  obtain ⟨t, ht1, ht2⟩ := hf.isSeparable_ae_range
  refine aestronglyMeasurable_id_of_isSeparable ht1.closure ?_
.2 ?_ refine ae_map_iff hf.aemeasurable isClosed_closure.measurableSet
  filter_upwards [ht2] with ω hω using subset_closure hω

中文:
引理 aestronglyMeasurable_id_map
  结论: {mβ : 可测空间 β}
  证明: by
  obtain ⟨t, ht1, ht2⟩ := hf.isSeparable_ae_range
  refine aestronglyMeasurable_id_of_isSeparable ht1.closure ?_
.2 ?_ refine ae_map_iff hf.aemeasurable isClosed_closure.measurableSet
  filter_upwards [ht2] with ω hω using subset_closure hω

Depends on / 依赖: ae_map_iff, aemeasurable, aestronglyMeasurable_id_of_isSeparable, closure, filter_upwards, hf.aemeasurable, hf.isSeparable_ae_range, ht1.closure, isClosed_closure, isClosed_closure.measurableSet, isSeparable_ae_range, measurableSet, subset_closure
-/
lemma aestronglyMeasurable_id_map {mβ : MeasurableSpace β}
    [TopologicalSpace.PseudoMetrizableSpace β] [BorelSpace β]
    {f : α -> β} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable id (μ.map f) := by
  obtain ⟨t, ht1, ht2⟩ := hf.isSeparable_ae_range
  refine aestronglyMeasurable_id_of_isSeparable ht1.closure ?_
.2 ?_ refine ae_map_iff hf.aemeasurable isClosed_closure.measurableSet
  filter_upwards [ht2] with ω hω using subset_closure hω

/--
theorem `_root_.aestronglyMeasurable_iff_aemeasurable_separable` / 定理 `_root_.aestronglyMeasurable_iff_aemeasurable_separable`

English:
theorem _root_.aestronglyMeasurable_iff_aemeasurable_separable
  statement: [PseudoMetrizableSpace β]
  proof: by
  refine ⟨fun H => ⟨H.aemeasurable, H.isSeparable_ae_range⟩, ?_⟩
  rintro ⟨H, ⟨t, t_sep, ht⟩⟩
  rcases eq_empty_or_nonempty t with (rfl | h₀)
  · simp only [mem_empty_iff_false, eventually_false_iff_eq_bot, ae_eq_bot] at ht
    rw [ht]
    exact aestronglyMeasurable_zero_measure f
  · obtain ⟨g, 

中文:
定理 _root_.aestronglyMeasurable_iff_aemeasurable_separable
  结论: [PseudoMetrizable空间 β]
  证明: by
  refine ⟨fun H => ⟨H.aemeasurable, H.isSeparable_ae_range⟩, ?_⟩
  rintro ⟨H, ⟨t, t_sep, ht⟩⟩
  rcases eq_empty_or_nonempty t with (rfl | h₀)
  · simp only [mem_empty_iff_false, eventually_false_iff_eq_bot, ae_eq_bot] at ht
    rw [ht]
    exact aestronglyMeasurable_zero_measure f
  · obtain ⟨g, 

Depends on / 依赖: H.aemeasurable, H.exists_ae_eq_range_subset, H.isSeparable_ae_range, Measurable, ae_eq_bot, aemeasurable, aestronglyMeasurable_zero_measure, eq_empty_or_nonempty, eventually_false_iff_eq_bot, exists_ae_eq_range_subset, g_meas, isSeparable_ae_range, mem_empty_iff_false, stronglyMeasurable_iff_measurable_separable, subseteq, t_sep, t_sep.mono
-/
theorem _root_.aestronglyMeasurable_iff_aemeasurable_separable [PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β] :
    AEStronglyMeasurable f μ ↔
      AEMeasurable f μ ∧ exists t : Set β, IsSeparable t ∧ forallᵐ x ∂μ, f x in t := by
  refine ⟨fun H => ⟨H.aemeasurable, H.isSeparable_ae_range⟩, ?_⟩
  rintro ⟨H, ⟨t, t_sep, ht⟩⟩
  rcases eq_empty_or_nonempty t with (rfl | h₀)
  · simp only [mem_empty_iff_false, eventually_false_iff_eq_bot, ae_eq_bot] at ht
    rw [ht]
    exact aestronglyMeasurable_zero_measure f
  · obtain ⟨g, g_meas, gt, fg⟩ : exists g : α -> β, Measurable g ∧ range g subseteq t ∧ f =ᵐ[μ] g :=
      H.exists_ae_eq_range_subset ht h₀
    refine ⟨g, ?_, fg⟩
    exact stronglyMeasurable_iff_measurable_separable.2 ⟨g_meas, t_sep.mono gt⟩

/--
theorem `_root_.aestronglyMeasurable_iff_nullMeasurable_separable` / 定理 `_root_.aestronglyMeasurable_iff_nullMeasurable_separable`

English:
theorem _root_.aestronglyMeasurable_iff_nullMeasurable_separable
  statement: [PseudoMetrizableSpace β]
  proof: aestronglyMeasurable_iff_aemeasurable_separable.trans and_congr_left fun ⟨_, hsep, h⟩ =>
    have := hsep.secondCountableTopology
    ⟨AEMeasurable.nullMeasurable, fun hf => hf.aemeasurable_of_aerange h⟩

中文:
定理 _root_.aestronglyMeasurable_iff_nullMeasurable_separable
  结论: [PseudoMetrizable空间 β]
  证明: aestronglyMeasurable_iff_aemeasurable_separable.trans and_congr_left fun ⟨_, hsep, h⟩ =>
    have := hsep.secondCountableTopology
    ⟨AEMeasurable.nullMeasurable, fun hf => hf.aemeasurable_of_aerange h⟩

Depends on / 依赖: AEMeasurable, AEMeasurable.nullMeasurable, aemeasurable_of_aerange, aestronglyMeasurable_iff_aemeasurable_separable, aestronglyMeasurable_iff_aemeasurable_separable.trans, and_congr_left, hf.aemeasurable_of_aerange, hsep.secondCountableTopology, nullMeasurable, secondCountableTopology
-/
theorem _root_.aestronglyMeasurable_iff_nullMeasurable_separable [PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β] :
    AEStronglyMeasurable f μ ↔
      NullMeasurable f μ ∧ exists t : Set β, IsSeparable t ∧ forallᵐ x ∂μ, f x in t :=
aestronglyMeasurable_iff_aemeasurable_separable.trans and_congr_left fun ⟨_, hsep, h⟩ =>
    have := hsep.secondCountableTopology
    ⟨AEMeasurable.nullMeasurable, fun hf => hf.aemeasurable_of_aerange h⟩

/--
theorem `_root_.MeasurableEmbedding.aestronglyMeasurable_map_iff` / 定理 `_root_.MeasurableEmbedding.aestronglyMeasurable_map_iff`

English:
theorem _root_.MeasurableEmbedding.aestronglyMeasurable_map_iff
  statement: {γ : Type*}
  proof: by
  refine ⟨fun H => H.comp_measurable hf.measurable, ?_⟩
  rintro ⟨g₁, hgm₁, heq⟩
  rcases hf.exists_stronglyMeasurable_extend hgm₁ fun x => ⟨g x⟩ with ⟨g₂, hgm₂, rfl⟩
  exact ⟨g₂, hgm₂, hf.ae_map_iff.2 heq⟩

中文:
定理 _root_.可测嵌入.aestronglyMeasurable_map_iff
  结论: {γ : 类型}
  证明: by
  refine ⟨fun H => H.comp_measurable hf.measurable, ?_⟩
  rintro ⟨g₁, hgm₁, heq⟩
  rcases hf.exists_stronglyMeasurable_extend hgm₁ fun x => ⟨g x⟩ with ⟨g₂, hgm₂, rfl⟩
  exact ⟨g₂, hgm₂, hf.ae_map_iff.2 heq⟩

Depends on / 依赖: H.comp_measurable, ae_map_iff, comp_measurable, exists_stronglyMeasurable_extend, hf.ae_map_iff, hf.exists_stronglyMeasurable_extend, hf.measurable, measurable
-/
theorem _root_.MeasurableEmbedding.aestronglyMeasurable_map_iff {γ : Type*}
    {mγ : MeasurableSpace γ} {mα : MeasurableSpace α} {f : γ -> α} {μ : Measure γ}
    (hf : MeasurableEmbedding f) {g : α -> β} :
    AEStronglyMeasurable g (Measure.map f μ) ↔ AEStronglyMeasurable (g ∘ f) μ := by
  refine ⟨fun H => H.comp_measurable hf.measurable, ?_⟩
  rintro ⟨g₁, hgm₁, heq⟩
  rcases hf.exists_stronglyMeasurable_extend hgm₁ fun x => ⟨g x⟩ with ⟨g₂, hgm₂, rfl⟩
  exact ⟨g₂, hgm₂, hf.ae_map_iff.2 heq⟩

/--
theorem `_root_.Topology.IsEmbedding.aestronglyMeasurable_comp_iff` / 定理 `_root_.Topology.IsEmbedding.aestronglyMeasurable_comp_iff`

English:
theorem _root_.Topology.IsEmbedding.aestronglyMeasurable_comp_iff
  statement: [PseudoMetrizableSpace β]
  proof: by
  let := pseudoMetrizableSpacePseudoMetric γ
  borelize β γ
  refine
    ⟨fun H => aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨?_, ?_⟩, fun H =>
      hg.continuous.comp_aestronglyMeasurable H⟩
  · let G : β -> range g := rangeFactorization g
    have hG : IsClosedEmbedding G :=
      { hg

中文:
定理 _root_.拓扑.是嵌入.aestronglyMeasurable_comp_iff
  结论: [PseudoMetrizable空间 β]
  证明: by
  let := pseudoMetrizableSpacePseudoMetric γ
  borelize β γ
  refine
    ⟨fun H => aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨?_, ?_⟩, fun H =>
      hg.continuous.comp_aestronglyMeasurable H⟩
  · let G : β -> range g := rangeFactorization g
    have hG : IsClosedEmbedding G :=
      { hg

Depends on / 依赖: AEMeasurable, AEMeasurable.subtype_mk, H.aemeasurable, IsClosedEmbedding, aemeasurable, aemeasurable_comp, aestronglyMeasurable_iff_aemeasurable_separable, borelize, codRestrict, comp_aestronglyMeasurable, continuous, hG.measurableEmbedding.aemeasurable_comp, hg.codRestrict, hg.continuous.comp_aestronglyMeasurable, isClosed_range, isClosed_univ, measurableEmbedding, pseudoMetrizableSpacePseudoMetric, rangeFactorization, rangeFactorization_surjective
-/
theorem _root_.Topology.IsEmbedding.aestronglyMeasurable_comp_iff [PseudoMetrizableSpace β]
    [PseudoMetrizableSpace γ] {g : β -> γ} {f : α -> β} (hg : IsEmbedding g) :
    AEStronglyMeasurable (fun x => g (f x)) μ ↔ AEStronglyMeasurable f μ := by
  let := pseudoMetrizableSpacePseudoMetric γ
  borelize β γ
  refine
    ⟨fun H => aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨?_, ?_⟩, fun H =>
      hg.continuous.comp_aestronglyMeasurable H⟩
  · let G : β -> range g := rangeFactorization g
    have hG : IsClosedEmbedding G :=
      { hg.codRestrict _ _ with
        isClosed_range := by rw [rangeFactorization_surjective.range_eq]; exact isClosed_univ }
    have : AEMeasurable (G ∘ f) μ := AEMeasurable.subtype_mk H.aemeasurable
    exact hG.measurableEmbedding.aemeasurable_comp_iff.1 this
  · rcases (aestronglyMeasurable_iff_aemeasurable_separable.1 H).2 with ⟨t, ht, h't⟩
    exact ⟨g ⁻¹' t, hg.isSeparable_preimage ht, h't⟩

/--
theorem `_root_.aestronglyMeasurable_of_tendsto_ae` / 定理 `_root_.aestronglyMeasurable_of_tendsto_ae`

English:
theorem _root_.aestronglyMeasurable_of_tendsto_ae
  statement: {ι : Type*} [PseudoMetrizableSpace β]
  proof: by
  borelize β
  refine aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨?_, ?_⟩
  · exact aemeasurable_of_tendsto_metrizable_ae _ (fun n => (hf n).aemeasurable) lim
  · rcases u.exists_seq_tendsto with ⟨v, hv⟩
    have : forall n : Nat, exists t : Set β, IsSeparable t ∧ f (v n) ⁻¹' t in ae μ := 

中文:
定理 _root_.aestronglyMeasurable_of_tendsto_ae
  结论: {ι : 类型} [PseudoMetrizable空间 β]
  证明: by
  borelize β
  refine aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨?_, ?_⟩
  · exact aemeasurable_of_tendsto_metrizable_ae _ (fun n => (hf n).aemeasurable) lim
  · rcases u.exists_seq_tendsto with ⟨v, hv⟩
    have : forall n : Nat, exists t : Set β, IsSeparable t ∧ f (v n) ⁻¹' t in ae μ := 

Depends on / 依赖: IsSeparable, ae_all_iff, aemeasurable, aemeasurable_of_tendsto_metrizable_ae, aestronglyMeasurable_iff_aemeasurable_separable, borelize, closure, exists_seq_tendsto, filter_upwards, iUnion, t_sep, u.exists_seq_tendsto
-/
theorem _root_.aestronglyMeasurable_of_tendsto_ae {ι : Type*} [PseudoMetrizableSpace β]
    (u : Filter ι) [NeBot u] [IsCountablyGenerated u] {f : ι -> α -> β} {g : α -> β}
    (hf : forall i, AEStronglyMeasurable (f i) μ) (lim : forallᵐ x ∂μ, Tendsto (fun n => f n x) u (𝓝 (g x))) :
    AEStronglyMeasurable g μ := by
  borelize β
  refine aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨?_, ?_⟩
  · exact aemeasurable_of_tendsto_metrizable_ae _ (fun n => (hf n).aemeasurable) lim
  · rcases u.exists_seq_tendsto with ⟨v, hv⟩
    have : forall n : Nat, exists t : Set β, IsSeparable t ∧ f (v n) ⁻¹' t in ae μ := fun n =>
      (aestronglyMeasurable_iff_aemeasurable_separable.1 (hf (v n))).2
    choose t t_sep ht using this
refine ⟨closure (⋃ i, t i), .closure .iUnion t_sep, ?_⟩
    filter_upwards [ae_all_iff.2 ht, lim] with x hx h'x
    apply mem_closure_of_tendsto (h'x.comp hv)
    filter_upwards with n using mem_iUnion_of_mem n (hx n)

/--
theorem `_root_.exists_stronglyMeasurable_limit_of_tendsto_ae` / 定理 `_root_.exists_stronglyMeasurable_limit_of_tendsto_ae`

English:
theorem _root_.exists_stronglyMeasurable_limit_of_tendsto_ae
  statement: [PseudoMetrizableSpace β]
  proof: by
  borelize β
  obtain ⟨g, _, hg⟩ :
    exists g : α -> β, Measurable g ∧ forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)) :=
    measurable_limit_of_tendsto_metrizable_ae (fun n => (hf n).aemeasurable) h_ae_tendsto
  have Hg : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae _

中文:
定理 _root_.存在_stronglyMeasurable_limit_of_tendsto_ae
  结论: [PseudoMetrizable空间 β]
  证明: by
  borelize β
  obtain ⟨g, _, hg⟩ :
    exists g : α -> β, Measurable g ∧ forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)) :=
    measurable_limit_of_tendsto_metrizable_ae (fun n => (hf n).aemeasurable) h_ae_tendsto
  have Hg : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae _

Depends on / 依赖: AEStronglyMeasurable, Hg.ae_eq_mk, Hg.mk, Hg.stronglyMeasurable_mk, Measurable, Tendsto, ae_eq_mk, aemeasurable, aestronglyMeasurable_of_tendsto_ae, borelize, filter_upwards, h_ae_tendsto, measurable_limit_of_tendsto_metrizable_ae, stronglyMeasurable_mk
-/
theorem _root_.exists_stronglyMeasurable_limit_of_tendsto_ae [PseudoMetrizableSpace β]
    {f : Nat -> α -> β} (hf : forall n, AEStronglyMeasurable (f n) μ)
    (h_ae_tendsto : forallᵐ x ∂μ, exists l : β, Tendsto (fun n => f n x) atTop (𝓝 l)) :
    exists f_lim : α -> β, StronglyMeasurable f_lim ∧
      forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x)) := by
  borelize β
  obtain ⟨g, _, hg⟩ :
    exists g : α -> β, Measurable g ∧ forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)) :=
    measurable_limit_of_tendsto_metrizable_ae (fun n => (hf n).aemeasurable) h_ae_tendsto
  have Hg : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae _ hf hg
  refine ⟨Hg.mk g, Hg.stronglyMeasurable_mk, ?_⟩
  filter_upwards [hg, Hg.ae_eq_mk] with x hx h'x
  rwa [h'x] at hx

/--
lemma `exists_stronglyMeasurable_range_subset` / 引理 `exists_stronglyMeasurable_range_subset`

English:
lemma exists_stronglyMeasurable_range_subset
  statement: {α β : Type*}
  proof: by
  obtain ⟨f', hf', hff'⟩ := hf
  classical
  refine ⟨(f' ⁻¹' s).piecewise f' (fun _ => h_nonempty.some), ?meas, ?subset, ?ae_eq⟩
  case meas => exact hf'.piecewise (hf'.measurable hs) stronglyMeasurable_const
  case subset =>
    rw [← Set.range_subset_iff]
    simpa [Set.range_piecewise] using! 

中文:
引理 存在_stronglyMeasurable_range_subset
  结论: {α β : 类型}
  证明: by
  obtain ⟨f', hf', hff'⟩ := hf
  classical
  refine ⟨(f' ⁻¹' s).piecewise f' (fun _ => h_nonempty.some), ?meas, ?subset, ?ae_eq⟩
  case meas => exact hf'.piecewise (hf'.measurable hs) stronglyMeasurable_const
  case subset =>
    rw [← Set.range_subset_iff]
    simpa [Set.range_piecewise] using! 

Depends on / 依赖: Eq.symm, Set.range_piecewise, Set.range_subset_iff, ae_eq, classical, filter_upwards, h_mem, h_nonempty, h_nonempty.some, h_nonempty.some_mem, measurable, piecewise, piecewise_eq_of_mem, range_piecewise, range_subset_iff, some_mem, stronglyMeasurable_const, subset
-/
lemma exists_stronglyMeasurable_range_subset {α β : Type*}
    [TopologicalSpace β] [PseudoMetrizableSpace β] [mb : MeasurableSpace β] [BorelSpace β]
    [m : MeasurableSpace α] {μ : Measure α} {f : α -> β} (hf : AEStronglyMeasurable f μ)
    {s : Set β} (hs : MeasurableSet s) (h_nonempty : s.Nonempty) (h_mem : forallᵐ x ∂μ, f x in s) :
    exists g : α -> β, StronglyMeasurable g ∧ (forall x, g x in s) ∧ f =ᵐ[μ] g := by
  obtain ⟨f', hf', hff'⟩ := hf
  classical
  refine ⟨(f' ⁻¹' s).piecewise f' (fun _ => h_nonempty.some), ?meas, ?subset, ?ae_eq⟩
  case meas => exact hf'.piecewise (hf'.measurable hs) stronglyMeasurable_const
  case subset =>
    rw [← Set.range_subset_iff]
    simpa [Set.range_piecewise] using! fun _ _ => h_nonempty.some_mem
  case ae_eq =>
    apply hff'.trans
    filter_upwards [h_mem, hff'] with x hx hx'
exact Eq.symm (f' ⁻¹' s).piecewise_eq_of_mem f' _ (by simpa [hx'] using! hx)

/--
theorem `piecewise` / 定理 `piecewise`

English:
theorem piecewise
  statement: {s : Set α} [DecidablePred (· in s)]
  proof: by
  refine ⟨s.piecewise (hf.mk f) (hg.mk g),
    StronglyMeasurable.piecewise hs hf.stronglyMeasurable_mk hg.stronglyMeasurable_mk, ?_⟩
  refine ae_of_ae_restrict_of_ae_restrict_compl s ?_ ?_
  · have h := hf.ae_eq_mk
    rw [Filter.EventuallyEq]; rw [ae_restrict_iff' hs] at h
    rw [ae_restrict_i

中文:
定理 piecewise
  结论: {s : 集合 α} [DecidablePred (· in s)]
  证明: by
  refine ⟨s.piecewise (hf.mk f) (hg.mk g),
    StronglyMeasurable.piecewise hs hf.stronglyMeasurable_mk hg.stronglyMeasurable_mk, ?_⟩
  refine ae_of_ae_restrict_of_ae_restrict_compl s ?_ ?_
  · have h := hf.ae_eq_mk
    rw [Filter.EventuallyEq]; rw [ae_restrict_iff' hs] at h
    rw [ae_restrict_i

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq, Set.piecewise_eq_of_mem, StronglyMeasurable, StronglyMeasurable.piecewise, ae_eq_mk, ae_of_ae_restrict_of_ae_restrict_compl, ae_restrict_iff, filter_upwards, hf.ae_eq_mk, hf.mk, hf.stronglyMeasurable_mk, hg.ae_eq_mk, hg.mk, hg.stronglyMeasurable_mk, hs.com, hs.compl, hx_mem, piecewise
-/
theorem piecewise {s : Set α} [DecidablePred (· in s)]
    (hs : MeasurableSet s) (hf : AEStronglyMeasurable f (μ.restrict s))
    (hg : AEStronglyMeasurable g (μ.restrict sᶜ)) :
    AEStronglyMeasurable (s.piecewise f g) μ := by
  refine ⟨s.piecewise (hf.mk f) (hg.mk g),
    StronglyMeasurable.piecewise hs hf.stronglyMeasurable_mk hg.stronglyMeasurable_mk, ?_⟩
  refine ae_of_ae_restrict_of_ae_restrict_compl s ?_ ?_
  · have h := hf.ae_eq_mk
    rw [Filter.EventuallyEq]; rw [ae_restrict_iff' hs] at h
    rw [ae_restrict_iff' hs]
    filter_upwards [h] with x hx
    intro hx_mem
    simp only [hx_mem, Set.piecewise_eq_of_mem, hx hx_mem]
  · have h := hg.ae_eq_mk
    rw [Filter.EventuallyEq]; rw [ae_restrict_iff' hs.compl] at h
    rw [ae_restrict_iff' hs.compl]
    filter_upwards [h] with x hx
    intro hx_mem
    rw [Set.mem_compl_iff] at hx_mem
    simp only [hx_mem, not_false_eq_true, Set.piecewise_eq_of_notMem, hx hx_mem]

@[fun_prop]
/--
theorem `sum_measure` / 定理 `sum_measure`

English:
theorem sum_measure
  statement: [PseudoMetrizableSpace β] {m : MeasurableSpace α} {μ : ι -> Measure α}
  proof: by
  borelize β
  refine
    aestronglyMeasurable_iff_aemeasurable_separable.2
      ⟨AEMeasurable.sum_measure fun i => (h i).aemeasurable, ?_⟩
  have A : forall i : ι, exists t : Set β, IsSeparable t ∧ f ⁻¹' t in ae (μ i) := fun i =>
    (aestronglyMeasurable_iff_aemeasurable_separable.1 (h i)).2
 

中文:
定理 sum_measure
  结论: [PseudoMetrizable空间 β] {m : 可测空间 α} {μ : ι -> 测度 α}
  证明: by
  borelize β
  refine
    aestronglyMeasurable_iff_aemeasurable_separable.2
      ⟨AEMeasurable.sum_measure fun i => (h i).aemeasurable, ?_⟩
  have A : forall i : ι, exists t : Set β, IsSeparable t ∧ f ⁻¹' t in ae (μ i) := fun i =>
    (aestronglyMeasurable_iff_aemeasurable_separable.1 (h i)).2
 

Depends on / 依赖: AEMeasurable, AEMeasurable.sum_measure, IsSeparable, Measure, Measure.ae_sum_eq, ae_sum_eq, aemeasurable, aestronglyMeasurable_iff_aemeasurable_separable, borelize, eventually_iSup, filter_upwards, iUnion, mem_iUnion, sum_measure, t_sep
-/
theorem sum_measure [PseudoMetrizableSpace β] {m : MeasurableSpace α} {μ : ι -> Measure α}
    (h : forall i, AEStronglyMeasurable f (μ i)) : AEStronglyMeasurable f (Measure.sum μ) := by
  borelize β
  refine
    aestronglyMeasurable_iff_aemeasurable_separable.2
      ⟨AEMeasurable.sum_measure fun i => (h i).aemeasurable, ?_⟩
  have A : forall i : ι, exists t : Set β, IsSeparable t ∧ f ⁻¹' t in ae (μ i) := fun i =>
    (aestronglyMeasurable_iff_aemeasurable_separable.1 (h i)).2
  choose t t_sep ht using A
  refine ⟨⋃ i, t i, .iUnion t_sep, ?_⟩
  simp only [Measure.ae_sum_eq, mem_iUnion, eventually_iSup]
  intro i
  filter_upwards [ht i] with x hx
  exact ⟨i, hx⟩

@[simp]
/--
theorem `_root_.aestronglyMeasurable_sum_measure_iff` / 定理 `_root_.aestronglyMeasurable_sum_measure_iff`

English:
theorem _root_.aestronglyMeasurable_sum_measure_iff
  statement: [PseudoMetrizableSpace β]
  proof: ⟨fun h _ => h.mono_measure (Measure.le_sum _ _), sum_measure⟩

@[simp]

中文:
定理 _root_.aestronglyMeasurable_sum_measure_iff
  结论: [PseudoMetrizable空间 β]
  证明: ⟨fun h _ => h.mono_measure (Measure.le_sum _ _), sum_measure⟩

@[simp]

Depends on / 依赖: Measure, Measure.le_sum, h.mono_measure, le_sum, mono_measure, sum_measure
-/
theorem _root_.aestronglyMeasurable_sum_measure_iff [PseudoMetrizableSpace β]
    {_m : MeasurableSpace α} {μ : ι -> Measure α} :
    AEStronglyMeasurable f (sum μ) ↔ forall i, AEStronglyMeasurable f (μ i) :=
  ⟨fun h _ => h.mono_measure (Measure.le_sum _ _), sum_measure⟩

@[simp]
/--
theorem `_root_.aestronglyMeasurable_add_measure_iff` / 定理 `_root_.aestronglyMeasurable_add_measure_iff`

English:
theorem _root_.aestronglyMeasurable_add_measure_iff
  given: [PseudoMetrizableSpace β] {ν : Measure α}
  proof: by
  rw [← sum_cond]; rw [aestronglyMeasurable_sum_measure_iff]; rw [Bool.forall_bool]; rw [and_comm]
  rfl

@[fun_prop]

中文:
定理 _root_.aestronglyMeasurable_add_measure_iff
  条件: [PseudoMetrizable空间 β] {ν : 测度 α}
  证明: by
  rw [← sum_cond]; rw [aestronglyMeasurable_sum_measure_iff]; rw [Bool.forall_bool]; rw [and_comm]
  rfl

@[fun_prop]

Depends on / 依赖: Bool.forall_bool, aestronglyMeasurable_sum_measure_iff, and_comm, forall_bool, sum_cond
-/
theorem _root_.aestronglyMeasurable_add_measure_iff [PseudoMetrizableSpace β] {ν : Measure α} :
    AEStronglyMeasurable f (μ + ν) ↔ AEStronglyMeasurable f μ ∧ AEStronglyMeasurable f ν := by
  rw [← sum_cond]; rw [aestronglyMeasurable_sum_measure_iff]; rw [Bool.forall_bool]; rw [and_comm]
  rfl

@[fun_prop]
/--
theorem `add_measure` / 定理 `add_measure`

English:
theorem add_measure
  statement: [PseudoMetrizableSpace β] {ν : Measure α} {f : α -> β}
  proof: aestronglyMeasurable_add_measure_iff.2 ⟨hμ, hν⟩

@[fun_prop]

中文:
定理 add_measure
  结论: [PseudoMetrizable空间 β] {ν : 测度 α} {f : α -> β}
  证明: aestronglyMeasurable_add_measure_iff.2 ⟨hμ, hν⟩

@[fun_prop]

Depends on / 依赖: aestronglyMeasurable_add_measure_iff
-/
theorem add_measure [PseudoMetrizableSpace β] {ν : Measure α} {f : α -> β}
    (hμ : AEStronglyMeasurable f μ) (hν : AEStronglyMeasurable f ν) :
    AEStronglyMeasurable f (μ + ν) :=
  aestronglyMeasurable_add_measure_iff.2 ⟨hμ, hν⟩

@[fun_prop]
/--
theorem `iUnion` / 定理 `iUnion`

English:
theorem iUnion
  statement: [PseudoMetrizableSpace β] {s : ι -> Set α}
  proof: (sum_measure h).mono_measure restrict_iUnion_le

@[simp]

中文:
定理 iUnion
  结论: [PseudoMetrizable空间 β] {s : ι -> 集合 α}
  证明: (sum_measure h).mono_measure restrict_iUnion_le

@[simp]
-/
protected theorem iUnion [PseudoMetrizableSpace β] {s : ι -> Set α}
    (h : forall i, AEStronglyMeasurable f (μ.restrict (s i))) :
    AEStronglyMeasurable f (μ.restrict (⋃ i, s i)) :=
(sum_measure h).mono_measure restrict_iUnion_le

@[simp]
/--
theorem `_root_.aestronglyMeasurable_iUnion_iff` / 定理 `_root_.aestronglyMeasurable_iUnion_iff`

English:
theorem _root_.aestronglyMeasurable_iUnion_iff
  given: [PseudoMetrizableSpace β] {s : ι -> Set α}
  proof: ⟨fun h _ => h.mono_measure restrict_mono (subset_iUnion _ _) le_rfl,
    AEStronglyMeasurable.iUnion⟩

@[simp]

中文:
定理 _root_.aestronglyMeasurable_iUnion_iff
  条件: [PseudoMetrizable空间 β] {s : ι -> 集合 α}
  证明: ⟨fun h _ => h.mono_measure restrict_mono (subset_iUnion _ _) le_rfl,
    AEStronglyMeasurable.iUnion⟩

@[simp]

Depends on / 依赖: AEStronglyMeasurable, AEStronglyMeasurable.iUnion, h.mono_measure, iUnion, le_rfl, mono_measure, restrict_mono, subset_iUnion
-/
theorem _root_.aestronglyMeasurable_iUnion_iff [PseudoMetrizableSpace β] {s : ι -> Set α} :
    AEStronglyMeasurable f (μ.restrict (⋃ i, s i)) ↔
      forall i, AEStronglyMeasurable f (μ.restrict (s i)) :=
⟨fun h _ => h.mono_measure restrict_mono (subset_iUnion _ _) le_rfl,
    AEStronglyMeasurable.iUnion⟩

@[simp]
/--
theorem `_root_.aestronglyMeasurable_union_iff` / 定理 `_root_.aestronglyMeasurable_union_iff`

English:
theorem _root_.aestronglyMeasurable_union_iff
  given: [PseudoMetrizableSpace β] {s t : Set α}
  proof: by
  simp only [union_eq_iUnion, aestronglyMeasurable_iUnion_iff, Bool.forall_bool, cond, and_comm]

中文:
定理 _root_.aestronglyMeasurable_union_iff
  条件: [PseudoMetrizable空间 β] {s t : 集合 α}
  证明: by
  simp only [union_eq_iUnion, aestronglyMeasurable_iUnion_iff, Bool.forall_bool, cond, and_comm]

Depends on / 依赖: Bool.forall_bool, aestronglyMeasurable_iUnion_iff, and_comm, forall_bool, union_eq_iUnion
-/
theorem _root_.aestronglyMeasurable_union_iff [PseudoMetrizableSpace β] {s t : Set α} :
    AEStronglyMeasurable f (μ.restrict (s union t)) ↔
      AEStronglyMeasurable f (μ.restrict s) ∧ AEStronglyMeasurable f (μ.restrict t) := by
  simp only [union_eq_iUnion, aestronglyMeasurable_iUnion_iff, Bool.forall_bool, cond, and_comm]

/--
theorem `aestronglyMeasurable_uIoc_iff` / 定理 `aestronglyMeasurable_uIoc_iff`

English:
theorem aestronglyMeasurable_uIoc_iff
  statement: [LinearOrder α] [PseudoMetrizableSpace β] {f : α -> β}
  proof: by
  rw [uIoc_eq_union]; rw [aestronglyMeasurable_union_iff]

@[fun_prop]

中文:
定理 aestronglyMeasurable_uIoc_iff
  结论: [线性序 α] [PseudoMetrizable空间 β] {f : α -> β}
  证明: by
  rw [uIoc_eq_union]; rw [aestronglyMeasurable_union_iff]

@[fun_prop]

Depends on / 依赖: aestronglyMeasurable_union_iff, uIoc_eq_union
-/
theorem aestronglyMeasurable_uIoc_iff [LinearOrder α] [PseudoMetrizableSpace β] {f : α -> β}
    {a b : α} :
    AEStronglyMeasurable f (μ.restrict <| uIoc a b) ↔
      AEStronglyMeasurable f (μ.restrict <| Ioc a b) ∧
        AEStronglyMeasurable f (μ.restrict <| Ioc b a) := by
  rw [uIoc_eq_union]; rw [aestronglyMeasurable_union_iff]

@[fun_prop]
/--
theorem `smul_measure` / 定理 `smul_measure`

English:
theorem smul_measure
  statement: {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
  proof: ⟨h.mk f, h.stronglyMeasurable_mk, ae_smul_measure h.ae_eq_mk c⟩

中文:
定理 smul_measure
  结论: {R : 类型} [标量乘法 R 实数>=0∞] [标量塔 R 实数>=0∞ 实数>=0∞]
  证明: ⟨h.mk f, h.stronglyMeasurable_mk, ae_smul_measure h.ae_eq_mk c⟩

Depends on / 依赖: ae_eq_mk, ae_smul_measure, h.ae_eq_mk, h.mk, h.stronglyMeasurable_mk, stronglyMeasurable_mk
-/
theorem smul_measure {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
    (h : AEStronglyMeasurable f μ) (c : R) : AEStronglyMeasurable f (c • μ) :=
  ⟨h.mk f, h.stronglyMeasurable_mk, ae_smul_measure h.ae_eq_mk c⟩

section MulAction

variable {M G G₀ : Type*}
variable [Monoid M] [MulAction M β]
variable [Group G] [MulAction G β]
variable [GroupWithZero G₀] [MulAction G₀ β]

/--
theorem `_root_.aestronglyMeasurable_const_smul_iff` / 定理 `_root_.aestronglyMeasurable_const_smul_iff`

English:
theorem _root_.aestronglyMeasurable_const_smul_iff
  given: [ContinuousConstSMul G β] (c : G)
  proof: ⟨fun h => by simpa only [inv_smul_smul] using h.fun_const_smul c⁻¹, fun h => h.const_smul c⟩

中文:
定理 _root_.aestronglyMeasurable_const_smul_iff
  条件: [连续常数标量乘法 G β] (c : G)
  证明: ⟨fun h => by simpa only [inv_smul_smul] using h.fun_const_smul c⁻¹, fun h => h.const_smul c⟩

Depends on / 依赖: const_smul, fun_const_smul, h.const_smul, h.fun_const_smul, inv_smul_smul
-/
theorem _root_.aestronglyMeasurable_const_smul_iff [ContinuousConstSMul G β] (c : G) :
    AEStronglyMeasurable (fun x => c • f x) μ ↔ AEStronglyMeasurable f μ :=
  ⟨fun h => by simpa only [inv_smul_smul] using h.fun_const_smul c⁻¹, fun h => h.const_smul c⟩

/--
theorem `_root_.aestronglyMeasurable_smul_iff` / 定理 `_root_.aestronglyMeasurable_smul_iff`

English:
theorem _root_.aestronglyMeasurable_smul_iff
  statement: [TopologicalSpace G] [ContinuousInv G]
  proof: ⟨fun h => (hc.fun_inv.fun_smul h).congr (by simp), fun h => hc.fun_smul h⟩

nonrec theorem _root_.IsUnit.aestronglyMeasurable_const_smul_iff [ContinuousConstSMul M β] {c : M}
    (hc : IsUnit c) :
    AEStronglyMeasurable (fun x => c • f x) μ ↔ AEStronglyMeasurable f μ :=
  let ⟨u, hu⟩ := hc
  hu ▸ 

中文:
定理 _root_.aestronglyMeasurable_smul_iff
  结论: [拓扑空间 G] [连续取逆 G]
  证明: ⟨fun h => (hc.fun_inv.fun_smul h).congr (by simp), fun h => hc.fun_smul h⟩

nonrec theorem _root_.IsUnit.aestronglyMeasurable_const_smul_iff [ContinuousConstSMul M β] {c : M}
    (hc : IsUnit c) :
    AEStronglyMeasurable (fun x => c • f x) μ ↔ AEStronglyMeasurable f μ :=
  let ⟨u, hu⟩ := hc
  hu ▸ 

Depends on / 依赖: fun_inv, fun_smul, hc.fun_inv.fun_smul, hc.fun_smul
-/
theorem _root_.aestronglyMeasurable_smul_iff [TopologicalSpace G] [ContinuousInv G]
    [ContinuousSMul G β] {c : α -> G} (hc : AEStronglyMeasurable c μ) :
    AEStronglyMeasurable (fun x => c x • f x) μ ↔ AEStronglyMeasurable f μ :=
  ⟨fun h => (hc.fun_inv.fun_smul h).congr (by simp), fun h => hc.fun_smul h⟩

nonrec theorem _root_.IsUnit.aestronglyMeasurable_const_smul_iff [ContinuousConstSMul M β] {c : M}
    (hc : IsUnit c) :
    AEStronglyMeasurable (fun x => c • f x) μ ↔ AEStronglyMeasurable f μ :=
  let ⟨u, hu⟩ := hc
  hu ▸ aestronglyMeasurable_const_smul_iff u

/--
theorem `_root_.aestronglyMeasurable_const_smul_iff₀` / 定理 `_root_.aestronglyMeasurable_const_smul_iff₀`

English:
theorem _root_.aestronglyMeasurable_const_smul_iff₀
  statement: [ContinuousConstSMul G₀ β] {c : G₀}
  proof: (IsUnit.mk0 _ hc).aestronglyMeasurable_const_smul_iff

中文:
定理 _root_.aestronglyMeasurable_const_smul_iff₀
  结论: [连续常数标量乘法 G₀ β] {c : G₀}
  证明: (IsUnit.mk0 _ hc).aestronglyMeasurable_const_smul_iff

Depends on / 依赖: IsUnit, IsUnit.mk0, aestronglyMeasurable_const_smul_iff
-/
theorem _root_.aestronglyMeasurable_const_smul_iff₀ [ContinuousConstSMul G₀ β] {c : G₀}
    (hc : c != 0) :
    AEStronglyMeasurable (fun x => c • f x) μ ↔ AEStronglyMeasurable f μ :=
  (IsUnit.mk0 _ hc).aestronglyMeasurable_const_smul_iff

/--
theorem `_root_.aestronglyMeasurable_smul_iff₀` / 定理 `_root_.aestronglyMeasurable_smul_iff₀`

English:
theorem _root_.aestronglyMeasurable_smul_iff₀
  statement: [TopologicalSpace G₀] [ContinuousInv₀ G₀]
  proof: by
  refine ⟨fun h => (hc.fun_inv₀.fun_smul h).congr ?_, fun h => hc.fun_smul h⟩
  filter_upwards [hc0] with x hx
  simp [hx]

中文:
定理 _root_.aestronglyMeasurable_smul_iff₀
  结论: [拓扑空间 G₀] [余ntinuousInv₀ G₀]
  证明: by
  refine ⟨fun h => (hc.fun_inv₀.fun_smul h).congr ?_, fun h => hc.fun_smul h⟩
  filter_upwards [hc0] with x hx
  simp [hx]

Depends on / 依赖: filter_upwards, fun_smul, hc.fun_inv, hc.fun_smul
-/
theorem _root_.aestronglyMeasurable_smul_iff₀ [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MetrizableSpace G₀] [ContinuousSMul G₀ β] {c : α -> G₀}
    (hc : AEStronglyMeasurable c μ) (hc0 : forallᵐ x ∂μ, c x != 0) :
    AEStronglyMeasurable (fun x => c x • f x) μ ↔ AEStronglyMeasurable f μ := by
  refine ⟨fun h => (hc.fun_inv₀.fun_smul h).congr ?_, fun h => hc.fun_smul h⟩
  filter_upwards [hc0] with x hx
  simp [hx]

end MulAction

end AEStronglyMeasurable
end AEStronglyMeasurable

/-! ## Almost everywhere finitely strongly measurable functions -/


namespace AEFinStronglyMeasurable

variable {m : MeasurableSpace α} {μ : Measure α} [TopologicalSpace β] {f g : α -> β}

section Mk

variable [Zero β]

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def mk (f : α -> β) (hf : AEFinStronglyMeasurable f μ)
  body: hf.choose

中文:
定义 noncomputable
  签名: def mk (f : α -> β) (hf : AEFinStronglyMeasurable f μ)
  定义体: hf.choose
-/
protected noncomputable def mk (f : α -> β) (hf : AEFinStronglyMeasurable f μ) : α -> β :=
  hf.choose

/--
theorem `finStronglyMeasurable_mk` / 定理 `finStronglyMeasurable_mk`

English:
theorem finStronglyMeasurable_mk
  given: (hf : AEFinStronglyMeasurable f μ)
  proof: hf.choose_spec.1

中文:
定理 finStronglyMeasurable_mk
  条件: (hf : AEFinStronglyMeasurable f μ)
  证明: hf.choose_spec.1

Depends on / 依赖: choose_spec, hf.choose_spec
-/
theorem finStronglyMeasurable_mk (hf : AEFinStronglyMeasurable f μ) :
    FinStronglyMeasurable (hf.mk f) μ :=
  hf.choose_spec.1

/--
theorem `ae_eq_mk` / 定理 `ae_eq_mk`

English:
theorem ae_eq_mk
  given: (hf : AEFinStronglyMeasurable f μ)
  statement: f =ᵐ[μ] hf.mk f
  proof: hf.choose_spec.2

@[fun_prop]

中文:
定理 ae_eq_mk
  条件: (hf : AEFinStronglyMeasurable f μ)
  结论: f =ᵐ[μ] hf.mk f
  证明: hf.choose_spec.2

@[fun_prop]

Depends on / 依赖: choose_spec, hf.choose_spec
-/
theorem ae_eq_mk (hf : AEFinStronglyMeasurable f μ) : f =ᵐ[μ] hf.mk f :=
  hf.choose_spec.2

@[fun_prop]
/--
theorem `aemeasurable` / 定理 `aemeasurable`

English:
theorem aemeasurable
  statement: {β} [Zero β] [MeasurableSpace β] [TopologicalSpace β]
  proof: ⟨hf.mk f, hf.finStronglyMeasurable_mk.measurable, hf.ae_eq_mk⟩

中文:
定理 aemeasurable
  结论: {β} [零 β] [可测空间 β] [拓扑空间 β]
  证明: ⟨hf.mk f, hf.finStronglyMeasurable_mk.measurable, hf.ae_eq_mk⟩
-/
protected theorem aemeasurable {β} [Zero β] [MeasurableSpace β] [TopologicalSpace β]
    [PseudoMetrizableSpace β] [BorelSpace β] {f : α -> β} (hf : AEFinStronglyMeasurable f μ) :
    AEMeasurable f μ :=
  ⟨hf.mk f, hf.finStronglyMeasurable_mk.measurable, hf.ae_eq_mk⟩

end Mk

section Arithmetic

@[aesop safe 20 (rule_sets := [Measurable])]
/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  statement: [MulZeroClass β] [ContinuousMul β] (hf : AEFinStronglyMeasurable f μ)
  proof: ⟨hf.mk f * hg.mk g, hf.finStronglyMeasurable_mk.mul hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.mul hg.ae_eq_mk⟩

@[aesop safe 20 (rule_sets := [Measurable])]

中文:
定理 mul
  结论: [乘零类 β] [连续乘法 β] (hf : AEFinStronglyMeasurable f μ)
  证明: ⟨hf.mk f * hg.mk g, hf.finStronglyMeasurable_mk.mul hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.mul hg.ae_eq_mk⟩

@[aesop safe 20 (rule_sets := [Measurable])]
-/
protected theorem mul [MulZeroClass β] [ContinuousMul β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f * g) μ :=
  ⟨hf.mk f * hg.mk g, hf.finStronglyMeasurable_mk.mul hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.mul hg.ae_eq_mk⟩

@[aesop safe 20 (rule_sets := [Measurable])]
/--
theorem `add` / 定理 `add`

English:
theorem add
  statement: [AddZeroClass β] [ContinuousAdd β] (hf : AEFinStronglyMeasurable f μ)
  proof: ⟨hf.mk f + hg.mk g, hf.finStronglyMeasurable_mk.add hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.add hg.ae_eq_mk⟩

@[measurability]

中文:
定理 add
  结论: [加法零类 β] [连续加法 β] (hf : AEFinStronglyMeasurable f μ)
  证明: ⟨hf.mk f + hg.mk g, hf.finStronglyMeasurable_mk.add hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.add hg.ae_eq_mk⟩

@[measurability]
-/
protected theorem add [AddZeroClass β] [ContinuousAdd β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f + g) μ :=
  ⟨hf.mk f + hg.mk g, hf.finStronglyMeasurable_mk.add hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.add hg.ae_eq_mk⟩

@[measurability]
/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: [SubtractionMonoid β] [ContinuousNeg β] (hf : AEFinStronglyMeasurable f μ)
  proof: ⟨-hf.mk f, hf.finStronglyMeasurable_mk.neg, hf.ae_eq_mk.neg⟩

@[measurability]

中文:
定理 neg
  条件: [Subtraction幺半群 β] [连续取负 β] (hf : AEFinStronglyMeasurable f μ)
  证明: ⟨-hf.mk f, hf.finStronglyMeasurable_mk.neg, hf.ae_eq_mk.neg⟩

@[measurability]
-/
protected theorem neg [SubtractionMonoid β] [ContinuousNeg β] (hf : AEFinStronglyMeasurable f μ) :
    AEFinStronglyMeasurable (-f) μ :=
  ⟨-hf.mk f, hf.finStronglyMeasurable_mk.neg, hf.ae_eq_mk.neg⟩

@[measurability]
/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  statement: [SubtractionMonoid β] [ContinuousSub β] (hf : AEFinStronglyMeasurable f μ)
  proof: ⟨hf.mk f - hg.mk g, hf.finStronglyMeasurable_mk.sub hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.sub hg.ae_eq_mk⟩

@[measurability]

中文:
定理 sub
  结论: [Subtraction幺半群 β] [余ntinuousSub β] (hf : AEFinStronglyMeasurable f μ)
  证明: ⟨hf.mk f - hg.mk g, hf.finStronglyMeasurable_mk.sub hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.sub hg.ae_eq_mk⟩

@[measurability]
-/
protected theorem sub [SubtractionMonoid β] [ContinuousSub β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f - g) μ :=
  ⟨hf.mk f - hg.mk g, hf.finStronglyMeasurable_mk.sub hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.sub hg.ae_eq_mk⟩

@[measurability]
/--
theorem `const_smul` / 定理 `const_smul`

English:
theorem const_smul
  statement: {𝕜} [TopologicalSpace 𝕜] [Zero β]
  proof: ⟨c • hf.mk f, hf.finStronglyMeasurable_mk.const_smul c, hf.ae_eq_mk.const_smul c⟩

中文:
定理 const_smul
  结论: {𝕜} [拓扑空间 𝕜] [零 β]
  证明: ⟨c • hf.mk f, hf.finStronglyMeasurable_mk.const_smul c, hf.ae_eq_mk.const_smul c⟩
-/
protected theorem const_smul {𝕜} [TopologicalSpace 𝕜] [Zero β]
    [SMulZeroClass 𝕜 β] [ContinuousSMul 𝕜 β] (hf : AEFinStronglyMeasurable f μ) (c : 𝕜) :
    AEFinStronglyMeasurable (c • f) μ :=
  ⟨c • hf.mk f, hf.finStronglyMeasurable_mk.const_smul c, hf.ae_eq_mk.const_smul c⟩

end Arithmetic

section Order

variable [Zero β]

@[aesop safe 20 (rule_sets := [Measurable])]
/--
theorem `sup` / 定理 `sup`

English:
theorem sup
  statement: [SemilatticeSup β] [ContinuousSup β] (hf : AEFinStronglyMeasurable f μ)
  proof: ⟨hf.mk f ⊔ hg.mk g, hf.finStronglyMeasurable_mk.sup hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.sup hg.ae_eq_mk⟩

@[aesop safe 20 (rule_sets := [Measurable])]

中文:
定理 上确界
  结论: [SemilatticeSup β] [余ntinuousSup β] (hf : AEFinStronglyMeasurable f μ)
  证明: ⟨hf.mk f ⊔ hg.mk g, hf.finStronglyMeasurable_mk.sup hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.sup hg.ae_eq_mk⟩

@[aesop safe 20 (rule_sets := [Measurable])]
-/
protected theorem sup [SemilatticeSup β] [ContinuousSup β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f ⊔ g) μ :=
  ⟨hf.mk f ⊔ hg.mk g, hf.finStronglyMeasurable_mk.sup hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.sup hg.ae_eq_mk⟩

@[aesop safe 20 (rule_sets := [Measurable])]
/--
theorem `inf` / 定理 `inf`

English:
theorem inf
  statement: [SemilatticeInf β] [ContinuousInf β] (hf : AEFinStronglyMeasurable f μ)
  proof: ⟨hf.mk f ⊓ hg.mk g, hf.finStronglyMeasurable_mk.inf hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.inf hg.ae_eq_mk⟩

中文:
定理 下确界
  结论: [SemilatticeInf β] [余ntinuousInf β] (hf : AEFinStronglyMeasurable f μ)
  证明: ⟨hf.mk f ⊓ hg.mk g, hf.finStronglyMeasurable_mk.inf hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.inf hg.ae_eq_mk⟩
-/
protected theorem inf [SemilatticeInf β] [ContinuousInf β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f ⊓ g) μ :=
  ⟨hf.mk f ⊓ hg.mk g, hf.finStronglyMeasurable_mk.inf hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.inf hg.ae_eq_mk⟩

end Order

variable [Zero β] [T2Space β]

/--
theorem `exists_set_sigmaFinite` / 定理 `exists_set_sigmaFinite`

English:
theorem exists_set_sigmaFinite
  given: (hf : AEFinStronglyMeasurable f μ)
  proof: by
  rcases hf with ⟨g, hg, hfg⟩
  obtain ⟨t, ht, hgt_zero, htμ⟩ := hg.exists_set_sigmaFinite
  refine ⟨t, ht, ?_, htμ⟩
  refine EventuallyEq.trans (ae_restrict_of_ae hfg) ?_
  rw [EventuallyEq]; rw [ae_restrict_iff' ht.compl]
  exact Eventually.of_forall hgt_zero

中文:
定理 存在_set_sigmaFinite
  条件: (hf : AEFinStronglyMeasurable f μ)
  证明: by
  rcases hf with ⟨g, hg, hfg⟩
  obtain ⟨t, ht, hgt_zero, htμ⟩ := hg.exists_set_sigmaFinite
  refine ⟨t, ht, ?_, htμ⟩
  refine EventuallyEq.trans (ae_restrict_of_ae hfg) ?_
  rw [EventuallyEq]; rw [ae_restrict_iff' ht.compl]
  exact Eventually.of_forall hgt_zero

Depends on / 依赖: Eventually, Eventually.of_forall, EventuallyEq, EventuallyEq.trans, ae_restrict_iff, ae_restrict_of_ae, exists_set_sigmaFinite, hg.exists_set_sigmaFinite, hgt_zero, ht.compl, of_forall
-/
theorem exists_set_sigmaFinite (hf : AEFinStronglyMeasurable f μ) :
    exists t, MeasurableSet t ∧ f =ᵐ[μ.restrict tᶜ] 0 ∧ SigmaFinite (μ.restrict t) := by
  rcases hf with ⟨g, hg, hfg⟩
  obtain ⟨t, ht, hgt_zero, htμ⟩ := hg.exists_set_sigmaFinite
  refine ⟨t, ht, ?_, htμ⟩
  refine EventuallyEq.trans (ae_restrict_of_ae hfg) ?_
  rw [EventuallyEq]; rw [ae_restrict_iff' ht.compl]
  exact Eventually.of_forall hgt_zero

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `sigmaFiniteSet` / `sigmaFiniteSet` 的定义

English:
definition sigmaFiniteSet
  signature: (hf : AEFinStronglyMeasurable f μ)
  body: hf.exists_set_sigmaFinite.choose

中文:
定义 sigmaFiniteSet
  签名: (hf : AEFinStronglyMeasurable f μ)
  定义体: hf.exists_set_sigmaFinite.choose

Depends on / 依赖: exists_set_sigmaFinite, hf.exists_set_sigmaFinite.choose
-/
noncomputable def sigmaFiniteSet (hf : AEFinStronglyMeasurable f μ) : Set α :=
  hf.exists_set_sigmaFinite.choose

/--
theorem `measurableSet` / 定理 `measurableSet`

English:
theorem measurableSet
  given: (hf : AEFinStronglyMeasurable f μ)
  proof: hf.exists_set_sigmaFinite.choose_spec.1

中文:
定理 measurableSet
  条件: (hf : AEFinStronglyMeasurable f μ)
  证明: hf.exists_set_sigmaFinite.choose_spec.1
-/
protected theorem measurableSet (hf : AEFinStronglyMeasurable f μ) :
    MeasurableSet hf.sigmaFiniteSet :=
  hf.exists_set_sigmaFinite.choose_spec.1

/--
theorem `ae_eq_zero_compl` / 定理 `ae_eq_zero_compl`

English:
theorem ae_eq_zero_compl
  given: (hf : AEFinStronglyMeasurable f μ)
  proof: hf.exists_set_sigmaFinite.choose_spec.2.1

中文:
定理 ae_eq_zero_compl
  条件: (hf : AEFinStronglyMeasurable f μ)
  证明: hf.exists_set_sigmaFinite.choose_spec.2.1

Depends on / 依赖: choose_spec, exists_set_sigmaFinite, hf.exists_set_sigmaFinite.choose_spec
-/
theorem ae_eq_zero_compl (hf : AEFinStronglyMeasurable f μ) :
    f =ᵐ[μ.restrict hf.sigmaFiniteSetᶜ] 0 :=
  hf.exists_set_sigmaFinite.choose_spec.2.1

/--
Instance `sigmaFinite_restrict` / 实例 `sigmaFinite_restrict`

English:
instance sigmaFinite_restrict
  signature: (hf : AEFinStronglyMeasurable f μ)
  body: hf.exists_set_sigmaFinite.choose_spec.2.2

中文:
实例 sigmaFinite_restrict
  签名: (hf : AEFinStronglyMeasurable f μ)
  定义体: hf.exists_set_sigmaFinite.choose_spec.2.2

Depends on / 依赖: choose_spec, exists_set_sigmaFinite, hf.exists_set_sigmaFinite.choose_spec
-/
instance sigmaFinite_restrict (hf : AEFinStronglyMeasurable f μ) :
    SigmaFinite (μ.restrict hf.sigmaFiniteSet) :=
  hf.exists_set_sigmaFinite.choose_spec.2.2

end AEFinStronglyMeasurable

section SecondCountableTopology

variable {G : Type*} [SeminormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] {f : α -> G}

/--
theorem `aefinStronglyMeasurable_iff_aemeasurable` / 定理 `aefinStronglyMeasurable_iff_aemeasurable`

English:
theorem aefinStronglyMeasurable_iff_aemeasurable
  statement: {_m0 : MeasurableSpace α} (μ : Measure α)
  proof: by
  simp_rw [AEFinStronglyMeasurable, AEMeasurable, finStronglyMeasurable_iff_measurable]

中文:
定理 aefinStronglyMeasurable_iff_aemeasurable
  结论: {_m0 : 可测空间 α} (μ : 测度 α)
  证明: by
  simp_rw [AEFinStronglyMeasurable, AEMeasurable, finStronglyMeasurable_iff_measurable]

Depends on / 依赖: AEFinStronglyMeasurable, AEMeasurable, finStronglyMeasurable_iff_measurable, simp_rw
-/
theorem aefinStronglyMeasurable_iff_aemeasurable {_m0 : MeasurableSpace α} (μ : Measure α)
    [SigmaFinite μ] : AEFinStronglyMeasurable f μ ↔ AEMeasurable f μ := by
  simp_rw [AEFinStronglyMeasurable, AEMeasurable, finStronglyMeasurable_iff_measurable]

/-- In a space with second countable topology and a sigma-finite measure,
  an `AEMeasurable` function is `AEFinStronglyMeasurable`. -/
@[aesop 90% apply (rule_sets := [Measurable])]
/--
theorem `aefinStronglyMeasurable_of_aemeasurable` / 定理 `aefinStronglyMeasurable_of_aemeasurable`

English:
theorem aefinStronglyMeasurable_of_aemeasurable
  statement: {_m0 : MeasurableSpace α} (μ : Measure α)
  proof: (aefinStronglyMeasurable_iff_aemeasurable μ).mpr hf

中文:
定理 aefinStronglyMeasurable_of_aemeasurable
  结论: {_m0 : 可测空间 α} (μ : 测度 α)
  证明: (aefinStronglyMeasurable_iff_aemeasurable μ).mpr hf

Depends on / 依赖: aefinStronglyMeasurable_iff_aemeasurable
-/
theorem aefinStronglyMeasurable_of_aemeasurable {_m0 : MeasurableSpace α} (μ : Measure α)
    [SigmaFinite μ] (hf : AEMeasurable f μ) : AEFinStronglyMeasurable f μ :=
  (aefinStronglyMeasurable_iff_aemeasurable μ).mpr hf

end SecondCountableTopology

end MeasureTheory
