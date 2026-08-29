/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL1
public import Mathlib.Tactic.CrossRefAttribute

import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-! # Conditional expectation

We build the conditional expectation of an integrable function `f` with value in a Banach space
with respect to a measure `μ` (defined on a measurable space structure `m₀`) and a measurable space
structure `m` with `hm : m ≤ m₀` (a sub-sigma-algebra). This is an `m`-strongly measurable
function `μ[f | m]` which is integrable and verifies `∫ x in s, μ[f | m] x ∂μ = ∫ x in s, f x ∂μ`
for all `m`-measurable sets `s`. It is unique as an element of `L¹`.

The construction is done in four steps:
* Define the conditional expectation of an `L²` function, as an element of `L²`. This is the
  orthogonal projection on the subspace of almost everywhere `m`-measurable functions.
* Show that the conditional expectation of the indicator of a measurable set with finite measure
  is integrable and define a map `Set α → (E →L[ℝ] (α →₁[μ] E))` which to a set associates a linear
  map. That linear map sends `x ∈ E` to the conditional expectation of the indicator of the set
  with value `x`.
* Extend that map to `condExpL1CLM : (α →₁[μ] E) →L[ℝ] (α →₁[μ] E)`. This is done using the same
  construction as the Bochner integral (see the file `MeasureTheory/Integral/SetToL1`).
* Define the conditional expectation of a function `f : α → E`, which is an integrable function
  `α → E` equal to 0 if `f` is not integrable, and equal to an `m`-measurable representative of
  `condExpL1CLM` applied to `[f]`, the equivalence class of `f` in `L¹`.

The first step is done in `MeasureTheory.Function.ConditionalExpectation.CondexpL2`, the two
next steps in `MeasureTheory.Function.ConditionalExpectation.CondexpL1` and the final step is
performed in this file.

## Main results

The conditional expectation and its properties

* `condExp (m : MeasurableSpace α) (μ : Measure α) (f : α → E)`: conditional expectation of `f`
  with respect to `m`.
* `integrable_condExp` : `condExp` is integrable.
* `stronglyMeasurable_condExp` : `condExp` is `m`-strongly-measurable.
* `setIntegral_condExp (hf : Integrable f μ) (hs : MeasurableSet[m] s)` : if `m ≤ m₀` (the
  σ-algebra over which the measure is defined), then the conditional expectation verifies
  `∫ x in s, condExp m μ f x ∂μ = ∫ x in s, f x ∂μ` for any `m`-measurable set `s`.

While `condExp` is function-valued, we also define `condExpL1` with value in `L1` and a continuous
linear map `condExpL1CLM` from `L1` to `L1`. `condExp` should be used in most cases.

Uniqueness of the conditional expectation

* `ae_eq_condExp_of_forall_setIntegral_eq`: an a.e. `m`-measurable function which verifies the
  equality of integrals is a.e. equal to `condExp`.

## Notation

For a measure `μ` defined on a measurable space structure `m₀`, another measurable space structure
`m` with `hm : m ≤ m₀` (a sub-σ-algebra) and a function `f`, we define the notation
* `μ[f | m] = condExp m μ f`.

## TODO

See https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Conditional.20expectation.20of.20product
for how to prove that we can pull `m`-measurable continuous linear maps out of the `m`-conditional
expectation. This would generalise `MeasureTheory.condExp_mul_of_stronglyMeasurable_left`.

## Tags

conditional expectation, conditional expected value

-/

@[expose] public section

open TopologicalSpace MeasureTheory.Lp Filter
open scoped ENNReal Topology MeasureTheory

namespace MeasureTheory
  -- 𝕜 for ℝ or ℂ
  -- E for integrals on a Lp submodule
variable {α β E 𝕜 : Type*} [RCLike 𝕜] {m m₀ : MeasurableSpace α} {μ : Measure α} {f g : α -> E}
  {s : Set α}

section NormedAddCommGroup
variable [NormedAddCommGroup E]

section NormedSpace
variable [NormedSpace Real E]

open scoped Classical in
variable (m) in
/-- Conditional expectation of a function, with notation `μ[f | m]`.

It is defined as 0 if any one of the following conditions is true:
- `m` is not a sub-σ-algebra of `m₀`,
- `μ` is not σ-finite with respect to `m`,
- `f` is not integrable. -/
@[wikidata Q772232]
noncomputable irreducible_def condExp (μ : Measure[m₀] α) (f : α -> E) : α -> E :=
  if hm : m <= m₀ then
    if h : SigmaFinite (μ.trim hm) ∧ Integrable f μ then
      if StronglyMeasurable[m] f then f
      else have := h.1; aestronglyMeasurable_condExpL1.mk (condExpL1 hm μ f)
    else 0
  else 0

@[inherit_doc MeasureTheory.condExp]
scoped macro:max μ:term noWs "[" f:term " | " m:term "]" : term =>
  `(MeasureTheory.condExp $m $μ $f)

/-- Unexpander for `μ[f | m]` notation. -/
@[app_unexpander MeasureTheory.condExp]
meta def condExpUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $m $μ $f) => `($μ[$f|$m])
  | _ => throw ()

/-- info: μ[f | m] : α → E -/
#guard_msgs in
#check μ[f | m]
/-- info: μ[f | m] sorry : E -/
#guard_msgs in
#check μ[f | m] (sorry : α)

/--
theorem `condExp_of_not_le` / 定理 `condExp_of_not_le`

English:
theorem condExp_of_not_le
  given: (hm_not : ¬m <= m₀)
  statement: μ[f | m] = 0
  proof: by rw [condExp, dif_neg hm_not]

中文:
定理 condExp_of_not_le
  条件: (hm_not : ¬m <= m₀)
  结论: μ[f | m] = 0
  证明: by rw [condExp, dif_neg hm_not]

Depends on / 依赖: condExp, dif_neg, hm_not
-/
theorem condExp_of_not_le (hm_not : ¬m <= m₀) : μ[f | m] = 0 := by rw [condExp, dif_neg hm_not]

/--
theorem `condExp_of_not_sigmaFinite` / 定理 `condExp_of_not_sigmaFinite`

English:
theorem condExp_of_not_sigmaFinite
  given: (hm : m <= m₀) (hμm_not : ¬SigmaFinite (μ.trim hm))
  proof: by rw [condExp, dif_pos hm, dif_neg]; push Not; exact fun h => absurd h hμm_not

中文:
定理 condExp_of_not_sigmaFinite
  条件: (hm : m <= m₀) (hμm_not : ¬SigmaFinite (μ.trim hm))
  证明: by rw [condExp, dif_pos hm, dif_neg]; push Not; exact fun h => absurd h hμm_not

Depends on / 依赖: absurd, condExp, dif_neg, dif_pos
-/
theorem condExp_of_not_sigmaFinite (hm : m <= m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) :
    μ[f | m] = 0 := by rw [condExp, dif_pos hm, dif_neg]; push Not; exact fun h => absurd h hμm_not

open scoped Classical in
/--
theorem `condExp_of_sigmaFinite` / 定理 `condExp_of_sigmaFinite`

English:
theorem condExp_of_sigmaFinite
  given: (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)]
  proof: by
  rw [condExp]; rw [dif_pos hm]
  grind

中文:
定理 condExp_of_sigmaFinite
  条件: (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)]
  证明: by
  rw [condExp]; rw [dif_pos hm]
  grind

Depends on / 依赖: condExp, dif_pos
-/
theorem condExp_of_sigmaFinite (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] :
    μ[f | m] =
      if Integrable f μ then
        if StronglyMeasurable[m] f then f
        else aestronglyMeasurable_condExpL1.mk (condExpL1 hm μ f)
      else 0 := by
  rw [condExp]; rw [dif_pos hm]
  grind

/--
theorem `condExp_of_stronglyMeasurable` / 定理 `condExp_of_stronglyMeasurable`

English:
theorem condExp_of_stronglyMeasurable
  statement: (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E}
  proof: by
  rw [condExp_of_sigmaFinite hm]; rw [if_pos hfi]; rw [if_pos hf]

@[simp]

中文:
定理 condExp_of_stronglyMeasurable
  结论: (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E}
  证明: by
  rw [condExp_of_sigmaFinite hm]; rw [if_pos hfi]; rw [if_pos hf]

@[simp]

Depends on / 依赖: condExp_of_sigmaFinite, if_pos
-/
theorem condExp_of_stronglyMeasurable (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E}
    (hf : StronglyMeasurable[m] f) (hfi : Integrable f μ) : μ[f | m] = f := by
  rw [condExp_of_sigmaFinite hm]; rw [if_pos hfi]; rw [if_pos hf]

@[simp]
/--
theorem `condExp_const` / 定理 `condExp_const`

English:
theorem condExp_const
  given: (hm : m <= m₀) (c : E) [IsFiniteMeasure μ]
  proof: condExp_of_stronglyMeasurable hm stronglyMeasurable_const (integrable_const c)

中文:
定理 condExp_const
  条件: (hm : m <= m₀) (c : E) [IsFiniteMeasure μ]
  证明: condExp_of_stronglyMeasurable hm stronglyMeasurable_const (integrable_const c)

Depends on / 依赖: condExp_of_stronglyMeasurable, integrable_const, stronglyMeasurable_const
-/
theorem condExp_const (hm : m <= m₀) (c : E) [IsFiniteMeasure μ] :
    μ[fun _ : α => c | m] = fun _ => c :=
  condExp_of_stronglyMeasurable hm stronglyMeasurable_const (integrable_const c)

/--
theorem `condExp_ae_eq_condExpL1` / 定理 `condExp_ae_eq_condExpL1`

English:
theorem condExp_ae_eq_condExpL1
  statement: [CompleteSpace E]
  proof: by
  rw [condExp_of_sigmaFinite hm]
  by_cases hfi : Integrable f μ
  · rw [if_pos hfi]
    by_cases hfm : StronglyMeasurable[m] f
    · rw [if_pos hfm]
      exact (condExpL1_of_aestronglyMeasurable' hfm.aestronglyMeasurable hfi).symm
    · rw [if_neg hfm]
      exact aestronglyMeasurable_condExpL1

中文:
定理 condExp_ae_eq_condExpL1
  结论: [CompleteSpace E]
  证明: by
  rw [condExp_of_sigmaFinite hm]
  by_cases hfi : Integrable f μ
  · rw [if_pos hfi]
    by_cases hfm : StronglyMeasurable[m] f
    · rw [if_pos hfm]
      exact (condExpL1_of_aestronglyMeasurable' hfm.aestronglyMeasurable hfi).symm
    · rw [if_neg hfm]
      exact aestronglyMeasurable_condExpL1

Depends on / 依赖: Integrable, StronglyMeasurable, ae_eq_mk, aestronglyMeasurable, aestronglyMeasurable_condExpL1, aestronglyMeasurable_condExpL1.ae_eq_mk.symm, coeFn_zero, condExpL1_of_aestronglyMeasurable, condExpL1_undef, condExp_of_sigmaFinite, hfm.aestronglyMeasurable, if_neg, if_pos
-/
theorem condExp_ae_eq_condExpL1 [CompleteSpace E]
    (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] (f : α -> E) :
    μ[f | m] =ᵐ[μ] condExpL1 hm μ f := by
  rw [condExp_of_sigmaFinite hm]
  by_cases hfi : Integrable f μ
  · rw [if_pos hfi]
    by_cases hfm : StronglyMeasurable[m] f
    · rw [if_pos hfm]
      exact (condExpL1_of_aestronglyMeasurable' hfm.aestronglyMeasurable hfi).symm
    · rw [if_neg hfm]
      exact aestronglyMeasurable_condExpL1.ae_eq_mk.symm
  rw [if_neg hfi]; rw [condExpL1_undef hfi]
  exact (coeFn_zero _ _ _).symm

/--
theorem `condExp_ae_eq_condExpL1CLM` / 定理 `condExp_ae_eq_condExpL1CLM`

English:
theorem condExp_ae_eq_condExpL1CLM
  statement: [CompleteSpace E]
  proof: by
  refine (condExp_ae_eq_condExpL1 hm f).trans (Eventually.of_forall fun x => ?_)
  rw [condExpL1_eq hf]

中文:
定理 condExp_ae_eq_condExpL1CLM
  结论: [CompleteSpace E]
  证明: by
  refine (condExp_ae_eq_condExpL1 hm f).trans (Eventually.of_forall fun x => ?_)
  rw [condExpL1_eq hf]

Depends on / 依赖: Eventually, Eventually.of_forall, condExpL1_eq, condExp_ae_eq_condExpL1, of_forall
-/
theorem condExp_ae_eq_condExpL1CLM [CompleteSpace E]
    (hm : m <= m₀) [SigmaFinite (μ.trim hm)] (hf : Integrable f μ) :
    μ[f | m] =ᵐ[μ] condExpL1CLM E hm μ (hf.toL1 f) := by
  refine (condExp_ae_eq_condExpL1 hm f).trans (Eventually.of_forall fun x => ?_)
  rw [condExpL1_eq hf]

/--
theorem `condExp_of_not_integrable` / 定理 `condExp_of_not_integrable`

English:
theorem condExp_of_not_integrable
  given: (hf : ¬Integrable f μ)
  statement: μ[f | m] = 0
  proof: by
  by_cases hm : m <= m₀
  swap; · rw [condExp_of_not_le hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condExp_of_not_sigmaFinite hm hμm]
  rw [condExp_of_sigmaFinite]; rw [if_neg hf]

@[to_fun (attr := simp) condExp_fun_zero]

中文:
定理 condExp_of_not_integrable
  条件: (hf : ¬整数egrable f μ)
  结论: μ[f | m] = 0
  证明: by
  by_cases hm : m <= m₀
  swap; · rw [condExp_of_not_le hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condExp_of_not_sigmaFinite hm hμm]
  rw [condExp_of_sigmaFinite]; rw [if_neg hf]

@[to_fun (attr := simp) condExp_fun_zero]

Depends on / 依赖: SigmaFinite, condExp_of_not_le, condExp_of_not_sigmaFinite, condExp_of_sigmaFinite, if_neg
-/
theorem condExp_of_not_integrable (hf : ¬Integrable f μ) : μ[f | m] = 0 := by
  by_cases hm : m <= m₀
  swap; · rw [condExp_of_not_le hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condExp_of_not_sigmaFinite hm hμm]
  rw [condExp_of_sigmaFinite]; rw [if_neg hf]

@[to_fun (attr := simp) condExp_fun_zero]
/--
theorem `condExp_zero` / 定理 `condExp_zero`

English:
theorem condExp_zero
  statement: μ[(0 : α -> E) | m] = 0
  proof: by
  by_cases hm : m <= m₀
  swap; · rw [condExp_of_not_le hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condExp_of_not_sigmaFinite hm hμm]
  exact condExp_of_stronglyMeasurable hm stronglyMeasurable_zero (integrable_zero _ _ _)

@[fun_prop]

中文:
定理 condExp_zero
  结论: μ[(0 : α -> E) | m] = 0
  证明: by
  by_cases hm : m <= m₀
  swap; · rw [condExp_of_not_le hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condExp_of_not_sigmaFinite hm hμm]
  exact condExp_of_stronglyMeasurable hm stronglyMeasurable_zero (integrable_zero _ _ _)

@[fun_prop]

Depends on / 依赖: SigmaFinite, condExp_of_not_le, condExp_of_not_sigmaFinite, condExp_of_stronglyMeasurable, integrable_zero, stronglyMeasurable_zero
-/
theorem condExp_zero : μ[(0 : α -> E) | m] = 0 := by
  by_cases hm : m <= m₀
  swap; · rw [condExp_of_not_le hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condExp_of_not_sigmaFinite hm hμm]
  exact condExp_of_stronglyMeasurable hm stronglyMeasurable_zero (integrable_zero _ _ _)

@[fun_prop]
/--
theorem `stronglyMeasurable_condExp` / 定理 `stronglyMeasurable_condExp`

English:
theorem stronglyMeasurable_condExp
  statement: StronglyMeasurable[m] (μ[f | m])
  proof: by
  by_cases hm : m <= m₀
  swap; · rw [condExp_of_not_le hm]; exact stronglyMeasurable_zero
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condExp_of_not_sigmaFinite hm hμm]; exact stronglyMeasurable_zero
  rw [condExp_of_sigmaFinite hm]
  split_ifs with hfi hfm
  · exact hfm
  · exact aes

中文:
定理 stronglyMeasurable_condExp
  结论: StronglyMeasurable[m] (μ[f | m])
  证明: by
  by_cases hm : m <= m₀
  swap; · rw [condExp_of_not_le hm]; exact stronglyMeasurable_zero
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condExp_of_not_sigmaFinite hm hμm]; exact stronglyMeasurable_zero
  rw [condExp_of_sigmaFinite hm]
  split_ifs with hfi hfm
  · exact hfm
  · exact aes

Depends on / 依赖: SigmaFinite, aestronglyMeasurable_condExpL1, aestronglyMeasurable_condExpL1.stronglyMeasurable_mk, condExp_of_not_le, condExp_of_not_sigmaFinite, condExp_of_sigmaFinite, split_ifs, stronglyMeasurable_mk, stronglyMeasurable_zero
-/
theorem stronglyMeasurable_condExp : StronglyMeasurable[m] (μ[f | m]) := by
  by_cases hm : m <= m₀
  swap; · rw [condExp_of_not_le hm]; exact stronglyMeasurable_zero
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condExp_of_not_sigmaFinite hm hμm]; exact stronglyMeasurable_zero
  rw [condExp_of_sigmaFinite hm]
  split_ifs with hfi hfm
  · exact hfm
  · exact aestronglyMeasurable_condExpL1.stronglyMeasurable_mk
  · exact stronglyMeasurable_zero

variable [CompleteSpace E]

@[gcongr]
/--
theorem `condExp_congr_ae` / 定理 `condExp_congr_ae`

English:
theorem condExp_congr_ae
  given: (h : f =ᵐ[μ] g)
  statement: μ[f | m] =ᵐ[μ] μ[g | m]
  proof: by
  by_cases hm : m <= m₀
  swap; · simp_rw [condExp_of_not_le hm]; rfl
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; rfl
  exact (condExp_ae_eq_condExpL1 hm f).trans
    (Filter.EventuallyEq.trans (by rw [condExpL1_congr_ae hm h])
      (condExp_ae

中文:
定理 condExp_congr_ae
  条件: (h : f =ᵐ[μ] g)
  结论: μ[f | m] =ᵐ[μ] μ[g | m]
  证明: by
  by_cases hm : m <= m₀
  swap; · simp_rw [condExp_of_not_le hm]; rfl
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; rfl
  exact (condExp_ae_eq_condExpL1 hm f).trans
    (Filter.EventuallyEq.trans (by rw [condExpL1_congr_ae hm h])
      (condExp_ae

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.trans, SigmaFinite, condExpL1_congr_ae, condExp_ae_eq_condExpL1, condExp_of_not_le, condExp_of_not_sigmaFinite, simp_rw
-/
theorem condExp_congr_ae (h : f =ᵐ[μ] g) : μ[f | m] =ᵐ[μ] μ[g | m] := by
  by_cases hm : m <= m₀
  swap; · simp_rw [condExp_of_not_le hm]; rfl
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; rfl
  exact (condExp_ae_eq_condExpL1 hm f).trans
    (Filter.EventuallyEq.trans (by rw [condExpL1_congr_ae hm h])
      (condExp_ae_eq_condExpL1 hm g).symm)

/--
lemma `condExp_congr_ae_trim` / 引理 `condExp_congr_ae_trim`

English:
lemma condExp_congr_ae_trim
  given: (hm : m <= m₀) (hfg : f =ᵐ[μ] g)
  proof: StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm
    stronglyMeasurable_condExp stronglyMeasurable_condExp (condExp_congr_ae hfg)

中文:
引理 condExp_congr_ae_trim
  条件: (hm : m <= m₀) (hfg : f =ᵐ[μ] g)
  证明: StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm
    stronglyMeasurable_condExp stronglyMeasurable_condExp (condExp_congr_ae hfg)

Depends on / 依赖: StronglyMeasurable, StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable, ae_eq_trim_of_stronglyMeasurable, condExp_congr_ae, stronglyMeasurable_condExp
-/
lemma condExp_congr_ae_trim (hm : m <= m₀) (hfg : f =ᵐ[μ] g) :
    μ[f | m] =ᵐ[μ.trim hm] μ[g | m] :=
  StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm
    stronglyMeasurable_condExp stronglyMeasurable_condExp (condExp_congr_ae hfg)

/--
theorem `condExp_of_aestronglyMeasurable'` / 定理 `condExp_of_aestronglyMeasurable'`

English:
theorem condExp_of_aestronglyMeasurable'
  statement: (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E}
  proof: by
  refine ((condExp_congr_ae hf.ae_eq_mk).trans ?_).trans hf.ae_eq_mk.symm
  rw [condExp_of_stronglyMeasurable hm hf.stronglyMeasurable_mk
    ((integrable_congr hf.ae_eq_mk).mp hfi)]

@[fun_prop]

中文:
定理 condExp_of_aestronglyMeasurable'
  结论: (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E}
  证明: by
  refine ((condExp_congr_ae hf.ae_eq_mk).trans ?_).trans hf.ae_eq_mk.symm
  rw [condExp_of_stronglyMeasurable hm hf.stronglyMeasurable_mk
    ((integrable_congr hf.ae_eq_mk).mp hfi)]

@[fun_prop]

Depends on / 依赖: ae_eq_mk, condExp_congr_ae, condExp_of_stronglyMeasurable, hf.ae_eq_mk, hf.ae_eq_mk.symm, hf.stronglyMeasurable_mk, integrable_congr, stronglyMeasurable_mk
-/
theorem condExp_of_aestronglyMeasurable' (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E}
    (hf : AEStronglyMeasurable[m] f μ) (hfi : Integrable f μ) : μ[f | m] =ᵐ[μ] f := by
  refine ((condExp_congr_ae hf.ae_eq_mk).trans ?_).trans hf.ae_eq_mk.symm
  rw [condExp_of_stronglyMeasurable hm hf.stronglyMeasurable_mk
    ((integrable_congr hf.ae_eq_mk).mp hfi)]

@[fun_prop]
/--
theorem `integrable_condExp` / 定理 `integrable_condExp`

English:
theorem integrable_condExp
  statement: Integrable (μ[f | m]) μ
  proof: by
  by_cases hm : m <= m₀
  swap; · rw [condExp_of_not_le hm]; exact integrable_zero _ _ _
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condExp_of_not_sigmaFinite hm hμm]; exact integrable_zero _ _ _
  exact (integrable_condExpL1 f).congr (condExp_ae_eq_condExpL1 hm f).symm

中文:
定理 integrable_condExp
  结论: 整数egrable (μ[f | m]) μ
  证明: by
  by_cases hm : m <= m₀
  swap; · rw [condExp_of_not_le hm]; exact integrable_zero _ _ _
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condExp_of_not_sigmaFinite hm hμm]; exact integrable_zero _ _ _
  exact (integrable_condExpL1 f).congr (condExp_ae_eq_condExpL1 hm f).symm

Depends on / 依赖: SigmaFinite, condExp_ae_eq_condExpL1, condExp_of_not_le, condExp_of_not_sigmaFinite, integrable_condExpL1, integrable_zero
-/
theorem integrable_condExp : Integrable (μ[f | m]) μ := by
  by_cases hm : m <= m₀
  swap; · rw [condExp_of_not_le hm]; exact integrable_zero _ _ _
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condExp_of_not_sigmaFinite hm hμm]; exact integrable_zero _ _ _
  exact (integrable_condExpL1 f).congr (condExp_ae_eq_condExpL1 hm f).symm

/--
theorem `setIntegral_condExp` / 定理 `setIntegral_condExp`

English:
theorem setIntegral_condExp
  statement: (hm : m <= m₀) [SigmaFinite (μ.trim hm)] (hf : Integrable f μ)
  proof: by
  rw [setIntegral_congr_ae (hm s hs) ((condExp_ae_eq_condExpL1 hm f).mono fun x hx _ => hx)]
  exact setIntegral_condExpL1 hf hs

中文:
定理 setIntegral_condExp
  结论: (hm : m <= m₀) [SigmaFinite (μ.trim hm)] (hf : 整数egrable f μ)
  证明: by
  rw [setIntegral_congr_ae (hm s hs) ((condExp_ae_eq_condExpL1 hm f).mono fun x hx _ => hx)]
  exact setIntegral_condExpL1 hf hs

Depends on / 依赖: condExp_ae_eq_condExpL1, setIntegral_condExpL1, setIntegral_congr_ae
-/
theorem setIntegral_condExp (hm : m <= m₀) [SigmaFinite (μ.trim hm)] (hf : Integrable f μ)
    (hs : MeasurableSet[m] s) : ∫ x in s, (μ[f | m]) x ∂μ = ∫ x in s, f x ∂μ := by
  rw [setIntegral_congr_ae (hm s hs) ((condExp_ae_eq_condExpL1 hm f).mono fun x hx _ => hx)]
  exact setIntegral_condExpL1 hf hs

/--
theorem `integral_condExp` / 定理 `integral_condExp`

English:
theorem integral_condExp
  given: (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)]
  proof: by
  by_cases hf : Integrable f μ
  · suffices ∫ x in Set.univ, (μ[f | m]) x ∂μ = ∫ x in Set.univ, f x ∂μ by
      simp_rw [setIntegral_univ] at this; exact this
    exact setIntegral_condExp hm hf .univ
  simp only [condExp_of_not_integrable hf, Pi.zero_apply, integral_zero, integral_undef hf]

中文:
定理 integral_condExp
  条件: (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)]
  证明: by
  by_cases hf : Integrable f μ
  · suffices ∫ x in Set.univ, (μ[f | m]) x ∂μ = ∫ x in Set.univ, f x ∂μ by
      simp_rw [setIntegral_univ] at this; exact this
    exact setIntegral_condExp hm hf .univ
  simp only [condExp_of_not_integrable hf, Pi.zero_apply, integral_zero, integral_undef hf]

Depends on / 依赖: Integrable, Pi.zero_apply, Set.univ, condExp_of_not_integrable, integral_undef, integral_zero, setIntegral_condExp, setIntegral_univ, simp_rw, zero_apply
-/
theorem integral_condExp (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] :
    ∫ x, (μ[f | m]) x ∂μ = ∫ x, f x ∂μ := by
  by_cases hf : Integrable f μ
  · suffices ∫ x in Set.univ, (μ[f | m]) x ∂μ = ∫ x in Set.univ, f x ∂μ by
      simp_rw [setIntegral_univ] at this; exact this
    exact setIntegral_condExp hm hf .univ
  simp only [condExp_of_not_integrable hf, Pi.zero_apply, integral_zero, integral_undef hf]

/--
theorem `integral_condExp_indicator` / 定理 `integral_condExp_indicator`

English:
theorem integral_condExp_indicator
  statement: [mβ : MeasurableSpace β] {Y : α -> β} (hY : Measurable Y)
  proof: by
  rw [integral_condExp]; rw [integral_indicator hA]; rw [setIntegral_const]; rw [smul_eq_mul]; rw [mul_one]

中文:
定理 integral_condExp_indicator
  结论: [mβ : MeasurableSpace β] {Y : α -> β} (hY : Measurable Y)
  证明: by
  rw [integral_condExp]; rw [integral_indicator hA]; rw [setIntegral_const]; rw [smul_eq_mul]; rw [mul_one]

Depends on / 依赖: integral_condExp, integral_indicator, mul_one, setIntegral_const, smul_eq_mul
-/
theorem integral_condExp_indicator [mβ : MeasurableSpace β] {Y : α -> β} (hY : Measurable Y)
    [SigmaFinite (μ.trim hY.comap_le)] {A : Set α} (hA : MeasurableSet A) :
    ∫ x, (μ[(A.indicator fun _ => (1 : Real)) | mβ.comap Y]) x ∂μ = μ.real A := by
  rw [integral_condExp]; rw [integral_indicator hA]; rw [setIntegral_const]; rw [smul_eq_mul]; rw [mul_one]

/--
theorem `ae_eq_condExp_of_forall_setIntegral_eq` / 定理 `ae_eq_condExp_of_forall_setIntegral_eq`

English:
theorem ae_eq_condExp_of_forall_setIntegral_eq
  statement: (hm : m <= m₀) [SigmaFinite (μ.trim hm)]
  proof: by
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hm hg_int_finite
    (fun s _ _ => integrable_condExp.integrableOn) (fun s hs hμs => ?_) hgm
    (StronglyMeasurable.aestronglyMeasurable stronglyMeasurable_condExp)
  rw [hg_eq s hs hμs]; rw [setIntegral_condExp hm hf hs]

中文:
定理 ae_eq_condExp_of_forall_setIntegral_eq
  结论: (hm : m <= m₀) [SigmaFinite (μ.trim hm)]
  证明: by
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hm hg_int_finite
    (fun s _ _ => integrable_condExp.integrableOn) (fun s hs hμs => ?_) hgm
    (StronglyMeasurable.aestronglyMeasurable stronglyMeasurable_condExp)
  rw [hg_eq s hs hμs]; rw [setIntegral_condExp hm hf hs]

Depends on / 依赖: StronglyMeasurable, StronglyMeasurable.aestronglyMeasurable, ae_eq_of_forall_setIntegral_eq_of_sigmaFinite, aestronglyMeasurable, hg_eq, hg_int_finite, integrableOn, integrable_condExp, integrable_condExp.integrableOn, setIntegral_condExp, stronglyMeasurable_condExp
-/
theorem ae_eq_condExp_of_forall_setIntegral_eq (hm : m <= m₀) [SigmaFinite (μ.trim hm)]
    {f g : α -> E} (hf : Integrable f μ)
    (hg_int_finite : forall s, MeasurableSet[m] s -> μ s < ∞ -> IntegrableOn g s μ)
    (hg_eq : forall s : Set α, MeasurableSet[m] s -> μ s < ∞ -> ∫ x in s, g x ∂μ = ∫ x in s, f x ∂μ)
    (hgm : AEStronglyMeasurable[m] g μ) : g =ᵐ[μ] μ[f | m] := by
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hm hg_int_finite
    (fun s _ _ => integrable_condExp.integrableOn) (fun s hs hμs => ?_) hgm
    (StronglyMeasurable.aestronglyMeasurable stronglyMeasurable_condExp)
  rw [hg_eq s hs hμs]; rw [setIntegral_condExp hm hf hs]

/--
theorem `condExp_bot'` / 定理 `condExp_bot'`

English:
theorem condExp_bot'
  given: [hμ : NeZero μ] (f : α -> E)
  proof: by
  by_cases hμ_finite : IsFiniteMeasure μ
  swap
  · have h : ¬SigmaFinite (μ.trim bot_le) := by rwa [sigmaFinite_trim_bot_iff]
    rw [not_isFiniteMeasure_iff] at hμ_finite
    rw [condExp_of_not_sigmaFinite bot_le h]
    simp only [hμ_finite, ENNReal.toReal_top, inv_zero, zero_smul, measureReal_

中文:
定理 condExp_bot'
  条件: [hμ : NeZero μ] (f : α -> E)
  证明: by
  by_cases hμ_finite : IsFiniteMeasure μ
  swap
  · have h : ¬SigmaFinite (μ.trim bot_le) := by rwa [sigmaFinite_trim_bot_iff]
    rw [not_isFiniteMeasure_iff] at hμ_finite
    rw [condExp_of_not_sigmaFinite bot_le h]
    simp only [hμ_finite, ENNReal.toReal_top, inv_zero, zero_smul, measureReal_

Depends on / 依赖: ENNReal, ENNReal.toReal_top, IsFiniteMeasure, SigmaFinite, StronglyMeasurable, bot_le, condExp_of_not_sigmaFinite, h_eq, h_integral, h_meas, integral_, inv_zero, measureReal_def, not_isFiniteMeasure_iff, sigmaFinite_trim_bot_iff, stronglyMeasurable_bot_iff, stronglyMeasurable_bot_iff.mp, stronglyMeasurable_condExp, toReal_top, zero_smul
-/
theorem condExp_bot' [hμ : NeZero μ] (f : α -> E) :
    μ[f | ⊥] = fun _ => (μ.real Set.univ)⁻¹ • ∫ x, f x ∂μ := by
  by_cases hμ_finite : IsFiniteMeasure μ
  swap
  · have h : ¬SigmaFinite (μ.trim bot_le) := by rwa [sigmaFinite_trim_bot_iff]
    rw [not_isFiniteMeasure_iff] at hμ_finite
    rw [condExp_of_not_sigmaFinite bot_le h]
    simp only [hμ_finite, ENNReal.toReal_top, inv_zero, zero_smul, measureReal_def]
    rfl
  have h_meas : StronglyMeasurable[⊥] (μ[f | ⊥]) := stronglyMeasurable_condExp
  obtain ⟨c, h_eq⟩ := stronglyMeasurable_bot_iff.mp h_meas
  rw [h_eq]
  have h_integral : ∫ x, (μ[f | ⊥]) x ∂μ = ∫ x, f x ∂μ := integral_condExp bot_le
  simp_rw [h_eq, integral_const] at h_integral
  rw [← h_integral]; rw [← smul_assoc]; rw [smul_eq_mul]; rw [inv_mul_cancel₀]; rw [one_smul]
  rw [Ne]; rw [measureReal_def]; rw [ENNReal.toReal_eq_zero_iff]; rw [not_or]
  exact ⟨NeZero.ne _, measure_ne_top μ Set.univ⟩

/--
theorem `condExp_bot_ae_eq` / 定理 `condExp_bot_ae_eq`

English:
theorem condExp_bot_ae_eq
  given: (f : α -> E)
  proof: by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · rw [ae_zero]; exact eventually_bot
· exact Eventually.of_forall congr_fun (condExp_bot' f)

@[simp]

中文:
定理 condExp_bot_ae_eq
  条件: (f : α -> E)
  证明: by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · rw [ae_zero]; exact eventually_bot
· exact Eventually.of_forall congr_fun (condExp_bot' f)

@[simp]

Depends on / 依赖: Eventually, Eventually.of_forall, ae_zero, condExp_bot, congr_fun, eq_zero_or_neZero, eventually_bot, of_forall
-/
theorem condExp_bot_ae_eq (f : α -> E) :
    μ[f | ⊥] =ᵐ[μ] fun _ => (μ.real Set.univ)⁻¹ • ∫ x, f x ∂μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · rw [ae_zero]; exact eventually_bot
· exact Eventually.of_forall congr_fun (condExp_bot' f)

@[simp]
/--
theorem `condExp_bot` / 定理 `condExp_bot`

English:
theorem condExp_bot
  given: [IsProbabilityMeasure μ] (f : α -> E)
  statement: μ[f | ⊥] = fun _ => ∫ x, f x ∂μ
  proof: by
  refine (condExp_bot' f).trans ?_
  rw [probReal_univ]; rw [inv_one]; rw [one_smul]

中文:
定理 condExp_bot
  条件: [IsProbabilityMeasure μ] (f : α -> E)
  结论: μ[f | ⊥] = fun _ => ∫ x, f x ∂μ
  证明: by
  refine (condExp_bot' f).trans ?_
  rw [probReal_univ]; rw [inv_one]; rw [one_smul]

Depends on / 依赖: condExp_bot, inv_one, one_smul, probReal_univ
-/
theorem condExp_bot [IsProbabilityMeasure μ] (f : α -> E) : μ[f | ⊥] = fun _ => ∫ x, f x ∂μ := by
  refine (condExp_bot' f).trans ?_
  rw [probReal_univ]; rw [inv_one]; rw [one_smul]

/--
theorem `condExp_add` / 定理 `condExp_add`

English:
theorem condExp_add
  given: (hf : Integrable f μ) (hg : Integrable g μ) (m : MeasurableSpace α)
  proof: by
  by_cases hm : m <= m₀
  swap; · simp_rw [condExp_of_not_le hm]; simp
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; simp
  refine (condExp_ae_eq_condExpL1 hm _).trans ?_
  rw [condExpL1_add hf hg]
  exact (coeFn_add _ _).trans
    ((condExp_ae_eq

中文:
定理 condExp_add
  条件: (hf : 整数egrable f μ) (hg : 整数egrable g μ) (m : MeasurableSpace α)
  证明: by
  by_cases hm : m <= m₀
  swap; · simp_rw [condExp_of_not_le hm]; simp
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; simp
  refine (condExp_ae_eq_condExpL1 hm _).trans ?_
  rw [condExpL1_add hf hg]
  exact (coeFn_add _ _).trans
    ((condExp_ae_eq

Depends on / 依赖: SigmaFinite, coeFn_add, condExpL1_add, condExp_ae_eq_condExpL1, condExp_of_not_le, condExp_of_not_sigmaFinite, simp_rw, symm.add
-/
theorem condExp_add (hf : Integrable f μ) (hg : Integrable g μ) (m : MeasurableSpace α) :
    μ[f + g | m] =ᵐ[μ] μ[f | m] + μ[g | m] := by
  by_cases hm : m <= m₀
  swap; · simp_rw [condExp_of_not_le hm]; simp
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; simp
  refine (condExp_ae_eq_condExpL1 hm _).trans ?_
  rw [condExpL1_add hf hg]
  exact (coeFn_add _ _).trans
    ((condExp_ae_eq_condExpL1 hm _).symm.add (condExp_ae_eq_condExpL1 hm _).symm)

/--
theorem `condExp_finsetSum` / 定理 `condExp_finsetSum`

English:
theorem condExp_finsetSum
  statement: {ι : Type*} {s : Finset ι} {f : ι -> α -> E}
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, condExp_zero]
  | insert i s his heq =>
    rw [Finset.sum_insert his]; rw [Finset.sum_insert his]
    exact (condExp_add (hf i <| Finset.mem_insert_self i s)
      (integrable_finsetSum'

中文:
定理 condExp_finsetSum
  结论: {ι : 类型} {s : Finset ι} {f : ι -> α -> E}
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, condExp_zero]
  | insert i s his heq =>
    rw [Finset.sum_insert his]; rw [Finset.sum_insert his]
    exact (condExp_add (hf i <| Finset.mem_insert_self i s)
      (integrable_finsetSum'

Depends on / 依赖: EventuallyEq, EventuallyEq.refl, Finset, Finset.forall_of_forall_insert, Finset.induction_on, Finset.mem_insert_self, Finset.sum_empty, Finset.sum_insert, classical, condExp_add, condExp_zero, forall_of_forall_insert, induction_on, insert, integrable_finsetSum, mem_insert_self, sum_empty, sum_insert
-/
theorem condExp_finsetSum {ι : Type*} {s : Finset ι} {f : ι -> α -> E}
    (hf : forall i in s, Integrable (f i) μ) (m : MeasurableSpace α) :
    μ[∑ i in s, f i | m] =ᵐ[μ] ∑ i in s, μ[f i | m] := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, condExp_zero]
  | insert i s his heq =>
    rw [Finset.sum_insert his]; rw [Finset.sum_insert his]
    exact (condExp_add (hf i <| Finset.mem_insert_self i s)
      (integrable_finsetSum' _ <| Finset.forall_of_forall_insert hf) _).trans
        ((EventuallyEq.refl _ _).add <| heq <| Finset.forall_of_forall_insert hf)

@[deprecated (since := "2026-04-08")] alias condExp_finset_sum := condExp_finsetSum

/--
theorem `condExp_smul` / 定理 `condExp_smul`

English:
theorem condExp_smul
  given: [NormedSpace 𝕜 E] (c : 𝕜) (f : α -> E) (m : MeasurableSpace α)
  proof: by
  by_cases hm : m <= m₀
  swap; · simp_rw [condExp_of_not_le hm]; simp
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; simp
  refine (condExp_ae_eq_condExpL1 hm _).trans ?_
  rw [condExpL1_smul c f]
  refine (condExp_ae_eq_condExpL1 hm f).mp ?_
  re

中文:
定理 condExp_smul
  条件: [NormedSpace 𝕜 E] (c : 𝕜) (f : α -> E) (m : MeasurableSpace α)
  证明: by
  by_cases hm : m <= m₀
  swap; · simp_rw [condExp_of_not_le hm]; simp
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; simp
  refine (condExp_ae_eq_condExpL1 hm _).trans ?_
  rw [condExpL1_smul c f]
  refine (condExp_ae_eq_condExpL1 hm f).mp ?_
  re

Depends on / 依赖: Pi.smul_apply, SigmaFinite, coeFn_smul, condExpL1, condExpL1_smul, condExp_ae_eq_condExpL1, condExp_of_not_le, condExp_of_not_sigmaFinite, simp_rw, smul_apply
-/
theorem condExp_smul [NormedSpace 𝕜 E] (c : 𝕜) (f : α -> E) (m : MeasurableSpace α) :
    μ[c • f | m] =ᵐ[μ] c • μ[f | m] := by
  by_cases hm : m <= m₀
  swap; · simp_rw [condExp_of_not_le hm]; simp
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; simp
  refine (condExp_ae_eq_condExpL1 hm _).trans ?_
  rw [condExpL1_smul c f]
  refine (condExp_ae_eq_condExpL1 hm f).mp ?_
  refine (coeFn_smul c (condExpL1 hm μ f)).mono fun x hx1 hx2 => ?_
  simp only [hx1, hx2, Pi.smul_apply]

/--
theorem `condExp_neg` / 定理 `condExp_neg`

English:
theorem condExp_neg
  given: (f : α -> E) (m : MeasurableSpace α)
  statement: μ[-f | m] =ᵐ[μ] -μ[f | m]
  proof: by
  calc
    μ[-f | m] = μ[(-1 : Real) • f | m] := by rw [neg_one_smul Real f]
    _ =ᵐ[μ] (-1 : Real) • μ[f | m] := condExp_smul ..
    _ = -μ[f | m] := neg_one_smul Real (μ[f | m])

中文:
定理 condExp_neg
  条件: (f : α -> E) (m : MeasurableSpace α)
  结论: μ[-f | m] =ᵐ[μ] -μ[f | m]
  证明: by
  calc
    μ[-f | m] = μ[(-1 : Real) • f | m] := by rw [neg_one_smul Real f]
    _ =ᵐ[μ] (-1 : Real) • μ[f | m] := condExp_smul ..
    _ = -μ[f | m] := neg_one_smul Real (μ[f | m])

Depends on / 依赖: condExp_smul, neg_one_smul
-/
theorem condExp_neg (f : α -> E) (m : MeasurableSpace α) : μ[-f | m] =ᵐ[μ] -μ[f | m] := by
  calc
    μ[-f | m] = μ[(-1 : Real) • f | m] := by rw [neg_one_smul Real f]
    _ =ᵐ[μ] (-1 : Real) • μ[f | m] := condExp_smul ..
    _ = -μ[f | m] := neg_one_smul Real (μ[f | m])

/--
theorem `condExp_sub` / 定理 `condExp_sub`

English:
theorem condExp_sub
  given: (hf : Integrable f μ) (hg : Integrable g μ) (m : MeasurableSpace α)
  proof: by
  simp_rw [sub_eq_add_neg]
  exact (condExp_add hf hg.neg _).trans (EventuallyEq.rfl.add (condExp_neg ..))

中文:
定理 condExp_sub
  条件: (hf : 整数egrable f μ) (hg : 整数egrable g μ) (m : MeasurableSpace α)
  证明: by
  simp_rw [sub_eq_add_neg]
  exact (condExp_add hf hg.neg _).trans (EventuallyEq.rfl.add (condExp_neg ..))

Depends on / 依赖: EventuallyEq, EventuallyEq.rfl.add, condExp_add, condExp_neg, hg.neg, simp_rw, sub_eq_add_neg
-/
theorem condExp_sub (hf : Integrable f μ) (hg : Integrable g μ) (m : MeasurableSpace α) :
    μ[f - g | m] =ᵐ[μ] μ[f | m] - μ[g | m] := by
  simp_rw [sub_eq_add_neg]
  exact (condExp_add hf hg.neg _).trans (EventuallyEq.rfl.add (condExp_neg ..))

/--
theorem `condExp_condExp_of_le` / 定理 `condExp_condExp_of_le`

English:
theorem condExp_condExp_of_le
  statement: {m₁ m₂ m₀ : MeasurableSpace α} {μ : Measure α} (hm₁₂ : m₁ <= m₂)
  proof: by
  by_cases hμm₁ : SigmaFinite (μ.trim (hm₁₂.trans hm₂))
  swap; · simp_rw [condExp_of_not_sigmaFinite (hm₁₂.trans hm₂) hμm₁]; rfl
  by_cases hf : Integrable f μ
  swap; · simp_rw [condExp_of_not_integrable hf, condExp_zero]; rfl
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (hm₁₂.trans 

中文:
定理 condExp_condExp_of_le
  结论: {m₁ m₂ m₀ : MeasurableSpace α} {μ : Measure α} (hm₁₂ : m₁ <= m₂)
  证明: by
  by_cases hμm₁ : SigmaFinite (μ.trim (hm₁₂.trans hm₂))
  swap; · simp_rw [condExp_of_not_sigmaFinite (hm₁₂.trans hm₂) hμm₁]; rfl
  by_cases hf : Integrable f μ
  swap; · simp_rw [condExp_of_not_integrable hf, condExp_zero]; rfl
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (hm₁₂.trans 

Depends on / 依赖: Integrable, SigmaFinite, ae_eq_of_forall_setIntegral_eq_of_sigmaFinite, aestronglyMeasurable, condExp_of_not_integrable, condExp_of_not_sigmaFinite, condExp_zero, integrableOn, integrable_condExp, integrable_condExp.integrableOn, simp_rw, stronglyMeasurable_condExp, stronglyMeasurable_condExp.aestronglyMeasurable
-/
theorem condExp_condExp_of_le {m₁ m₂ m₀ : MeasurableSpace α} {μ : Measure α} (hm₁₂ : m₁ <= m₂)
    (hm₂ : m₂ <= m₀) [SigmaFinite (μ.trim hm₂)] : μ[μ[f | m₂] | m₁] =ᵐ[μ] μ[f | m₁] := by
  by_cases hμm₁ : SigmaFinite (μ.trim (hm₁₂.trans hm₂))
  swap; · simp_rw [condExp_of_not_sigmaFinite (hm₁₂.trans hm₂) hμm₁]; rfl
  by_cases hf : Integrable f μ
  swap; · simp_rw [condExp_of_not_integrable hf, condExp_zero]; rfl
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (hm₁₂.trans hm₂)
    (fun s _ _ => integrable_condExp.integrableOn) (fun s _ _ => integrable_condExp.integrableOn) ?_
    stronglyMeasurable_condExp.aestronglyMeasurable
    stronglyMeasurable_condExp.aestronglyMeasurable
  intro s hs _
  rw [setIntegral_condExp (hm₁₂.trans hm₂) integrable_condExp hs]
  rw [setIntegral_condExp (hm₁₂.trans hm₂) hf hs]; rw [setIntegral_condExp hm₂ hf (hm₁₂ s hs)]

/--
theorem `_root_.ContinuousLinearMap.comp_condExp_comm` / 定理 `_root_.ContinuousLinearMap.comp_condExp_comm`

English:
theorem _root_.ContinuousLinearMap.comp_condExp_comm
  statement: {F : Type*} [NormedAddCommGroup F]
  proof: by
  by_cases hm : m <= m₀
  · by_cases hμ : SigmaFinite (μ.trim hm)
    · refine ae_eq_condExp_of_forall_setIntegral_eq hm ?_ (fun s ms hs => ?_) (fun s ms hs => ?_) ?_
      · exact T.integrable_comp hf_int
      · exact (T.integrable_comp integrable_condExp).integrableOn
      · calc
          ∫ 

中文:
定理 _root_.ContinuousLinearMap.comp_condExp_comm
  结论: {F : 类型} [NormedAddCommGroup F]
  证明: by
  by_cases hm : m <= m₀
  · by_cases hμ : SigmaFinite (μ.trim hm)
    · refine ae_eq_condExp_of_forall_setIntegral_eq hm ?_ (fun s ms hs => ?_) (fun s ms hs => ?_) ?_
      · exact T.integrable_comp hf_int
      · exact (T.integrable_comp integrable_condExp).integrableOn
      · calc
          ∫ 

Depends on / 依赖: CuspFormClass, FunLike, ModularFormClass, SigmaFinite, T.integrable_comp, T.integral_comp_comm, ae_eq_condExp_of_forall_setIntegral_eq, hf_int, integrableOn, integrable_comp, integrable_condExp, integrable_condExp.restrict, integral_comp_comm, restrict, setIntegral_condExp
-/
theorem _root_.ContinuousLinearMap.comp_condExp_comm {F : Type*} [NormedAddCommGroup F]
    [CompleteSpace F] [NormedSpace Real F] (hf_int : Integrable f μ) (T : E ->L[Real] F) :
    T ∘ μ[f | m] =ᵐ[μ] μ[T ∘ f | m] := by
  by_cases hm : m <= m₀
  · by_cases hμ : SigmaFinite (μ.trim hm)
    · refine ae_eq_condExp_of_forall_setIntegral_eq hm ?_ (fun s ms hs => ?_) (fun s ms hs => ?_) ?_
      · exact T.integrable_comp hf_int
      · exact (T.integrable_comp integrable_condExp).integrableOn
      · calc
          ∫ x in s, (T ∘ μ[f | m]) x ∂μ = T (∫ x in s, μ[f | m] x ∂μ) :=
            T.integral_comp_comm integrable_condExp.restrict
          _ = T (∫ x in s, f x ∂μ) := congrArg T (setIntegral_condExp hm hf_int ms)
          _ = ∫ x in s, (T ∘ f) x ∂μ := (T.integral_comp_comm hf_int.restrict).symm
      · exact T.cont.comp_aestronglyMeasurable stronglyMeasurable_condExp.aestronglyMeasurable
    · simp [condExp_of_not_sigmaFinite hm hμ]
  · simp [condExp_of_not_le hm]

/--
theorem `_root_.ContinuousLinearMap.comp_condExp_add_const_comm` / 定理 `_root_.ContinuousLinearMap.comp_condExp_add_const_comm`

English:
theorem _root_.ContinuousLinearMap.comp_condExp_add_const_comm
  statement: {F : Type*} [NormedAddCommGroup F]
  proof: by
  have hp : (fun x => T (μ[f | m] x) + a) =ᵐ[μ] μ[T ∘ f | m] + μ[(fun y => a) | m] := by
    filter_upwards [T.comp_condExp_comm hf_int] with b hb
    simpa [condExp_const hm a]
  exact hp.trans (condExp_add (T.integrable_comp hf_int) (integrable_const a) m).symm

中文:
定理 _root_.ContinuousLinearMap.comp_condExp_add_const_comm
  结论: {F : 类型} [NormedAddCommGroup F]
  证明: by
  have hp : (fun x => T (μ[f | m] x) + a) =ᵐ[μ] μ[T ∘ f | m] + μ[(fun y => a) | m] := by
    filter_upwards [T.comp_condExp_comm hf_int] with b hb
    simpa [condExp_const hm a]
  exact hp.trans (condExp_add (T.integrable_comp hf_int) (integrable_const a) m).symm

Depends on / 依赖: T.comp_condExp_comm, T.integrable_comp, comp_condExp_comm, condExp_add, condExp_const, filter_upwards, hf_int, hp.trans, integrable_comp, integrable_const
-/
theorem _root_.ContinuousLinearMap.comp_condExp_add_const_comm {F : Type*} [NormedAddCommGroup F]
    [CompleteSpace F] [NormedSpace Real F] [IsFiniteMeasure μ] (hm : m <= m₀) (hf_int : Integrable f μ)
    (T : E ->L[Real] F) (a : F) : (fun x => T (μ[f | m] x) + a) =ᵐ[μ] μ[fun y => T (f y) + a | m] := by
  have hp : (fun x => T (μ[f | m] x) + a) =ᵐ[μ] μ[T ∘ f | m] + μ[(fun y => a) | m] := by
    filter_upwards [T.comp_condExp_comm hf_int] with b hb
    simpa [condExp_const hm a]
  exact hp.trans (condExp_add (T.integrable_comp hf_int) (integrable_const a) m).symm

section RCLike

variable [InnerProductSpace 𝕜 E]

/--
lemma `MemLp.condExpL2_ae_eq_condExp'` / 引理 `MemLp.condExpL2_ae_eq_condExp'`

English:
lemma MemLp.condExpL2_ae_eq_condExp'
  statement: (hm : m <= m₀) (hf1 : Integrable f μ) (hf2 : MemLp f 2 μ)
  proof: by
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hf1
    (fun s hs htop => integrableOn_condExpL2_of_measure_ne_top hm htop.ne _) (fun s hs htop => ?_)
    (aestronglyMeasurable_condExpL2 hm _)
  rw [integral_condExpL2_eq hm (hf2.toLp _) hs htop.ne]
  refine setIntegral_congr_ae (hm _ hs) ?_
  

中文:
引理 MemLp.condExpL2_ae_eq_condExp'
  结论: (hm : m <= m₀) (hf1 : 整数egrable f μ) (hf2 : MemLp f 2 μ)
  证明: by
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hf1
    (fun s hs htop => integrableOn_condExpL2_of_measure_ne_top hm htop.ne _) (fun s hs htop => ?_)
    (aestronglyMeasurable_condExpL2 hm _)
  rw [integral_condExpL2_eq hm (hf2.toLp _) hs htop.ne]
  refine setIntegral_congr_ae (hm _ hs) ?_
  

Depends on / 依赖: ae_eq_condExp_of_forall_setIntegral_eq, aestronglyMeasurable_condExpL2, coeFn_toLp, filter_upwards, hf2.coeFn_toLp, hf2.toLp, htop.ne, integrableOn_condExpL2_of_measure_ne_top, integral_condExpL2_eq, setIntegral_congr_ae
-/
lemma MemLp.condExpL2_ae_eq_condExp' (hm : m <= m₀) (hf1 : Integrable f μ) (hf2 : MemLp f 2 μ)
    [SigmaFinite (μ.trim hm)] : condExpL2 E 𝕜 hm hf2.toLp =ᵐ[μ] μ[f | m] := by
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hf1
    (fun s hs htop => integrableOn_condExpL2_of_measure_ne_top hm htop.ne _) (fun s hs htop => ?_)
    (aestronglyMeasurable_condExpL2 hm _)
  rw [integral_condExpL2_eq hm (hf2.toLp _) hs htop.ne]
  refine setIntegral_congr_ae (hm _ hs) ?_
  filter_upwards [hf2.coeFn_toLp] with ω hω _ using hω

/--
lemma `MemLp.condExpL2_ae_eq_condExp` / 引理 `MemLp.condExpL2_ae_eq_condExp`

English:
lemma MemLp.condExpL2_ae_eq_condExp
  given: (hm : m <= m₀) (hf : MemLp f 2 μ) [IsFiniteMeasure μ]
  proof: hf.condExpL2_ae_eq_condExp' hm (memLp_one_iff_integrable.1 <| hf.mono_exponent one_le_two)

中文:
引理 MemLp.condExpL2_ae_eq_condExp
  条件: (hm : m <= m₀) (hf : MemLp f 2 μ) [IsFiniteMeasure μ]
  证明: hf.condExpL2_ae_eq_condExp' hm (memLp_one_iff_integrable.1 <| hf.mono_exponent one_le_two)

Depends on / 依赖: condExpL2_ae_eq_condExp, hf.condExpL2_ae_eq_condExp, hf.mono_exponent, memLp_one_iff_integrable, mono_exponent, one_le_two
-/
lemma MemLp.condExpL2_ae_eq_condExp (hm : m <= m₀) (hf : MemLp f 2 μ) [IsFiniteMeasure μ] :
    condExpL2 E 𝕜 hm hf.toLp =ᵐ[μ] μ[f | m] :=
  hf.condExpL2_ae_eq_condExp' hm (memLp_one_iff_integrable.1 <| hf.mono_exponent one_le_two)

end RCLike

end NormedSpace

end NormedAddCommGroup

section NormedRing
variable {R : Type*} [NormedRing R] [NormedSpace Real R] [CompleteSpace R]

@[simp]
/--
lemma `condExp_ofNat` / 引理 `condExp_ofNat`

English:
lemma condExp_ofNat
  given: (n : Nat) [n.AtLeastTwo] (f : α -> R)
  proof: by
  simpa [Nat.cast_smul_eq_nsmul] using! condExp_smul (μ := μ) (m := m) (n : Real) f

中文:
引理 condExp_ofNat
  条件: (n : 自然数) [n.AtLeastTwo] (f : α -> R)
  证明: by
  simpa [Nat.cast_smul_eq_nsmul] using! condExp_smul (μ := μ) (m := m) (n : Real) f

Depends on / 依赖: Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul, condExp_smul
-/
lemma condExp_ofNat (n : Nat) [n.AtLeastTwo] (f : α -> R) :
    μ[ofNat(n) * f | m] =ᵐ[μ] ofNat(n) * μ[f | m] := by
  simpa [Nat.cast_smul_eq_nsmul] using! condExp_smul (μ := μ) (m := m) (n : Real) f

end NormedRing

section NormedLatticeAddCommGroup
variable [NormedAddCommGroup E] [NormedSpace Real E]

/--
theorem `tendsto_condExpL1_of_dominated_convergence` / 定理 `tendsto_condExpL1_of_dominated_convergence`

English:
theorem tendsto_condExpL1_of_dominated_convergence
  statement: (hm : m <= m₀) [SigmaFinite (μ.trim hm)]
  proof: tendsto_setToFun_of_dominated_convergence _ bound_fs hfs_meas h_int_bound_fs hfs_bound hfs

中文:
定理 tendsto_condExpL1_of_dominated_convergence
  结论: (hm : m <= m₀) [SigmaFinite (μ.trim hm)]
  证明: tendsto_setToFun_of_dominated_convergence _ bound_fs hfs_meas h_int_bound_fs hfs_bound hfs

Depends on / 依赖: bound_fs, h_int_bound_fs, hfs_bound, hfs_meas, tendsto_setToFun_of_dominated_convergence
-/
theorem tendsto_condExpL1_of_dominated_convergence (hm : m <= m₀) [SigmaFinite (μ.trim hm)]
    {fs : Nat -> α -> E} {f : α -> E} (bound_fs : α -> Real)
    (hfs_meas : forall n, AEStronglyMeasurable (fs n) μ) (h_int_bound_fs : Integrable bound_fs μ)
    (hfs_bound : forall n, forallᵐ x ∂μ, ‖fs n x‖ <= bound_fs x)
    (hfs : forallᵐ x ∂μ, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => condExpL1 hm μ (fs n)) atTop (𝓝 (condExpL1 hm μ f)) :=
  tendsto_setToFun_of_dominated_convergence _ bound_fs hfs_meas h_int_bound_fs hfs_bound hfs

/--
theorem `condExp_tsum` / 定理 `condExp_tsum`

English:
theorem condExp_tsum
  statement: [CompleteSpace E]
  proof: by
  by_cases hm : m <= m₀; swap
  · simp only [condExp_of_not_le hm, Pi.zero_apply, tsum_zero]
    exact ae_eq_rfl
  by_cases hμm : SigmaFinite (μ.trim hm); swap
  · simp only [condExp_of_not_sigmaFinite hm hμm, Pi.zero_apply, tsum_zero]
    exact ae_eq_rfl
  grw [condExp_ae_eq_condExpL1 hm]
  have

中文:
定理 condExp_tsum
  结论: [CompleteSpace E]
  证明: by
  by_cases hm : m <= m₀; swap
  · simp only [condExp_of_not_le hm, Pi.zero_apply, tsum_zero]
    exact ae_eq_rfl
  by_cases hμm : SigmaFinite (μ.trim hm); swap
  · simp only [condExp_of_not_sigmaFinite hm hμm, Pi.zero_apply, tsum_zero]
    exact ae_eq_rfl
  grw [condExp_ae_eq_condExpL1 hm]
  have

Depends on / 依赖: Pi.zero_apply, SigmaFinite, ae_all_iff, ae_eq_rfl, condExpL1, condExp_ae_eq_condExpL1, condExp_of_not_le, condExp_of_not_sigmaFinite, lt_of_le_of_lt, lt_top, tsum_zero, zero_apply
-/
theorem condExp_tsum [CompleteSpace E]
    {ι : Type*} [Countable ι] {f : ι -> α -> E} (hf : forall i, AEStronglyMeasurable (f i) μ)
    (hf' : ∑' i, ∫⁻ a, ‖f i a‖ₑ ∂μ != ∞) :
    μ[fun a => ∑' i, f i a | m] =ᵐ[μ] fun a => ∑' i, μ[f i | m] a := by
  by_cases hm : m <= m₀; swap
  · simp only [condExp_of_not_le hm, Pi.zero_apply, tsum_zero]
    exact ae_eq_rfl
  by_cases hμm : SigmaFinite (μ.trim hm); swap
  · simp only [condExp_of_not_sigmaFinite hm hμm, Pi.zero_apply, tsum_zero]
    exact ae_eq_rfl
  grw [condExp_ae_eq_condExpL1 hm]
  have A : forallᵐ a ∂μ, forall i, μ[f i | m] a = condExpL1 hm μ (f i) a :=
    ae_all_iff.2 (fun i => condExp_ae_eq_condExpL1 hm _)
  have B : ∑' (n : ι), ‖condExpL1 hm μ (f n)‖ₑ != ∞ := by
    apply (lt_of_le_of_lt ?_ hf'.lt_top).ne
    gcongr with i
    exact (enorm_setToFun_le _ (by simp)).trans_eq (by simp)
  have C := coeFn_tsum (f := fun i => condExpL1 hm μ (f i)) B
  filter_upwards [A, C] with a ha h'a
  simp_all [condExpL1, setToFun_tsum]

variable [CompleteSpace E]

/--
theorem `tendsto_condExp_unique` / 定理 `tendsto_condExp_unique`

English:
theorem tendsto_condExp_unique
  statement: (fs gs : Nat -> α -> E) (f g : α -> E)
  proof: by
  by_cases hm : m <= m₀; swap; · simp_rw [condExp_of_not_le hm]; rfl
  by_cases hμm : SigmaFinite (μ.trim hm); swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; rfl
  refine (condExp_ae_eq_condExpL1 hm f).trans ((condExp_ae_eq_condExpL1 hm g).trans ?_).symm
  rw [← Lp.ext_iff]
  have hn_eq : f

中文:
定理 tendsto_condExp_unique
  结论: (fs gs : 自然数 -> α -> E) (f g : α -> E)
  证明: by
  by_cases hm : m <= m₀; swap; · simp_rw [condExp_of_not_le hm]; rfl
  by_cases hμm : SigmaFinite (μ.trim hm); swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; rfl
  refine (condExp_ae_eq_condExpL1 hm f).trans ((condExp_ae_eq_condExpL1 hm g).trans ?_).symm
  rw [← Lp.ext_iff]
  have hn_eq : f

Depends on / 依赖: Lp.ext_iff, SigmaFinite, condExpL1, condExp_ae_eq_condExpL1, condExp_of_not_le, condExp_of_not_sigmaFinite, ext_iff, hcond_fs, hn_eq, simp_rw, symm.trans
-/
theorem tendsto_condExp_unique (fs gs : Nat -> α -> E) (f g : α -> E)
    (hfs_int : forall n, Integrable (fs n) μ) (hgs_int : forall n, Integrable (gs n) μ)
    (hfs : forallᵐ x ∂μ, Tendsto (fun n => fs n x) atTop (𝓝 (f x)))
    (hgs : forallᵐ x ∂μ, Tendsto (fun n => gs n x) atTop (𝓝 (g x))) (bound_fs : α -> Real)
    (h_int_bound_fs : Integrable bound_fs μ) (bound_gs : α -> Real)
    (h_int_bound_gs : Integrable bound_gs μ) (hfs_bound : forall n, forallᵐ x ∂μ, ‖fs n x‖ <= bound_fs x)
    (hgs_bound : forall n, forallᵐ x ∂μ, ‖gs n x‖ <= bound_gs x) (hfg : forall n, μ[fs n | m] =ᵐ[μ] μ[gs n | m]) :
    μ[f | m] =ᵐ[μ] μ[g | m] := by
  by_cases hm : m <= m₀; swap; · simp_rw [condExp_of_not_le hm]; rfl
  by_cases hμm : SigmaFinite (μ.trim hm); swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; rfl
  refine (condExp_ae_eq_condExpL1 hm f).trans ((condExp_ae_eq_condExpL1 hm g).trans ?_).symm
  rw [← Lp.ext_iff]
  have hn_eq : forall n, condExpL1 hm μ (gs n) = condExpL1 hm μ (fs n) := by
    intro n
    ext1
    refine (condExp_ae_eq_condExpL1 hm (gs n)).symm.trans ((hfg n).symm.trans ?_)
    exact condExp_ae_eq_condExpL1 hm (fs n)
  have hcond_fs : Tendsto (fun n => condExpL1 hm μ (fs n)) atTop (𝓝 (condExpL1 hm μ f)) :=
    tendsto_condExpL1_of_dominated_convergence hm _ (fun n => (hfs_int n).1) h_int_bound_fs
      hfs_bound hfs
  have hcond_gs : Tendsto (fun n => condExpL1 hm μ (gs n)) atTop (𝓝 (condExpL1 hm μ g)) :=
    tendsto_condExpL1_of_dominated_convergence hm _ (fun n => (hgs_int n).1) h_int_bound_gs
      hgs_bound hgs
  exact tendsto_nhds_unique_of_eventuallyEq hcond_gs hcond_fs (Eventually.of_forall hn_eq)

variable [PartialOrder E] [ClosedIciTopology E] [IsOrderedAddMonoid E] [IsOrderedModule Real E]

/--
lemma `condExp_mono` / 引理 `condExp_mono`

English:
lemma condExp_mono
  given: (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f <=ᵐ[μ] g)
  proof: by
  by_cases hm : m <= m₀
  swap; · simp_rw [condExp_of_not_le hm]; rfl
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; rfl
  exact (condExp_ae_eq_condExpL1 hm _).trans_le
    ((condExpL1_mono hf hg hfg).trans_eq (condExp_ae_eq_condExpL1 hm _).symm)

中文:
引理 condExp_mono
  条件: (hf : 整数egrable f μ) (hg : 整数egrable g μ) (hfg : f <=ᵐ[μ] g)
  证明: by
  by_cases hm : m <= m₀
  swap; · simp_rw [condExp_of_not_le hm]; rfl
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; rfl
  exact (condExp_ae_eq_condExpL1 hm _).trans_le
    ((condExpL1_mono hf hg hfg).trans_eq (condExp_ae_eq_condExpL1 hm _).symm)

Depends on / 依赖: SigmaFinite, condExpL1_mono, condExp_ae_eq_condExpL1, condExp_of_not_le, condExp_of_not_sigmaFinite, simp_rw, trans_eq, trans_le
-/
lemma condExp_mono (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f <=ᵐ[μ] g) :
    μ[f | m] <=ᵐ[μ] μ[g | m] := by
  by_cases hm : m <= m₀
  swap; · simp_rw [condExp_of_not_le hm]; rfl
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; rfl
  exact (condExp_ae_eq_condExpL1 hm _).trans_le
    ((condExpL1_mono hf hg hfg).trans_eq (condExp_ae_eq_condExpL1 hm _).symm)

/--
lemma `condExp_nonneg` / 引理 `condExp_nonneg`

English:
lemma condExp_nonneg
  given: (hf : 0 <=ᵐ[μ] f)
  statement: 0 <=ᵐ[μ] μ[f | m]
  proof: by
  by_cases hfint : Integrable f μ
  · rw [(condExp_zero.symm : (0 : α -> E) = μ[0 | m])]
    exact condExp_mono (integrable_zero _ _ _) hfint hf
  · rw [condExp_of_not_integrable hfint]

中文:
引理 condExp_nonneg
  条件: (hf : 0 <=ᵐ[μ] f)
  结论: 0 <=ᵐ[μ] μ[f | m]
  证明: by
  by_cases hfint : Integrable f μ
  · rw [(condExp_zero.symm : (0 : α -> E) = μ[0 | m])]
    exact condExp_mono (integrable_zero _ _ _) hfint hf
  · rw [condExp_of_not_integrable hfint]

Depends on / 依赖: Integrable, condExp_mono, condExp_of_not_integrable, condExp_zero, condExp_zero.symm, integrable_zero
-/
lemma condExp_nonneg (hf : 0 <=ᵐ[μ] f) : 0 <=ᵐ[μ] μ[f | m] := by
  by_cases hfint : Integrable f μ
  · rw [(condExp_zero.symm : (0 : α -> E) = μ[0 | m])]
    exact condExp_mono (integrable_zero _ _ _) hfint hf
  · rw [condExp_of_not_integrable hfint]

/--
lemma `condExp_nonpos` / 引理 `condExp_nonpos`

English:
lemma condExp_nonpos
  given: (hf : f <=ᵐ[μ] 0)
  statement: μ[f | m] <=ᵐ[μ] 0
  proof: by
  by_cases hfint : Integrable f μ
  · rw [(condExp_zero.symm : (0 : α -> E) = μ[0 | m])]
    exact condExp_mono hfint (integrable_zero _ _ _) hf
  · rw [condExp_of_not_integrable hfint]

中文:
引理 condExp_nonpos
  条件: (hf : f <=ᵐ[μ] 0)
  结论: μ[f | m] <=ᵐ[μ] 0
  证明: by
  by_cases hfint : Integrable f μ
  · rw [(condExp_zero.symm : (0 : α -> E) = μ[0 | m])]
    exact condExp_mono hfint (integrable_zero _ _ _) hf
  · rw [condExp_of_not_integrable hfint]

Depends on / 依赖: Integrable, condExp_mono, condExp_of_not_integrable, condExp_zero, condExp_zero.symm, f.mul, integrable_zero
-/
lemma condExp_nonpos (hf : f <=ᵐ[μ] 0) : μ[f | m] <=ᵐ[μ] 0 := by
  by_cases hfint : Integrable f μ
  · rw [(condExp_zero.symm : (0 : α -> E) = μ[0 | m])]
    exact condExp_mono hfint (integrable_zero _ _ _) hf
  · rw [condExp_of_not_integrable hfint]

end NormedLatticeAddCommGroup
end MeasureTheory
