/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Order

/-!
# Principles of Isolated Zeros and Identity Principles for Meromorphic Functions

In line with results in `Mathlib.Analysis.Analytic.IsolatedZeros` and
`Mathlib.Analysis.Analytic.Uniqueness`, this file establishes principles of isolated zeros and
identity principles for meromorphic functions.

Compared to the results for analytic functions, the principles established here are a little more
complicated to state. This is because meromorphic functions can be modified at will along discrete
subsets and still remain meromorphic.
-/

public section

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜} {x : 𝕜} {f g : 𝕜 -> E}

open Filter Topology

namespace MeromorphicAt

/-!
## Principles of Isolated Zeros
-/

/--
theorem `frequently_zero_iff_eventuallyEq_zero` / 定理 `frequently_zero_iff_eventuallyEq_zero`

English:
theorem frequently_zero_iff_eventuallyEq_zero
  given: (hf : MeromorphicAt f x)
  proof: ⟨hf.eventually_eq_zero_or_eventually_ne_zero.resolve_right, fun h => h.frequently⟩

中文:
定理 frequently_zero_iff_eventuallyEq_zero
  条件: (hf : MeromorphicAt f x)
  证明: ⟨hf.eventually_eq_zero_or_eventually_ne_zero.resolve_right, fun h => h.frequently⟩

Depends on / 依赖: eventually_eq_zero_or_eventually_ne_zero, frequently, h.frequently, hf.eventually_eq_zero_or_eventually_ne_zero.resolve_right, resolve_right
-/
theorem frequently_zero_iff_eventuallyEq_zero (hf : MeromorphicAt f x) :
    (existsᶠ z in 𝓝[!=] x, f z = 0) ↔ f =ᶠ[𝓝[!=] x] 0 :=
  ⟨hf.eventually_eq_zero_or_eventually_ne_zero.resolve_right, fun h => h.frequently⟩

/--
theorem `eventuallyEq_zero_nhdsNE_of_eventuallyEq_zero_codiscreteWithin` / 定理 `eventuallyEq_zero_nhdsNE_of_eventuallyEq_zero_codiscreteWithin`

English:
theorem eventuallyEq_zero_nhdsNE_of_eventuallyEq_zero_codiscreteWithin
  statement: (hf : MeromorphicAt f x)
  proof: by
  rw [← hf.frequently_zero_iff_eventuallyEq_zero]
  apply ((accPt_iff_frequently_nhdsNE.1 h₂x).and_eventually <| eventually_mem_set.2
    (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h x h₁x)).mono
  simp +contextual

中文:
定理 eventuallyEq_zero_nhdsNE_of_eventuallyEq_zero_codiscreteWithin
  结论: (hf : MeromorphicAt f x)
  证明: by
  rw [← hf.frequently_zero_iff_eventuallyEq_zero]
  apply ((accPt_iff_frequently_nhdsNE.1 h₂x).and_eventually <| eventually_mem_set.2
    (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h x h₁x)).mono
  simp +contextual

Depends on / 依赖: accPt_iff_frequently_nhdsNE, and_eventually, contextual, eventually_mem_set, frequently_zero_iff_eventuallyEq_zero, hf.frequently_zero_iff_eventuallyEq_zero, mem_codiscreteWithin_iff_forall_mem_nhdsNE
-/
theorem eventuallyEq_zero_nhdsNE_of_eventuallyEq_zero_codiscreteWithin (hf : MeromorphicAt f x)
    (h₁x : x in U) (h₂x : AccPt x (𝓟 U)) (h : f =ᶠ[codiscreteWithin U] 0) :
    f =ᶠ[𝓝[!=] x] 0 := by
  rw [← hf.frequently_zero_iff_eventuallyEq_zero]
  apply ((accPt_iff_frequently_nhdsNE.1 h₂x).and_eventually <| eventually_mem_set.2
    (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h x h₁x)).mono
  simp +contextual

/--
theorem `MeromorphicOn.codiscreteWithin_setOfPred_ne_zero` / 定理 `MeromorphicOn.codiscreteWithin_setOfPred_ne_zero`

English:
theorem MeromorphicOn.codiscreteWithin_setOfPred_ne_zero
  statement: (h₁f : MeromorphicOn f U)
  proof: by
  filter_upwards [h₁f.analyticAt_mem_codiscreteWithin,
    h₁f.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top h₂f] with x h₁x h₂x
  have := h₂f x h₂x.1
  simp_all [← h₁x.analyticOrderAt_eq_zero, h₁x.meromorphicOrderAt_eq]

@[deprecated (since := "2026-07-09")]
alias MeromorphicOn.codiscreteWithin_setOf_ne_zero :=
  MeromorphicOn.codiscreteWithin_setOfPred_ne_zero

中文:
定理 MeromorphicOn.codiscreteWithin_setOfPred_ne_zero
  结论: (h₁f : MeromorphicOn f U)
  证明: by
  filter_upwards [h₁f.analyticAt_mem_codiscreteWithin,
    h₁f.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top h₂f] with x h₁x h₂x
  have := h₂f x h₂x.1
  simp_all [← h₁x.analyticOrderAt_eq_zero, h₁x.meromorphicOrderAt_eq]

@[deprecated (since := "2026-07-09")]
alias MeromorphicOn.codiscreteWithin_setOf_ne_zero :=
  MeromorphicOn.codiscreteWithin_setOfPred_ne_zero

Depends on / 依赖: analyticAt_mem_codiscreteWithin, analyticOrderAt_eq_zero, codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top, f.analyticAt_mem_codiscreteWithin, f.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top, filter_upwards, meromorphicOrderAt_eq, x.analyticOrderAt_eq_zero, x.meromorphicOrderAt_eq
-/
theorem MeromorphicOn.codiscreteWithin_setOfPred_ne_zero (h₁f : MeromorphicOn f U)
    (h₂f : forall u in U, meromorphicOrderAt f u != ⊤) :
    forallᶠ x in codiscreteWithin U, f x != 0 := by
  filter_upwards [h₁f.analyticAt_mem_codiscreteWithin,
    h₁f.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top h₂f] with x h₁x h₂x
  have := h₂f x h₂x.1
  simp_all [← h₁x.analyticOrderAt_eq_zero, h₁x.meromorphicOrderAt_eq]

@[deprecated (since := "2026-07-09")]
alias MeromorphicOn.codiscreteWithin_setOf_ne_zero :=
  MeromorphicOn.codiscreteWithin_setOfPred_ne_zero

/-!
## Identity Principles
-/

/--
theorem `frequently_eq_iff_eventuallyEq` / 定理 `frequently_eq_iff_eventuallyEq`

English:
theorem frequently_eq_iff_eventuallyEq
  given: (hf : MeromorphicAt f x) (hg : MeromorphicAt g x)
  proof: by
  rw [eventuallyEq_iff_sub]; rw [← (hf.sub hg).frequently_zero_iff_eventuallyEq_zero]
  simp_rw [Pi.sub_apply, sub_eq_zero]

中文:
定理 frequently_eq_iff_eventuallyEq
  条件: (hf : MeromorphicAt f x) (hg : MeromorphicAt g x)
  证明: by
  rw [eventuallyEq_iff_sub]; rw [← (hf.sub hg).frequently_zero_iff_eventuallyEq_zero]
  simp_rw [Pi.sub_apply, sub_eq_zero]

Depends on / 依赖: Pi.sub_apply, eventuallyEq_iff_sub, frequently_zero_iff_eventuallyEq_zero, hf.sub, simp_rw, sub_apply, sub_eq_zero
-/
theorem frequently_eq_iff_eventuallyEq (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    (existsᶠ z in 𝓝[!=] x, f z = g z) ↔ f =ᶠ[𝓝[!=] x] g := by
  rw [eventuallyEq_iff_sub]; rw [← (hf.sub hg).frequently_zero_iff_eventuallyEq_zero]
  simp_rw [Pi.sub_apply, sub_eq_zero]

/--
theorem `eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin` / 定理 `eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin`

English:
theorem eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
  statement: (hf : MeromorphicAt f x)
  proof: by
  rw [eventuallyEq_iff_sub] at *
  apply (hf.sub hg).eventuallyEq_zero_nhdsNE_of_eventuallyEq_zero_codiscreteWithin h₁x h₂x h

中文:
定理 eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
  结论: (hf : MeromorphicAt f x)
  证明: by
  rw [eventuallyEq_iff_sub] at *
  apply (hf.sub hg).eventuallyEq_zero_nhdsNE_of_eventuallyEq_zero_codiscreteWithin h₁x h₂x h

Depends on / 依赖: eventuallyEq_iff_sub, eventuallyEq_zero_nhdsNE_of_eventuallyEq_zero_codiscreteWithin, hf.sub
-/
theorem eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (hf : MeromorphicAt f x)
    (hg : MeromorphicAt g x) (h₁x : x in U) (h₂x : AccPt x (𝓟 U)) (h : f =ᶠ[codiscreteWithin U] g) :
    f =ᶠ[𝓝[!=] x] g := by
  rw [eventuallyEq_iff_sub] at *
  apply (hf.sub hg).eventuallyEq_zero_nhdsNE_of_eventuallyEq_zero_codiscreteWithin h₁x h₂x h

/--
theorem `eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect` / 定理 `eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect`

English:
theorem eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
  statement: (hf : MeromorphicAt f x)
  proof: hf.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin hg hx (hU x hx) h

中文:
定理 eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
  结论: (hf : MeromorphicAt f x)
  证明: hf.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin hg hx (hU x hx) h

Depends on / 依赖: eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin, hf.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
-/
theorem eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect (hf : MeromorphicAt f x)
    (hg : MeromorphicAt g x) (hx : x in U) (hU : Preperfect U) (h : f =ᶠ[codiscreteWithin U] g) :
    f =ᶠ[𝓝[!=] x] g :=
  hf.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin hg hx (hU x hx) h

/--
theorem `eventually_nhdsSet_eventuallyEq_codiscreteWithin` / 定理 `eventually_nhdsSet_eventuallyEq_codiscreteWithin`

English:
theorem eventually_nhdsSet_eventuallyEq_codiscreteWithin
  statement: (hf : MeromorphicOn f U)
  proof: by
  rw [eventually_nhdsSet_iff_exists]
  use {x | f =ᶠ[𝓝[!=] x] g}
  simp only [Set.mem_ofPred_eq, imp_self, implies_true, and_true]
  constructor
  · apply isOpen_setOfPred_eventually_nhdsWithin
  · intro x hx
    rw [Set.mem_ofPred]
    exact eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (hf x hx) (hg x hx) hx (hU x hx) h

中文:
定理 eventually_nhdsSet_eventuallyEq_codiscreteWithin
  结论: (hf : MeromorphicOn f U)
  证明: by
  rw [eventually_nhdsSet_iff_exists]
  use {x | f =ᶠ[𝓝[!=] x] g}
  simp only [Set.mem_ofPred_eq, imp_self, implies_true, and_true]
  constructor
  · apply isOpen_setOfPred_eventually_nhdsWithin
  · intro x hx
    rw [Set.mem_ofPred]
    exact eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (hf x hx) (hg x hx) hx (hU x hx) h

Depends on / 依赖: Set.mem_ofPred, Set.mem_ofPred_eq, and_true, eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin, eventually_nhdsSet_iff_exists, imp_self, implies_true, isOpen_setOfPred_eventually_nhdsWithin, mem_ofPred, mem_ofPred_eq
-/
theorem eventually_nhdsSet_eventuallyEq_codiscreteWithin (hf : MeromorphicOn f U)
    (hg : MeromorphicOn g U) (hU : Preperfect U) (h : f =ᶠ[codiscreteWithin U] g) :
    forallᶠ x in 𝓝ˢ U, f =ᶠ[𝓝[!=] x] g := by
  rw [eventually_nhdsSet_iff_exists]
  use {x | f =ᶠ[𝓝[!=] x] g}
  simp only [Set.mem_ofPred_eq, imp_self, implies_true, and_true]
  constructor
  · apply isOpen_setOfPred_eventually_nhdsWithin
  · intro x hx
    rw [Set.mem_ofPred]
    exact eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (hf x hx) (hg x hx) hx (hU x hx) h

end MeromorphicAt

/--
theorem `MeromorphicOn.deriv_eventuallyEq_codiscreteWithin` / 定理 `MeromorphicOn.deriv_eventuallyEq_codiscreteWithin`

English:
theorem MeromorphicOn.deriv_eventuallyEq_codiscreteWithin
  statement: (hf : MeromorphicOn f U)
  proof: by
  rw [EventuallyEq]; rw [Filter.Eventually]; rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro x hx
  by_cases hacc : AccPt x (𝓟 U)
  · have h : f =ᶠ[𝓝[!=] x] g :=
      (hf x hx).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (hg x hx) hx hacc h
    filter_upwards [h.nhdsNE_deriv] using by simp +contextual
  · rw [accPt_iff_frequently_nhdsNE, not_frequently] at hacc
    filter_upwards [hacc] using by grind

中文:
定理 MeromorphicOn.deriv_eventuallyEq_codiscreteWithin
  结论: (hf : MeromorphicOn f U)
  证明: by
  rw [EventuallyEq]; rw [Filter.Eventually]; rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro x hx
  by_cases hacc : AccPt x (𝓟 U)
  · have h : f =ᶠ[𝓝[!=] x] g :=
      (hf x hx).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (hg x hx) hx hacc h
    filter_upwards [h.nhdsNE_deriv] using by simp +contextual
  · rw [accPt_iff_frequently_nhdsNE, not_frequently] at hacc
    filter_upwards [hacc] using by grind

Depends on / 依赖: Eventually, EventuallyEq, Filter, Filter.Eventually, accPt_iff_frequently_nhdsNE, contextual, eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin, filter_upwards, h.nhdsNE_deriv, mem_codiscreteWithin_iff_forall_mem_nhdsNE, nhdsNE_deriv, not_frequently
-/
theorem MeromorphicOn.deriv_eventuallyEq_codiscreteWithin (hf : MeromorphicOn f U)
    (hg : MeromorphicOn g U) (h : f =ᶠ[codiscreteWithin U] g) :
    deriv f =ᶠ[codiscreteWithin U] deriv g := by
  rw [EventuallyEq]; rw [Filter.Eventually]; rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro x hx
  by_cases hacc : AccPt x (𝓟 U)
  · have h : f =ᶠ[𝓝[!=] x] g :=
      (hf x hx).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (hg x hx) hx hacc h
    filter_upwards [h.nhdsNE_deriv] using by simp +contextual
  · rw [accPt_iff_frequently_nhdsNE, not_frequently] at hacc
    filter_upwards [hacc] using by grind
