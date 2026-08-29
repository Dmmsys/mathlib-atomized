/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Algebra.Order.WithTop.Untop0
public import Mathlib.Analysis.Meromorphic.IsolatedZeros
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Topology.LocallyFinsupp

/-!
# The Divisor of a meromorphic function

This file defines the divisor of a meromorphic function and proves the most basic lemmas about those
divisors. The lemma `MeromorphicOn.divisor_restrict` guarantees compatibility between restrictions
of divisors and of meromorphic functions to subsets of their domain of definition.
-/

@[expose] public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜} {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

open Filter Metric Topology

namespace MeromorphicOn

/-!
## Definition of the Divisor
-/

open scoped Classical in
/--
Definition of `divisor` / `divisor` 的定义

English:
definition divisor
  signature: (f : 𝕜 -> E) (U : Set 𝕜)
  body: fun z => if MeromorphicOn f U ∧ z in U then (meromorphicOrderAt f z).untop₀ else 0
  supportWithinDomain' z hz := by
    by_contra h₂z
    simp [h₂z] at hz
  supportLocallyFiniteWithinDomain' := by
    simp_all only [Function.support_subset_iff, ne_eq, ite_eq_right_iff, WithTop.untop₀_eq_zero,
      and_imp, Classical.not_imp, not_or, implies_true,
      ← supportDiscreteWithin_iff_locallyFiniteWithin]
    by_cases hf : MeromorphicOn f U
    · filter_upwards [mem_codiscrete_subtype_iff_mem_codiscreteWithin.1
        hf.codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top]
      simp only [Set.mem_image, Set.mem_ofPred_eq, Subtype.exists, exists_and_left, exists_prop,
        exists_eq_right_right, Pi.ofNat_apply, ite_eq_right_iff, WithTop.untop₀_eq_zero, and_imp]
      tauto
    · simp [hf, Pi.zero_def]

中文:
定义 divisor
  签名: (f : 𝕜 -> E) (U : 集合 𝕜)
  定义体: fun z => if MeromorphicOn f U ∧ z in U then (meromorphicOrderAt f z).untop₀ else 0
  supportWithinDomain' z hz := by
    by_contra h₂z
    simp [h₂z] at hz
  supportLocallyFiniteWithinDomain' := by
    simp_all only [Function.support_subset_iff, ne_eq, ite_eq_right_iff, WithTop.untop₀_eq_zero,
      and_imp, Classical.not_imp, not_or, implies_true,
      ← supportDiscreteWithin_iff_locallyFiniteWithin]
    by_cases hf : MeromorphicOn f U
    · filter_upwards [mem_codiscrete_subtype_iff_mem_codiscreteWithin.1
        hf.codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top]
      simp only [Set.mem_image, Set.mem_ofPred_eq, Subtype.exists, exists_and_left, exists_prop,
        exists_eq_right_right, Pi.ofNat_apply, ite_eq_right_iff, WithTop.untop₀_eq_zero, and_imp]
      tauto
    · simp [hf, Pi.zero_def]

Depends on / 依赖: MeromorphicOn, meromorphicOrderAt
-/
noncomputable def divisor (f : 𝕜 -> E) (U : Set 𝕜) :
    Function.locallyFinsuppWithin U Int where
  toFun := fun z => if MeromorphicOn f U ∧ z in U then (meromorphicOrderAt f z).untop₀ else 0
  supportWithinDomain' z hz := by
    by_contra h₂z
    simp [h₂z] at hz
  supportLocallyFiniteWithinDomain' := by
    simp_all only [Function.support_subset_iff, ne_eq, ite_eq_right_iff, WithTop.untop₀_eq_zero,
      and_imp, Classical.not_imp, not_or, implies_true,
      ← supportDiscreteWithin_iff_locallyFiniteWithin]
    by_cases hf : MeromorphicOn f U
    · filter_upwards [mem_codiscrete_subtype_iff_mem_codiscreteWithin.1
        hf.codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top]
      simp only [Set.mem_image, Set.mem_ofPred_eq, Subtype.exists, exists_and_left, exists_prop,
        exists_eq_right_right, Pi.ofNat_apply, ite_eq_right_iff, WithTop.untop₀_eq_zero, and_imp]
      tauto
    · simp [hf, Pi.zero_def]

open scoped Classical in
/--
theorem `divisor_def` / 定理 `divisor_def`

English:
theorem divisor_def
  given: (f : 𝕜 -> E) (U : Set 𝕜)
  proof: rfl

中文:
定理 divisor_def
  条件: (f : 𝕜 -> E) (U : 集合 𝕜)
  证明: rfl
-/
theorem divisor_def (f : 𝕜 -> E) (U : Set 𝕜) :
    divisor f U z = if MeromorphicOn f U ∧ z in U then (meromorphicOrderAt f z).untop₀ else 0 :=
  rfl

/--
Simplifier lemma: on `U`, the divisor of a function `f` that is meromorphic on `U` evaluates to
`order.untop₀`.
-/
@[simp]
/--
lemma `divisor_apply` / 引理 `divisor_apply`

English:
lemma divisor_apply
  given: {f : 𝕜 -> E} (hf : MeromorphicOn f U) (hz : z in U)
  proof: by simp_all [MeromorphicOn.divisor_def]

中文:
引理 divisor_apply
  条件: {f : 𝕜 -> E} (hf : MeromorphicOn f U) (hz : z in U)
  证明: by simp_all [MeromorphicOn.divisor_def]

Depends on / 依赖: MeromorphicOn, MeromorphicOn.divisor_def, divisor_def
-/
lemma divisor_apply {f : 𝕜 -> E} (hf : MeromorphicOn f U) (hz : z in U) :
    divisor f U z = (meromorphicOrderAt f z).untop₀ := by simp_all [MeromorphicOn.divisor_def]

/--
theorem `divisor_eq_zero_of_not_meromorphicOn` / 定理 `divisor_eq_zero_of_not_meromorphicOn`

English:
theorem divisor_eq_zero_of_not_meromorphicOn
  given: {f : 𝕜 -> E} (hf : ¬ MeromorphicOn f U)
  proof: by
  unfold divisor
  aesop

中文:
定理 divisor_eq_zero_of_not_meromorphicOn
  条件: {f : 𝕜 -> E} (hf : ¬ MeromorphicOn f U)
  证明: by
  unfold divisor
  aesop
-/
@[simp] theorem divisor_eq_zero_of_not_meromorphicOn {f : 𝕜 -> E} (hf : ¬ MeromorphicOn f U) :
    divisor f U z = 0 := by
  unfold divisor
  aesop

/--
lemma `AnalyticOnNhd.divisor_apply` / 引理 `AnalyticOnNhd.divisor_apply`

English:
lemma AnalyticOnNhd.divisor_apply
  given: {f : 𝕜 -> E} (hf : AnalyticOnNhd 𝕜 f U) (hz : z in U)
  proof: by
  rw [hf.meromorphicOn.divisor_apply hz]; rw [(hf z hz).meromorphicOrderAt_eq]

中文:
引理 AnalyticOnNhd.divisor_apply
  条件: {f : 𝕜 -> E} (hf : AnalyticOnNhd 𝕜 f U) (hz : z in U)
  证明: by
  rw [hf.meromorphicOn.divisor_apply hz]; rw [(hf z hz).meromorphicOrderAt_eq]

Depends on / 依赖: divisor_apply, hf.meromorphicOn.divisor_apply, meromorphicOn, meromorphicOrderAt_eq
-/
lemma AnalyticOnNhd.divisor_apply {f : 𝕜 -> E} (hf : AnalyticOnNhd 𝕜 f U) (hz : z in U) :
    divisor f U z = ((analyticOrderAt f z).map (↑)).untop₀ := by
  rw [hf.meromorphicOn.divisor_apply hz]; rw [(hf z hz).meromorphicOrderAt_eq]

/-!
## Support Properties
-/

/--
lemma `_root_.divisor_sphere_support_finite` / 引理 `_root_.divisor_sphere_support_finite`

English:
lemma _root_.divisor_sphere_support_finite
  given: [ProperSpace 𝕜] {f : 𝕜 -> E} {R : Real} {c : 𝕜}
  proof: (divisor f (sphere c R)).finiteSupport (isCompact_sphere c R)

中文:
引理 _root_.divisor_sphere_support_finite
  条件: [真空间 𝕜] {f : 𝕜 -> E} {R : 实数} {c : 𝕜}
  证明: (divisor f (sphere c R)).finiteSupport (isCompact_sphere c R)

Depends on / 依赖: divisor, finiteSupport, isCompact_sphere, sphere
-/
lemma _root_.divisor_sphere_support_finite [ProperSpace 𝕜] {f : 𝕜 -> E} {R : Real} {c : 𝕜} :
    (divisor f (sphere c R)).support.Finite :=
  (divisor f (sphere c R)).finiteSupport (isCompact_sphere c R)

/--
lemma `divisor_support_finite_of_subset` / 引理 `divisor_support_finite_of_subset`

English:
lemma divisor_support_finite_of_subset
  statement: {f : 𝕜 -> E} {V : Set 𝕜} (hf : MeromorphicOn f U)
  proof: by
  apply ((divisor f U).finiteSupport hU).subset
  intro b hb
  rw [Function.mem_support]; rw [ne_eq]; rw [divisor_apply hf (hV ((divisor f V).supportWithinDomain hb))]
  rwa [Function.mem_support, ne_eq, divisor_apply (fun x hx => hf x (hV hx))
    ((divisor f V).supportWithinDomain hb)] at hb

中文:
引理 divisor_support_finite_of_subset
  结论: {f : 𝕜 -> E} {V : 集合 𝕜} (hf : MeromorphicOn f U)
  证明: by
  apply ((divisor f U).finiteSupport hU).subset
  intro b hb
  rw [Function.mem_support]; rw [ne_eq]; rw [divisor_apply hf (hV ((divisor f V).supportWithinDomain hb))]
  rwa [Function.mem_support, ne_eq, divisor_apply (fun x hx => hf x (hV hx))
    ((divisor f V).supportWithinDomain hb)] at hb

Depends on / 依赖: Function, Function.mem_support, divisor, divisor_apply, finiteSupport, mem_support, ne_eq, subset, supportWithinDomain
-/
lemma divisor_support_finite_of_subset {f : 𝕜 -> E} {V : Set 𝕜} (hf : MeromorphicOn f U)
    (hU : IsCompact U) (hV : V subseteq U) :
    (divisor f V).support.Finite := by
  apply ((divisor f U).finiteSupport hU).subset
  intro b hb
  rw [Function.mem_support]; rw [ne_eq]; rw [divisor_apply hf (hV ((divisor f V).supportWithinDomain hb))]
  rwa [Function.mem_support, ne_eq, divisor_apply (fun x hx => hf x (hV hx))
    ((divisor f V).supportWithinDomain hb)] at hb

/--
lemma `divisor_ball_support_finite` / 引理 `divisor_ball_support_finite`

English:
lemma divisor_ball_support_finite
  statement: [ProperSpace 𝕜] {f : 𝕜 -> E} {R : Real} {c : 𝕜}
  proof: hf.divisor_support_finite_of_subset (isCompact_closedBall c R) ball_subset_closedBall

中文:
引理 divisor_ball_support_finite
  结论: [真空间 𝕜] {f : 𝕜 -> E} {R : 实数} {c : 𝕜}
  证明: hf.divisor_support_finite_of_subset (isCompact_closedBall c R) ball_subset_closedBall

Depends on / 依赖: ball_subset_closedBall, divisor_support_finite_of_subset, hf.divisor_support_finite_of_subset, isCompact_closedBall
-/
lemma divisor_ball_support_finite [ProperSpace 𝕜] {f : 𝕜 -> E} {R : Real} {c : 𝕜}
    (hf : MeromorphicOn f (closedBall c R)) :
    (divisor f (ball c R)).support.Finite :=
  hf.divisor_support_finite_of_subset (isCompact_closedBall c R) ball_subset_closedBall

/-!
## Congruence Lemmas
-/

/--
theorem `divisor_congr_codiscreteWithin_of_eqOn_compl` / 定理 `divisor_congr_codiscreteWithin_of_eqOn_compl`

English:
theorem divisor_congr_codiscreteWithin_of_eqOn_compl
  statement: {f₁ f₂ : 𝕜 -> E} (hf₁ : MeromorphicOn f₁ U)
  proof: by
  ext x
  by_cases hx : x in U
  · simp only [hf₁, hx, divisor_apply, hf₁.congr_codiscreteWithin_of_eqOn_compl h₁ h₂]
    congr 1
    apply meromorphicOrderAt_congr
    simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin, disjoint_principal_right] at h₁
    filter_upwards [h₁ x hx] with a ha
    simp at ha
    tauto
  · simp [hx]

中文:
定理 divisor_congr_codiscreteWithin_of_eqOn_compl
  结论: {f₁ f₂ : 𝕜 -> E} (hf₁ : MeromorphicOn f₁ U)
  证明: by
  ext x
  by_cases hx : x in U
  · simp only [hf₁, hx, divisor_apply, hf₁.congr_codiscreteWithin_of_eqOn_compl h₁ h₂]
    congr 1
    apply meromorphicOrderAt_congr
    simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin, disjoint_principal_right] at h₁
    filter_upwards [h₁ x hx] with a ha
    simp at ha
    tauto
  · simp [hx]

Depends on / 依赖: Eventually, EventuallyEq, Filter, Filter.Eventually, congr_codiscreteWithin_of_eqOn_compl, disjoint_principal_right, divisor_apply, filter_upwards, mem_codiscreteWithin, meromorphicOrderAt_congr, simp_rw
-/
theorem divisor_congr_codiscreteWithin_of_eqOn_compl {f₁ f₂ : 𝕜 -> E} (hf₁ : MeromorphicOn f₁ U)
    (h₁ : f₁ =ᶠ[codiscreteWithin U] f₂) (h₂ : Set.EqOn f₁ f₂ Uᶜ) :
    divisor f₁ U = divisor f₂ U := by
  ext x
  by_cases hx : x in U
  · simp only [hf₁, hx, divisor_apply, hf₁.congr_codiscreteWithin_of_eqOn_compl h₁ h₂]
    congr 1
    apply meromorphicOrderAt_congr
    simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin, disjoint_principal_right] at h₁
    filter_upwards [h₁ x hx] with a ha
    simp at ha
    tauto
  · simp [hx]

/--
theorem `divisor_of_eventuallyEq_codiscreteWithin_preperfect` / 定理 `divisor_of_eventuallyEq_codiscreteWithin_preperfect`

English:
theorem divisor_of_eventuallyEq_codiscreteWithin_preperfect
  statement: {f₁ f₂ : 𝕜 -> E}
  proof: by
  ext z
  by_cases hz : z ∉ U
  · simp_all
  rw [not_not] at hz
  rw [divisor_apply hf₁ hz]; rw [divisor_apply hf₂ hz]
  congr 1
  apply meromorphicOrderAt_congr
  apply (hf₁ z hz).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
    (hf₂ z hz) hz hU h

中文:
定理 divisor_of_eventuallyEq_codiscreteWithin_preperfect
  结论: {f₁ f₂ : 𝕜 -> E}
  证明: by
  ext z
  by_cases hz : z ∉ U
  · simp_all
  rw [not_not] at hz
  rw [divisor_apply hf₁ hz]; rw [divisor_apply hf₂ hz]
  congr 1
  apply meromorphicOrderAt_congr
  apply (hf₁ z hz).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
    (hf₂ z hz) hz hU h

Depends on / 依赖: divisor_apply, eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect, meromorphicOrderAt_congr, not_not
-/
theorem divisor_of_eventuallyEq_codiscreteWithin_preperfect {f₁ f₂ : 𝕜 -> E}
    (hf₁ : MeromorphicOn f₁ U) (hf₂ : MeromorphicOn f₂ U) (hU : Preperfect U)
    (h : f₁ =ᶠ[codiscreteWithin U] f₂) :
    divisor f₁ U = divisor f₂ U := by
  ext z
  by_cases hz : z ∉ U
  · simp_all
  rw [not_not] at hz
  rw [divisor_apply hf₁ hz]; rw [divisor_apply hf₂ hz]
  congr 1
  apply meromorphicOrderAt_congr
  apply (hf₁ z hz).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
    (hf₂ z hz) hz hU h

/--
theorem `divisor_congr_codiscreteWithin` / 定理 `divisor_congr_codiscreteWithin`

English:
theorem divisor_congr_codiscreteWithin
  statement: {f₁ f₂ : 𝕜 -> E} (h₁ : f₁ =ᶠ[codiscreteWithin U] f₂)
  proof: by
  by_cases hf₁ : MeromorphicOn f₁ U
  · ext x
    by_cases hx : x in U
    · simp only [hf₁, hx, divisor_apply, hf₁.congr_codiscreteWithin h₁ h₂]
      congr 1
      apply meromorphicOrderAt_congr
      simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin,
        disjoint_principal_right] at h₁
      have : U in 𝓝[!=] x := by
        apply mem_nhdsWithin.mpr
        use U, h₂, hx, Set.inter_subset_left
      filter_upwards [this, h₁ x hx] with a h₁a h₂a
      simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_ofPred_eq, not_and] at h₂a
      tauto
    · simp [hx]
  · simp [divisor, hf₁, (meromorphicOn_congr_codiscreteWithin h₁ h₂).not.1 hf₁]

中文:
定理 divisor_congr_codiscreteWithin
  结论: {f₁ f₂ : 𝕜 -> E} (h₁ : f₁ =ᶠ[codiscreteWithin U] f₂)
  证明: by
  by_cases hf₁ : MeromorphicOn f₁ U
  · ext x
    by_cases hx : x in U
    · simp only [hf₁, hx, divisor_apply, hf₁.congr_codiscreteWithin h₁ h₂]
      congr 1
      apply meromorphicOrderAt_congr
      simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin,
        disjoint_principal_right] at h₁
      have : U in 𝓝[!=] x := by
        apply mem_nhdsWithin.mpr
        use U, h₂, hx, Set.inter_subset_left
      filter_upwards [this, h₁ x hx] with a h₁a h₂a
      simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_ofPred_eq, not_and] at h₂a
      tauto
    · simp [hx]
  · simp [divisor, hf₁, (meromorphicOn_congr_codiscreteWithin h₁ h₂).not.1 hf₁]

Depends on / 依赖: Eventually, EventuallyEq, Filter, Filter.Eventually, MeromorphicOn, Set.inter_subset_left, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_sdiff, congr_codiscreteWithin, disjoint_principal_right, divisor_apply, filter_upwards, inter_subset_left, mem_codiscreteWithin, mem_compl_iff, mem_nhdsWithin, mem_nhdsWithin.mpr, mem_ofPred_eq, mem_sdiff
-/
theorem divisor_congr_codiscreteWithin {f₁ f₂ : 𝕜 -> E} (h₁ : f₁ =ᶠ[codiscreteWithin U] f₂)
    (h₂ : IsOpen U) :
    divisor f₁ U = divisor f₂ U := by
  by_cases hf₁ : MeromorphicOn f₁ U
  · ext x
    by_cases hx : x in U
    · simp only [hf₁, hx, divisor_apply, hf₁.congr_codiscreteWithin h₁ h₂]
      congr 1
      apply meromorphicOrderAt_congr
      simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin,
        disjoint_principal_right] at h₁
      have : U in 𝓝[!=] x := by
        apply mem_nhdsWithin.mpr
        use U, h₂, hx, Set.inter_subset_left
      filter_upwards [this, h₁ x hx] with a h₁a h₂a
      simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_ofPred_eq, not_and] at h₂a
      tauto
    · simp [hx]
  · simp [divisor, hf₁, (meromorphicOn_congr_codiscreteWithin h₁ h₂).not.1 hf₁]

/-!
## Divisors of Analytic Functions
-/

/--
theorem `AnalyticOnNhd.divisor_nonneg` / 定理 `AnalyticOnNhd.divisor_nonneg`

English:
theorem AnalyticOnNhd.divisor_nonneg
  given: {f : 𝕜 -> E} (hf : AnalyticOnNhd 𝕜 f U)
  proof: by
  intro x
  by_cases hx : x in U
  · simp [hf.meromorphicOn, hx, (hf x hx).meromorphicOrderAt_nonneg]
  simp [hx]

中文:
定理 AnalyticOnNhd.divisor_nonneg
  条件: {f : 𝕜 -> E} (hf : AnalyticOnNhd 𝕜 f U)
  证明: by
  intro x
  by_cases hx : x in U
  · simp [hf.meromorphicOn, hx, (hf x hx).meromorphicOrderAt_nonneg]
  simp [hx]

Depends on / 依赖: hf.meromorphicOn, meromorphicOn, meromorphicOrderAt_nonneg
-/
theorem AnalyticOnNhd.divisor_nonneg {f : 𝕜 -> E} (hf : AnalyticOnNhd 𝕜 f U) :
    0 <= MeromorphicOn.divisor f U := by
  intro x
  by_cases hx : x in U
  · simp [hf.meromorphicOn, hx, (hf x hx).meromorphicOrderAt_nonneg]
  simp [hx]

/--
The divisor of a constant function is `0`.
-/
@[simp]
/--
theorem `divisor_const` / 定理 `divisor_const`

English:
theorem divisor_const
  given: (e : E)
  proof: by
  classical
  ext x
  simp only [divisor_def, meromorphicOrderAt_const, Function.locallyFinsuppWithin.coe_zero,
    Pi.zero_apply, ite_eq_right_iff, WithTop.untop₀_eq_zero,
    LinearOrderedAddCommGroupWithTop.top_ne_zero, imp_false, ite_eq_left_iff, WithTop.zero_ne_top,
    Decidable.not_not, and_imp]
  tauto

中文:
定理 divisor_const
  条件: (e : E)
  证明: by
  classical
  ext x
  simp only [divisor_def, meromorphicOrderAt_const, Function.locallyFinsuppWithin.coe_zero,
    Pi.zero_apply, ite_eq_right_iff, WithTop.untop₀_eq_zero,
    LinearOrderedAddCommGroupWithTop.top_ne_zero, imp_false, ite_eq_left_iff, WithTop.zero_ne_top,
    Decidable.not_not, and_imp]
  tauto

Depends on / 依赖: CStarRing, Decidable, Decidable.not_not, Function, Function.locallyFinsuppWithin.coe_zero, LinearOrderedAddCommGroupWithTop, LinearOrderedAddCommGroupWithTop.top_ne_zero, Pi.zero_apply, WithTop, WithTop.untop, WithTop.zero_ne_top, and_imp, classical, coe_zero, divisor_def, imp_false, ite_eq_left_iff, ite_eq_right_iff, locallyFinsuppWithin, meromorphicOrderAt_const
-/
theorem divisor_const (e : E) :
    divisor (fun _ => e) U = 0 := by
  classical
  ext x
  simp only [divisor_def, meromorphicOrderAt_const, Function.locallyFinsuppWithin.coe_zero,
    Pi.zero_apply, ite_eq_right_iff, WithTop.untop₀_eq_zero,
    LinearOrderedAddCommGroupWithTop.top_ne_zero, imp_false, ite_eq_left_iff, WithTop.zero_ne_top,
    Decidable.not_not, and_imp]
  tauto

/--
The divisor of a constant function is `0`.
-/
@[simp]
/--
theorem `divisor_intCast` / 定理 `divisor_intCast`

English:
theorem divisor_intCast
  given: (n : Int)
  proof: divisor_const (n : 𝕜)

中文:
定理 divisor_intCast
  条件: (n : 整数)
  证明: divisor_const (n : 𝕜)

Depends on / 依赖: divisor_const
-/
theorem divisor_intCast (n : Int) :
    divisor (n : 𝕜 -> 𝕜) U = 0 := divisor_const (n : 𝕜)

/--
The divisor of a constant function is `0`.
-/
@[simp]
/--
theorem `divisor_natCast` / 定理 `divisor_natCast`

English:
theorem divisor_natCast
  given: (n : Nat)
  proof: divisor_const (n : 𝕜)

中文:
定理 divisor_natCast
  条件: (n : 自然数)
  证明: divisor_const (n : 𝕜)

Depends on / 依赖: divisor_const
-/
theorem divisor_natCast (n : Nat) :
    divisor (n : 𝕜 -> 𝕜) U = 0 := divisor_const (n : 𝕜)

/--
theorem `divisor_ofNat` / 定理 `divisor_ofNat`

English:
theorem divisor_ofNat
  given: (n : Nat)
  proof: by
  convert! divisor_const (n : 𝕜)
  simp [Semiring.toGrindSemiring_ofNat 𝕜 n]

中文:
定理 divisor_of自然数
  条件: (n : 自然数)
  证明: by
  convert! divisor_const (n : 𝕜)
  simp [Semiring.toGrindSemiring_ofNat 𝕜 n]
-/
@[simp] theorem divisor_ofNat (n : Nat) :
    divisor (ofNat(n) : 𝕜 -> 𝕜) U = 0 := by
  convert! divisor_const (n : 𝕜)
  simp [Semiring.toGrindSemiring_ofNat 𝕜 n]

/-!
## Behavior under Standard Operations
-/

/--
theorem `min_divisor_le_divisor_add` / 定理 `min_divisor_le_divisor_add`

English:
theorem min_divisor_le_divisor_add
  statement: {f₁ f₂ : 𝕜 -> E} {z : 𝕜} {U : Set 𝕜} (hf₁ : MeromorphicOn f₁ U)
  proof: by
  by_cases! hz : z ∉ U
  · simp_all
  rw [divisor_apply hf₁ hz]; rw [divisor_apply hf₂ hz]; rw [divisor_apply (hf₁.add hf₂) hz]
  by_cases h₁ : meromorphicOrderAt f₁ z = ⊤
  · simp_all
  by_cases h₂ : meromorphicOrderAt f₂ z = ⊤
  · simp_all
  rw [← WithTop.untop₀_min h₁ h₂]
  apply WithTop.untop₀_le_untop₀ h₃
  exact meromorphicOrderAt_add (hf₁ z hz) (hf₂ z hz)

中文:
定理 min_divisor_le_divisor_add
  结论: {f₁ f₂ : 𝕜 -> E} {z : 𝕜} {U : 集合 𝕜} (hf₁ : MeromorphicOn f₁ U)
  证明: by
  by_cases! hz : z ∉ U
  · simp_all
  rw [divisor_apply hf₁ hz]; rw [divisor_apply hf₂ hz]; rw [divisor_apply (hf₁.add hf₂) hz]
  by_cases h₁ : meromorphicOrderAt f₁ z = ⊤
  · simp_all
  by_cases h₂ : meromorphicOrderAt f₂ z = ⊤
  · simp_all
  rw [← WithTop.untop₀_min h₁ h₂]
  apply WithTop.untop₀_le_untop₀ h₃
  exact meromorphicOrderAt_add (hf₁ z hz) (hf₂ z hz)

Depends on / 依赖: WithTop, WithTop.untop, divisor_apply, meromorphicOrderAt, meromorphicOrderAt_add
-/
theorem min_divisor_le_divisor_add {f₁ f₂ : 𝕜 -> E} {z : 𝕜} {U : Set 𝕜} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : MeromorphicOn f₂ U) (h₁z : z in U) (h₃ : meromorphicOrderAt (f₁ + f₂) z != ⊤) :
    min (divisor f₁ U z) (divisor f₂ U z) <= divisor (f₁ + f₂) U z := by
  by_cases! hz : z ∉ U
  · simp_all
  rw [divisor_apply hf₁ hz]; rw [divisor_apply hf₂ hz]; rw [divisor_apply (hf₁.add hf₂) hz]
  by_cases h₁ : meromorphicOrderAt f₁ z = ⊤
  · simp_all
  by_cases h₂ : meromorphicOrderAt f₂ z = ⊤
  · simp_all
  rw [← WithTop.untop₀_min h₁ h₂]
  apply WithTop.untop₀_le_untop₀ h₃
  exact meromorphicOrderAt_add (hf₁ z hz) (hf₂ z hz)

/--
theorem `negPart_divisor_add_le_max` / 定理 `negPart_divisor_add_le_max`

English:
theorem negPart_divisor_add_le_max
  statement: {f₁ f₂ : 𝕜 -> E} {U : Set 𝕜} (hf₁ : MeromorphicOn f₁ U)
  proof: by
  intro z
  by_cases! hz : z ∉ U
  · simp [hz]
  simp only [Function.locallyFinsuppWithin.negPart_apply, Function.locallyFinsuppWithin.max_apply]
  by_cases hf₁₂ : meromorphicOrderAt (f₁ + f₂) z = ⊤
  · simp [divisor_apply (hf₁.add hf₂) hz, hf₁₂, negPart_nonneg]
  rw [← negPart_min]
  apply ((le_iff_posPart_negPart _ _).1 (min_divisor_le_divisor_add hf₁ hf₂ hz hf₁₂)).2

中文:
定理 negPart_divisor_add_le_max
  结论: {f₁ f₂ : 𝕜 -> E} {U : 集合 𝕜} (hf₁ : MeromorphicOn f₁ U)
  证明: by
  intro z
  by_cases! hz : z ∉ U
  · simp [hz]
  simp only [Function.locallyFinsuppWithin.negPart_apply, Function.locallyFinsuppWithin.max_apply]
  by_cases hf₁₂ : meromorphicOrderAt (f₁ + f₂) z = ⊤
  · simp [divisor_apply (hf₁.add hf₂) hz, hf₁₂, negPart_nonneg]
  rw [← negPart_min]
  apply ((le_iff_posPart_negPart _ _).1 (min_divisor_le_divisor_add hf₁ hf₂ hz hf₁₂)).2

Depends on / 依赖: Function, Function.locallyFinsuppWithin.max_apply, Function.locallyFinsuppWithin.negPart_apply, divisor_apply, le_iff_posPart_negPart, locallyFinsuppWithin, max_apply, meromorphicOrderAt, min_divisor_le_divisor_add, negPart_apply, negPart_min, negPart_nonneg
-/
theorem negPart_divisor_add_le_max {f₁ f₂ : 𝕜 -> E} {U : Set 𝕜} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : MeromorphicOn f₂ U) :
    (divisor (f₁ + f₂) U)⁻ <= max (divisor f₁ U)⁻ (divisor f₂ U)⁻ := by
  intro z
  by_cases! hz : z ∉ U
  · simp [hz]
  simp only [Function.locallyFinsuppWithin.negPart_apply, Function.locallyFinsuppWithin.max_apply]
  by_cases hf₁₂ : meromorphicOrderAt (f₁ + f₂) z = ⊤
  · simp [divisor_apply (hf₁.add hf₂) hz, hf₁₂, negPart_nonneg]
  rw [← negPart_min]
  apply ((le_iff_posPart_negPart _ _).1 (min_divisor_le_divisor_add hf₁ hf₂ hz hf₁₂)).2

/--
theorem `negPart_divisor_add_le_add` / 定理 `negPart_divisor_add_le_add`

English:
theorem negPart_divisor_add_le_add
  statement: {f₁ f₂ : 𝕜 -> E} {U : Set 𝕜} (hf₁ : MeromorphicOn f₁ U)
  proof: by
  calc (divisor (f₁ + f₂) U)⁻
    _ <= max (divisor f₁ U)⁻ (divisor f₂ U)⁻ :=
      negPart_divisor_add_le_max hf₁ hf₂
    _ <= (divisor f₁ U)⁻ + (divisor f₂ U)⁻ := by
      by_cases h : (divisor f₁ U)⁻ <= (divisor f₂ U)⁻
      <;> simp_all [negPart_nonneg]

中文:
定理 negPart_divisor_add_le_add
  结论: {f₁ f₂ : 𝕜 -> E} {U : 集合 𝕜} (hf₁ : MeromorphicOn f₁ U)
  证明: by
  calc (divisor (f₁ + f₂) U)⁻
    _ <= max (divisor f₁ U)⁻ (divisor f₂ U)⁻ :=
      negPart_divisor_add_le_max hf₁ hf₂
    _ <= (divisor f₁ U)⁻ + (divisor f₂ U)⁻ := by
      by_cases h : (divisor f₁ U)⁻ <= (divisor f₂ U)⁻
      <;> simp_all [negPart_nonneg]

Depends on / 依赖: divisor, negPart_divisor_add_le_max, negPart_nonneg
-/
theorem negPart_divisor_add_le_add {f₁ f₂ : 𝕜 -> E} {U : Set 𝕜} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : MeromorphicOn f₂ U) :
    (divisor (f₁ + f₂) U)⁻ <= (divisor f₁ U)⁻ + (divisor f₂ U)⁻ := by
  calc (divisor (f₁ + f₂) U)⁻
    _ <= max (divisor f₁ U)⁻ (divisor f₂ U)⁻ :=
      negPart_divisor_add_le_max hf₁ hf₂
    _ <= (divisor f₁ U)⁻ + (divisor f₂ U)⁻ := by
      by_cases h : (divisor f₁ U)⁻ <= (divisor f₂ U)⁻
      <;> simp_all [negPart_nonneg]

/--
theorem `divisor_smul` / 定理 `divisor_smul`

English:
theorem divisor_smul
  statement: {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 -> E} (h₁f₁ : MeromorphicOn f₁ U)
  proof: by
  ext z
  by_cases hz : z in U
  · lift meromorphicOrderAt f₁ z to Int using (h₂f₁ z hz) with a₁ ha₁
    lift meromorphicOrderAt f₂ z to Int using (h₂f₂ z hz) with a₂ ha₂
    simp [h₁f₁, h₁f₂, h₁f₁.smul h₁f₂, hz, meromorphicOrderAt_smul (h₁f₁ z hz) (h₁f₂ z hz),
      ← ha₁, ← ha₂, ← WithTop.coe_add]
  · simp [hz]

中文:
定理 divisor_smul
  结论: {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 -> E} (h₁f₁ : MeromorphicOn f₁ U)
  证明: by
  ext z
  by_cases hz : z in U
  · lift meromorphicOrderAt f₁ z to Int using (h₂f₁ z hz) with a₁ ha₁
    lift meromorphicOrderAt f₂ z to Int using (h₂f₂ z hz) with a₂ ha₂
    simp [h₁f₁, h₁f₂, h₁f₁.smul h₁f₂, hz, meromorphicOrderAt_smul (h₁f₁ z hz) (h₁f₂ z hz),
      ← ha₁, ← ha₂, ← WithTop.coe_add]
  · simp [hz]

Depends on / 依赖: WithTop, WithTop.coe_add, coe_add, meromorphicOrderAt, meromorphicOrderAt_smul
-/
theorem divisor_smul {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 -> E} (h₁f₁ : MeromorphicOn f₁ U)
    (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : forall z in U, meromorphicOrderAt f₁ z != ⊤)
    (h₂f₂ : forall z in U, meromorphicOrderAt f₂ z != ⊤) :
    divisor (f₁ • f₂) U = divisor f₁ U + divisor f₂ U := by
  ext z
  by_cases hz : z in U
  · lift meromorphicOrderAt f₁ z to Int using (h₂f₁ z hz) with a₁ ha₁
    lift meromorphicOrderAt f₂ z to Int using (h₂f₂ z hz) with a₂ ha₂
    simp [h₁f₁, h₁f₂, h₁f₁.smul h₁f₂, hz, meromorphicOrderAt_smul (h₁f₁ z hz) (h₁f₂ z hz),
      ← ha₁, ← ha₂, ← WithTop.coe_add]
  · simp [hz]

/--
theorem `divisor_fun_smul` / 定理 `divisor_fun_smul`

English:
theorem divisor_fun_smul
  statement: {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 -> E} (h₁f₁ : MeromorphicOn f₁ U)
  proof: divisor_smul h₁f₁ h₁f₂ h₂f₁ h₂f₂

中文:
定理 divisor_fun_smul
  结论: {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 -> E} (h₁f₁ : MeromorphicOn f₁ U)
  证明: divisor_smul h₁f₁ h₁f₂ h₂f₁ h₂f₂

Depends on / 依赖: divisor_smul
-/
theorem divisor_fun_smul {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 -> E} (h₁f₁ : MeromorphicOn f₁ U)
    (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : forall z in U, meromorphicOrderAt f₁ z != ⊤)
    (h₂f₂ : forall z in U, meromorphicOrderAt f₂ z != ⊤) :
    divisor (fun z => f₁ z • f₂ z) U = divisor f₁ U + divisor f₂ U :=
  divisor_smul h₁f₁ h₁f₂ h₂f₁ h₂f₂

/--
theorem `divisor_mul` / 定理 `divisor_mul`

English:
theorem divisor_mul
  statement: {f₁ f₂ : 𝕜 -> 𝕜} (h₁f₁ : MeromorphicOn f₁ U)
  proof: divisor_smul h₁f₁ h₁f₂ h₂f₁ h₂f₂

中文:
定理 divisor_mul
  结论: {f₁ f₂ : 𝕜 -> 𝕜} (h₁f₁ : MeromorphicOn f₁ U)
  证明: divisor_smul h₁f₁ h₁f₂ h₂f₁ h₂f₂

Depends on / 依赖: divisor_smul
-/
theorem divisor_mul {f₁ f₂ : 𝕜 -> 𝕜} (h₁f₁ : MeromorphicOn f₁ U)
    (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : forall z in U, meromorphicOrderAt f₁ z != ⊤)
    (h₂f₂ : forall z in U, meromorphicOrderAt f₂ z != ⊤) :
    divisor (f₁ * f₂) U = divisor f₁ U + divisor f₂ U := divisor_smul h₁f₁ h₁f₂ h₂f₁ h₂f₂

/--
theorem `divisor_fun_mul` / 定理 `divisor_fun_mul`

English:
theorem divisor_fun_mul
  statement: {f₁ f₂ : 𝕜 -> 𝕜} (h₁f₁ : MeromorphicOn f₁ U)
  proof: divisor_smul h₁f₁ h₁f₂ h₂f₁ h₂f₂

中文:
定理 divisor_fun_mul
  结论: {f₁ f₂ : 𝕜 -> 𝕜} (h₁f₁ : MeromorphicOn f₁ U)
  证明: divisor_smul h₁f₁ h₁f₂ h₂f₁ h₂f₂

Depends on / 依赖: divisor_smul
-/
theorem divisor_fun_mul {f₁ f₂ : 𝕜 -> 𝕜} (h₁f₁ : MeromorphicOn f₁ U)
    (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : forall z in U, meromorphicOrderAt f₁ z != ⊤)
    (h₂f₂ : forall z in U, meromorphicOrderAt f₂ z != ⊤) :
    divisor (fun z => f₁ z * f₂ z) U = divisor f₁ U + divisor f₂ U :=
  divisor_smul h₁f₁ h₁f₂ h₂f₁ h₂f₂

open Finset in
/--
theorem `divisor_prod` / 定理 `divisor_prod`

English:
theorem divisor_prod
  statement: {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜}
  proof: by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [prod_empty]; rw [sum_empty]
    exact divisor_ofNat 1
  | insert a s ha hs =>
    have (z) (hz : z in U) : meromorphicOrderAt (∏ i in s, f i) z != ⊤ := by
      simpa [meromorphicOrderAt_prod (fun i hi => h₁f i (mem_insert_of_mem hi) z hz)]
        using fun i hi => h₂f i (mem_insert_of_mem hi) z hz
    rw [prod_insert ha]; rw [sum_insert ha]; rw [divisor_mul (by aesop)
        (prod (fun i hi => h₁f i (mem_insert_of_mem hi)))
        (h₂f a (mem_insert_self a s)) this]; rw [hs (fun i hi => h₁f i (mem_insert_of_mem hi))
        (fun i hi => h₂f i (mem_insert_of_mem hi))]

中文:
定理 divisor_prod
  结论: {ι : 类型} {s : 有限集 ι} {f : ι -> 𝕜 -> 𝕜}
  证明: by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [prod_empty]; rw [sum_empty]
    exact divisor_ofNat 1
  | insert a s ha hs =>
    have (z) (hz : z in U) : meromorphicOrderAt (∏ i in s, f i) z != ⊤ := by
      simpa [meromorphicOrderAt_prod (fun i hi => h₁f i (mem_insert_of_mem hi) z hz)]
        using fun i hi => h₂f i (mem_insert_of_mem hi) z hz
    rw [prod_insert ha]; rw [sum_insert ha]; rw [divisor_mul (by aesop)
        (prod (fun i hi => h₁f i (mem_insert_of_mem hi)))
        (h₂f a (mem_insert_self a s)) this]; rw [hs (fun i hi => h₁f i (mem_insert_of_mem hi))
        (fun i hi => h₂f i (mem_insert_of_mem hi))]

Depends on / 依赖: Finset, Finset.induction, classical, divisor_mul, divisor_ofNat, insert, mem_insert_of_mem, mem_insert_self, meromorphicOrderAt, meromorphicOrderAt_prod, prod_empty, prod_insert, sum_empty, sum_insert
-/
theorem divisor_prod {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜}
    (h₁f : forall i in s, MeromorphicOn (f i) U)
    (h₂f : forall i in s, forall z in U, meromorphicOrderAt (f i) z != ⊤) :
    divisor (∏ i in s, f i) U = ∑ i in s, divisor (f i) U := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [prod_empty]; rw [sum_empty]
    exact divisor_ofNat 1
  | insert a s ha hs =>
    have (z) (hz : z in U) : meromorphicOrderAt (∏ i in s, f i) z != ⊤ := by
      simpa [meromorphicOrderAt_prod (fun i hi => h₁f i (mem_insert_of_mem hi) z hz)]
        using fun i hi => h₂f i (mem_insert_of_mem hi) z hz
    rw [prod_insert ha]; rw [sum_insert ha]; rw [divisor_mul (by aesop)
        (prod (fun i hi => h₁f i (mem_insert_of_mem hi)))
        (h₂f a (mem_insert_self a s)) this]; rw [hs (fun i hi => h₁f i (mem_insert_of_mem hi))
        (fun i hi => h₂f i (mem_insert_of_mem hi))]

/--
theorem `divisor_fun_prod` / 定理 `divisor_fun_prod`

English:
theorem divisor_fun_prod
  statement: {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜}
  proof: by
  convert! divisor_prod h₁f h₂f
  exact (Finset.prod_apply _ s f).symm

中文:
定理 divisor_fun_prod
  结论: {ι : 类型} {s : 有限集 ι} {f : ι -> 𝕜 -> 𝕜}
  证明: by
  convert! divisor_prod h₁f h₂f
  exact (Finset.prod_apply _ s f).symm

Depends on / 依赖: Finset, Finset.prod_apply, convert, divisor_prod, prod_apply
-/
theorem divisor_fun_prod {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜}
    (h₁f : forall i in s, MeromorphicOn (f i) U)
    (h₂f : forall i in s, forall z in U, meromorphicOrderAt (f i) z != ⊤) :
    divisor (fun x => ∏ i in s, f i x) U = ∑ i in s, divisor (f i) U := by
  convert! divisor_prod h₁f h₂f
  exact (Finset.prod_apply _ s f).symm

/-- The divisor of the inverse is the negative of the divisor. -/
@[simp]
/--
theorem `divisor_inv` / 定理 `divisor_inv`

English:
theorem divisor_inv
  given: {f : 𝕜 -> 𝕜}
  proof: by
  ext z
  by_cases h : MeromorphicOn f U ∧ z in U
  · simp [divisor_apply, h, meromorphicOrderAt_inv]
  · simp [divisor_def, h]

中文:
定理 divisor_inv
  条件: {f : 𝕜 -> 𝕜}
  证明: by
  ext z
  by_cases h : MeromorphicOn f U ∧ z in U
  · simp [divisor_apply, h, meromorphicOrderAt_inv]
  · simp [divisor_def, h]

Depends on / 依赖: MeromorphicOn, divisor_apply, divisor_def, meromorphicOrderAt_inv
-/
theorem divisor_inv {f : 𝕜 -> 𝕜} :
    divisor f⁻¹ U = -divisor f U := by
  ext z
  by_cases h : MeromorphicOn f U ∧ z in U
  · simp [divisor_apply, h, meromorphicOrderAt_inv]
  · simp [divisor_def, h]

/-- The divisor of the inverse is the negative of the divisor. -/
@[simp]
/--
theorem `divisor_fun_inv` / 定理 `divisor_fun_inv`

English:
theorem divisor_fun_inv
  given: {f : 𝕜 -> 𝕜}
  statement: divisor (fun z => (f z)⁻¹) U = -divisor f U
  proof: divisor_inv

中文:
定理 divisor_fun_inv
  条件: {f : 𝕜 -> 𝕜}
  结论: divisor (fun z => (f z)⁻¹) U = -divisor f U
  证明: divisor_inv

Depends on / 依赖: divisor_inv
-/
theorem divisor_fun_inv {f : 𝕜 -> 𝕜} : divisor (fun z => (f z)⁻¹) U = -divisor f U := divisor_inv

/--
theorem `divisor_pow` / 定理 `divisor_pow`

English:
theorem divisor_pow
  given: {f : 𝕜 -> 𝕜} (hf : MeromorphicOn f U) (n : Nat)
  proof: by
  ext z
  by_cases hn : n = 0
  · simp [hn]
  by_cases hz : z in U
  · simp [hf.pow, divisor_apply, meromorphicOrderAt_pow (hf z hz), hf, hz]
  · simp [hz]

中文:
定理 divisor_pow
  条件: {f : 𝕜 -> 𝕜} (hf : MeromorphicOn f U) (n : 自然数)
  证明: by
  ext z
  by_cases hn : n = 0
  · simp [hn]
  by_cases hz : z in U
  · simp [hf.pow, divisor_apply, meromorphicOrderAt_pow (hf z hz), hf, hz]
  · simp [hz]

Depends on / 依赖: divisor_apply, hf.pow, meromorphicOrderAt_pow
-/
theorem divisor_pow {f : 𝕜 -> 𝕜} (hf : MeromorphicOn f U) (n : Nat) :
    divisor (f ^ n) U = n • divisor f U := by
  ext z
  by_cases hn : n = 0
  · simp [hn]
  by_cases hz : z in U
  · simp [hf.pow, divisor_apply, meromorphicOrderAt_pow (hf z hz), hf, hz]
  · simp [hz]

/--
theorem `divisor_fun_pow` / 定理 `divisor_fun_pow`

English:
theorem divisor_fun_pow
  given: {f : 𝕜 -> 𝕜} (hf : MeromorphicOn f U) (n : Nat)
  proof: divisor_pow hf n

中文:
定理 divisor_fun_pow
  条件: {f : 𝕜 -> 𝕜} (hf : MeromorphicOn f U) (n : 自然数)
  证明: divisor_pow hf n

Depends on / 依赖: divisor_pow
-/
theorem divisor_fun_pow {f : 𝕜 -> 𝕜} (hf : MeromorphicOn f U) (n : Nat) :
    divisor (fun z => f z ^ n) U = n • divisor f U := divisor_pow hf n

/--
theorem `divisor_zpow` / 定理 `divisor_zpow`

English:
theorem divisor_zpow
  given: {f : 𝕜 -> 𝕜} (hf : MeromorphicOn f U) (n : Int)
  proof: by
  ext z
  by_cases hn : n = 0
  · simp [hn]
  by_cases hz : z in U
  · simp [hf.zpow, divisor_apply, meromorphicOrderAt_zpow (hf z hz), hf, hz]
  · simp [hz]

中文:
定理 divisor_zpow
  条件: {f : 𝕜 -> 𝕜} (hf : MeromorphicOn f U) (n : 整数)
  证明: by
  ext z
  by_cases hn : n = 0
  · simp [hn]
  by_cases hz : z in U
  · simp [hf.zpow, divisor_apply, meromorphicOrderAt_zpow (hf z hz), hf, hz]
  · simp [hz]

Depends on / 依赖: divisor_apply, hf.zpow, meromorphicOrderAt_zpow
-/
theorem divisor_zpow {f : 𝕜 -> 𝕜} (hf : MeromorphicOn f U) (n : Int) :
    divisor (f ^ n) U = n • divisor f U := by
  ext z
  by_cases hn : n = 0
  · simp [hn]
  by_cases hz : z in U
  · simp [hf.zpow, divisor_apply, meromorphicOrderAt_zpow (hf z hz), hf, hz]
  · simp [hz]

/--
theorem `divisor_fun_zpow` / 定理 `divisor_fun_zpow`

English:
theorem divisor_fun_zpow
  given: {f : 𝕜 -> 𝕜} (hf : MeromorphicOn f U) (n : Int)
  proof: divisor_zpow hf n

中文:
定理 divisor_fun_zpow
  条件: {f : 𝕜 -> 𝕜} (hf : MeromorphicOn f U) (n : 整数)
  证明: divisor_zpow hf n

Depends on / 依赖: divisor_zpow
-/
theorem divisor_fun_zpow {f : 𝕜 -> 𝕜} (hf : MeromorphicOn f U) (n : Int) :
    divisor (fun z => f z ^ n) U = n • divisor f U := divisor_zpow hf n

/--
Taking the divisor of a meromorphic function commutes with restriction.
-/
@[simp]
/--
theorem `divisor_restrict` / 定理 `divisor_restrict`

English:
theorem divisor_restrict
  given: {f : 𝕜 -> E} {V : Set 𝕜} (hf : MeromorphicOn f U) (hV : V subseteq U)
  proof: by
  ext x
  by_cases hx : x in V
  · rw [Function.locallyFinsuppWithin.restrict_apply]
    simp [hf, hx, hf.mono_set hV, hV hx]
  · simp [hx]

中文:
定理 divisor_restrict
  条件: {f : 𝕜 -> E} {V : 集合 𝕜} (hf : MeromorphicOn f U) (hV : V subseteq U)
  证明: by
  ext x
  by_cases hx : x in V
  · rw [Function.locallyFinsuppWithin.restrict_apply]
    simp [hf, hx, hf.mono_set hV, hV hx]
  · simp [hx]

Depends on / 依赖: Function, Function.locallyFinsuppWithin.restrict_apply, hf.mono_set, locallyFinsuppWithin, mono_set, restrict_apply
-/
theorem divisor_restrict {f : 𝕜 -> E} {V : Set 𝕜} (hf : MeromorphicOn f U) (hV : V subseteq U) :
    (divisor f U).restrict hV = divisor f V := by
  ext x
  by_cases hx : x in V
  · rw [Function.locallyFinsuppWithin.restrict_apply]
    simp [hf, hx, hf.mono_set hV, hV hx]
  · simp [hx]

/--
theorem `negPart_divisor_add_of_analyticNhdOn_right` / 定理 `negPart_divisor_add_of_analyticNhdOn_right`

English:
theorem negPart_divisor_add_of_analyticNhdOn_right
  statement: {f₁ f₂ : 𝕜 -> E} (hf₁ : MeromorphicOn f₁ U)
  proof: by
  ext x
  by_cases hx : x in U
  · suffices -(meromorphicOrderAt (f₁ + f₂) x).untop₀ ⊔ 0 = -(meromorphicOrderAt f₁ x).untop₀ ⊔ 0 by
      simpa [negPart_def, hx, hf₁, hf₁.add hf₂.meromorphicOn]
    by_cases h : 0 <= meromorphicOrderAt f₁ x
    · suffices 0 <= meromorphicOrderAt (f₁ + f₂) x by simp_all
      calc 0
      _ <= min (meromorphicOrderAt f₁ x) (meromorphicOrderAt f₂ x) :=
        le_inf h (hf₂ x hx).meromorphicOrderAt_nonneg
      _ <= meromorphicOrderAt (f₁ + f₂) x :=
        meromorphicOrderAt_add (hf₁ x hx) (hf₂ x hx).meromorphicAt
    · suffices meromorphicOrderAt f₁ x < meromorphicOrderAt f₂ x by
        rwa [meromorphicOrderAt_add_eq_left_of_lt (hf₂.meromorphicOn x hx)]
      calc meromorphicOrderAt f₁ x
      _ < 0 := by simpa using h
      _ <= meromorphicOrderAt f₂ x := (hf₂ x hx).meromorphicOrderAt_nonneg
  simp [hx]

中文:
定理 negPart_divisor_add_of_analyticNhdOn_right
  结论: {f₁ f₂ : 𝕜 -> E} (hf₁ : MeromorphicOn f₁ U)
  证明: by
  ext x
  by_cases hx : x in U
  · suffices -(meromorphicOrderAt (f₁ + f₂) x).untop₀ ⊔ 0 = -(meromorphicOrderAt f₁ x).untop₀ ⊔ 0 by
      simpa [negPart_def, hx, hf₁, hf₁.add hf₂.meromorphicOn]
    by_cases h : 0 <= meromorphicOrderAt f₁ x
    · suffices 0 <= meromorphicOrderAt (f₁ + f₂) x by simp_all
      calc 0
      _ <= min (meromorphicOrderAt f₁ x) (meromorphicOrderAt f₂ x) :=
        le_inf h (hf₂ x hx).meromorphicOrderAt_nonneg
      _ <= meromorphicOrderAt (f₁ + f₂) x :=
        meromorphicOrderAt_add (hf₁ x hx) (hf₂ x hx).meromorphicAt
    · suffices meromorphicOrderAt f₁ x < meromorphicOrderAt f₂ x by
        rwa [meromorphicOrderAt_add_eq_left_of_lt (hf₂.meromorphicOn x hx)]
      calc meromorphicOrderAt f₁ x
      _ < 0 := by simpa using h
      _ <= meromorphicOrderAt f₂ x := (hf₂ x hx).meromorphicOrderAt_nonneg
  simp [hx]

Depends on / 依赖: le_inf, meromorphicAt, meromorphicOn, meromorphicOrderAt, meromorphicOrderAt_add, meromorphicOrderAt_nonneg, negPart_def
-/
theorem negPart_divisor_add_of_analyticNhdOn_right {f₁ f₂ : 𝕜 -> E} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : AnalyticOnNhd 𝕜 f₂ U) :
    (divisor (f₁ + f₂) U)⁻ = (divisor f₁ U)⁻ := by
  ext x
  by_cases hx : x in U
  · suffices -(meromorphicOrderAt (f₁ + f₂) x).untop₀ ⊔ 0 = -(meromorphicOrderAt f₁ x).untop₀ ⊔ 0 by
      simpa [negPart_def, hx, hf₁, hf₁.add hf₂.meromorphicOn]
    by_cases h : 0 <= meromorphicOrderAt f₁ x
    · suffices 0 <= meromorphicOrderAt (f₁ + f₂) x by simp_all
      calc 0
      _ <= min (meromorphicOrderAt f₁ x) (meromorphicOrderAt f₂ x) :=
        le_inf h (hf₂ x hx).meromorphicOrderAt_nonneg
      _ <= meromorphicOrderAt (f₁ + f₂) x :=
        meromorphicOrderAt_add (hf₁ x hx) (hf₂ x hx).meromorphicAt
    · suffices meromorphicOrderAt f₁ x < meromorphicOrderAt f₂ x by
        rwa [meromorphicOrderAt_add_eq_left_of_lt (hf₂.meromorphicOn x hx)]
      calc meromorphicOrderAt f₁ x
      _ < 0 := by simpa using h
      _ <= meromorphicOrderAt f₂ x := (hf₂ x hx).meromorphicOrderAt_nonneg
  simp [hx]

/--
theorem `negPart_divisor_add_of_analyticNhdOn_left` / 定理 `negPart_divisor_add_of_analyticNhdOn_left`

English:
theorem negPart_divisor_add_of_analyticNhdOn_left
  statement: {f₁ f₂ : 𝕜 -> E} (hf₁ : AnalyticOnNhd 𝕜 f₁ U)
  proof: by
  rw [add_comm]
  exact negPart_divisor_add_of_analyticNhdOn_right hf₂ hf₁

中文:
定理 negPart_divisor_add_of_analyticNhdOn_left
  结论: {f₁ f₂ : 𝕜 -> E} (hf₁ : AnalyticOnNhd 𝕜 f₁ U)
  证明: by
  rw [add_comm]
  exact negPart_divisor_add_of_analyticNhdOn_right hf₂ hf₁

Depends on / 依赖: add_comm, negPart_divisor_add_of_analyticNhdOn_right
-/
theorem negPart_divisor_add_of_analyticNhdOn_left {f₁ f₂ : 𝕜 -> E} (hf₁ : AnalyticOnNhd 𝕜 f₁ U)
    (hf₂ : MeromorphicOn f₂ U) :
    (divisor (f₁ + f₂) U)⁻ = (divisor f₂ U)⁻ := by
  rw [add_comm]
  exact negPart_divisor_add_of_analyticNhdOn_right hf₂ hf₁

open WithTop in
/--
lemma `divisor_sub_const_of_ne` / 引理 `divisor_sub_const_of_ne`

English:
lemma divisor_sub_const_of_ne
  given: {U : Set 𝕜} {z₀ x : 𝕜} (hx : x != z₀)
  statement: divisor (· - z₀) U x = 0
  proof: by
  by_cases hu : x in U
  · rw [divisor_apply (show MeromorphicOn (· - z₀) U from fun_sub id <| const z₀) hu,
      ← untop₀_coe 0]
    congr
    exact (meromorphicOrderAt_eq_int_iff (by fun_prop)).mpr
      ⟨(· - z₀), analyticAt_id.fun_sub analyticAt_const, by simp [sub_ne_zero_of_ne hx]⟩
  · exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu

中文:
引理 divisor_sub_const_of_ne
  条件: {U : 集合 𝕜} {z₀ x : 𝕜} (hx : x != z₀)
  结论: divisor (· - z₀) U x = 0
  证明: by
  by_cases hu : x in U
  · rw [divisor_apply (show MeromorphicOn (· - z₀) U from fun_sub id <| const z₀) hu,
      ← untop₀_coe 0]
    congr
    exact (meromorphicOrderAt_eq_int_iff (by fun_prop)).mpr
      ⟨(· - z₀), analyticAt_id.fun_sub analyticAt_const, by simp [sub_ne_zero_of_ne hx]⟩
  · exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu

Depends on / 依赖: Function, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem, MeromorphicOn, analyticAt_const, analyticAt_id, analyticAt_id.fun_sub, apply_eq_zero_of_notMem, divisor_apply, fun_prop, fun_sub, locallyFinsuppWithin, meromorphicOrderAt_eq_int_iff, sub_ne_zero_of_ne
-/
lemma divisor_sub_const_of_ne {U : Set 𝕜} {z₀ x : 𝕜} (hx : x != z₀) : divisor (· - z₀) U x = 0 := by
  by_cases hu : x in U
  · rw [divisor_apply (show MeromorphicOn (· - z₀) U from fun_sub id <| const z₀) hu,
      ← untop₀_coe 0]
    congr
    exact (meromorphicOrderAt_eq_int_iff (by fun_prop)).mpr
      ⟨(· - z₀), analyticAt_id.fun_sub analyticAt_const, by simp [sub_ne_zero_of_ne hx]⟩
  · exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu

open WithTop in
/--
lemma `divisor_sub_const_self` / 引理 `divisor_sub_const_self`

English:
lemma divisor_sub_const_self
  given: {z₀ : 𝕜} {U : Set 𝕜} (h : z₀ in U)
  statement: divisor (· - z₀) U z₀ = 1
  proof: by
  rw [divisor_apply (show MeromorphicOn (· - z₀) U from fun_sub id <| const z₀) h]; rw [← untop₀_coe 1]
  congr
  exact (meromorphicOrderAt_eq_int_iff (by fun_prop)).mpr ⟨fun _ => 1, analyticAt_const, by simp⟩

中文:
引理 divisor_sub_const_self
  条件: {z₀ : 𝕜} {U : 集合 𝕜} (h : z₀ in U)
  结论: divisor (· - z₀) U z₀ = 1
  证明: by
  rw [divisor_apply (show MeromorphicOn (· - z₀) U from fun_sub id <| const z₀) h]; rw [← untop₀_coe 1]
  congr
  exact (meromorphicOrderAt_eq_int_iff (by fun_prop)).mpr ⟨fun _ => 1, analyticAt_const, by simp⟩

Depends on / 依赖: MeromorphicOn, analyticAt_const, divisor_apply, fun_prop, fun_sub, meromorphicOrderAt_eq_int_iff
-/
lemma divisor_sub_const_self {z₀ : 𝕜} {U : Set 𝕜} (h : z₀ in U) : divisor (· - z₀) U z₀ = 1 := by
  rw [divisor_apply (show MeromorphicOn (· - z₀) U from fun_sub id <| const z₀) h]; rw [← untop₀_coe 1]
  congr
  exact (meromorphicOrderAt_eq_int_iff (by fun_prop)).mpr ⟨fun _ => 1, analyticAt_const, by simp⟩

open scoped Pointwise

/-- Divisors are invariant under translation. -/
@[to_fun divisor_fun_comp_add_const_eq_divisor]
/--
theorem `divisor_comp_add_const_eq_divisor` / 定理 `divisor_comp_add_const_eq_divisor`

English:
theorem divisor_comp_add_const_eq_divisor
  given: {c x : 𝕜} {f : 𝕜 -> E}
  proof: by
  by_cases h : ¬ MeromorphicOn f (U + {c})
  · have := meromorphicOn_comp_add_const_iff_meromorphicOn.not.2 h
    simp_all
  rw [not_not] at h
  have := meromorphicOn_comp_add_const_iff_meromorphicOn.2 h
  by_cases h₁ : ¬ x in (U + {c})
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem]
    <;> simp_all [← sub_eq_add_neg]
  rw [divisor_apply]; rw [divisor_apply]
  <;> simp_all [← sub_eq_add_neg, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]

中文:
定理 divisor_comp_add_const_eq_divisor
  条件: {c x : 𝕜} {f : 𝕜 -> E}
  证明: by
  by_cases h : ¬ MeromorphicOn f (U + {c})
  · have := meromorphicOn_comp_add_const_iff_meromorphicOn.not.2 h
    simp_all
  rw [not_not] at h
  have := meromorphicOn_comp_add_const_iff_meromorphicOn.2 h
  by_cases h₁ : ¬ x in (U + {c})
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem]
    <;> simp_all [← sub_eq_add_neg]
  rw [divisor_apply]; rw [divisor_apply]
  <;> simp_all [← sub_eq_add_neg, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]

Depends on / 依赖: Function, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem, MeromorphicOn, apply_eq_zero_of_notMem, divisor_apply, locallyFinsuppWithin, meromorphicOn_comp_add_const_iff_meromorphicOn, meromorphicOn_comp_add_const_iff_meromorphicOn.not, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt, not_not, sub_eq_add_neg
-/
theorem divisor_comp_add_const_eq_divisor {c x : 𝕜} {f : 𝕜 -> E} :
    divisor (f ∘ (· + c)) U (x - c) = divisor f (U + {c}) x := by
  by_cases h : ¬ MeromorphicOn f (U + {c})
  · have := meromorphicOn_comp_add_const_iff_meromorphicOn.not.2 h
    simp_all
  rw [not_not] at h
  have := meromorphicOn_comp_add_const_iff_meromorphicOn.2 h
  by_cases h₁ : ¬ x in (U + {c})
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem]
    <;> simp_all [← sub_eq_add_neg]
  rw [divisor_apply]; rw [divisor_apply]
  <;> simp_all [← sub_eq_add_neg, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]

/-- Divisors are invariant under translation. -/
@[to_fun divisor_fun_comp_sub_const_eq_divisor]
/--
theorem `divisor_comp_sub_const_eq_divisor` / 定理 `divisor_comp_sub_const_eq_divisor`

English:
theorem divisor_comp_sub_const_eq_divisor
  given: {c : 𝕜} {f : 𝕜 -> E}
  proof: by
  rw [sub_eq_add_neg]; rw [Set.neg_singleton]; rw [← divisor_comp_add_const_eq_divisor]
  simp_rw [← sub_eq_add_neg, sub_neg_eq_add]

中文:
定理 divisor_comp_sub_const_eq_divisor
  条件: {c : 𝕜} {f : 𝕜 -> E}
  证明: by
  rw [sub_eq_add_neg]; rw [Set.neg_singleton]; rw [← divisor_comp_add_const_eq_divisor]
  simp_rw [← sub_eq_add_neg, sub_neg_eq_add]

Depends on / 依赖: Set.neg_singleton, divisor_comp_add_const_eq_divisor, neg_singleton, simp_rw, sub_eq_add_neg, sub_neg_eq_add
-/
theorem divisor_comp_sub_const_eq_divisor {c : 𝕜} {f : 𝕜 -> E} :
    divisor (f ∘ (· - c)) U (z + c) = divisor f (U - {c}) z := by
  rw [sub_eq_add_neg]; rw [Set.neg_singleton]; rw [← divisor_comp_add_const_eq_divisor]
  simp_rw [← sub_eq_add_neg, sub_neg_eq_add]

/-- Divisors are invariant under translation, special case where the set is a ball.. -/
@[to_fun (attr := simp) divisor_ball_fun_comp_sub_const_eq_divisor_ball]
/--
theorem `divisor_ball_comp_sub_const_eq_divisor_ball` / 定理 `divisor_ball_comp_sub_const_eq_divisor_ball`

English:
theorem divisor_ball_comp_sub_const_eq_divisor_ball
  given: {c : 𝕜} {R : Real} {f : 𝕜 -> E}
  proof: by
  rw [divisor_comp_sub_const_eq_divisor]; rw [ball_sub_singleton]; rw [sub_self]

中文:
定理 divisor_ball_comp_sub_const_eq_divisor_ball
  条件: {c : 𝕜} {R : 实数} {f : 𝕜 -> E}
  证明: by
  rw [divisor_comp_sub_const_eq_divisor]; rw [ball_sub_singleton]; rw [sub_self]

Depends on / 依赖: ball_sub_singleton, divisor_comp_sub_const_eq_divisor, sub_self
-/
theorem divisor_ball_comp_sub_const_eq_divisor_ball {c : 𝕜} {R : Real} {f : 𝕜 -> E} :
    divisor (f ∘ (· - c)) (ball c R) (z + c) = divisor f (ball 0 R) z := by
  rw [divisor_comp_sub_const_eq_divisor]; rw [ball_sub_singleton]; rw [sub_self]

/-- Divisors are invariant under translation, special case where the set is a closed ball. -/
@[to_fun (attr := simp) divisor_closedBall_fun_comp_sub_const_eq_divisor_closedBall]
/--
theorem `divisor_closedBall_comp_sub_const_eq_divisor_closedBall` / 定理 `divisor_closedBall_comp_sub_const_eq_divisor_closedBall`

English:
theorem divisor_closedBall_comp_sub_const_eq_divisor_closedBall
  given: {c : 𝕜} {R : Real} {f : 𝕜 -> E}
  proof: by
  rw [divisor_comp_sub_const_eq_divisor]; rw [closedBall_sub_singleton]; rw [sub_self]

中文:
定理 divisor_closedBall_comp_sub_const_eq_divisor_closedBall
  条件: {c : 𝕜} {R : 实数} {f : 𝕜 -> E}
  证明: by
  rw [divisor_comp_sub_const_eq_divisor]; rw [closedBall_sub_singleton]; rw [sub_self]

Depends on / 依赖: closedBall_sub_singleton, divisor_comp_sub_const_eq_divisor, sub_self
-/
theorem divisor_closedBall_comp_sub_const_eq_divisor_closedBall {c : 𝕜} {R : Real} {f : 𝕜 -> E} :
    divisor (f ∘ (· - c)) (closedBall c R) (z + c) = divisor f (closedBall 0 R) z := by
  rw [divisor_comp_sub_const_eq_divisor]; rw [closedBall_sub_singleton]; rw [sub_self]

/-- Divisors are invariant under translation, special case where the set is a sphere. -/
@[to_fun (attr := simp) divisor_sphere_fun_comp_sub_const_eq_divisor_sphere]
/--
theorem `divisor_sphere_comp_sub_const_eq_divisor_sphere` / 定理 `divisor_sphere_comp_sub_const_eq_divisor_sphere`

English:
theorem divisor_sphere_comp_sub_const_eq_divisor_sphere
  given: {c : 𝕜} {R : Real} {f : 𝕜 -> E}
  proof: by
  rw [divisor_comp_sub_const_eq_divisor]; rw [sphere_sub_singleton]; rw [sub_self]

中文:
定理 divisor_sphere_comp_sub_const_eq_divisor_sphere
  条件: {c : 𝕜} {R : 实数} {f : 𝕜 -> E}
  证明: by
  rw [divisor_comp_sub_const_eq_divisor]; rw [sphere_sub_singleton]; rw [sub_self]

Depends on / 依赖: divisor_comp_sub_const_eq_divisor, sphere_sub_singleton, sub_self
-/
theorem divisor_sphere_comp_sub_const_eq_divisor_sphere {c : 𝕜} {R : Real} {f : 𝕜 -> E} :
    divisor (f ∘ (· - c)) (sphere c R) (z + c) = divisor f (sphere 0 R) z := by
  rw [divisor_comp_sub_const_eq_divisor]; rw [sphere_sub_singleton]; rw [sub_self]

end MeromorphicOn
