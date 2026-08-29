/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Algebra.Order.WithTop.Untop0

/-!
# Orders of Meromorphic Functions

This file defines the order of a meromorphic function `f` at a point `z₀`, as an element of
`ℤ ∪ {∞}`.

We characterize the order being `< 0`, or `= 0`, or `> 0`, as the convergence of the function
to infinity, resp. a nonzero constant, resp. zero.

## TODO

Uniformize API between analytic and meromorphic functions
-/

@[expose] public section

open Filter Set WithTop.LinearOrderedAddCommGroup
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {R : Type*} [NormedRing R] [NoZeroDivisors R]
  [Module R E] [IsBoundedSMul R E] [Module.IsTorsionFree R E]
  {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {f f₁ f₂ : 𝕜 -> E} {x : 𝕜}

/-!
## Order at a Point: Definition and Characterization
-/

open scoped Classical in
/--
Definition of `meromorphicOrderAt` / `meromorphicOrderAt` 的定义

English:
definition meromorphicOrderAt
  signature: (f : 𝕜 -> E) (x : 𝕜)
  body: if hf : MeromorphicAt f x then
    ((analyticOrderAt (fun z => (z - x) ^ hf.choose • f z) x).map (↑· : Nat -> Int)) - hf.choose
  else 0

@[simp]

中文:
定义 meromorphicOrderAt
  签名: (f : 𝕜 -> E) (x : 𝕜)
  定义体: if hf : MeromorphicAt f x then
    ((analyticOrderAt (fun z => (z - x) ^ hf.choose • f z) x).map (↑· : Nat -> Int)) - hf.choose
  else 0

@[simp]

Depends on / 依赖: MeromorphicAt, analyticOrderAt, hf.choose
-/
noncomputable def meromorphicOrderAt (f : 𝕜 -> E) (x : 𝕜) : WithTop Int :=
  if hf : MeromorphicAt f x then
    ((analyticOrderAt (fun z => (z - x) ^ hf.choose • f z) x).map (↑· : Nat -> Int)) - hf.choose
  else 0

@[simp]
/--
lemma `meromorphicOrderAt_of_not_meromorphicAt` / 引理 `meromorphicOrderAt_of_not_meromorphicAt`

English:
lemma meromorphicOrderAt_of_not_meromorphicAt
  given: (hf : ¬ MeromorphicAt f x)
  proof: dif_neg hf

中文:
引理 meromorphicOrderAt_of_not_meromorphicAt
  条件: (hf : ¬ MeromorphicAt f x)
  证明: dif_neg hf

Depends on / 依赖: dif_neg
-/
lemma meromorphicOrderAt_of_not_meromorphicAt (hf : ¬ MeromorphicAt f x) :
    meromorphicOrderAt f x = 0 :=
  dif_neg hf

/--
lemma `meromorphicAt_of_meromorphicOrderAt_ne_zero` / 引理 `meromorphicAt_of_meromorphicOrderAt_ne_zero`

English:
lemma meromorphicAt_of_meromorphicOrderAt_ne_zero
  given: (hf : meromorphicOrderAt f x != 0)
  proof: by
  contrapose hf
  simp [hf]

中文:
引理 meromorphicAt_of_meromorphicOrderAt_ne_zero
  条件: (hf : meromorphicOrderAt f x != 0)
  证明: by
  contrapose hf
  simp [hf]

Depends on / 依赖: contrapose
-/
lemma meromorphicAt_of_meromorphicOrderAt_ne_zero (hf : meromorphicOrderAt f x != 0) :
    MeromorphicAt f x := by
  contrapose hf
  simp [hf]

/--
lemma `meromorphicOrderAt_eq_top_iff` / 引理 `meromorphicOrderAt_eq_top_iff`

English:
lemma meromorphicOrderAt_eq_top_iff
  proof: by
  by_cases hf : MeromorphicAt f x; swap
  · simp only [hf, not_false_eq_true, meromorphicOrderAt_of_not_meromorphicAt, WithTop.zero_ne_top,
      false_iff]
    contrapose hf
    exact (MeromorphicAt.const 0 x).congr (EventuallyEq.symm hf)
  simp only [meromorphicOrderAt, hf, ↓reduceDIte, sub_eq_top_iff, ENat.map_eq_top_iff,
    WithTop.natCast_ne_top, or_false]
  by_cases h : analyticOrderAt (fun z => (z - x) ^ hf.choose • f z) x = ⊤
  · simp only [h, eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff, true_iff]
    rw [analyticOrderAt_eq_top] at h
    filter_upwards [h] with z hf hz
    rwa [smul_eq_zero_iff_right <| pow_ne_zero _ (sub_ne_zero.mpr hz)] at hf
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h
    simp only [← hm, ENat.natCast_ne_top, false_iff]
    contrapose h
    rw [analyticOrderAt_eq_top]
    rw [← hf.choose_spec.frequently_eq_iff_eventually_eq analyticAt_const]
    apply Eventually.frequently
    filter_upwards [h] with z hfz
    rw [hfz]; rw [smul_zero]

中文:
引理 meromorphicOrderAt_eq_top_iff
  证明: by
  by_cases hf : MeromorphicAt f x; swap
  · simp only [hf, not_false_eq_true, meromorphicOrderAt_of_not_meromorphicAt, WithTop.zero_ne_top,
      false_iff]
    contrapose hf
    exact (MeromorphicAt.const 0 x).congr (EventuallyEq.symm hf)
  simp only [meromorphicOrderAt, hf, ↓reduceDIte, sub_eq_top_iff, ENat.map_eq_top_iff,
    WithTop.natCast_ne_top, or_false]
  by_cases h : analyticOrderAt (fun z => (z - x) ^ hf.choose • f z) x = ⊤
  · simp only [h, eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff, true_iff]
    rw [analyticOrderAt_eq_top] at h
    filter_upwards [h] with z hf hz
    rwa [smul_eq_zero_iff_right <| pow_ne_zero _ (sub_ne_zero.mpr hz)] at hf
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h
    simp only [← hm, ENat.natCast_ne_top, false_iff]
    contrapose h
    rw [analyticOrderAt_eq_top]
    rw [← hf.choose_spec.frequently_eq_iff_eventually_eq analyticAt_const]
    apply Eventually.frequently
    filter_upwards [h] with z hfz
    rw [hfz]; rw [smul_zero]

Depends on / 依赖: ENat.map_eq_top_iff, EventuallyEq, EventuallyEq.symm, MeromorphicAt, MeromorphicAt.const, WithTop, WithTop.natCast_ne_top, WithTop.zero_ne_top, analyticOrderAt, contrapose, eventually_nhdsWithin_iff, false_iff, hf.choose, map_eq_top_iff, mem_compl_iff, mem_singleton_iff, meromorphicOrderAt, meromorphicOrderAt_of_not_meromorphicAt, natCast_ne_top, not_false_eq_true
-/
lemma meromorphicOrderAt_eq_top_iff :
    meromorphicOrderAt f x = ⊤ ↔ forallᶠ z in 𝓝[!=] x, f z = 0 := by
  by_cases hf : MeromorphicAt f x; swap
  · simp only [hf, not_false_eq_true, meromorphicOrderAt_of_not_meromorphicAt, WithTop.zero_ne_top,
      false_iff]
    contrapose hf
    exact (MeromorphicAt.const 0 x).congr (EventuallyEq.symm hf)
  simp only [meromorphicOrderAt, hf, ↓reduceDIte, sub_eq_top_iff, ENat.map_eq_top_iff,
    WithTop.natCast_ne_top, or_false]
  by_cases h : analyticOrderAt (fun z => (z - x) ^ hf.choose • f z) x = ⊤
  · simp only [h, eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff, true_iff]
    rw [analyticOrderAt_eq_top] at h
    filter_upwards [h] with z hf hz
    rwa [smul_eq_zero_iff_right <| pow_ne_zero _ (sub_ne_zero.mpr hz)] at hf
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h
    simp only [← hm, ENat.natCast_ne_top, false_iff]
    contrapose h
    rw [analyticOrderAt_eq_top]
    rw [← hf.choose_spec.frequently_eq_iff_eventually_eq analyticAt_const]
    apply Eventually.frequently
    filter_upwards [h] with z hfz
    rw [hfz]; rw [smul_zero]

/--
lemma `eventuallyConst_nhdsNE_iff_meromorphicOrderAt_sub_eq_top` / 引理 `eventuallyConst_nhdsNE_iff_meromorphicOrderAt_sub_eq_top`

English:
lemma eventuallyConst_nhdsNE_iff_meromorphicOrderAt_sub_eq_top
  proof: by
  simp only [eventuallyConst_iff_exists_eventuallyEq, meromorphicOrderAt_eq_top_iff,
    sub_eq_zero, EventuallyEq]

中文:
引理 eventuallyConst_nhdsNE_iff_meromorphicOrderAt_sub_eq_top
  证明: by
  simp only [eventuallyConst_iff_exists_eventuallyEq, meromorphicOrderAt_eq_top_iff,
    sub_eq_zero, EventuallyEq]

Depends on / 依赖: EventuallyEq, eventuallyConst_iff_exists_eventuallyEq, meromorphicOrderAt_eq_top_iff, sub_eq_zero
-/
lemma eventuallyConst_nhdsNE_iff_meromorphicOrderAt_sub_eq_top :
    EventuallyConst f (𝓝[!=] x) ↔ exists c, meromorphicOrderAt (f · - c) x = ⊤ := by
  simp only [eventuallyConst_iff_exists_eventuallyEq, meromorphicOrderAt_eq_top_iff,
    sub_eq_zero, EventuallyEq]

/--
lemma `meromorphicOrderAt_eq_int_iff` / 引理 `meromorphicOrderAt_eq_int_iff`

English:
lemma meromorphicOrderAt_eq_int_iff
  given: {n : Int} (hf : MeromorphicAt f x)
  statement: meromorphicOrderAt f x = n ↔
  proof: by
  simp only [meromorphicOrderAt, hf, ↓reduceDIte]
  by_cases h : analyticOrderAt (fun z => (z - x) ^ hf.choose • f z) x = ⊤
  · rw [h, ENat.map_top, ← WithTop.coe_natCast, top_sub,
      eq_false_intro WithTop.top_ne_coe, false_iff]
    rw [analyticOrderAt_eq_top] at h
    refine fun ⟨g, hg_an, hg_ne, hg_eq⟩ => hg_ne ?_
    apply EventuallyEq.eq_of_nhds
    rw [EventuallyEq]; rw [← AnalyticAt.frequently_eq_iff_eventually_eq hg_an analyticAt_const]
    apply Eventually.frequently
    rw [eventually_nhdsWithin_iff] at hg_eq ⊢
    filter_upwards [h, hg_eq] with z hfz hfz_eq hz
    rwa [hfz_eq hz, ← mul_smul, smul_eq_zero_iff_right] at hfz
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hz)) (zpow_ne_zero _ (sub_ne_zero.mpr hz))
  · obtain ⟨m, h⟩ := ENat.ne_top_iff_exists.mp h
    rw [← h]; rw [ENat.map_natCast]; rw [← WithTop.coe_natCast]; rw [← coe_sub]; rw [WithTop.coe_inj]
    obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := hf.choose_spec.analyticOrderAt_eq_natCast.mp h.symm
    replace hg_eq : forallᶠ (z : 𝕜) in 𝓝[!=] x, f z = (z - x) ^ (↑m - ↑hf.choose : Int) • g z := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [hg_eq] with z hg_eq hz
      rwa [← smul_right_inj <| zpow_ne_zero _ (sub_ne_zero.mpr hz), ← mul_smul,
        ← zpow_add₀ (sub_ne_zero.mpr hz), ← add_sub_assoc, add_sub_cancel_left, zpow_natCast,
        zpow_natCast]
    exact ⟨fun h => ⟨g, hg_an, hg_ne, h ▸ hg_eq⟩,
      AnalyticAt.unique_eventuallyEq_zpow_smul_nonzero ⟨g, hg_an, hg_ne, hg_eq⟩⟩

中文:
引理 meromorphicOrderAt_eq_int_iff
  条件: {n : 整数} (hf : MeromorphicAt f x)
  结论: meromorphicOrderAt f x = n ↔
  证明: by
  simp only [meromorphicOrderAt, hf, ↓reduceDIte]
  by_cases h : analyticOrderAt (fun z => (z - x) ^ hf.choose • f z) x = ⊤
  · rw [h, ENat.map_top, ← WithTop.coe_natCast, top_sub,
      eq_false_intro WithTop.top_ne_coe, false_iff]
    rw [analyticOrderAt_eq_top] at h
    refine fun ⟨g, hg_an, hg_ne, hg_eq⟩ => hg_ne ?_
    apply EventuallyEq.eq_of_nhds
    rw [EventuallyEq]; rw [← AnalyticAt.frequently_eq_iff_eventually_eq hg_an analyticAt_const]
    apply Eventually.frequently
    rw [eventually_nhdsWithin_iff] at hg_eq ⊢
    filter_upwards [h, hg_eq] with z hfz hfz_eq hz
    rwa [hfz_eq hz, ← mul_smul, smul_eq_zero_iff_right] at hfz
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hz)) (zpow_ne_zero _ (sub_ne_zero.mpr hz))
  · obtain ⟨m, h⟩ := ENat.ne_top_iff_exists.mp h
    rw [← h]; rw [ENat.map_natCast]; rw [← WithTop.coe_natCast]; rw [← coe_sub]; rw [WithTop.coe_inj]
    obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := hf.choose_spec.analyticOrderAt_eq_natCast.mp h.symm
    replace hg_eq : forallᶠ (z : 𝕜) in 𝓝[!=] x, f z = (z - x) ^ (↑m - ↑hf.choose : Int) • g z := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [hg_eq] with z hg_eq hz
      rwa [← smul_right_inj <| zpow_ne_zero _ (sub_ne_zero.mpr hz), ← mul_smul,
        ← zpow_add₀ (sub_ne_zero.mpr hz), ← add_sub_assoc, add_sub_cancel_left, zpow_natCast,
        zpow_natCast]
    exact ⟨fun h => ⟨g, hg_an, hg_ne, h ▸ hg_eq⟩,
      AnalyticAt.unique_eventuallyEq_zpow_smul_nonzero ⟨g, hg_an, hg_ne, hg_eq⟩⟩

Depends on / 依赖: AnalyticAt, AnalyticAt.frequently_eq_iff_eventually_eq, ENat.map_top, Eventually, Eventually.frequently, EventuallyEq, EventuallyEq.eq_of_nhds, WithTop, WithTop.coe_natCast, WithTop.top_ne_coe, analyticAt_const, analyticOrderAt, analyticOrderAt_eq_top, coe_natCast, eq_false_intro, eq_of_nhds, eventually_nhdsWithin_iff, false_iff, frequently, frequently_eq_iff_eventually_eq
-/
lemma meromorphicOrderAt_eq_int_iff {n : Int} (hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔
    exists g : 𝕜 -> E, AnalyticAt 𝕜 g x ∧ g x != 0 ∧ forallᶠ z in 𝓝[!=] x, f z = (z - x) ^ n • g z := by
  simp only [meromorphicOrderAt, hf, ↓reduceDIte]
  by_cases h : analyticOrderAt (fun z => (z - x) ^ hf.choose • f z) x = ⊤
  · rw [h, ENat.map_top, ← WithTop.coe_natCast, top_sub,
      eq_false_intro WithTop.top_ne_coe, false_iff]
    rw [analyticOrderAt_eq_top] at h
    refine fun ⟨g, hg_an, hg_ne, hg_eq⟩ => hg_ne ?_
    apply EventuallyEq.eq_of_nhds
    rw [EventuallyEq]; rw [← AnalyticAt.frequently_eq_iff_eventually_eq hg_an analyticAt_const]
    apply Eventually.frequently
    rw [eventually_nhdsWithin_iff] at hg_eq ⊢
    filter_upwards [h, hg_eq] with z hfz hfz_eq hz
    rwa [hfz_eq hz, ← mul_smul, smul_eq_zero_iff_right] at hfz
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hz)) (zpow_ne_zero _ (sub_ne_zero.mpr hz))
  · obtain ⟨m, h⟩ := ENat.ne_top_iff_exists.mp h
    rw [← h]; rw [ENat.map_natCast]; rw [← WithTop.coe_natCast]; rw [← coe_sub]; rw [WithTop.coe_inj]
    obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := hf.choose_spec.analyticOrderAt_eq_natCast.mp h.symm
    replace hg_eq : forallᶠ (z : 𝕜) in 𝓝[!=] x, f z = (z - x) ^ (↑m - ↑hf.choose : Int) • g z := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [hg_eq] with z hg_eq hz
      rwa [← smul_right_inj <| zpow_ne_zero _ (sub_ne_zero.mpr hz), ← mul_smul,
        ← zpow_add₀ (sub_ne_zero.mpr hz), ← add_sub_assoc, add_sub_cancel_left, zpow_natCast,
        zpow_natCast]
    exact ⟨fun h => ⟨g, hg_an, hg_ne, h ▸ hg_eq⟩,
      AnalyticAt.unique_eventuallyEq_zpow_smul_nonzero ⟨g, hg_an, hg_ne, hg_eq⟩⟩

/--
theorem `meromorphicOrderAt_ne_top_iff` / 定理 `meromorphicOrderAt_ne_top_iff`

English:
theorem meromorphicOrderAt_ne_top_iff
  given: {f : 𝕜 -> E} {z₀ : 𝕜} (hf : MeromorphicAt f z₀)
  proof: ⟨fun h => (meromorphicOrderAt_eq_int_iff hf).1 (WithTop.coe_untop₀_of_ne_top h).symm,
    fun h => Option.ne_none_iff_exists'.2
      ⟨(meromorphicOrderAt f z₀).untopD 0, (meromorphicOrderAt_eq_int_iff hf).2 h⟩⟩

中文:
定理 meromorphicOrderAt_ne_top_iff
  条件: {f : 𝕜 -> E} {z₀ : 𝕜} (hf : MeromorphicAt f z₀)
  证明: ⟨fun h => (meromorphicOrderAt_eq_int_iff hf).1 (WithTop.coe_untop₀_of_ne_top h).symm,
    fun h => Option.ne_none_iff_exists'.2
      ⟨(meromorphicOrderAt f z₀).untopD 0, (meromorphicOrderAt_eq_int_iff hf).2 h⟩⟩

Depends on / 依赖: Option.ne_none_iff_exists, WithTop, WithTop.coe_untop, meromorphicOrderAt, meromorphicOrderAt_eq_int_iff, ne_none_iff_exists, untopD
-/
theorem meromorphicOrderAt_ne_top_iff {f : 𝕜 -> E} {z₀ : 𝕜} (hf : MeromorphicAt f z₀) :
    meromorphicOrderAt f z₀ != ⊤ ↔ exists (g : 𝕜 -> E), AnalyticAt 𝕜 g z₀ ∧ g z₀ != 0 ∧
      f =ᶠ[𝓝[!=] z₀] fun z => (z - z₀) ^ ((meromorphicOrderAt f z₀).untop₀) • g z :=
  ⟨fun h => (meromorphicOrderAt_eq_int_iff hf).1 (WithTop.coe_untop₀_of_ne_top h).symm,
    fun h => Option.ne_none_iff_exists'.2
      ⟨(meromorphicOrderAt f z₀).untopD 0, (meromorphicOrderAt_eq_int_iff hf).2 h⟩⟩

/--
theorem `meromorphicOrderAt_ne_top_iff_eventually_ne_zero` / 定理 `meromorphicOrderAt_ne_top_iff_eventually_ne_zero`

English:
theorem meromorphicOrderAt_ne_top_iff_eventually_ne_zero
  given: {f : 𝕜 -> E} (hf : MeromorphicAt f x)
  proof: by
  constructor
  · intro h
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h
    filter_upwards [h₃g, self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      ((h₁g.continuousAt.ne_iff_eventually_ne continuousAt_const).mp h₂g)]
    simp_all [zpow_ne_zero, sub_ne_zero]
  · simp_all [meromorphicOrderAt_eq_top_iff, Eventually.frequently]

中文:
定理 meromorphicOrderAt_ne_top_iff_eventually_ne_zero
  条件: {f : 𝕜 -> E} (hf : MeromorphicAt f x)
  证明: by
  constructor
  · intro h
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h
    filter_upwards [h₃g, self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      ((h₁g.continuousAt.ne_iff_eventually_ne continuousAt_const).mp h₂g)]
    simp_all [zpow_ne_zero, sub_ne_zero]
  · simp_all [meromorphicOrderAt_eq_top_iff, Eventually.frequently]

Depends on / 依赖: Eventually, Eventually.frequently, continuousAt, continuousAt_const, eventually_nhdsWithin_of_eventually_nhds, filter_upwards, frequently, g.continuousAt.ne_iff_eventually_ne, meromorphicOrderAt_eq_top_iff, meromorphicOrderAt_ne_top_iff, ne_iff_eventually_ne, self_mem_nhdsWithin, sub_ne_zero, zpow_ne_zero
-/
theorem meromorphicOrderAt_ne_top_iff_eventually_ne_zero {f : 𝕜 -> E} (hf : MeromorphicAt f x) :
    meromorphicOrderAt f x != ⊤ ↔ forallᶠ x in 𝓝[!=] x, f x != 0 := by
  constructor
  · intro h
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h
    filter_upwards [h₃g, self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      ((h₁g.continuousAt.ne_iff_eventually_ne continuousAt_const).mp h₂g)]
    simp_all [zpow_ne_zero, sub_ne_zero]
  · simp_all [meromorphicOrderAt_eq_top_iff, Eventually.frequently]

/--
theorem `MeromorphicOn.eventually_codiscreteWithin_apply_ne_zero` / 定理 `MeromorphicOn.eventually_codiscreteWithin_apply_ne_zero`

English:
theorem MeromorphicOn.eventually_codiscreteWithin_apply_ne_zero
  statement: {U : Set 𝕜} {f : 𝕜 -> E}
  proof: by
  simp_rw [eventually_iff, mem_codiscreteWithin, disjoint_principal_right]
  intro x hx
  filter_upwards [(meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf x hx)).1 (h'f x hx)]
    with y hy
  simp [hy]

中文:
定理 MeromorphicOn.eventually_codiscreteWithin_apply_ne_zero
  结论: {U : 集合 𝕜} {f : 𝕜 -> E}
  证明: by
  simp_rw [eventually_iff, mem_codiscreteWithin, disjoint_principal_right]
  intro x hx
  filter_upwards [(meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf x hx)).1 (h'f x hx)]
    with y hy
  simp [hy]

Depends on / 依赖: disjoint_principal_right, eventually_iff, filter_upwards, mem_codiscreteWithin, meromorphicOrderAt_ne_top_iff_eventually_ne_zero, simp_rw
-/
theorem MeromorphicOn.eventually_codiscreteWithin_apply_ne_zero {U : Set 𝕜} {f : 𝕜 -> E}
    (hf : MeromorphicOn f U) (h'f : forall x in U, meromorphicOrderAt f x != ⊤) :
    forallᶠ x in codiscreteWithin U, f x != 0 := by
  simp_rw [eventually_iff, mem_codiscreteWithin, disjoint_principal_right]
  intro x hx
  filter_upwards [(meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf x hx)).1 (h'f x hx)]
    with y hy
  simp [hy]

/--
lemma `tendsto_cobounded_of_meromorphicOrderAt_neg` / 引理 `tendsto_cobounded_of_meromorphicOrderAt_neg`

English:
lemma tendsto_cobounded_of_meromorphicOrderAt_neg
  given: (ho : meromorphicOrderAt f x < 0)
  proof: by
  have hf : MeromorphicAt f x := meromorphicAt_of_meromorphicOrderAt_ne_zero ho.ne
  simp only [← tendsto_norm_atTop_iff_cobounded]
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp ho.ne_top
  have m_neg : m < 0 := by simpa [← hm] using ho
  rcases (meromorphicOrderAt_eq_int_iff hf).1 hm.symm with ⟨g, g_an, gx, hg⟩
  have A : Tendsto (fun z => ‖(z - x) ^ m • g z‖) (𝓝[!=] x) atTop := by
    simp only [norm_smul]
    apply Filter.Tendsto.atTop_mul_pos (C := ‖g x‖) (by simp [gx]) _
      g_an.continuousAt.continuousWithinAt.tendsto.norm
    have : Tendsto (fun z => z - x) (𝓝[!=] x) (𝓝[!=] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : ContinuousWithinAt (fun z => z - x) {x}ᶜ x := by fun_prop
        simpa using this.tendsto
      · filter_upwards [self_mem_nhdsWithin] with y hy
        simpa [sub_eq_zero] using hy
    exact (tendsto_norm_cobounded_atTop.comp (tendsto_zpow_nhdsNE_zero_cobounded m_neg)).comp this
  apply A.congr'
  filter_upwards [hg] with z hz using by simp [hz]

中文:
引理 tendsto_cobounded_of_meromorphicOrderAt_neg
  条件: (ho : meromorphicOrderAt f x < 0)
  证明: by
  have hf : MeromorphicAt f x := meromorphicAt_of_meromorphicOrderAt_ne_zero ho.ne
  simp only [← tendsto_norm_atTop_iff_cobounded]
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp ho.ne_top
  have m_neg : m < 0 := by simpa [← hm] using ho
  rcases (meromorphicOrderAt_eq_int_iff hf).1 hm.symm with ⟨g, g_an, gx, hg⟩
  have A : Tendsto (fun z => ‖(z - x) ^ m • g z‖) (𝓝[!=] x) atTop := by
    simp only [norm_smul]
    apply Filter.Tendsto.atTop_mul_pos (C := ‖g x‖) (by simp [gx]) _
      g_an.continuousAt.continuousWithinAt.tendsto.norm
    have : Tendsto (fun z => z - x) (𝓝[!=] x) (𝓝[!=] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : ContinuousWithinAt (fun z => z - x) {x}ᶜ x := by fun_prop
        simpa using this.tendsto
      · filter_upwards [self_mem_nhdsWithin] with y hy
        simpa [sub_eq_zero] using hy
    exact (tendsto_norm_cobounded_atTop.comp (tendsto_zpow_nhdsNE_zero_cobounded m_neg)).comp this
  apply A.congr'
  filter_upwards [hg] with z hz using by simp [hz]

Depends on / 依赖: Filter, Filter.Tendsto.atTop_mul_pos, IsRCLikeNormedField, MeromorphicAt, RCLike, Tendsto, WithTop, WithTop.ne_top_iff_exists.mp, atTop_mul_pos, continuousAt, continuousWithi, g_an, g_an.continuousAt.continuousWithi, hm.symm, ho.ne, ho.ne_top, m_neg, meromorphicAt_of_meromorphicOrderAt_ne_zero, meromorphicOrderAt_eq_int_iff, ne_top
-/
lemma tendsto_cobounded_of_meromorphicOrderAt_neg (ho : meromorphicOrderAt f x < 0) :
    Tendsto f (𝓝[!=] x) (Bornology.cobounded E) := by
  have hf : MeromorphicAt f x := meromorphicAt_of_meromorphicOrderAt_ne_zero ho.ne
  simp only [← tendsto_norm_atTop_iff_cobounded]
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp ho.ne_top
  have m_neg : m < 0 := by simpa [← hm] using ho
  rcases (meromorphicOrderAt_eq_int_iff hf).1 hm.symm with ⟨g, g_an, gx, hg⟩
  have A : Tendsto (fun z => ‖(z - x) ^ m • g z‖) (𝓝[!=] x) atTop := by
    simp only [norm_smul]
    apply Filter.Tendsto.atTop_mul_pos (C := ‖g x‖) (by simp [gx]) _
      g_an.continuousAt.continuousWithinAt.tendsto.norm
    have : Tendsto (fun z => z - x) (𝓝[!=] x) (𝓝[!=] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : ContinuousWithinAt (fun z => z - x) {x}ᶜ x := by fun_prop
        simpa using this.tendsto
      · filter_upwards [self_mem_nhdsWithin] with y hy
        simpa [sub_eq_zero] using hy
    exact (tendsto_norm_cobounded_atTop.comp (tendsto_zpow_nhdsNE_zero_cobounded m_neg)).comp this
  apply A.congr'
  filter_upwards [hg] with z hz using by simp [hz]

/--
lemma `tendsto_ne_zero_of_meromorphicOrderAt_eq_zero` / 引理 `tendsto_ne_zero_of_meromorphicOrderAt_eq_zero`

English:
lemma tendsto_ne_zero_of_meromorphicOrderAt_eq_zero
  proof: by
  rcases (meromorphicOrderAt_eq_int_iff hf).1 ho with ⟨g, g_an, gx, hg⟩
  refine ⟨g x, gx, ?_⟩
  apply g_an.continuousAt.continuousWithinAt.tendsto.congr'
  filter_upwards [hg] with y hy using by simp [hy]

中文:
引理 tendsto_ne_zero_of_meromorphicOrderAt_eq_zero
  证明: by
  rcases (meromorphicOrderAt_eq_int_iff hf).1 ho with ⟨g, g_an, gx, hg⟩
  refine ⟨g x, gx, ?_⟩
  apply g_an.continuousAt.continuousWithinAt.tendsto.congr'
  filter_upwards [hg] with y hy using by simp [hy]

Depends on / 依赖: continuousAt, continuousWithinAt, filter_upwards, g_an, g_an.continuousAt.continuousWithinAt.tendsto.congr, meromorphicOrderAt_eq_int_iff, tendsto
-/
lemma tendsto_ne_zero_of_meromorphicOrderAt_eq_zero
    (hf : MeromorphicAt f x) (ho : meromorphicOrderAt f x = 0) :
    exists c != 0, Tendsto f (𝓝[!=] x) (𝓝 c) := by
  rcases (meromorphicOrderAt_eq_int_iff hf).1 ho with ⟨g, g_an, gx, hg⟩
  refine ⟨g x, gx, ?_⟩
  apply g_an.continuousAt.continuousWithinAt.tendsto.congr'
  filter_upwards [hg] with y hy using by simp [hy]

/--
lemma `tendsto_zero_of_meromorphicOrderAt_pos` / 引理 `tendsto_zero_of_meromorphicOrderAt_pos`

English:
lemma tendsto_zero_of_meromorphicOrderAt_pos
  given: (ho : 0 < meromorphicOrderAt f x)
  proof: by
  have hf : MeromorphicAt f x := meromorphicAt_of_meromorphicOrderAt_ne_zero ho.ne'
  cases h'o : meromorphicOrderAt f x with
  | top =>
    apply tendsto_const_nhds.congr'
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h'o] with y hy using hy.symm
  | coe n =>
    rcases (meromorphicOrderAt_eq_int_iff hf).1 h'o with ⟨g, g_an, gx, hg⟩
    lift n to Nat using by simpa [h'o] using ho.le
    have : (0 : E) = (x - x) ^ n • g x := by
      have : 0 < n := by simpa [h'o] using ho
      simp [zero_pow_eq_zero.2 this.ne']
    rw [this]
    have : ContinuousAt (fun z => (z - x) ^ n • g z) x := by fun_prop
    apply this.continuousWithinAt.tendsto.congr'
    filter_upwards [hg] with y hy using by simp [hy]

中文:
引理 tendsto_zero_of_meromorphicOrderAt_pos
  条件: (ho : 0 < meromorphicOrderAt f x)
  证明: by
  have hf : MeromorphicAt f x := meromorphicAt_of_meromorphicOrderAt_ne_zero ho.ne'
  cases h'o : meromorphicOrderAt f x with
  | top =>
    apply tendsto_const_nhds.congr'
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h'o] with y hy using hy.symm
  | coe n =>
    rcases (meromorphicOrderAt_eq_int_iff hf).1 h'o with ⟨g, g_an, gx, hg⟩
    lift n to Nat using by simpa [h'o] using ho.le
    have : (0 : E) = (x - x) ^ n • g x := by
      have : 0 < n := by simpa [h'o] using ho
      simp [zero_pow_eq_zero.2 this.ne']
    rw [this]
    have : ContinuousAt (fun z => (z - x) ^ n • g z) x := by fun_prop
    apply this.continuousWithinAt.tendsto.congr'
    filter_upwards [hg] with y hy using by simp [hy]

Depends on / 依赖: MeromorphicAt, filter_upwards, g_an, ho.le, ho.ne, hy.symm, meromorphicAt_of_meromorphicOrderAt_ne_zero, meromorphicOrderAt, meromorphicOrderAt_eq_int_iff, meromorphicOrderAt_eq_top_iff, tendsto_const_nhds, tendsto_const_nhds.congr, this.ne, zero_pow_eq_zero
-/
lemma tendsto_zero_of_meromorphicOrderAt_pos (ho : 0 < meromorphicOrderAt f x) :
    Tendsto f (𝓝[!=] x) (𝓝 0) := by
  have hf : MeromorphicAt f x := meromorphicAt_of_meromorphicOrderAt_ne_zero ho.ne'
  cases h'o : meromorphicOrderAt f x with
  | top =>
    apply tendsto_const_nhds.congr'
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h'o] with y hy using hy.symm
  | coe n =>
    rcases (meromorphicOrderAt_eq_int_iff hf).1 h'o with ⟨g, g_an, gx, hg⟩
    lift n to Nat using by simpa [h'o] using ho.le
    have : (0 : E) = (x - x) ^ n • g x := by
      have : 0 < n := by simpa [h'o] using ho
      simp [zero_pow_eq_zero.2 this.ne']
    rw [this]
    have : ContinuousAt (fun z => (z - x) ^ n • g z) x := by fun_prop
    apply this.continuousWithinAt.tendsto.congr'
    filter_upwards [hg] with y hy using by simp [hy]

/--
lemma `tendsto_nhds_of_meromorphicOrderAt_nonneg` / 引理 `tendsto_nhds_of_meromorphicOrderAt_nonneg`

English:
lemma tendsto_nhds_of_meromorphicOrderAt_nonneg
  proof: by
  rcases ho.eq_or_lt with ho | ho
  · rcases tendsto_ne_zero_of_meromorphicOrderAt_eq_zero hf ho.symm with ⟨c, -, hc⟩
    exact ⟨c, hc⟩
  · exact ⟨0, tendsto_zero_of_meromorphicOrderAt_pos ho⟩

中文:
引理 tendsto_nhds_of_meromorphicOrderAt_nonneg
  证明: by
  rcases ho.eq_or_lt with ho | ho
  · rcases tendsto_ne_zero_of_meromorphicOrderAt_eq_zero hf ho.symm with ⟨c, -, hc⟩
    exact ⟨c, hc⟩
  · exact ⟨0, tendsto_zero_of_meromorphicOrderAt_pos ho⟩

Depends on / 依赖: eq_or_lt, ho.eq_or_lt, ho.symm, tendsto_ne_zero_of_meromorphicOrderAt_eq_zero, tendsto_zero_of_meromorphicOrderAt_pos
-/
lemma tendsto_nhds_of_meromorphicOrderAt_nonneg
    (hf : MeromorphicAt f x) (ho : 0 <= meromorphicOrderAt f x) :
    exists c, Tendsto f (𝓝[!=] x) (𝓝 c) := by
  rcases ho.eq_or_lt with ho | ho
  · rcases tendsto_ne_zero_of_meromorphicOrderAt_eq_zero hf ho.symm with ⟨c, -, hc⟩
    exact ⟨c, hc⟩
  · exact ⟨0, tendsto_zero_of_meromorphicOrderAt_pos ho⟩

/--
lemma `tendsto_cobounded_iff_meromorphicOrderAt_neg` / 引理 `tendsto_cobounded_iff_meromorphicOrderAt_neg`

English:
lemma tendsto_cobounded_iff_meromorphicOrderAt_neg
  given: (hf : MeromorphicAt f x)
  proof: by
  rcases lt_or_ge (meromorphicOrderAt f x) 0 with ho | ho
  · simp [ho, tendsto_cobounded_of_meromorphicOrderAt_neg]
  · simp only [lt_iff_not_ge, ho, not_true_eq_false, iff_false, ← tendsto_norm_atTop_iff_cobounded]
    obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hf ho
    exact not_tendsto_atTop_of_tendsto_nhds hc.norm

中文:
引理 tendsto_cobounded_iff_meromorphicOrderAt_neg
  条件: (hf : MeromorphicAt f x)
  证明: by
  rcases lt_or_ge (meromorphicOrderAt f x) 0 with ho | ho
  · simp [ho, tendsto_cobounded_of_meromorphicOrderAt_neg]
  · simp only [lt_iff_not_ge, ho, not_true_eq_false, iff_false, ← tendsto_norm_atTop_iff_cobounded]
    obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hf ho
    exact not_tendsto_atTop_of_tendsto_nhds hc.norm

Depends on / 依赖: hc.norm, iff_false, lt_iff_not_ge, lt_or_ge, meromorphicOrderAt, not_tendsto_atTop_of_tendsto_nhds, not_true_eq_false, tendsto_cobounded_of_meromorphicOrderAt_neg, tendsto_nhds_of_meromorphicOrderAt_nonneg, tendsto_norm_atTop_iff_cobounded
-/
lemma tendsto_cobounded_iff_meromorphicOrderAt_neg (hf : MeromorphicAt f x) :
    Tendsto f (𝓝[!=] x) (Bornology.cobounded E) ↔ meromorphicOrderAt f x < 0 := by
  rcases lt_or_ge (meromorphicOrderAt f x) 0 with ho | ho
  · simp [ho, tendsto_cobounded_of_meromorphicOrderAt_neg]
  · simp only [lt_iff_not_ge, ho, not_true_eq_false, iff_false, ← tendsto_norm_atTop_iff_cobounded]
    obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hf ho
    exact not_tendsto_atTop_of_tendsto_nhds hc.norm

/--
lemma `tendsto_nhds_iff_meromorphicOrderAt_nonneg` / 引理 `tendsto_nhds_iff_meromorphicOrderAt_nonneg`

English:
lemma tendsto_nhds_iff_meromorphicOrderAt_nonneg
  given: (hf : MeromorphicAt f x)
  proof: by
  rcases lt_or_ge (meromorphicOrderAt f x) 0 with ho | ho
  · simp only [← not_lt, ho, not_true_eq_false, iff_false, not_exists]
    intro c hc
    apply not_tendsto_atTop_of_tendsto_nhds hc.norm
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg ho
  · simp [ho, tendsto_nhds_of_meromorphicOrderAt_nonneg hf ho]

中文:
引理 tendsto_nhds_iff_meromorphicOrderAt_nonneg
  条件: (hf : MeromorphicAt f x)
  证明: by
  rcases lt_or_ge (meromorphicOrderAt f x) 0 with ho | ho
  · simp only [← not_lt, ho, not_true_eq_false, iff_false, not_exists]
    intro c hc
    apply not_tendsto_atTop_of_tendsto_nhds hc.norm
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg ho
  · simp [ho, tendsto_nhds_of_meromorphicOrderAt_nonneg hf ho]

Depends on / 依赖: hc.norm, iff_false, lt_or_ge, meromorphicOrderAt, not_exists, not_lt, not_tendsto_atTop_of_tendsto_nhds, not_true_eq_false, tendsto_cobounded_of_meromorphicOrderAt_neg, tendsto_nhds_of_meromorphicOrderAt_nonneg, tendsto_norm_atTop_iff_cobounded
-/
lemma tendsto_nhds_iff_meromorphicOrderAt_nonneg (hf : MeromorphicAt f x) :
    (exists c, Tendsto f (𝓝[!=] x) (𝓝 c)) ↔ 0 <= meromorphicOrderAt f x := by
  rcases lt_or_ge (meromorphicOrderAt f x) 0 with ho | ho
  · simp only [← not_lt, ho, not_true_eq_false, iff_false, not_exists]
    intro c hc
    apply not_tendsto_atTop_of_tendsto_nhds hc.norm
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg ho
  · simp [ho, tendsto_nhds_of_meromorphicOrderAt_nonneg hf ho]

/--
lemma `tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero` / 引理 `tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero`

English:
lemma tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero
  given: (hf : MeromorphicAt f x)
  proof: by
  rcases eq_or_ne (meromorphicOrderAt f x) 0 with ho | ho
  · simp [ho, tendsto_ne_zero_of_meromorphicOrderAt_eq_zero hf ho]
  simp only [ne_eq, ho, iff_false, not_exists, not_and]
  intro c c_ne hc
  rcases ho.lt_or_gt with ho | ho
  · apply not_tendsto_atTop_of_tendsto_nhds hc.norm
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg ho
  · apply c_ne
    exact tendsto_nhds_unique hc (tendsto_zero_of_meromorphicOrderAt_pos ho)

中文:
引理 tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero
  条件: (hf : MeromorphicAt f x)
  证明: by
  rcases eq_or_ne (meromorphicOrderAt f x) 0 with ho | ho
  · simp [ho, tendsto_ne_zero_of_meromorphicOrderAt_eq_zero hf ho]
  simp only [ne_eq, ho, iff_false, not_exists, not_and]
  intro c c_ne hc
  rcases ho.lt_or_gt with ho | ho
  · apply not_tendsto_atTop_of_tendsto_nhds hc.norm
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg ho
  · apply c_ne
    exact tendsto_nhds_unique hc (tendsto_zero_of_meromorphicOrderAt_pos ho)

Depends on / 依赖: c_ne, eq_or_ne, hc.norm, ho.lt_or_gt, iff_false, lt_or_gt, meromorphicOrderAt, ne_eq, not_and, not_exists, not_tendsto_atTop_of_tendsto_nhds, tendsto_cobounded_of_meromorphicOrderAt_neg, tendsto_ne_zero_of_meromorphicOrderAt_eq_zero, tendsto_nhds_unique, tendsto_norm_atTop_iff_cobounded, tendsto_zero_of_meromorphicOrderAt_pos
-/
lemma tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero (hf : MeromorphicAt f x) :
    (exists c != 0, Tendsto f (𝓝[!=] x) (𝓝 c)) ↔ meromorphicOrderAt f x = 0 := by
  rcases eq_or_ne (meromorphicOrderAt f x) 0 with ho | ho
  · simp [ho, tendsto_ne_zero_of_meromorphicOrderAt_eq_zero hf ho]
  simp only [ne_eq, ho, iff_false, not_exists, not_and]
  intro c c_ne hc
  rcases ho.lt_or_gt with ho | ho
  · apply not_tendsto_atTop_of_tendsto_nhds hc.norm
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg ho
  · apply c_ne
    exact tendsto_nhds_unique hc (tendsto_zero_of_meromorphicOrderAt_pos ho)

/--
lemma `tendsto_zero_iff_meromorphicOrderAt_pos` / 引理 `tendsto_zero_iff_meromorphicOrderAt_pos`

English:
lemma tendsto_zero_iff_meromorphicOrderAt_pos
  given: (hf : MeromorphicAt f x)
  proof: by
  rcases lt_or_ge 0 (meromorphicOrderAt f x) with ho | ho
  · simp [ho, tendsto_zero_of_meromorphicOrderAt_pos ho]
  simp only [← not_le, ho, not_true_eq_false, iff_false]
  intro hc
  rcases ho.eq_or_lt with ho | ho
  · obtain ⟨c, c_ne, h'c⟩ := tendsto_ne_zero_of_meromorphicOrderAt_eq_zero hf ho
    apply c_ne
    exact tendsto_nhds_unique h'c hc
  · apply not_tendsto_atTop_of_tendsto_nhds hc.norm
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg ho

中文:
引理 tendsto_zero_iff_meromorphicOrderAt_pos
  条件: (hf : MeromorphicAt f x)
  证明: by
  rcases lt_or_ge 0 (meromorphicOrderAt f x) with ho | ho
  · simp [ho, tendsto_zero_of_meromorphicOrderAt_pos ho]
  simp only [← not_le, ho, not_true_eq_false, iff_false]
  intro hc
  rcases ho.eq_or_lt with ho | ho
  · obtain ⟨c, c_ne, h'c⟩ := tendsto_ne_zero_of_meromorphicOrderAt_eq_zero hf ho
    apply c_ne
    exact tendsto_nhds_unique h'c hc
  · apply not_tendsto_atTop_of_tendsto_nhds hc.norm
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg ho

Depends on / 依赖: c_ne, eq_or_lt, hc.norm, ho.eq_or_lt, iff_false, lt_or_ge, meromorphicOrderAt, not_le, not_tendsto_atTop_of_tendsto_nhds, not_true_eq_false, tendsto_cobounded_of_meromorphicOrderAt_neg, tendsto_ne_zero_of_meromorphicOrderAt_eq_zero, tendsto_nhds_unique, tendsto_norm_atTop_iff_cobounded, tendsto_zero_of_meromorphicOrderAt_pos
-/
lemma tendsto_zero_iff_meromorphicOrderAt_pos (hf : MeromorphicAt f x) :
    (Tendsto f (𝓝[!=] x) (𝓝 0)) ↔ 0 < meromorphicOrderAt f x := by
  rcases lt_or_ge 0 (meromorphicOrderAt f x) with ho | ho
  · simp [ho, tendsto_zero_of_meromorphicOrderAt_pos ho]
  simp only [← not_le, ho, not_true_eq_false, iff_false]
  intro hc
  rcases ho.eq_or_lt with ho | ho
  · obtain ⟨c, c_ne, h'c⟩ := tendsto_ne_zero_of_meromorphicOrderAt_eq_zero hf ho
    apply c_ne
    exact tendsto_nhds_unique h'c hc
  · apply not_tendsto_atTop_of_tendsto_nhds hc.norm
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg ho

/--
theorem `meromorphicOrderAt_congr` / 定理 `meromorphicOrderAt_congr`

English:
theorem meromorphicOrderAt_congr
  given: (hf₁₂ : f₁ =ᶠ[𝓝[!=] x] f₂)
  proof: by
  by_cases hf₁ : MeromorphicAt f₁ x; swap
  · have : ¬ MeromorphicAt f₂ x := by
      contrapose hf₁
      exact hf₁.congr hf₁₂.symm
    simp [hf₁, this]
  rw [eq_comm]
  cases h₁f₁ : meromorphicOrderAt f₁ x with
  | top =>
    rw [meromorphicOrderAt_eq_top_iff] at h₁f₁ ⊢
    filter_upwards [hf₁₂, h₁f₁] using by grind
  | coe n =>
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 h₁f₁
    rw [meromorphicOrderAt_eq_int_iff (hf₁.congr hf₁₂)]
    use g, h₁g, h₂g
    filter_upwards [hf₁₂, h₃g] using by grind

中文:
定理 meromorphicOrderAt_congr
  条件: (hf₁₂ : f₁ =ᶠ[𝓝[!=] x] f₂)
  证明: by
  by_cases hf₁ : MeromorphicAt f₁ x; swap
  · have : ¬ MeromorphicAt f₂ x := by
      contrapose hf₁
      exact hf₁.congr hf₁₂.symm
    simp [hf₁, this]
  rw [eq_comm]
  cases h₁f₁ : meromorphicOrderAt f₁ x with
  | top =>
    rw [meromorphicOrderAt_eq_top_iff] at h₁f₁ ⊢
    filter_upwards [hf₁₂, h₁f₁] using by grind
  | coe n =>
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 h₁f₁
    rw [meromorphicOrderAt_eq_int_iff (hf₁.congr hf₁₂)]
    use g, h₁g, h₂g
    filter_upwards [hf₁₂, h₃g] using by grind

Depends on / 依赖: MeromorphicAt, contrapose, eq_comm, filter_upwards, meromorphicOrderAt, meromorphicOrderAt_eq_int_iff, meromorphicOrderAt_eq_top_iff
-/
theorem meromorphicOrderAt_congr (hf₁₂ : f₁ =ᶠ[𝓝[!=] x] f₂) :
    meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x := by
  by_cases hf₁ : MeromorphicAt f₁ x; swap
  · have : ¬ MeromorphicAt f₂ x := by
      contrapose hf₁
      exact hf₁.congr hf₁₂.symm
    simp [hf₁, this]
  rw [eq_comm]
  cases h₁f₁ : meromorphicOrderAt f₁ x with
  | top =>
    rw [meromorphicOrderAt_eq_top_iff] at h₁f₁ ⊢
    filter_upwards [hf₁₂, h₁f₁] using by grind
  | coe n =>
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 h₁f₁
    rw [meromorphicOrderAt_eq_int_iff (hf₁.congr hf₁₂)]
    use g, h₁g, h₂g
    filter_upwards [hf₁₂, h₃g] using by grind

/--
lemma `AnalyticAt.meromorphicOrderAt_eq` / 引理 `AnalyticAt.meromorphicOrderAt_eq`

English:
lemma AnalyticAt.meromorphicOrderAt_eq
  given: (hf : AnalyticAt 𝕜 f x)
  proof: by
  cases hn : analyticOrderAt f x
  · rw [ENat.map_top, meromorphicOrderAt_eq_top_iff]
    exact (analyticOrderAt_eq_top.mp hn).filter_mono nhdsWithin_le_nhds
  · simp_rw [ENat.map_natCast, meromorphicOrderAt_eq_int_iff hf.meromorphicAt, zpow_natCast]
    rcases hf.analyticOrderAt_eq_natCast.mp hn with ⟨g, h1, h2, h3⟩
    exact ⟨g, h1, h2, h3.filter_mono nhdsWithin_le_nhds⟩

中文:
引理 AnalyticAt.meromorphicOrderAt_eq
  条件: (hf : AnalyticAt 𝕜 f x)
  证明: by
  cases hn : analyticOrderAt f x
  · rw [ENat.map_top, meromorphicOrderAt_eq_top_iff]
    exact (analyticOrderAt_eq_top.mp hn).filter_mono nhdsWithin_le_nhds
  · simp_rw [ENat.map_natCast, meromorphicOrderAt_eq_int_iff hf.meromorphicAt, zpow_natCast]
    rcases hf.analyticOrderAt_eq_natCast.mp hn with ⟨g, h1, h2, h3⟩
    exact ⟨g, h1, h2, h3.filter_mono nhdsWithin_le_nhds⟩

Depends on / 依赖: ENat.map_natCast, ENat.map_top, analyticOrderAt, analyticOrderAt_eq_natCast, analyticOrderAt_eq_top, analyticOrderAt_eq_top.mp, filter_mono, h3.filter_mono, hf.analyticOrderAt_eq_natCast.mp, hf.meromorphicAt, map_natCast, map_top, meromorphicAt, meromorphicOrderAt_eq_int_iff, meromorphicOrderAt_eq_top_iff, nhdsWithin_le_nhds, simp_rw, zpow_natCast
-/
lemma AnalyticAt.meromorphicOrderAt_eq (hf : AnalyticAt 𝕜 f x) :
    meromorphicOrderAt f x = (analyticOrderAt f x).map (↑) := by
  cases hn : analyticOrderAt f x
  · rw [ENat.map_top, meromorphicOrderAt_eq_top_iff]
    exact (analyticOrderAt_eq_top.mp hn).filter_mono nhdsWithin_le_nhds
  · simp_rw [ENat.map_natCast, meromorphicOrderAt_eq_int_iff hf.meromorphicAt, zpow_natCast]
    rcases hf.analyticOrderAt_eq_natCast.mp hn with ⟨g, h1, h2, h3⟩
    exact ⟨g, h1, h2, h3.filter_mono nhdsWithin_le_nhds⟩

/--
theorem `AnalyticAt.meromorphicOrderAt_nonneg` / 定理 `AnalyticAt.meromorphicOrderAt_nonneg`

English:
theorem AnalyticAt.meromorphicOrderAt_nonneg
  given: (hf : AnalyticAt 𝕜 f x)
  proof: by
  simp [hf.meromorphicOrderAt_eq]

中文:
定理 AnalyticAt.meromorphicOrderAt_nonneg
  条件: (hf : AnalyticAt 𝕜 f x)
  证明: by
  simp [hf.meromorphicOrderAt_eq]

Depends on / 依赖: hf.meromorphicOrderAt_eq, meromorphicOrderAt_eq
-/
theorem AnalyticAt.meromorphicOrderAt_nonneg (hf : AnalyticAt 𝕜 f x) :
    0 <= meromorphicOrderAt f x := by
  simp [hf.meromorphicOrderAt_eq]

/--
theorem `MeromorphicAt.meromorphicOrderAt_nonneg_iff` / 定理 `MeromorphicAt.meromorphicOrderAt_nonneg_iff`

English:
theorem MeromorphicAt.meromorphicOrderAt_nonneg_iff
  proof: by
  refine ⟨fun nneg => ?_, fun ⟨g, hg₁, hg₂⟩ => ?_⟩
  · cases h₀ : meromorphicOrderAt f x with
    | top => exact ⟨0, analyticAt_const, meromorphicOrderAt_eq_top_iff.mp h₀⟩
    | coe n =>
      obtain ⟨g, hg, -, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp h₀
      refine ⟨fun z => (z - x) ^ n • g z, ?_, hfg⟩
      exact (AnalyticAt.zpow_nonneg (by fun_prop) (by simpa [h₀] using nneg)).smul hg
  · simp [meromorphicOrderAt_congr hg₂, hg₁.meromorphicOrderAt_nonneg]

中文:
定理 MeromorphicAt.meromorphicOrderAt_nonneg_iff
  证明: by
  refine ⟨fun nneg => ?_, fun ⟨g, hg₁, hg₂⟩ => ?_⟩
  · cases h₀ : meromorphicOrderAt f x with
    | top => exact ⟨0, analyticAt_const, meromorphicOrderAt_eq_top_iff.mp h₀⟩
    | coe n =>
      obtain ⟨g, hg, -, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp h₀
      refine ⟨fun z => (z - x) ^ n • g z, ?_, hfg⟩
      exact (AnalyticAt.zpow_nonneg (by fun_prop) (by simpa [h₀] using nneg)).smul hg
  · simp [meromorphicOrderAt_congr hg₂, hg₁.meromorphicOrderAt_nonneg]

Depends on / 依赖: AnalyticAt, AnalyticAt.zpow_nonneg, analyticAt_const, fun_prop, meromorphicOrderAt, meromorphicOrderAt_congr, meromorphicOrderAt_eq_int_iff, meromorphicOrderAt_eq_top_iff, meromorphicOrderAt_eq_top_iff.mp, meromorphicOrderAt_nonneg, zpow_nonneg
-/
theorem MeromorphicAt.meromorphicOrderAt_nonneg_iff
    (hf : MeromorphicAt f x) :
    0 <= meromorphicOrderAt f x ↔ exists g : 𝕜 -> E, AnalyticAt 𝕜 g x ∧ f =ᶠ[𝓝[!=] x] g := by
  refine ⟨fun nneg => ?_, fun ⟨g, hg₁, hg₂⟩ => ?_⟩
  · cases h₀ : meromorphicOrderAt f x with
    | top => exact ⟨0, analyticAt_const, meromorphicOrderAt_eq_top_iff.mp h₀⟩
    | coe n =>
      obtain ⟨g, hg, -, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp h₀
      refine ⟨fun z => (z - x) ^ n • g z, ?_, hfg⟩
      exact (AnalyticAt.zpow_nonneg (by fun_prop) (by simpa [h₀] using nneg)).smul hg
  · simp [meromorphicOrderAt_congr hg₂, hg₁.meromorphicOrderAt_nonneg]

/--
theorem `MeromorphicAt.analyticAt` / 定理 `MeromorphicAt.analyticAt`

English:
theorem MeromorphicAt.analyticAt
  statement: {f : 𝕜 -> E} {x : 𝕜}
  proof: by
  cases ho : meromorphicOrderAt f x with
  | top =>
    /- If the order is infinite, then `f` vanishes on a pointed neighborhood of `x`. By continuity,
    it also vanishes at `x`.-/
    have : AnalyticAt 𝕜 (fun _ => (0 : E)) x := analyticAt_const
    apply this.congr
    rw [← ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE continuousAt_const h']
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 ho] with y hy using by simp [hy]
  | coe n =>
    /- If the order is finite, then the order has to be nonnegative, as otherwise the norm of `f`
    would tend to infinity at `x`. Then the local expression of `f` coming from its meromorphicity
    shows that it coincides with an analytic function close to `x`, except maybe at `x`. By
    continuity of `f`, the two functions also coincide at `x`. -/
    rcases (meromorphicOrderAt_eq_int_iff h).1 ho with ⟨g, g_an, gx, hg⟩
    have : 0 <= meromorphicOrderAt f x := by
      apply (tendsto_nhds_iff_meromorphicOrderAt_nonneg h).1
      exact ⟨f x, h'.continuousWithinAt.tendsto⟩
    lift n to Nat using by simpa [ho] using this
    have A : forallᶠ (z : 𝕜) in 𝓝 x, (z - x) ^ n • g z = f z := by
      apply (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (by fun_prop) h').1
      filter_upwards [hg] with z hz using by simpa using hz.symm
    exact AnalyticAt.congr (by fun_prop) A

中文:
定理 MeromorphicAt.analyticAt
  结论: {f : 𝕜 -> E} {x : 𝕜}
  证明: by
  cases ho : meromorphicOrderAt f x with
  | top =>
    /- If the order is infinite, then `f` vanishes on a pointed neighborhood of `x`. By continuity,
    it also vanishes at `x`.-/
    have : AnalyticAt 𝕜 (fun _ => (0 : E)) x := analyticAt_const
    apply this.congr
    rw [← ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE continuousAt_const h']
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 ho] with y hy using by simp [hy]
  | coe n =>
    /- If the order is finite, then the order has to be nonnegative, as otherwise the norm of `f`
    would tend to infinity at `x`. Then the local expression of `f` coming from its meromorphicity
    shows that it coincides with an analytic function close to `x`, except maybe at `x`. By
    continuity of `f`, the two functions also coincide at `x`. -/
    rcases (meromorphicOrderAt_eq_int_iff h).1 ho with ⟨g, g_an, gx, hg⟩
    have : 0 <= meromorphicOrderAt f x := by
      apply (tendsto_nhds_iff_meromorphicOrderAt_nonneg h).1
      exact ⟨f x, h'.continuousWithinAt.tendsto⟩
    lift n to Nat using by simpa [ho] using this
    have A : forallᶠ (z : 𝕜) in 𝓝 x, (z - x) ^ n • g z = f z := by
      apply (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (by fun_prop) h').1
      filter_upwards [hg] with z hz using by simpa using hz.symm
    exact AnalyticAt.congr (by fun_prop) A
-/
protected theorem MeromorphicAt.analyticAt {f : 𝕜 -> E} {x : 𝕜}
    (h : MeromorphicAt f x) (h' : ContinuousAt f x) :
    AnalyticAt 𝕜 f x := by
  cases ho : meromorphicOrderAt f x with
  | top =>
    /- If the order is infinite, then `f` vanishes on a pointed neighborhood of `x`. By continuity,
    it also vanishes at `x`.-/
    have : AnalyticAt 𝕜 (fun _ => (0 : E)) x := analyticAt_const
    apply this.congr
    rw [← ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE continuousAt_const h']
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 ho] with y hy using by simp [hy]
  | coe n =>
    /- If the order is finite, then the order has to be nonnegative, as otherwise the norm of `f`
    would tend to infinity at `x`. Then the local expression of `f` coming from its meromorphicity
    shows that it coincides with an analytic function close to `x`, except maybe at `x`. By
    continuity of `f`, the two functions also coincide at `x`. -/
    rcases (meromorphicOrderAt_eq_int_iff h).1 ho with ⟨g, g_an, gx, hg⟩
    have : 0 <= meromorphicOrderAt f x := by
      apply (tendsto_nhds_iff_meromorphicOrderAt_nonneg h).1
      exact ⟨f x, h'.continuousWithinAt.tendsto⟩
    lift n to Nat using by simpa [ho] using this
    have A : forallᶠ (z : 𝕜) in 𝓝 x, (z - x) ^ n • g z = f z := by
      apply (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (by fun_prop) h').1
      filter_upwards [hg] with z hz using by simpa using hz.symm
    exact AnalyticAt.congr (by fun_prop) A

/--
lemma `AnalyticAt.of_meromorphicOrderAt_pos` / 引理 `AnalyticAt.of_meromorphicOrderAt_pos`

English:
lemma AnalyticAt.of_meromorphicOrderAt_pos
  statement: {f : 𝕜 -> E} {x : 𝕜}
  proof: by
  refine (meromorphicAt_of_meromorphicOrderAt_ne_zero h.ne').analyticAt ?_
  rw [continuousAt_iff_punctured_nhds]; rw [hf]
  exact tendsto_zero_of_meromorphicOrderAt_pos h

中文:
引理 AnalyticAt.of_meromorphicOrderAt_pos
  结论: {f : 𝕜 -> E} {x : 𝕜}
  证明: by
  refine (meromorphicAt_of_meromorphicOrderAt_ne_zero h.ne').analyticAt ?_
  rw [continuousAt_iff_punctured_nhds]; rw [hf]
  exact tendsto_zero_of_meromorphicOrderAt_pos h

Depends on / 依赖: analyticAt, continuousAt_iff_punctured_nhds, h.ne, meromorphicAt_of_meromorphicOrderAt_ne_zero, tendsto_zero_of_meromorphicOrderAt_pos
-/
lemma AnalyticAt.of_meromorphicOrderAt_pos {f : 𝕜 -> E} {x : 𝕜}
    (h : 0 < meromorphicOrderAt f x) (hf : f x = 0) :
    AnalyticAt 𝕜 f x := by
  refine (meromorphicAt_of_meromorphicOrderAt_ne_zero h.ne').analyticAt ?_
  rw [continuousAt_iff_punctured_nhds]; rw [hf]
  exact tendsto_zero_of_meromorphicOrderAt_pos h

/--
theorem `meromorphicOrderAt_const` / 定理 `meromorphicOrderAt_const`

English:
theorem meromorphicOrderAt_const
  given: (z₀ : 𝕜) (e : E) [Decidable (e = 0)]
  proof: by
  split_ifs with he
  · simp [he, meromorphicOrderAt_eq_top_iff]
  · exact (meromorphicOrderAt_eq_int_iff (.const e z₀)).2 ⟨fun _ => e, by fun_prop, by simpa⟩

@[simp]

中文:
定理 meromorphicOrderAt_const
  条件: (z₀ : 𝕜) (e : E) [可判定 (e = 0)]
  证明: by
  split_ifs with he
  · simp [he, meromorphicOrderAt_eq_top_iff]
  · exact (meromorphicOrderAt_eq_int_iff (.const e z₀)).2 ⟨fun _ => e, by fun_prop, by simpa⟩

@[simp]

Depends on / 依赖: fun_prop, meromorphicOrderAt_eq_int_iff, meromorphicOrderAt_eq_top_iff, split_ifs
-/
theorem meromorphicOrderAt_const (z₀ : 𝕜) (e : E) [Decidable (e = 0)] :
    meromorphicOrderAt (fun _ => e) z₀ = if e = 0 then ⊤ else (0 : WithTop Int) := by
  split_ifs with he
  · simp [he, meromorphicOrderAt_eq_top_iff]
  · exact (meromorphicOrderAt_eq_int_iff (.const e z₀)).2 ⟨fun _ => e, by fun_prop, by simpa⟩

@[simp]
/--
lemma `meromorphicOrderAt_id` / 引理 `meromorphicOrderAt_id`

English:
lemma meromorphicOrderAt_id
  statement: meromorphicOrderAt (𝕜 := 𝕜) id 0 = 1
  proof: by
  simp [analyticAt_id.meromorphicOrderAt_eq]

中文:
引理 meromorphicOrderAt_id
  结论: meromorphicOrderAt (𝕜 := 𝕜) id 0 = 1
  证明: by
  simp [analyticAt_id.meromorphicOrderAt_eq]

Depends on / 依赖: analyticAt_id, analyticAt_id.meromorphicOrderAt_eq, meromorphicOrderAt_eq
-/
lemma meromorphicOrderAt_id : meromorphicOrderAt (𝕜 := 𝕜) id 0 = 1 := by
  simp [analyticAt_id.meromorphicOrderAt_eq]

/--
theorem `meromorphicOrderAt_const_intCast` / 定理 `meromorphicOrderAt_const_intCast`

English:
theorem meromorphicOrderAt_const_intCast
  given: (z₀ : 𝕜) (n : Int) [Decidable ((n : 𝕜') = 0)]
  proof: meromorphicOrderAt_const z₀ (n : 𝕜')

中文:
定理 meromorphicOrderAt_const_intCast
  条件: (z₀ : 𝕜) (n : 整数) [可判定 ((n : 𝕜') = 0)]
  证明: meromorphicOrderAt_const z₀ (n : 𝕜')

Depends on / 依赖: meromorphicOrderAt_const
-/
theorem meromorphicOrderAt_const_intCast (z₀ : 𝕜) (n : Int) [Decidable ((n : 𝕜') = 0)] :
    meromorphicOrderAt (n : 𝕜 -> 𝕜') z₀ = if (n : 𝕜') = 0 then ⊤ else (0 : WithTop Int) :=
  meromorphicOrderAt_const z₀ (n : 𝕜')

/--
theorem `meromorphicOrderAt_const_natCast` / 定理 `meromorphicOrderAt_const_natCast`

English:
theorem meromorphicOrderAt_const_natCast
  given: (z₀ : 𝕜) (n : Nat) [Decidable ((n : 𝕜') = 0)]
  proof: meromorphicOrderAt_const z₀ (n : 𝕜')

中文:
定理 meromorphicOrderAt_const_natCast
  条件: (z₀ : 𝕜) (n : 自然数) [可判定 ((n : 𝕜') = 0)]
  证明: meromorphicOrderAt_const z₀ (n : 𝕜')

Depends on / 依赖: meromorphicOrderAt_const
-/
theorem meromorphicOrderAt_const_natCast (z₀ : 𝕜) (n : Nat) [Decidable ((n : 𝕜') = 0)] :
    meromorphicOrderAt (n : 𝕜 -> 𝕜') z₀ = if (n : 𝕜') = 0 then ⊤ else (0 : WithTop Int) :=
  meromorphicOrderAt_const z₀ (n : 𝕜')

/--
theorem `meromorphicOrderAt_const_ofNat` / 定理 `meromorphicOrderAt_const_ofNat`

English:
theorem meromorphicOrderAt_const_ofNat
  given: (z₀ : 𝕜) (n : Nat) [Decidable ((n : 𝕜') = 0)]
  proof: by
  convert! meromorphicOrderAt_const z₀ (n : 𝕜')
  simp [Semiring.toGrindSemiring_ofNat 𝕜' n]

中文:
定理 meromorphicOrderAt_const_of自然数
  条件: (z₀ : 𝕜) (n : 自然数) [可判定 ((n : 𝕜') = 0)]
  证明: by
  convert! meromorphicOrderAt_const z₀ (n : 𝕜')
  simp [Semiring.toGrindSemiring_ofNat 𝕜' n]
-/
@[simp] theorem meromorphicOrderAt_const_ofNat (z₀ : 𝕜) (n : Nat) [Decidable ((n : 𝕜') = 0)] :
    meromorphicOrderAt (ofNat(n) : 𝕜 -> 𝕜') z₀ = if (n : 𝕜') = 0 then ⊤ else (0 : WithTop Int) := by
  convert! meromorphicOrderAt_const z₀ (n : 𝕜')
  simp [Semiring.toGrindSemiring_ofNat 𝕜' n]

/--
theorem `meromorphicOrderAt_zpow_id_sub_const` / 定理 `meromorphicOrderAt_zpow_id_sub_const`

English:
theorem meromorphicOrderAt_zpow_id_sub_const
  given: {n : Int}
  proof: by
  rw [meromorphicOrderAt_eq_int_iff (by fun_prop)]
  exact ⟨fun z => 1, by fun_prop, one_ne_zero, by aesop⟩

中文:
定理 meromorphicOrderAt_zpow_id_sub_const
  条件: {n : 整数}
  证明: by
  rw [meromorphicOrderAt_eq_int_iff (by fun_prop)]
  exact ⟨fun z => 1, by fun_prop, one_ne_zero, by aesop⟩
-/
@[simp, to_fun] theorem meromorphicOrderAt_zpow_id_sub_const {n : Int} :
    meromorphicOrderAt ((· - x) ^ n) x = n := by
  rw [meromorphicOrderAt_eq_int_iff (by fun_prop)]
  exact ⟨fun z => 1, by fun_prop, one_ne_zero, by aesop⟩

/--
theorem `meromorphicOrderAt_pow_id_sub_const` / 定理 `meromorphicOrderAt_pow_id_sub_const`

English:
theorem meromorphicOrderAt_pow_id_sub_const
  given: {n : Nat}
  proof: by
  convert! meromorphicOrderAt_zpow_id_sub_const
  simp only [zpow_natCast]

中文:
定理 meromorphicOrderAt_pow_id_sub_const
  条件: {n : 自然数}
  证明: by
  convert! meromorphicOrderAt_zpow_id_sub_const
  simp only [zpow_natCast]
-/
@[simp, to_fun] theorem meromorphicOrderAt_pow_id_sub_const {n : Nat} :
    meromorphicOrderAt ((· - x) ^ n) x = n := by
  convert! meromorphicOrderAt_zpow_id_sub_const
  simp only [zpow_natCast]

/--
theorem `meromorphicOrderAt_id_sub_const` / 定理 `meromorphicOrderAt_id_sub_const`

English:
theorem meromorphicOrderAt_id_sub_const
  proof: by
  rw [← WithTop.coe_one]; rw [← meromorphicOrderAt_zpow_id_sub_const (𝕜 := 𝕜)]; rw [zpow_one]

中文:
定理 meromorphicOrderAt_id_sub_const
  证明: by
  rw [← WithTop.coe_one]; rw [← meromorphicOrderAt_zpow_id_sub_const (𝕜 := 𝕜)]; rw [zpow_one]
-/
@[simp] theorem meromorphicOrderAt_id_sub_const :
    meromorphicOrderAt (· - x) x = 1 := by
  rw [← WithTop.coe_one]; rw [← meromorphicOrderAt_zpow_id_sub_const (𝕜 := 𝕜)]; rw [zpow_one]

/-!
## Order at a Point: Behaviour under Ring Operations

We establish additivity of the order under multiplication and taking powers.
-/

/--
theorem `meromorphicOrderAt_neg` / 定理 `meromorphicOrderAt_neg`

English:
theorem meromorphicOrderAt_neg
  given: {f : 𝕜 -> E}
  proof: by
  by_cases h₁ : ¬MeromorphicAt f x
  · aesop
  rw [not_not] at h₁
  by_cases h₂ : meromorphicOrderAt f x = ⊤
  · rw [h₂, eq_comm]
    simp_all [meromorphicOrderAt_eq_top_iff]
  lift meromorphicOrderAt f x to Int using h₂ with n hn
  rw [eq_comm]; rw [meromorphicOrderAt_eq_int_iff (by fun_prop)] at *
  obtain ⟨g, hg⟩ := hn
  use -g
  simp_all

中文:
定理 meromorphicOrderAt_neg
  条件: {f : 𝕜 -> E}
  证明: by
  by_cases h₁ : ¬MeromorphicAt f x
  · aesop
  rw [not_not] at h₁
  by_cases h₂ : meromorphicOrderAt f x = ⊤
  · rw [h₂, eq_comm]
    simp_all [meromorphicOrderAt_eq_top_iff]
  lift meromorphicOrderAt f x to Int using h₂ with n hn
  rw [eq_comm]; rw [meromorphicOrderAt_eq_int_iff (by fun_prop)] at *
  obtain ⟨g, hg⟩ := hn
  use -g
  simp_all

Depends on / 依赖: MeromorphicAt, eq_comm, fun_prop, meromorphicOrderAt, meromorphicOrderAt_eq_int_iff, meromorphicOrderAt_eq_top_iff, not_not
-/
theorem meromorphicOrderAt_neg {f : 𝕜 -> E} :
    meromorphicOrderAt f x = meromorphicOrderAt (-f) x := by
  by_cases h₁ : ¬MeromorphicAt f x
  · aesop
  rw [not_not] at h₁
  by_cases h₂ : meromorphicOrderAt f x = ⊤
  · rw [h₂, eq_comm]
    simp_all [meromorphicOrderAt_eq_top_iff]
  lift meromorphicOrderAt f x to Int using h₂ with n hn
  rw [eq_comm]; rw [meromorphicOrderAt_eq_int_iff (by fun_prop)] at *
  obtain ⟨g, hg⟩ := hn
  use -g
  simp_all

/--
theorem `meromorphicOrderAt_fun_neg` / 定理 `meromorphicOrderAt_fun_neg`

English:
theorem meromorphicOrderAt_fun_neg
  given: {f : 𝕜 -> E}
  proof: meromorphicOrderAt_neg

中文:
定理 meromorphicOrderAt_fun_neg
  条件: {f : 𝕜 -> E}
  证明: meromorphicOrderAt_neg

Depends on / 依赖: meromorphicOrderAt_neg
-/
theorem meromorphicOrderAt_fun_neg {f : 𝕜 -> E} :
    meromorphicOrderAt f x = meromorphicOrderAt (fun z => -f z) x := meromorphicOrderAt_neg

/--
theorem `meromorphicOrderAt_smul` / 定理 `meromorphicOrderAt_smul`

English:
theorem meromorphicOrderAt_smul
  statement: [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E]
  proof: by
  -- Trivial cases: one of the functions vanishes around z₀
  cases h₂f : meromorphicOrderAt f x with
  | top =>
    simp only [top_add, meromorphicOrderAt_eq_top_iff] at h₂f ⊢
    filter_upwards [h₂f] with z hz using by simp [hz]
  | coe m =>
    cases h₂g : meromorphicOrderAt g x with
    | top =>
      simp only [add_top, meromorphicOrderAt_eq_top_iff] at h₂g ⊢
      filter_upwards [h₂g] with z hz using by simp [hz]
    | coe n => -- Non-trivial case: both functions do not vanish around z₀
      rw [← WithTop.coe_add]; rw [meromorphicOrderAt_eq_int_iff (hf.smul hg)]
      obtain ⟨F, h₁F, h₂F, h₃F⟩ := (meromorphicOrderAt_eq_int_iff hf).1 h₂f
      obtain ⟨G, h₁G, h₂G, h₃G⟩ := (meromorphicOrderAt_eq_int_iff hg).1 h₂g
      use F • G, h₁F.smul h₁G, by simp [h₂F, h₂G]
      filter_upwards [self_mem_nhdsWithin, h₃F, h₃G] with a ha hfa hga
      simp [hfa, hga, smul_comm (F a), zpow_add₀ (sub_ne_zero.mpr ha), mul_smul]

中文:
定理 meromorphicOrderAt_smul
  结论: [赋范代数 𝕜 R] [标量塔 𝕜 R E]
  证明: by
  -- Trivial cases: one of the functions vanishes around z₀
  cases h₂f : meromorphicOrderAt f x with
  | top =>
    simp only [top_add, meromorphicOrderAt_eq_top_iff] at h₂f ⊢
    filter_upwards [h₂f] with z hz using by simp [hz]
  | coe m =>
    cases h₂g : meromorphicOrderAt g x with
    | top =>
      simp only [add_top, meromorphicOrderAt_eq_top_iff] at h₂g ⊢
      filter_upwards [h₂g] with z hz using by simp [hz]
    | coe n => -- Non-trivial case: both functions do not vanish around z₀
      rw [← WithTop.coe_add]; rw [meromorphicOrderAt_eq_int_iff (hf.smul hg)]
      obtain ⟨F, h₁F, h₂F, h₃F⟩ := (meromorphicOrderAt_eq_int_iff hf).1 h₂f
      obtain ⟨G, h₁G, h₂G, h₃G⟩ := (meromorphicOrderAt_eq_int_iff hg).1 h₂g
      use F • G, h₁F.smul h₁G, by simp [h₂F, h₂G]
      filter_upwards [self_mem_nhdsWithin, h₃F, h₃G] with a ha hfa hga
      simp [hfa, hga, smul_comm (F a), zpow_add₀ (sub_ne_zero.mpr ha), mul_smul]
-/
@[to_fun] theorem meromorphicOrderAt_smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E]
    {f : 𝕜 -> R} {g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    meromorphicOrderAt (f • g) x = meromorphicOrderAt f x + meromorphicOrderAt g x := by
  -- Trivial cases: one of the functions vanishes around z₀
  cases h₂f : meromorphicOrderAt f x with
  | top =>
    simp only [top_add, meromorphicOrderAt_eq_top_iff] at h₂f ⊢
    filter_upwards [h₂f] with z hz using by simp [hz]
  | coe m =>
    cases h₂g : meromorphicOrderAt g x with
    | top =>
      simp only [add_top, meromorphicOrderAt_eq_top_iff] at h₂g ⊢
      filter_upwards [h₂g] with z hz using by simp [hz]
    | coe n => -- Non-trivial case: both functions do not vanish around z₀
      rw [← WithTop.coe_add]; rw [meromorphicOrderAt_eq_int_iff (hf.smul hg)]
      obtain ⟨F, h₁F, h₂F, h₃F⟩ := (meromorphicOrderAt_eq_int_iff hf).1 h₂f
      obtain ⟨G, h₁G, h₂G, h₃G⟩ := (meromorphicOrderAt_eq_int_iff hg).1 h₂g
      use F • G, h₁F.smul h₁G, by simp [h₂F, h₂G]
      filter_upwards [self_mem_nhdsWithin, h₃F, h₃G] with a ha hfa hga
      simp [hfa, hga, smul_comm (F a), zpow_add₀ (sub_ne_zero.mpr ha), mul_smul]

/--
theorem `meromorphicOrderAt_mul` / 定理 `meromorphicOrderAt_mul`

English:
theorem meromorphicOrderAt_mul
  statement: {f g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x)
  proof: meromorphicOrderAt_smul hf hg

中文:
定理 meromorphicOrderAt_mul
  结论: {f g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x)
  证明: meromorphicOrderAt_smul hf hg
-/
@[to_fun] theorem meromorphicOrderAt_mul {f g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x)
    (hg : MeromorphicAt g x) :
    meromorphicOrderAt (f * g) x = meromorphicOrderAt f x + meromorphicOrderAt g x :=
  meromorphicOrderAt_smul hf hg

/--
theorem `meromorphicOrderAt_prod` / 定理 `meromorphicOrderAt_prod`

English:
theorem meromorphicOrderAt_prod
  statement: {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜'}
  proof: by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]; rw [Finset.sum_empty]; rw [← WithTop.coe_zero]; rw [meromorphicOrderAt_eq_int_iff]
    · exact ⟨1, analyticAt_const, by simp⟩
    · apply MeromorphicAt.const
  | insert a s ha hs =>
    rw [Finset.sum_insert ha]; rw [Finset.prod_insert ha]; rw [meromorphicOrderAt_mul
      (hf a (Finset.mem_insert_self a s))
      (MeromorphicAt.prod (fun i hi => hf i (Finset.mem_insert_of_mem hi)))]
    congr
    rw [hs (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

中文:
定理 meromorphicOrderAt_prod
  结论: {x : 𝕜} {ι : 类型} {s : 有限集 ι} {f : ι -> 𝕜 -> 𝕜'}
  证明: by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]; rw [Finset.sum_empty]; rw [← WithTop.coe_zero]; rw [meromorphicOrderAt_eq_int_iff]
    · exact ⟨1, analyticAt_const, by simp⟩
    · apply MeromorphicAt.const
  | insert a s ha hs =>
    rw [Finset.sum_insert ha]; rw [Finset.prod_insert ha]; rw [meromorphicOrderAt_mul
      (hf a (Finset.mem_insert_self a s))
      (MeromorphicAt.prod (fun i hi => hf i (Finset.mem_insert_of_mem hi)))]
    congr
    rw [hs (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

Depends on / 依赖: Finset, Finset.induction, Finset.mem_insert_o, Finset.mem_insert_of_mem, Finset.mem_insert_self, Finset.prod_empty, Finset.prod_insert, Finset.sum_empty, Finset.sum_insert, MeromorphicAt, MeromorphicAt.const, MeromorphicAt.prod, WithTop, WithTop.coe_zero, analyticAt_const, classical, coe_zero, insert, mem_insert_o, mem_insert_of_mem
-/
theorem meromorphicOrderAt_prod {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜'}
    (hf : forall i in s, MeromorphicAt (f i) x) :
    meromorphicOrderAt (∏ i in s, f i) x = ∑ i in s, meromorphicOrderAt (f i) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]; rw [Finset.sum_empty]; rw [← WithTop.coe_zero]; rw [meromorphicOrderAt_eq_int_iff]
    · exact ⟨1, analyticAt_const, by simp⟩
    · apply MeromorphicAt.const
  | insert a s ha hs =>
    rw [Finset.sum_insert ha]; rw [Finset.prod_insert ha]; rw [meromorphicOrderAt_mul
      (hf a (Finset.mem_insert_self a s))
      (MeromorphicAt.prod (fun i hi => hf i (Finset.mem_insert_of_mem hi)))]
    congr
    rw [hs (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

/--
theorem `meromorphicOrderAt_fun_prod` / 定理 `meromorphicOrderAt_fun_prod`

English:
theorem meromorphicOrderAt_fun_prod
  statement: {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜'}
  proof: by
  convert! meromorphicOrderAt_prod hf
  exact (Finset.prod_apply _ s f).symm

中文:
定理 meromorphicOrderAt_fun_prod
  结论: {x : 𝕜} {ι : 类型} {s : 有限集 ι} {f : ι -> 𝕜 -> 𝕜'}
  证明: by
  convert! meromorphicOrderAt_prod hf
  exact (Finset.prod_apply _ s f).symm

Depends on / 依赖: Finset, Finset.prod_apply, convert, meromorphicOrderAt_prod, prod_apply
-/
theorem meromorphicOrderAt_fun_prod {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜'}
    (hf : forall i in s, MeromorphicAt (f i) x) :
    meromorphicOrderAt (fun a => ∏ i in s, f i a) x = ∑ i in s, meromorphicOrderAt (f i) x := by
  convert! meromorphicOrderAt_prod hf
  exact (Finset.prod_apply _ s f).symm

/--
lemma `meromorphicOrderAt_finprod_ne_top` / 引理 `meromorphicOrderAt_finprod_ne_top`

English:
lemma meromorphicOrderAt_finprod_ne_top
  statement: {x : 𝕜} {ι : Type*} {F : ι -> 𝕜 -> 𝕜}
  proof: by
  classical
  by_cases hF : F.HasFiniteMulSupport
  · simpa [finprod_eq_prod F hF, meromorphicOrderAt_prod (fun x _ => h₁ x)] using fun x _ => h₂ x
  simp [finprod_of_not_hasFiniteMulSupport hF]

中文:
引理 meromorphicOrderAt_finprod_ne_top
  结论: {x : 𝕜} {ι : 类型} {F : ι -> 𝕜 -> 𝕜}
  证明: by
  classical
  by_cases hF : F.HasFiniteMulSupport
  · simpa [finprod_eq_prod F hF, meromorphicOrderAt_prod (fun x _ => h₁ x)] using fun x _ => h₂ x
  simp [finprod_of_not_hasFiniteMulSupport hF]

Depends on / 依赖: F.HasFiniteMulSupport, HasFiniteMulSupport, classical, finprod_eq_prod, finprod_of_not_hasFiniteMulSupport, meromorphicOrderAt_prod
-/
lemma meromorphicOrderAt_finprod_ne_top {x : 𝕜} {ι : Type*} {F : ι -> 𝕜 -> 𝕜}
    (h₁ : forall c, MeromorphicAt (F c) x) (h₂ : forall c, meromorphicOrderAt (F c) x != ⊤) :
    meromorphicOrderAt (∏ᶠ c, F c) x != ⊤ := by
  classical
  by_cases hF : F.HasFiniteMulSupport
  · simpa [finprod_eq_prod F hF, meromorphicOrderAt_prod (fun x _ => h₁ x)] using fun x _ => h₂ x
  simp [finprod_of_not_hasFiniteMulSupport hF]

/--
theorem `meromorphicOrderAt_pow` / 定理 `meromorphicOrderAt_pow`

English:
theorem meromorphicOrderAt_pow
  given: {f : 𝕜 -> 𝕜'} {x : 𝕜} (hf : MeromorphicAt f x) {n : Nat}
  proof: by
  induction n
  case zero =>
    simp only [pow_zero, CharP.cast_eq_zero, zero_mul]
    rw [← WithTop.coe_zero]; rw [meromorphicOrderAt_eq_int_iff]
    · exact ⟨1, analyticAt_const, by simp⟩
    · apply MeromorphicAt.const
  case succ n hn =>
    simp only [pow_add, pow_one, meromorphicOrderAt_mul (hf.pow n) hf, hn, Nat.cast_add,
      Nat.cast_one]
    cases meromorphicOrderAt f x
    · aesop
    · norm_cast
      simp only [Nat.cast_add, Nat.cast_one]
      ring

中文:
定理 meromorphicOrderAt_pow
  条件: {f : 𝕜 -> 𝕜'} {x : 𝕜} (hf : MeromorphicAt f x) {n : 自然数}
  证明: by
  induction n
  case zero =>
    simp only [pow_zero, CharP.cast_eq_zero, zero_mul]
    rw [← WithTop.coe_zero]; rw [meromorphicOrderAt_eq_int_iff]
    · exact ⟨1, analyticAt_const, by simp⟩
    · apply MeromorphicAt.const
  case succ n hn =>
    simp only [pow_add, pow_one, meromorphicOrderAt_mul (hf.pow n) hf, hn, Nat.cast_add,
      Nat.cast_one]
    cases meromorphicOrderAt f x
    · aesop
    · norm_cast
      simp only [Nat.cast_add, Nat.cast_one]
      ring
-/
@[to_fun] theorem meromorphicOrderAt_pow {f : 𝕜 -> 𝕜'} {x : 𝕜} (hf : MeromorphicAt f x) {n : Nat} :
    meromorphicOrderAt (f ^ n) x = n * meromorphicOrderAt f x := by
  induction n
  case zero =>
    simp only [pow_zero, CharP.cast_eq_zero, zero_mul]
    rw [← WithTop.coe_zero]; rw [meromorphicOrderAt_eq_int_iff]
    · exact ⟨1, analyticAt_const, by simp⟩
    · apply MeromorphicAt.const
  case succ n hn =>
    simp only [pow_add, pow_one, meromorphicOrderAt_mul (hf.pow n) hf, hn, Nat.cast_add,
      Nat.cast_one]
    cases meromorphicOrderAt f x
    · aesop
    · norm_cast
      simp only [Nat.cast_add, Nat.cast_one]
      ring

/--
theorem `meromorphicOrderAt_zpow` / 定理 `meromorphicOrderAt_zpow`

English:
theorem meromorphicOrderAt_zpow
  given: {f : 𝕜 -> 𝕜'} {x : 𝕜} (hf : MeromorphicAt f x) {n : Int}
  proof: by
  -- Trivial case: n = 0
  by_cases hn : n = 0
  · simp only [hn, zpow_zero, WithTop.coe_zero, zero_mul]
    rw [← WithTop.coe_zero]; rw [meromorphicOrderAt_eq_int_iff]
    · exact ⟨1, analyticAt_const, by simp⟩
    · apply MeromorphicAt.const
  -- Trivial case: f locally zero
  by_cases h : meromorphicOrderAt f x = ⊤
  · simp only [h, ne_eq, WithTop.coe_eq_zero, hn, not_false_eq_true, WithTop.mul_top]
    rw [meromorphicOrderAt_eq_top_iff] at *
    filter_upwards [h]
    intro y hy
    simp [hy, zero_zpow n hn]
  -- General case
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h
  rw [← WithTop.coe_untop₀_of_ne_top h]; rw [← WithTop.coe_mul]; rw [meromorphicOrderAt_eq_int_iff (hf.zpow n)]
  use g ^ n, h₁g.zpow h₂g
  constructor
  · simp_all [zpow_eq_zero_iff hn]
  · filter_upwards [h₃g]
    intro y hy
    rw [Pi.pow_apply]; rw [hy]; rw [Algebra.smul_def]; rw [Algebra.smul_def]; rw [mul_zpow]; rw [← map_zpow₀]
    congr 1
    rw [mul_comm]; rw [zpow_mul]

中文:
定理 meromorphicOrderAt_zpow
  条件: {f : 𝕜 -> 𝕜'} {x : 𝕜} (hf : MeromorphicAt f x) {n : 整数}
  证明: by
  -- Trivial case: n = 0
  by_cases hn : n = 0
  · simp only [hn, zpow_zero, WithTop.coe_zero, zero_mul]
    rw [← WithTop.coe_zero]; rw [meromorphicOrderAt_eq_int_iff]
    · exact ⟨1, analyticAt_const, by simp⟩
    · apply MeromorphicAt.const
  -- Trivial case: f locally zero
  by_cases h : meromorphicOrderAt f x = ⊤
  · simp only [h, ne_eq, WithTop.coe_eq_zero, hn, not_false_eq_true, WithTop.mul_top]
    rw [meromorphicOrderAt_eq_top_iff] at *
    filter_upwards [h]
    intro y hy
    simp [hy, zero_zpow n hn]
  -- General case
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h
  rw [← WithTop.coe_untop₀_of_ne_top h]; rw [← WithTop.coe_mul]; rw [meromorphicOrderAt_eq_int_iff (hf.zpow n)]
  use g ^ n, h₁g.zpow h₂g
  constructor
  · simp_all [zpow_eq_zero_iff hn]
  · filter_upwards [h₃g]
    intro y hy
    rw [Pi.pow_apply]; rw [hy]; rw [Algebra.smul_def]; rw [Algebra.smul_def]; rw [mul_zpow]; rw [← map_zpow₀]
    congr 1
    rw [mul_comm]; rw [zpow_mul]
-/
@[to_fun] theorem meromorphicOrderAt_zpow {f : 𝕜 -> 𝕜'} {x : 𝕜} (hf : MeromorphicAt f x) {n : Int} :
    meromorphicOrderAt (f ^ n) x = n * meromorphicOrderAt f x := by
  -- Trivial case: n = 0
  by_cases hn : n = 0
  · simp only [hn, zpow_zero, WithTop.coe_zero, zero_mul]
    rw [← WithTop.coe_zero]; rw [meromorphicOrderAt_eq_int_iff]
    · exact ⟨1, analyticAt_const, by simp⟩
    · apply MeromorphicAt.const
  -- Trivial case: f locally zero
  by_cases h : meromorphicOrderAt f x = ⊤
  · simp only [h, ne_eq, WithTop.coe_eq_zero, hn, not_false_eq_true, WithTop.mul_top]
    rw [meromorphicOrderAt_eq_top_iff] at *
    filter_upwards [h]
    intro y hy
    simp [hy, zero_zpow n hn]
  -- General case
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h
  rw [← WithTop.coe_untop₀_of_ne_top h]; rw [← WithTop.coe_mul]; rw [meromorphicOrderAt_eq_int_iff (hf.zpow n)]
  use g ^ n, h₁g.zpow h₂g
  constructor
  · simp_all [zpow_eq_zero_iff hn]
  · filter_upwards [h₃g]
    intro y hy
    rw [Pi.pow_apply]; rw [hy]; rw [Algebra.smul_def]; rw [Algebra.smul_def]; rw [mul_zpow]; rw [← map_zpow₀]
    congr 1
    rw [mul_comm]; rw [zpow_mul]

/--
theorem `meromorphicOrderAt_inv` / 定理 `meromorphicOrderAt_inv`

English:
theorem meromorphicOrderAt_inv
  given: {f : 𝕜 -> 𝕜'}
  proof: by
  by_cases hf : MeromorphicAt f x; swap
  · have : ¬ MeromorphicAt (f⁻¹) x := by
      contrapose hf
      simpa using hf.inv
    simp [hf, this]
  by_cases h₂f : meromorphicOrderAt f x = ⊤
  · rw [h₂f, ← LinearOrderedAddCommGroupWithTop.neg_top, neg_neg]
    rw [meromorphicOrderAt_eq_top_iff] at *
    filter_upwards [h₂f]
    simp
  lift meromorphicOrderAt f x to Int using h₂f with a ha
  apply (meromorphicOrderAt_eq_int_iff hf.inv).2
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_eq_int_iff hf).1 ha.symm
  use g⁻¹, h₁g.inv h₂g, inv_eq_zero.not.2 h₂g
  rw [eventually_nhdsWithin_iff] at *
  filter_upwards [h₃g]
  intro _ h₁a h₂a
  simp [h₁a h₂a, Algebra.smul_def, mul_comm]

中文:
定理 meromorphicOrderAt_inv
  条件: {f : 𝕜 -> 𝕜'}
  证明: by
  by_cases hf : MeromorphicAt f x; swap
  · have : ¬ MeromorphicAt (f⁻¹) x := by
      contrapose hf
      simpa using hf.inv
    simp [hf, this]
  by_cases h₂f : meromorphicOrderAt f x = ⊤
  · rw [h₂f, ← LinearOrderedAddCommGroupWithTop.neg_top, neg_neg]
    rw [meromorphicOrderAt_eq_top_iff] at *
    filter_upwards [h₂f]
    simp
  lift meromorphicOrderAt f x to Int using h₂f with a ha
  apply (meromorphicOrderAt_eq_int_iff hf.inv).2
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_eq_int_iff hf).1 ha.symm
  use g⁻¹, h₁g.inv h₂g, inv_eq_zero.not.2 h₂g
  rw [eventually_nhdsWithin_iff] at *
  filter_upwards [h₃g]
  intro _ h₁a h₂a
  simp [h₁a h₂a, Algebra.smul_def, mul_comm]
-/
@[to_fun] theorem meromorphicOrderAt_inv {f : 𝕜 -> 𝕜'} :
    meromorphicOrderAt (f⁻¹) x = -meromorphicOrderAt f x := by
  by_cases hf : MeromorphicAt f x; swap
  · have : ¬ MeromorphicAt (f⁻¹) x := by
      contrapose hf
      simpa using hf.inv
    simp [hf, this]
  by_cases h₂f : meromorphicOrderAt f x = ⊤
  · rw [h₂f, ← LinearOrderedAddCommGroupWithTop.neg_top, neg_neg]
    rw [meromorphicOrderAt_eq_top_iff] at *
    filter_upwards [h₂f]
    simp
  lift meromorphicOrderAt f x to Int using h₂f with a ha
  apply (meromorphicOrderAt_eq_int_iff hf.inv).2
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_eq_int_iff hf).1 ha.symm
  use g⁻¹, h₁g.inv h₂g, inv_eq_zero.not.2 h₂g
  rw [eventually_nhdsWithin_iff] at *
  filter_upwards [h₃g]
  intro _ h₁a h₂a
  simp [h₁a h₂a, Algebra.smul_def, mul_comm]

/--
theorem `meromorphicOrderAt_div` / 定理 `meromorphicOrderAt_div`

English:
theorem meromorphicOrderAt_div
  statement: {f g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x)
  proof: by
  rw [div_eq_mul_inv]; rw [meromorphicOrderAt_mul hf hg.inv]; rw [meromorphicOrderAt_inv]; rw [sub_eq_add_neg]

中文:
定理 meromorphicOrderAt_div
  结论: {f g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x)
  证明: by
  rw [div_eq_mul_inv]; rw [meromorphicOrderAt_mul hf hg.inv]; rw [meromorphicOrderAt_inv]; rw [sub_eq_add_neg]
-/
@[to_fun] theorem meromorphicOrderAt_div {f g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x)
    (hg : MeromorphicAt g x) :
    meromorphicOrderAt (f / g) x = meromorphicOrderAt f x - meromorphicOrderAt g x := by
  rw [div_eq_mul_inv]; rw [meromorphicOrderAt_mul hf hg.inv]; rw [meromorphicOrderAt_inv]; rw [sub_eq_add_neg]

/--
Adding a locally vanishing function does not change the order.
-/
@[simp]
/--
theorem `meromorphicOrderAt_add_of_top_left` / 定理 `meromorphicOrderAt_add_of_top_left`

English:
theorem meromorphicOrderAt_add_of_top_left
  proof: by
  rw [meromorphicOrderAt_congr]
  filter_upwards [meromorphicOrderAt_eq_top_iff.1 hf₁] with z hz
  simp_all

中文:
定理 meromorphicOrderAt_add_of_top_left
  证明: by
  rw [meromorphicOrderAt_congr]
  filter_upwards [meromorphicOrderAt_eq_top_iff.1 hf₁] with z hz
  simp_all

Depends on / 依赖: filter_upwards, meromorphicOrderAt_congr, meromorphicOrderAt_eq_top_iff
-/
theorem meromorphicOrderAt_add_of_top_left
    {f₁ f₂ : 𝕜 -> E} {x : 𝕜} (hf₁ : meromorphicOrderAt f₁ x = ⊤) :
    meromorphicOrderAt (f₁ + f₂) x = meromorphicOrderAt f₂ x := by
  rw [meromorphicOrderAt_congr]
  filter_upwards [meromorphicOrderAt_eq_top_iff.1 hf₁] with z hz
  simp_all

/--
Adding a locally vanishing function does not change the order.
-/
@[simp]
/--
theorem `meromorphicOrderAt_add_of_top_right` / 定理 `meromorphicOrderAt_add_of_top_right`

English:
theorem meromorphicOrderAt_add_of_top_right
  proof: by
  rw [add_comm]; rw [meromorphicOrderAt_add_of_top_left hf₂]

中文:
定理 meromorphicOrderAt_add_of_top_right
  证明: by
  rw [add_comm]; rw [meromorphicOrderAt_add_of_top_left hf₂]

Depends on / 依赖: add_comm, meromorphicOrderAt_add_of_top_left
-/
theorem meromorphicOrderAt_add_of_top_right
    {f₁ f₂ : 𝕜 -> E} {x : 𝕜} (hf₂ : meromorphicOrderAt f₂ x = ⊤) :
    meromorphicOrderAt (f₁ + f₂) x = meromorphicOrderAt f₁ x := by
  rw [add_comm]; rw [meromorphicOrderAt_add_of_top_left hf₂]

/--
theorem `meromorphicOrderAt_add` / 定理 `meromorphicOrderAt_add`

English:
theorem meromorphicOrderAt_add
  given: (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
  proof: by
  -- Handle the trivial cases where one of the orders equals ⊤
  by_cases h₂f₁ : meromorphicOrderAt f₁ x = ⊤
  · rw [h₂f₁, min_top_left, meromorphicOrderAt_congr]
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₂f₁]
    simp
  by_cases h₂f₂ : meromorphicOrderAt f₂ x = ⊤
  · simp only [h₂f₂, le_top, inf_of_le_left]
    rw [meromorphicOrderAt_congr]
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₂f₂]
    simp
  -- General case
  lift meromorphicOrderAt f₁ x to Int using h₂f₁ with n₁ hn₁
  lift meromorphicOrderAt f₂ x to Int using h₂f₂ with n₂ hn₂
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 hn₁.symm
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_eq_int_iff hf₂).1 hn₂.symm
  let n := min n₁ n₂
  let g := (fun z => (z - x) ^ (n₁ - n)) • g₁ + (fun z => (z - x) ^ (n₂ - n)) • g₂
  have h₁g : AnalyticAt 𝕜 g x := by
    apply AnalyticAt.add
    · apply (AnalyticAt.zpow_nonneg (by fun_prop) (sub_nonneg.2 (min_le_left n₁ n₂))).smul h₁g₁
    apply (AnalyticAt.zpow_nonneg (by fun_prop) (sub_nonneg.2 (min_le_right n₁ n₂))).smul h₁g₂
  have : f₁ + f₂ =ᶠ[𝓝[!=] x] ((· - x) ^ n) • g := by
    filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin]
    simp_all [g, ← smul_assoc, ← zpow_add', sub_ne_zero]
  have t₀ : MeromorphicAt ((· - x) ^ n) x := by fun_prop
  have t₁ : meromorphicOrderAt ((· - x) ^ n) x = n :=
    (meromorphicOrderAt_eq_int_iff t₀).2 ⟨1, analyticAt_const, by simp⟩
  rw [meromorphicOrderAt_congr this]; rw [meromorphicOrderAt_smul t₀ h₁g.meromorphicAt]; rw [t₁]
  exact le_add_of_nonneg_right h₁g.meromorphicOrderAt_nonneg

中文:
定理 meromorphicOrderAt_add
  条件: (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
  证明: by
  -- Handle the trivial cases where one of the orders equals ⊤
  by_cases h₂f₁ : meromorphicOrderAt f₁ x = ⊤
  · rw [h₂f₁, min_top_left, meromorphicOrderAt_congr]
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₂f₁]
    simp
  by_cases h₂f₂ : meromorphicOrderAt f₂ x = ⊤
  · simp only [h₂f₂, le_top, inf_of_le_left]
    rw [meromorphicOrderAt_congr]
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₂f₂]
    simp
  -- General case
  lift meromorphicOrderAt f₁ x to Int using h₂f₁ with n₁ hn₁
  lift meromorphicOrderAt f₂ x to Int using h₂f₂ with n₂ hn₂
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 hn₁.symm
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_eq_int_iff hf₂).1 hn₂.symm
  let n := min n₁ n₂
  let g := (fun z => (z - x) ^ (n₁ - n)) • g₁ + (fun z => (z - x) ^ (n₂ - n)) • g₂
  have h₁g : AnalyticAt 𝕜 g x := by
    apply AnalyticAt.add
    · apply (AnalyticAt.zpow_nonneg (by fun_prop) (sub_nonneg.2 (min_le_left n₁ n₂))).smul h₁g₁
    apply (AnalyticAt.zpow_nonneg (by fun_prop) (sub_nonneg.2 (min_le_right n₁ n₂))).smul h₁g₂
  have : f₁ + f₂ =ᶠ[𝓝[!=] x] ((· - x) ^ n) • g := by
    filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin]
    simp_all [g, ← smul_assoc, ← zpow_add', sub_ne_zero]
  have t₀ : MeromorphicAt ((· - x) ^ n) x := by fun_prop
  have t₁ : meromorphicOrderAt ((· - x) ^ n) x = n :=
    (meromorphicOrderAt_eq_int_iff t₀).2 ⟨1, analyticAt_const, by simp⟩
  rw [meromorphicOrderAt_congr this]; rw [meromorphicOrderAt_smul t₀ h₁g.meromorphicAt]; rw [t₁]
  exact le_add_of_nonneg_right h₁g.meromorphicOrderAt_nonneg
-/
theorem meromorphicOrderAt_add (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x) :
    min (meromorphicOrderAt f₁ x) (meromorphicOrderAt f₂ x) <= meromorphicOrderAt (f₁ + f₂) x := by
  -- Handle the trivial cases where one of the orders equals ⊤
  by_cases h₂f₁ : meromorphicOrderAt f₁ x = ⊤
  · rw [h₂f₁, min_top_left, meromorphicOrderAt_congr]
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₂f₁]
    simp
  by_cases h₂f₂ : meromorphicOrderAt f₂ x = ⊤
  · simp only [h₂f₂, le_top, inf_of_le_left]
    rw [meromorphicOrderAt_congr]
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₂f₂]
    simp
  -- General case
  lift meromorphicOrderAt f₁ x to Int using h₂f₁ with n₁ hn₁
  lift meromorphicOrderAt f₂ x to Int using h₂f₂ with n₂ hn₂
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 hn₁.symm
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_eq_int_iff hf₂).1 hn₂.symm
  let n := min n₁ n₂
  let g := (fun z => (z - x) ^ (n₁ - n)) • g₁ + (fun z => (z - x) ^ (n₂ - n)) • g₂
  have h₁g : AnalyticAt 𝕜 g x := by
    apply AnalyticAt.add
    · apply (AnalyticAt.zpow_nonneg (by fun_prop) (sub_nonneg.2 (min_le_left n₁ n₂))).smul h₁g₁
    apply (AnalyticAt.zpow_nonneg (by fun_prop) (sub_nonneg.2 (min_le_right n₁ n₂))).smul h₁g₂
  have : f₁ + f₂ =ᶠ[𝓝[!=] x] ((· - x) ^ n) • g := by
    filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin]
    simp_all [g, ← smul_assoc, ← zpow_add', sub_ne_zero]
  have t₀ : MeromorphicAt ((· - x) ^ n) x := by fun_prop
  have t₁ : meromorphicOrderAt ((· - x) ^ n) x = n :=
    (meromorphicOrderAt_eq_int_iff t₀).2 ⟨1, analyticAt_const, by simp⟩
  rw [meromorphicOrderAt_congr this]; rw [meromorphicOrderAt_smul t₀ h₁g.meromorphicAt]; rw [t₁]
  exact le_add_of_nonneg_right h₁g.meromorphicOrderAt_nonneg

/--
lemma `meromorphicOrderAt_add_eq_left_of_lt` / 引理 `meromorphicOrderAt_add_eq_left_of_lt`

English:
lemma meromorphicOrderAt_add_eq_left_of_lt
  statement: (hf₂ : MeromorphicAt f₂ x)
  proof: by
  by_cases hf₁ : MeromorphicAt f₁ x; swap
  · have : ¬ (MeromorphicAt (f₁ + f₂) x) := by
      contrapose hf₁
      simpa using hf₁.sub hf₂
    simp [this, hf₁]
  -- Trivial case: f₂ vanishes identically around z₀
  by_cases h₁f₂ : meromorphicOrderAt f₂ x = ⊤
  · rw [meromorphicOrderAt_congr]
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₁f₂]
    simp
  -- General case
  lift meromorphicOrderAt f₂ x to Int using h₁f₂ with n₂ hn₂
  lift meromorphicOrderAt f₁ x to Int using h.ne_top with n₁ hn₁
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 hn₁.symm
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_eq_int_iff hf₂).1 hn₂.symm
  rw [meromorphicOrderAt_eq_int_iff (hf₁.add hf₂)]
  refine ⟨g₁ + (· - x) ^ (n₂ - n₁) • g₂, ?_, ?_, ?_⟩
  · apply h₁g₁.add (AnalyticAt.smul _ h₁g₂)
    apply AnalyticAt.zpow_nonneg (by fun_prop)
      (sub_nonneg.2 (le_of_lt (WithTop.coe_lt_coe.1 h)))
  · simpa [zero_zpow _ <| sub_ne_zero.mpr (WithTop.coe_lt_coe.1 h).ne']
  · filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin]
    simp_all [smul_add, ← smul_assoc, ← zpow_add', sub_ne_zero]

中文:
引理 meromorphicOrderAt_add_eq_left_of_lt
  结论: (hf₂ : MeromorphicAt f₂ x)
  证明: by
  by_cases hf₁ : MeromorphicAt f₁ x; swap
  · have : ¬ (MeromorphicAt (f₁ + f₂) x) := by
      contrapose hf₁
      simpa using hf₁.sub hf₂
    simp [this, hf₁]
  -- Trivial case: f₂ vanishes identically around z₀
  by_cases h₁f₂ : meromorphicOrderAt f₂ x = ⊤
  · rw [meromorphicOrderAt_congr]
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₁f₂]
    simp
  -- General case
  lift meromorphicOrderAt f₂ x to Int using h₁f₂ with n₂ hn₂
  lift meromorphicOrderAt f₁ x to Int using h.ne_top with n₁ hn₁
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 hn₁.symm
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_eq_int_iff hf₂).1 hn₂.symm
  rw [meromorphicOrderAt_eq_int_iff (hf₁.add hf₂)]
  refine ⟨g₁ + (· - x) ^ (n₂ - n₁) • g₂, ?_, ?_, ?_⟩
  · apply h₁g₁.add (AnalyticAt.smul _ h₁g₂)
    apply AnalyticAt.zpow_nonneg (by fun_prop)
      (sub_nonneg.2 (le_of_lt (WithTop.coe_lt_coe.1 h)))
  · simpa [zero_zpow _ <| sub_ne_zero.mpr (WithTop.coe_lt_coe.1 h).ne']
  · filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin]
    simp_all [smul_add, ← smul_assoc, ← zpow_add', sub_ne_zero]

Depends on / 依赖: MeromorphicAt, contrapose
-/
lemma meromorphicOrderAt_add_eq_left_of_lt (hf₂ : MeromorphicAt f₂ x)
    (h : meromorphicOrderAt f₁ x < meromorphicOrderAt f₂ x) :
    meromorphicOrderAt (f₁ + f₂) x = meromorphicOrderAt f₁ x := by
  by_cases hf₁ : MeromorphicAt f₁ x; swap
  · have : ¬ (MeromorphicAt (f₁ + f₂) x) := by
      contrapose hf₁
      simpa using hf₁.sub hf₂
    simp [this, hf₁]
  -- Trivial case: f₂ vanishes identically around z₀
  by_cases h₁f₂ : meromorphicOrderAt f₂ x = ⊤
  · rw [meromorphicOrderAt_congr]
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₁f₂]
    simp
  -- General case
  lift meromorphicOrderAt f₂ x to Int using h₁f₂ with n₂ hn₂
  lift meromorphicOrderAt f₁ x to Int using h.ne_top with n₁ hn₁
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 hn₁.symm
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_eq_int_iff hf₂).1 hn₂.symm
  rw [meromorphicOrderAt_eq_int_iff (hf₁.add hf₂)]
  refine ⟨g₁ + (· - x) ^ (n₂ - n₁) • g₂, ?_, ?_, ?_⟩
  · apply h₁g₁.add (AnalyticAt.smul _ h₁g₂)
    apply AnalyticAt.zpow_nonneg (by fun_prop)
      (sub_nonneg.2 (le_of_lt (WithTop.coe_lt_coe.1 h)))
  · simpa [zero_zpow _ <| sub_ne_zero.mpr (WithTop.coe_lt_coe.1 h).ne']
  · filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin]
    simp_all [smul_add, ← smul_assoc, ← zpow_add', sub_ne_zero]

/--
lemma `meromorphicOrderAt_add_eq_right_of_lt` / 引理 `meromorphicOrderAt_add_eq_right_of_lt`

English:
lemma meromorphicOrderAt_add_eq_right_of_lt
  statement: (hf₁ : MeromorphicAt f₁ x)
  proof: by
  rw [add_comm]
  exact meromorphicOrderAt_add_eq_left_of_lt hf₁ h

中文:
引理 meromorphicOrderAt_add_eq_right_of_lt
  结论: (hf₁ : MeromorphicAt f₁ x)
  证明: by
  rw [add_comm]
  exact meromorphicOrderAt_add_eq_left_of_lt hf₁ h

Depends on / 依赖: add_comm, meromorphicOrderAt_add_eq_left_of_lt
-/
lemma meromorphicOrderAt_add_eq_right_of_lt (hf₁ : MeromorphicAt f₁ x)
    (h : meromorphicOrderAt f₂ x < meromorphicOrderAt f₁ x) :
    meromorphicOrderAt (f₁ + f₂) x = meromorphicOrderAt f₂ x := by
  rw [add_comm]
  exact meromorphicOrderAt_add_eq_left_of_lt hf₁ h

/--
theorem `meromorphicOrderAt_add_of_ne` / 定理 `meromorphicOrderAt_add_of_ne`

English:
theorem meromorphicOrderAt_add_of_ne
  proof: by
  rcases lt_or_lt_iff_ne.mpr h with h | h
  · simpa [h.le] using meromorphicOrderAt_add_eq_left_of_lt hf₂ h
  · simpa [h.le] using meromorphicOrderAt_add_eq_right_of_lt hf₁ h

中文:
定理 meromorphicOrderAt_add_of_ne
  证明: by
  rcases lt_or_lt_iff_ne.mpr h with h | h
  · simpa [h.le] using meromorphicOrderAt_add_eq_left_of_lt hf₂ h
  · simpa [h.le] using meromorphicOrderAt_add_eq_right_of_lt hf₁ h

Depends on / 依赖: h.le, lt_or_lt_iff_ne, lt_or_lt_iff_ne.mpr, meromorphicOrderAt_add_eq_left_of_lt, meromorphicOrderAt_add_eq_right_of_lt
-/
theorem meromorphicOrderAt_add_of_ne
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h : meromorphicOrderAt f₁ x != meromorphicOrderAt f₂ x) :
    meromorphicOrderAt (f₁ + f₂) x = min (meromorphicOrderAt f₁ x) (meromorphicOrderAt f₂ x) := by
  rcases lt_or_lt_iff_ne.mpr h with h | h
  · simpa [h.le] using meromorphicOrderAt_add_eq_left_of_lt hf₂ h
  · simpa [h.le] using meromorphicOrderAt_add_eq_right_of_lt hf₁ h

/-!
## Level Sets of the Order Function
-/

namespace MeromorphicOn

variable {U : Set 𝕜}

/--
theorem `isClopen_setOfPred_meromorphicOrderAt_eq_top` / 定理 `isClopen_setOfPred_meromorphicOrderAt_eq_top`

English:
theorem isClopen_setOfPred_meromorphicOrderAt_eq_top
  given: (hf : MeromorphicOn f U)
  proof: by
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    rcases (hf z.1 z.2).eventually_eq_zero_or_eventually_ne_zero with h | h
    · -- Case: f is locally zero in a punctured neighborhood of z
      rw [← meromorphicOrderAt_eq_top_iff] at h
      tauto
    · -- Case: f is locally nonzero in a punctured neighborhood of z
      obtain ⟨t', h₁t', h₂t', h₃t'⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h)
      use Subtype.val ⁻¹' t'
      constructor
      · intro w hw
        push _ in _
        by_cases h₁w : w = z
        · rwa [h₁w]
        · rw [meromorphicOrderAt_eq_top_iff, not_eventually]
          apply Filter.Eventually.frequently
          rw [eventually_nhdsWithin_iff]; rw [eventually_nhds_iff]
          use t' \ {z.1}, fun y h₁y h₂y => h₁t' y h₁y.1 h₁y.2, h₂t'.sdiff isClosed_singleton, hw,
            mem_singleton_iff.not.2 (Subtype.coe_ne_coe.mpr h₁w)
      · exact ⟨isOpen_induced h₂t', h₃t'⟩
  · apply isOpen_iff_forall_mem_open.mpr
    intro z hz
    conv =>
      arg 1; intro; left; right; arg 1; intro
      rw [meromorphicOrderAt_eq_top_iff]; rw [eventually_nhdsWithin_iff]; rw [eventually_nhds_iff]
    simp only [mem_ofPred_eq] at hz
    rw [meromorphicOrderAt_eq_top_iff]; rw [eventually_nhdsWithin_iff]; rw [eventually_nhds_iff] at hz
    obtain ⟨t', h₁t', h₂t', h₃t'⟩ := hz
    use Subtype.val ⁻¹' t'
    simp only [mem_compl_iff, mem_singleton_iff, isOpen_induced h₂t', mem_preimage,
      h₃t', and_self, and_true]
    intro w hw
    simp only [mem_ofPred_eq]
    -- Trivial case: w = z
    by_cases h₁w : w = z
    · rw [h₁w]
      tauto
    -- Nontrivial case: w ≠ z
    use t' \ {z.1}, fun y h₁y _ => h₁t' y (mem_of_mem_sdiff h₁y) (mem_of_mem_inter_right h₁y)
    constructor
    · exact h₂t'.sdiff isClosed_singleton
    · apply (mem_sdiff w).1
      exact ⟨hw, mem_singleton_iff.not.1 (Subtype.coe_ne_coe.2 h₁w)⟩

@[deprecated (since := "2026-07-09")]
alias isClopen_setOf_meromorphicOrderAt_eq_top := isClopen_setOfPred_meromorphicOrderAt_eq_top

中文:
定理 isClopen_setOfPred_meromorphicOrderAt_eq_top
  条件: (hf : MeromorphicOn f U)
  证明: by
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    rcases (hf z.1 z.2).eventually_eq_zero_or_eventually_ne_zero with h | h
    · -- Case: f is locally zero in a punctured neighborhood of z
      rw [← meromorphicOrderAt_eq_top_iff] at h
      tauto
    · -- Case: f is locally nonzero in a punctured neighborhood of z
      obtain ⟨t', h₁t', h₂t', h₃t'⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h)
      use Subtype.val ⁻¹' t'
      constructor
      · intro w hw
        push _ in _
        by_cases h₁w : w = z
        · rwa [h₁w]
        · rw [meromorphicOrderAt_eq_top_iff, not_eventually]
          apply Filter.Eventually.frequently
          rw [eventually_nhdsWithin_iff]; rw [eventually_nhds_iff]
          use t' \ {z.1}, fun y h₁y h₂y => h₁t' y h₁y.1 h₁y.2, h₂t'.sdiff isClosed_singleton, hw,
            mem_singleton_iff.not.2 (Subtype.coe_ne_coe.mpr h₁w)
      · exact ⟨isOpen_induced h₂t', h₃t'⟩
  · apply isOpen_iff_forall_mem_open.mpr
    intro z hz
    conv =>
      arg 1; intro; left; right; arg 1; intro
      rw [meromorphicOrderAt_eq_top_iff]; rw [eventually_nhdsWithin_iff]; rw [eventually_nhds_iff]
    simp only [mem_ofPred_eq] at hz
    rw [meromorphicOrderAt_eq_top_iff]; rw [eventually_nhdsWithin_iff]; rw [eventually_nhds_iff] at hz
    obtain ⟨t', h₁t', h₂t', h₃t'⟩ := hz
    use Subtype.val ⁻¹' t'
    simp only [mem_compl_iff, mem_singleton_iff, isOpen_induced h₂t', mem_preimage,
      h₃t', and_self, and_true]
    intro w hw
    simp only [mem_ofPred_eq]
    -- Trivial case: w = z
    by_cases h₁w : w = z
    · rw [h₁w]
      tauto
    -- Nontrivial case: w ≠ z
    use t' \ {z.1}, fun y h₁y _ => h₁t' y (mem_of_mem_sdiff h₁y) (mem_of_mem_inter_right h₁y)
    constructor
    · exact h₂t'.sdiff isClosed_singleton
    · apply (mem_sdiff w).1
      exact ⟨hw, mem_singleton_iff.not.1 (Subtype.coe_ne_coe.2 h₁w)⟩

@[deprecated (since := "2026-07-09")]
alias isClopen_setOf_meromorphicOrderAt_eq_top := isClopen_setOfPred_meromorphicOrderAt_eq_top

Depends on / 依赖: Subtype, Subtype.val, eventually_eq_zero_or_eventually_ne_zero, eventually_nhdsWithin_iff, eventually_nhds_iff, isOpen_compl_iff, isOpen_iff_forall_mem_open, locally, meromorphicOrderAt_eq_top_iff, neighborhood, nonzero, punctured
-/
theorem isClopen_setOfPred_meromorphicOrderAt_eq_top (hf : MeromorphicOn f U) :
    IsClopen { u : U | meromorphicOrderAt f u = ⊤ } := by
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    rcases (hf z.1 z.2).eventually_eq_zero_or_eventually_ne_zero with h | h
    · -- Case: f is locally zero in a punctured neighborhood of z
      rw [← meromorphicOrderAt_eq_top_iff] at h
      tauto
    · -- Case: f is locally nonzero in a punctured neighborhood of z
      obtain ⟨t', h₁t', h₂t', h₃t'⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h)
      use Subtype.val ⁻¹' t'
      constructor
      · intro w hw
        push _ in _
        by_cases h₁w : w = z
        · rwa [h₁w]
        · rw [meromorphicOrderAt_eq_top_iff, not_eventually]
          apply Filter.Eventually.frequently
          rw [eventually_nhdsWithin_iff]; rw [eventually_nhds_iff]
          use t' \ {z.1}, fun y h₁y h₂y => h₁t' y h₁y.1 h₁y.2, h₂t'.sdiff isClosed_singleton, hw,
            mem_singleton_iff.not.2 (Subtype.coe_ne_coe.mpr h₁w)
      · exact ⟨isOpen_induced h₂t', h₃t'⟩
  · apply isOpen_iff_forall_mem_open.mpr
    intro z hz
    conv =>
      arg 1; intro; left; right; arg 1; intro
      rw [meromorphicOrderAt_eq_top_iff]; rw [eventually_nhdsWithin_iff]; rw [eventually_nhds_iff]
    simp only [mem_ofPred_eq] at hz
    rw [meromorphicOrderAt_eq_top_iff]; rw [eventually_nhdsWithin_iff]; rw [eventually_nhds_iff] at hz
    obtain ⟨t', h₁t', h₂t', h₃t'⟩ := hz
    use Subtype.val ⁻¹' t'
    simp only [mem_compl_iff, mem_singleton_iff, isOpen_induced h₂t', mem_preimage,
      h₃t', and_self, and_true]
    intro w hw
    simp only [mem_ofPred_eq]
    -- Trivial case: w = z
    by_cases h₁w : w = z
    · rw [h₁w]
      tauto
    -- Nontrivial case: w ≠ z
    use t' \ {z.1}, fun y h₁y _ => h₁t' y (mem_of_mem_sdiff h₁y) (mem_of_mem_inter_right h₁y)
    constructor
    · exact h₂t'.sdiff isClosed_singleton
    · apply (mem_sdiff w).1
      exact ⟨hw, mem_singleton_iff.not.1 (Subtype.coe_ne_coe.2 h₁w)⟩

@[deprecated (since := "2026-07-09")]
alias isClopen_setOf_meromorphicOrderAt_eq_top := isClopen_setOfPred_meromorphicOrderAt_eq_top

/--
theorem `exists_meromorphicOrderAt_ne_top_iff_forall` / 定理 `exists_meromorphicOrderAt_ne_top_iff_forall`

English:
theorem exists_meromorphicOrderAt_ne_top_iff_forall
  given: (hf : MeromorphicOn f U) (hU : IsConnected U)
  proof: by
  constructor
  · intro h₂f
    have := isPreconnected_iff_preconnectedSpace.1 hU.isPreconnected
    rcases isClopen_iff.1 hf.isClopen_setOfPred_meromorphicOrderAt_eq_top with h | h
    · intro u
      have : u ∉ (∅ : Set U) := by exact fun a => a
      rw [← h] at this
      tauto
    · obtain ⟨u, hU⟩ := h₂f
      have : u in univ := by trivial
      rw [← h] at this
      tauto
  · intro h₂f
    obtain ⟨v, hv⟩ := hU.nonempty
    use ⟨v, hv⟩, h₂f ⟨v, hv⟩

中文:
定理 存在_meromorphicOrderAt_ne_top_iff_对任意
  条件: (hf : MeromorphicOn f U) (hU : 是连通 U)
  证明: by
  constructor
  · intro h₂f
    have := isPreconnected_iff_preconnectedSpace.1 hU.isPreconnected
    rcases isClopen_iff.1 hf.isClopen_setOfPred_meromorphicOrderAt_eq_top with h | h
    · intro u
      have : u ∉ (∅ : Set U) := by exact fun a => a
      rw [← h] at this
      tauto
    · obtain ⟨u, hU⟩ := h₂f
      have : u in univ := by trivial
      rw [← h] at this
      tauto
  · intro h₂f
    obtain ⟨v, hv⟩ := hU.nonempty
    use ⟨v, hv⟩, h₂f ⟨v, hv⟩

Depends on / 依赖: hU.isPreconnected, hU.nonempty, hf.isClopen_setOfPred_meromorphicOrderAt_eq_top, isClopen_iff, isClopen_setOfPred_meromorphicOrderAt_eq_top, isPreconnected, isPreconnected_iff_preconnectedSpace, nonempty
-/
theorem exists_meromorphicOrderAt_ne_top_iff_forall (hf : MeromorphicOn f U) (hU : IsConnected U) :
    (exists u : U, meromorphicOrderAt f u != ⊤) ↔ (forall u : U, meromorphicOrderAt f u != ⊤) := by
  constructor
  · intro h₂f
    have := isPreconnected_iff_preconnectedSpace.1 hU.isPreconnected
    rcases isClopen_iff.1 hf.isClopen_setOfPred_meromorphicOrderAt_eq_top with h | h
    · intro u
      have : u ∉ (∅ : Set U) := by exact fun a => a
      rw [← h] at this
      tauto
    · obtain ⟨u, hU⟩ := h₂f
      have : u in univ := by trivial
      rw [← h] at this
      tauto
  · intro h₂f
    obtain ⟨v, hv⟩ := hU.nonempty
    use ⟨v, hv⟩, h₂f ⟨v, hv⟩

/--
theorem `exists_meromorphicOrderAt_ne_top_iff_forall_mem` / 定理 `exists_meromorphicOrderAt_ne_top_iff_forall_mem`

English:
theorem exists_meromorphicOrderAt_ne_top_iff_forall_mem
  statement: (hf : MeromorphicOn f U)
  proof: by
  convert exists_meromorphicOrderAt_ne_top_iff_forall hf hU
  <;> simp

中文:
定理 存在_meromorphicOrderAt_ne_top_iff_对任意_mem
  结论: (hf : MeromorphicOn f U)
  证明: by
  convert exists_meromorphicOrderAt_ne_top_iff_forall hf hU
  <;> simp

Depends on / 依赖: convert, exists_meromorphicOrderAt_ne_top_iff_forall
-/
theorem exists_meromorphicOrderAt_ne_top_iff_forall_mem (hf : MeromorphicOn f U)
    (hU : IsConnected U) :
    (exists u in U, meromorphicOrderAt f u != ⊤) ↔ (forall u in U, meromorphicOrderAt f u != ⊤) := by
  convert exists_meromorphicOrderAt_ne_top_iff_forall hf hU
  <;> simp

/--
theorem `meromorphicOrderAt_ne_top_of_isPreconnected` / 定理 `meromorphicOrderAt_ne_top_of_isPreconnected`

English:
theorem meromorphicOrderAt_ne_top_of_isPreconnected
  statement: (hf : MeromorphicOn f U) {y : 𝕜}
  proof: (hf.exists_meromorphicOrderAt_ne_top_iff_forall ⟨nonempty_of_mem h₁x, hU⟩).1
    (by use ⟨x, h₁x⟩) ⟨y, hy⟩

中文:
定理 meromorphicOrderAt_ne_top_of_isPreconnected
  结论: (hf : MeromorphicOn f U) {y : 𝕜}
  证明: (hf.exists_meromorphicOrderAt_ne_top_iff_forall ⟨nonempty_of_mem h₁x, hU⟩).1
    (by use ⟨x, h₁x⟩) ⟨y, hy⟩

Depends on / 依赖: exists_meromorphicOrderAt_ne_top_iff_forall, hf.exists_meromorphicOrderAt_ne_top_iff_forall, nonempty_of_mem
-/
theorem meromorphicOrderAt_ne_top_of_isPreconnected (hf : MeromorphicOn f U) {y : 𝕜}
    (hU : IsPreconnected U) (h₁x : x in U) (hy : y in U) (h₂x : meromorphicOrderAt f x != ⊤) :
    meromorphicOrderAt f y != ⊤ :=
  (hf.exists_meromorphicOrderAt_ne_top_iff_forall ⟨nonempty_of_mem h₁x, hU⟩).1
    (by use ⟨x, h₁x⟩) ⟨y, hy⟩

/--
theorem `eventually_analyticAt` / 定理 `eventually_analyticAt`

English:
theorem eventually_analyticAt
  given: (h : MeromorphicOn f U) (hx : x in U)
  proof: by
  /- At neighboring points in `U`, the function `f` is both meromorphic (by meromorphicity on `U`)
  and continuous (thanks to the formula for a meromorphic function around the point `x`), so it is
  analytic. -/
  have : forallᶠ y in 𝓝[U \ {x}] x, ContinuousAt f y := by
    have : U \ {x} subseteq {x}ᶜ := by simp
    exact nhdsWithin_mono _ this (h x hx).eventually_continuousAt
  filter_upwards [this, self_mem_nhdsWithin] with y hy h'y
  exact (h y h'y.1).analyticAt hy

中文:
定理 eventually_analyticAt
  条件: (h : MeromorphicOn f U) (hx : x in U)
  证明: by
  /- At neighboring points in `U`, the function `f` is both meromorphic (by meromorphicity on `U`)
  and continuous (thanks to the formula for a meromorphic function around the point `x`), so it is
  analytic. -/
  have : forallᶠ y in 𝓝[U \ {x}] x, ContinuousAt f y := by
    have : U \ {x} subseteq {x}ᶜ := by simp
    exact nhdsWithin_mono _ this (h x hx).eventually_continuousAt
  filter_upwards [this, self_mem_nhdsWithin] with y hy h'y
  exact (h y h'y.1).analyticAt hy
-/
theorem eventually_analyticAt (h : MeromorphicOn f U) (hx : x in U) :
    forallᶠ y in 𝓝[U \ {x}] x, AnalyticAt 𝕜 f y := by
  /- At neighboring points in `U`, the function `f` is both meromorphic (by meromorphicity on `U`)
  and continuous (thanks to the formula for a meromorphic function around the point `x`), so it is
  analytic. -/
  have : forallᶠ y in 𝓝[U \ {x}] x, ContinuousAt f y := by
    have : U \ {x} subseteq {x}ᶜ := by simp
    exact nhdsWithin_mono _ this (h x hx).eventually_continuousAt
  filter_upwards [this, self_mem_nhdsWithin] with y hy h'y
  exact (h y h'y.1).analyticAt hy

/--
theorem `eventually_analyticAt_or_mem_compl` / 定理 `eventually_analyticAt_or_mem_compl`

English:
theorem eventually_analyticAt_or_mem_compl
  given: (h : MeromorphicOn f U) (hx : x in U)
  proof: by
  have : {x}ᶜ = (U \ {x}) union Uᶜ := by aesop (add simp Classical.em)
  rw [this]; rw [nhdsWithin_union]
  simp only [mem_compl_iff, eventually_sup]
  refine ⟨?_, ?_⟩
  · filter_upwards [h.eventually_analyticAt hx] with y hy using Or.inl hy
  · filter_upwards [self_mem_nhdsWithin] with y hy using Or.inr hy

中文:
定理 eventually_analyticAt_or_mem_compl
  条件: (h : MeromorphicOn f U) (hx : x in U)
  证明: by
  have : {x}ᶜ = (U \ {x}) union Uᶜ := by aesop (add simp Classical.em)
  rw [this]; rw [nhdsWithin_union]
  simp only [mem_compl_iff, eventually_sup]
  refine ⟨?_, ?_⟩
  · filter_upwards [h.eventually_analyticAt hx] with y hy using Or.inl hy
  · filter_upwards [self_mem_nhdsWithin] with y hy using Or.inr hy

Depends on / 依赖: Classical, Classical.em, Or.inl, Or.inr, eventually_analyticAt, eventually_sup, filter_upwards, h.eventually_analyticAt, mem_compl_iff, nhdsWithin_union, self_mem_nhdsWithin
-/
theorem eventually_analyticAt_or_mem_compl (h : MeromorphicOn f U) (hx : x in U) :
    forallᶠ y in 𝓝[!=] x, AnalyticAt 𝕜 f y ∨ y in Uᶜ := by
  have : {x}ᶜ = (U \ {x}) union Uᶜ := by aesop (add simp Classical.em)
  rw [this]; rw [nhdsWithin_union]
  simp only [mem_compl_iff, eventually_sup]
  refine ⟨?_, ?_⟩
  · filter_upwards [h.eventually_analyticAt hx] with y hy using Or.inl hy
  · filter_upwards [self_mem_nhdsWithin] with y hy using Or.inr hy

/--
theorem `analyticAt_mem_codiscreteWithin` / 定理 `analyticAt_mem_codiscreteWithin`

English:
theorem analyticAt_mem_codiscreteWithin
  given: (hf : MeromorphicOn f U)
  proof: by
  rw [mem_codiscreteWithin]
  intro x hx
  rw [Filter.disjoint_principal_right]; rw [← Filter.eventually_mem_set]
  filter_upwards [hf.eventually_analyticAt_or_mem_compl hx] with y hy
  simp
  tauto

中文:
定理 analyticAt_mem_codiscreteWithin
  条件: (hf : MeromorphicOn f U)
  证明: by
  rw [mem_codiscreteWithin]
  intro x hx
  rw [Filter.disjoint_principal_right]; rw [← Filter.eventually_mem_set]
  filter_upwards [hf.eventually_analyticAt_or_mem_compl hx] with y hy
  simp
  tauto

Depends on / 依赖: Filter, Filter.disjoint_principal_right, Filter.eventually_mem_set, disjoint_principal_right, eventually_analyticAt_or_mem_compl, eventually_mem_set, filter_upwards, hf.eventually_analyticAt_or_mem_compl, mem_codiscreteWithin
-/
theorem analyticAt_mem_codiscreteWithin (hf : MeromorphicOn f U) :
    { x | AnalyticAt 𝕜 f x } in Filter.codiscreteWithin U := by
  rw [mem_codiscreteWithin]
  intro x hx
  rw [Filter.disjoint_principal_right]; rw [← Filter.eventually_mem_set]
  filter_upwards [hf.eventually_analyticAt_or_mem_compl hx] with y hy
  simp
  tauto

/--
theorem `codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top` / 定理 `codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top`

English:
theorem codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top
  given: (hf : MeromorphicOn f U)
  proof: by
  rw [mem_codiscrete_subtype_iff_mem_codiscreteWithin]; rw [mem_codiscreteWithin]
  intro x hx
  rw [Filter.disjoint_principal_right]
  rcases (hf x hx).eventually_eq_zero_or_eventually_ne_zero with h₁f | h₁f
  · filter_upwards [eventually_eventually_nhdsWithin.2 h₁f] with a h₁a
    suffices forallᶠ (z : 𝕜) in 𝓝[!=] a, f z = 0 by
      simp +contextual [meromorphicOrderAt_eq_top_iff, this]
    obtain rfl | hax := eq_or_ne a x
    · exact h₁a
    rw [eventually_nhdsWithin_iff]; rw [eventually_nhds_iff] at h₁a ⊢
    obtain ⟨t, h₁t, h₂t, h₃t⟩ := h₁a
    use t \ {x}, fun y h₁y _ => h₁t y h₁y.1 h₁y.2
    exact ⟨h₂t.sdiff isClosed_singleton, Set.mem_sdiff_of_mem h₃t hax⟩
  · filter_upwards [hf.eventually_analyticAt_or_mem_compl hx, h₁f] with a h₁a h'₁a
    simp only [mem_compl_iff, Set.mem_sdiff, mem_image, mem_ofPred_eq, Subtype.exists,
      exists_and_right, exists_eq_right, not_exists, not_or, not_and, not_forall, Decidable.not_not]
    rcases h₁a with h' | h'
    · simp +contextual [h'.meromorphicOrderAt_eq, h'.analyticOrderAt_eq_zero.2, h'₁a]
    · exact fun ha => (h' ha).elim

@[deprecated (since := "2026-07-09")]
alias codiscrete_setOf_meromorphicOrderAt_eq_zero_or_top :=
  codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top

中文:
定理 codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top
  条件: (hf : MeromorphicOn f U)
  证明: by
  rw [mem_codiscrete_subtype_iff_mem_codiscreteWithin]; rw [mem_codiscreteWithin]
  intro x hx
  rw [Filter.disjoint_principal_right]
  rcases (hf x hx).eventually_eq_zero_or_eventually_ne_zero with h₁f | h₁f
  · filter_upwards [eventually_eventually_nhdsWithin.2 h₁f] with a h₁a
    suffices forallᶠ (z : 𝕜) in 𝓝[!=] a, f z = 0 by
      simp +contextual [meromorphicOrderAt_eq_top_iff, this]
    obtain rfl | hax := eq_or_ne a x
    · exact h₁a
    rw [eventually_nhdsWithin_iff]; rw [eventually_nhds_iff] at h₁a ⊢
    obtain ⟨t, h₁t, h₂t, h₃t⟩ := h₁a
    use t \ {x}, fun y h₁y _ => h₁t y h₁y.1 h₁y.2
    exact ⟨h₂t.sdiff isClosed_singleton, Set.mem_sdiff_of_mem h₃t hax⟩
  · filter_upwards [hf.eventually_analyticAt_or_mem_compl hx, h₁f] with a h₁a h'₁a
    simp only [mem_compl_iff, Set.mem_sdiff, mem_image, mem_ofPred_eq, Subtype.exists,
      exists_and_right, exists_eq_right, not_exists, not_or, not_and, not_forall, Decidable.not_not]
    rcases h₁a with h' | h'
    · simp +contextual [h'.meromorphicOrderAt_eq, h'.analyticOrderAt_eq_zero.2, h'₁a]
    · exact fun ha => (h' ha).elim

@[deprecated (since := "2026-07-09")]
alias codiscrete_setOf_meromorphicOrderAt_eq_zero_or_top :=
  codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top

Depends on / 依赖: Filter, Filter.disjoint_principal_right, contextual, disjoint_principal_right, eq_or_ne, eventually_eq_zero_or_eventually_ne_zero, eventually_eventually_nhdsWithin, eventually_nhdsWithin_iff, eventually_nhds_iff, filter_upwards, mem_codiscreteWithin, mem_codiscrete_subtype_iff_mem_codiscreteWithin, meromorphicOrderAt_eq_top_iff
-/
theorem codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top (hf : MeromorphicOn f U) :
    {u : U | meromorphicOrderAt f u = 0 ∨ meromorphicOrderAt f u = ⊤} in Filter.codiscrete U := by
  rw [mem_codiscrete_subtype_iff_mem_codiscreteWithin]; rw [mem_codiscreteWithin]
  intro x hx
  rw [Filter.disjoint_principal_right]
  rcases (hf x hx).eventually_eq_zero_or_eventually_ne_zero with h₁f | h₁f
  · filter_upwards [eventually_eventually_nhdsWithin.2 h₁f] with a h₁a
    suffices forallᶠ (z : 𝕜) in 𝓝[!=] a, f z = 0 by
      simp +contextual [meromorphicOrderAt_eq_top_iff, this]
    obtain rfl | hax := eq_or_ne a x
    · exact h₁a
    rw [eventually_nhdsWithin_iff]; rw [eventually_nhds_iff] at h₁a ⊢
    obtain ⟨t, h₁t, h₂t, h₃t⟩ := h₁a
    use t \ {x}, fun y h₁y _ => h₁t y h₁y.1 h₁y.2
    exact ⟨h₂t.sdiff isClosed_singleton, Set.mem_sdiff_of_mem h₃t hax⟩
  · filter_upwards [hf.eventually_analyticAt_or_mem_compl hx, h₁f] with a h₁a h'₁a
    simp only [mem_compl_iff, Set.mem_sdiff, mem_image, mem_ofPred_eq, Subtype.exists,
      exists_and_right, exists_eq_right, not_exists, not_or, not_and, not_forall, Decidable.not_not]
    rcases h₁a with h' | h'
    · simp +contextual [h'.meromorphicOrderAt_eq, h'.analyticOrderAt_eq_zero.2, h'₁a]
    · exact fun ha => (h' ha).elim

@[deprecated (since := "2026-07-09")]
alias codiscrete_setOf_meromorphicOrderAt_eq_zero_or_top :=
  codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top

/--
theorem `codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top` / 定理 `codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top`

English:
theorem codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top
  statement: (h₁f : MeromorphicOn f U)
  proof: by
  convert!
    mem_codiscrete_subtype_iff_mem_codiscreteWithin.1
      h₁f.codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top
  aesop

@[deprecated (since := "2026-07-09")]
alias codiscreteWithin_setOf_meromorphicOrderAt_eq_zero_or_top :=
  codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top

中文:
定理 codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top
  结论: (h₁f : MeromorphicOn f U)
  证明: by
  convert!
    mem_codiscrete_subtype_iff_mem_codiscreteWithin.1
      h₁f.codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top
  aesop

@[deprecated (since := "2026-07-09")]
alias codiscreteWithin_setOf_meromorphicOrderAt_eq_zero_or_top :=
  codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top

Depends on / 依赖: codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top, convert, f.codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top, mem_codiscrete_subtype_iff_mem_codiscreteWithin
-/
theorem codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top (h₁f : MeromorphicOn f U)
    (h₂f : forall u in U, meromorphicOrderAt f u != ⊤) :
    {u in U | meromorphicOrderAt f u = 0 ∨ meromorphicOrderAt f u = ⊤} in codiscreteWithin U := by
  convert!
    mem_codiscrete_subtype_iff_mem_codiscreteWithin.1
      h₁f.codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top
  aesop

@[deprecated (since := "2026-07-09")]
alias codiscreteWithin_setOf_meromorphicOrderAt_eq_zero_or_top :=
  codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top

end MeromorphicOn

section comp
/-!
## Order at a Point: Behaviour under Composition
-/
variable {x : 𝕜} {f : 𝕜 -> E} {g : 𝕜 -> 𝕜}

/--
lemma `MeromorphicAt.meromorphicOrderAt_comp` / 引理 `MeromorphicAt.meromorphicOrderAt_comp`

English:
lemma MeromorphicAt.meromorphicOrderAt_comp
  statement: (hf : MeromorphicAt f (g x)) (hg : AnalyticAt 𝕜 g x)
  proof: by
  -- First deal with the silly case that `f` is identically zero around `g x`.
  rcases eq_or_ne (meromorphicOrderAt f (g x)) ⊤ with hf' | hf'
  · rw [hf', WithTop.top_mul]
    · rw [meromorphicOrderAt_eq_top_iff] at hf' ⊢
      rw [Function.comp_def]; rw [← eventually_map (P := (f · = 0))]
      exact EventuallyEq.filter_mono hf' (hg.map_nhdsNE hg_nc)
    · simp [(show AnalyticAt 𝕜 (g · - g x) x by fun_prop).analyticOrderAt_eq_zero]
  -- Now the interesting case. First unpack the data
  have hr := (WithTop.coe_untop₀_of_ne_top hf').symm
  rw [meromorphicOrderAt_ne_top_iff hf] at hf'
  set r := (meromorphicOrderAt f (g x)).untop₀
  rw [hr]
  -- Now write `f = (· - g x) ^ r • F` for `F` analytic and nonzero at `g x`
  obtain ⟨F, hFan, hFne, hFev⟩ := hf'
  have aux1 : f ∘ g =ᶠ[𝓝[!=] x] (g · - g x) ^ r • (F ∘ g) := hFev.comp_tendsto (hg.map_nhdsNE hg_nc)
  have aux2 : meromorphicOrderAt (F ∘ g) x = 0 := by
    rw [AnalyticAt.meromorphicOrderAt_eq (by fun_prop)]; rw [analyticOrderAt_eq_zero.mpr (by exact .inr hFne)]; rw [ENat.map_zero]; rw [CharP.cast_eq_zero]; rw [WithTop.coe_zero]
  rw [meromorphicOrderAt_congr aux1]; rw [meromorphicOrderAt_smul ?_ (AnalyticAt.meromorphicAt ?_)]; rw [aux2]; rw [add_zero]; rw [meromorphicOrderAt_zpow]; rw [AnalyticAt.meromorphicOrderAt_eq] <;>
  fun_prop

中文:
引理 MeromorphicAt.meromorphicOrderAt_comp
  结论: (hf : MeromorphicAt f (g x)) (hg : AnalyticAt 𝕜 g x)
  证明: by
  -- First deal with the silly case that `f` is identically zero around `g x`.
  rcases eq_or_ne (meromorphicOrderAt f (g x)) ⊤ with hf' | hf'
  · rw [hf', WithTop.top_mul]
    · rw [meromorphicOrderAt_eq_top_iff] at hf' ⊢
      rw [Function.comp_def]; rw [← eventually_map (P := (f · = 0))]
      exact EventuallyEq.filter_mono hf' (hg.map_nhdsNE hg_nc)
    · simp [(show AnalyticAt 𝕜 (g · - g x) x by fun_prop).analyticOrderAt_eq_zero]
  -- Now the interesting case. First unpack the data
  have hr := (WithTop.coe_untop₀_of_ne_top hf').symm
  rw [meromorphicOrderAt_ne_top_iff hf] at hf'
  set r := (meromorphicOrderAt f (g x)).untop₀
  rw [hr]
  -- Now write `f = (· - g x) ^ r • F` for `F` analytic and nonzero at `g x`
  obtain ⟨F, hFan, hFne, hFev⟩ := hf'
  have aux1 : f ∘ g =ᶠ[𝓝[!=] x] (g · - g x) ^ r • (F ∘ g) := hFev.comp_tendsto (hg.map_nhdsNE hg_nc)
  have aux2 : meromorphicOrderAt (F ∘ g) x = 0 := by
    rw [AnalyticAt.meromorphicOrderAt_eq (by fun_prop)]; rw [analyticOrderAt_eq_zero.mpr (by exact .inr hFne)]; rw [ENat.map_zero]; rw [CharP.cast_eq_zero]; rw [WithTop.coe_zero]
  rw [meromorphicOrderAt_congr aux1]; rw [meromorphicOrderAt_smul ?_ (AnalyticAt.meromorphicAt ?_)]; rw [aux2]; rw [add_zero]; rw [meromorphicOrderAt_zpow]; rw [AnalyticAt.meromorphicOrderAt_eq] <;>
  fun_prop
-/
lemma MeromorphicAt.meromorphicOrderAt_comp (hf : MeromorphicAt f (g x)) (hg : AnalyticAt 𝕜 g x)
    (hg_nc : ¬EventuallyConst g (𝓝 x)) :
    meromorphicOrderAt (f ∘ g) x =
      (meromorphicOrderAt f (g x)) * (analyticOrderAt (g · - g x) x).map Nat.cast := by
  -- First deal with the silly case that `f` is identically zero around `g x`.
  rcases eq_or_ne (meromorphicOrderAt f (g x)) ⊤ with hf' | hf'
  · rw [hf', WithTop.top_mul]
    · rw [meromorphicOrderAt_eq_top_iff] at hf' ⊢
      rw [Function.comp_def]; rw [← eventually_map (P := (f · = 0))]
      exact EventuallyEq.filter_mono hf' (hg.map_nhdsNE hg_nc)
    · simp [(show AnalyticAt 𝕜 (g · - g x) x by fun_prop).analyticOrderAt_eq_zero]
  -- Now the interesting case. First unpack the data
  have hr := (WithTop.coe_untop₀_of_ne_top hf').symm
  rw [meromorphicOrderAt_ne_top_iff hf] at hf'
  set r := (meromorphicOrderAt f (g x)).untop₀
  rw [hr]
  -- Now write `f = (· - g x) ^ r • F` for `F` analytic and nonzero at `g x`
  obtain ⟨F, hFan, hFne, hFev⟩ := hf'
  have aux1 : f ∘ g =ᶠ[𝓝[!=] x] (g · - g x) ^ r • (F ∘ g) := hFev.comp_tendsto (hg.map_nhdsNE hg_nc)
  have aux2 : meromorphicOrderAt (F ∘ g) x = 0 := by
    rw [AnalyticAt.meromorphicOrderAt_eq (by fun_prop)]; rw [analyticOrderAt_eq_zero.mpr (by exact .inr hFne)]; rw [ENat.map_zero]; rw [CharP.cast_eq_zero]; rw [WithTop.coe_zero]
  rw [meromorphicOrderAt_congr aux1]; rw [meromorphicOrderAt_smul ?_ (AnalyticAt.meromorphicAt ?_)]; rw [aux2]; rw [add_zero]; rw [meromorphicOrderAt_zpow]; rw [AnalyticAt.meromorphicOrderAt_eq] <;>
  fun_prop

/--
lemma `meromorphicOrderAt_comp_of_deriv_ne_zero` / 引理 `meromorphicOrderAt_comp_of_deriv_ne_zero`

English:
lemma meromorphicOrderAt_comp_of_deriv_ne_zero
  statement: (hg : AnalyticAt 𝕜 g x) (hg' : deriv g x != 0)
  proof: by
  by_cases hf : MeromorphicAt f (g x)
  · have hgo : analyticOrderAt _ x = 1 := hg.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hg'
    rw [hf.meromorphicOrderAt_comp hg]; rw [hgo] <;>
    simp [eventuallyConst_iff_analyticOrderAt_sub_eq_top, hgo]
  · rw [meromorphicOrderAt_of_not_meromorphicAt hf, meromorphicOrderAt_of_not_meromorphicAt]
    rwa [meromorphicAt_comp_iff_of_deriv_ne_zero hg hg']

中文:
引理 meromorphicOrderAt_comp_of_deriv_ne_zero
  结论: (hg : AnalyticAt 𝕜 g x) (hg' : deriv g x != 0)
  证明: by
  by_cases hf : MeromorphicAt f (g x)
  · have hgo : analyticOrderAt _ x = 1 := hg.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hg'
    rw [hf.meromorphicOrderAt_comp hg]; rw [hgo] <;>
    simp [eventuallyConst_iff_analyticOrderAt_sub_eq_top, hgo]
  · rw [meromorphicOrderAt_of_not_meromorphicAt hf, meromorphicOrderAt_of_not_meromorphicAt]
    rwa [meromorphicAt_comp_iff_of_deriv_ne_zero hg hg']

Depends on / 依赖: MeromorphicAt, analyticOrderAt, analyticOrderAt_sub_eq_one_of_deriv_ne_zero, eventuallyConst_iff_analyticOrderAt_sub_eq_top, hf.meromorphicOrderAt_comp, hg.analyticOrderAt_sub_eq_one_of_deriv_ne_zero, meromorphicAt_comp_iff_of_deriv_ne_zero, meromorphicOrderAt_comp, meromorphicOrderAt_of_not_meromorphicAt
-/
lemma meromorphicOrderAt_comp_of_deriv_ne_zero (hg : AnalyticAt 𝕜 g x) (hg' : deriv g x != 0)
    [CompleteSpace 𝕜] [CharZero 𝕜] :
    meromorphicOrderAt (f ∘ g) x = meromorphicOrderAt f (g x) := by
  by_cases hf : MeromorphicAt f (g x)
  · have hgo : analyticOrderAt _ x = 1 := hg.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hg'
    rw [hf.meromorphicOrderAt_comp hg]; rw [hgo] <;>
    simp [eventuallyConst_iff_analyticOrderAt_sub_eq_top, hgo]
  · rw [meromorphicOrderAt_of_not_meromorphicAt hf, meromorphicOrderAt_of_not_meromorphicAt]
    rwa [meromorphicAt_comp_iff_of_deriv_ne_zero hg hg']

/-- `meromorphicOrderAt` is invariant under translation. -/
@[to_fun meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt]
/--
theorem `meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt` / 定理 `meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt`

English:
theorem meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt
  given: {c : 𝕜} {f : 𝕜 -> E}
  proof: by
  classical
  by_cases h : ¬ MeromorphicAt f (x + c)
  · simp_all [meromorphicAt_comp_add_const_iff_meromorphicAt.not.2 h]
  rw [MeromorphicAt.meromorphicOrderAt_comp (by simp_all) (by fun_prop)
    (by simp [eventuallyConst_iff_analyticOrderAt_sub_eq_top])]
  simp

中文:
定理 meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt
  条件: {c : 𝕜} {f : 𝕜 -> E}
  证明: by
  classical
  by_cases h : ¬ MeromorphicAt f (x + c)
  · simp_all [meromorphicAt_comp_add_const_iff_meromorphicAt.not.2 h]
  rw [MeromorphicAt.meromorphicOrderAt_comp (by simp_all) (by fun_prop)
    (by simp [eventuallyConst_iff_analyticOrderAt_sub_eq_top])]
  simp

Depends on / 依赖: MeromorphicAt, MeromorphicAt.meromorphicOrderAt_comp, classical, eventuallyConst_iff_analyticOrderAt_sub_eq_top, fun_prop, meromorphicAt_comp_add_const_iff_meromorphicAt, meromorphicAt_comp_add_const_iff_meromorphicAt.not, meromorphicOrderAt_comp
-/
theorem meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt {c : 𝕜} {f : 𝕜 -> E} :
    meromorphicOrderAt (f ∘ (· + c)) x = meromorphicOrderAt f (x + c) := by
  classical
  by_cases h : ¬ MeromorphicAt f (x + c)
  · simp_all [meromorphicAt_comp_add_const_iff_meromorphicAt.not.2 h]
  rw [MeromorphicAt.meromorphicOrderAt_comp (by simp_all) (by fun_prop)
    (by simp [eventuallyConst_iff_analyticOrderAt_sub_eq_top])]
  simp

/-- `meromorphicOrderAt` is invariant under translation. -/
@[to_fun meromorphicOrderAt_fun_comp_sub_const_eq_meromorphicOrderAt]
/--
theorem `meromorphicOrderAt_comp_sub_const_eq_meromorphicOrderAt` / 定理 `meromorphicOrderAt_comp_sub_const_eq_meromorphicOrderAt`

English:
theorem meromorphicOrderAt_comp_sub_const_eq_meromorphicOrderAt
  given: {c : 𝕜} {f : 𝕜 -> E}
  proof: by
  simp_rw [sub_eq_add_neg, ← meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]

中文:
定理 meromorphicOrderAt_comp_sub_const_eq_meromorphicOrderAt
  条件: {c : 𝕜} {f : 𝕜 -> E}
  证明: by
  simp_rw [sub_eq_add_neg, ← meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]

Depends on / 依赖: meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt, simp_rw, sub_eq_add_neg
-/
theorem meromorphicOrderAt_comp_sub_const_eq_meromorphicOrderAt {c : 𝕜} {f : 𝕜 -> E} :
    meromorphicOrderAt (f ∘ (· - c)) x = meromorphicOrderAt f (x - c) := by
  simp_rw [sub_eq_add_neg, ← meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]

end comp

section smul

variable {g : 𝕜 -> 𝕜}

/--
lemma `meromorphicOrderAt_smul_of_ne_zero` / 引理 `meromorphicOrderAt_smul_of_ne_zero`

English:
lemma meromorphicOrderAt_smul_of_ne_zero
  given: (hg : AnalyticAt 𝕜 g x) (hg' : g x != 0)
  proof: by
  by_cases hf : MeromorphicAt f x
  · simp [meromorphicOrderAt_smul hg.meromorphicAt hf, hg.meromorphicOrderAt_eq,
      hg.analyticOrderAt_eq_zero.mpr hg']
  · rw [meromorphicOrderAt_of_not_meromorphicAt hf, meromorphicOrderAt_of_not_meromorphicAt]
    rwa [meromorphicAt_smul_iff_of_ne_zero hg hg']

中文:
引理 meromorphicOrderAt_smul_of_ne_zero
  条件: (hg : AnalyticAt 𝕜 g x) (hg' : g x != 0)
  证明: by
  by_cases hf : MeromorphicAt f x
  · simp [meromorphicOrderAt_smul hg.meromorphicAt hf, hg.meromorphicOrderAt_eq,
      hg.analyticOrderAt_eq_zero.mpr hg']
  · rw [meromorphicOrderAt_of_not_meromorphicAt hf, meromorphicOrderAt_of_not_meromorphicAt]
    rwa [meromorphicAt_smul_iff_of_ne_zero hg hg']

Depends on / 依赖: MeromorphicAt, analyticOrderAt_eq_zero, hg.analyticOrderAt_eq_zero.mpr, hg.meromorphicAt, hg.meromorphicOrderAt_eq, meromorphicAt, meromorphicAt_smul_iff_of_ne_zero, meromorphicOrderAt_eq, meromorphicOrderAt_of_not_meromorphicAt, meromorphicOrderAt_smul
-/
lemma meromorphicOrderAt_smul_of_ne_zero (hg : AnalyticAt 𝕜 g x) (hg' : g x != 0) :
    meromorphicOrderAt (g • f) x = meromorphicOrderAt f x := by
  by_cases hf : MeromorphicAt f x
  · simp [meromorphicOrderAt_smul hg.meromorphicAt hf, hg.meromorphicOrderAt_eq,
      hg.analyticOrderAt_eq_zero.mpr hg']
  · rw [meromorphicOrderAt_of_not_meromorphicAt hf, meromorphicOrderAt_of_not_meromorphicAt]
    rwa [meromorphicAt_smul_iff_of_ne_zero hg hg']

/--
lemma `meromorphicOrderAt_mul_of_ne_zero` / 引理 `meromorphicOrderAt_mul_of_ne_zero`

English:
lemma meromorphicOrderAt_mul_of_ne_zero
  given: {f : 𝕜 -> 𝕜} (hg : AnalyticAt 𝕜 g x) (hg' : g x != 0)
  proof: meromorphicOrderAt_smul_of_ne_zero hg hg'

中文:
引理 meromorphicOrderAt_mul_of_ne_zero
  条件: {f : 𝕜 -> 𝕜} (hg : AnalyticAt 𝕜 g x) (hg' : g x != 0)
  证明: meromorphicOrderAt_smul_of_ne_zero hg hg'

Depends on / 依赖: meromorphicOrderAt_smul_of_ne_zero
-/
lemma meromorphicOrderAt_mul_of_ne_zero {f : 𝕜 -> 𝕜} (hg : AnalyticAt 𝕜 g x) (hg' : g x != 0) :
    meromorphicOrderAt (g * f) x = meromorphicOrderAt f x :=
  meromorphicOrderAt_smul_of_ne_zero hg hg'

end smul

/-!
## Order at a Point of the Derivative
-/

section deriv

/--
lemma `meromorphicOrderAt_deriv_eq_sub_one` / 引理 `meromorphicOrderAt_deriv_eq_sub_one`

English:
lemma meromorphicOrderAt_deriv_eq_sub_one
  statement: [CompleteSpace E] {f : 𝕜 -> E} {x : 𝕜} {n : Int}
  proof: by
  have hmero : MeromorphicAt f x := meromorphicAt_of_meromorphicOrderAt_ne_zero (by aesop)
  rw [meromorphicOrderAt_eq_int_iff hmero] at hf
  rw [meromorphicOrderAt_eq_int_iff hmero.deriv]
  obtain ⟨g, hga, hg0, (hg : f =ᶠ[𝓝[!=] x] fun z => (z - x) ^ n • g z)⟩ := hf
  refine ⟨fun z => (n : 𝕜) • g z + (z - x) • deriv g z, by fun_prop, by simpa using ⟨hn, hg0⟩, ?_⟩
  filter_upwards [hga.eventually_analyticAt.filter_mono (nhdsWithin_le_nhds),
    eventually_mem_nhdsWithin, hg.nhdsNE_deriv] with z hgz hmem hz
  have hzx : z - x != 0 := by simpa [sub_eq_zero] using hmem
  calc
    deriv f z = deriv (fun z => (z - x) ^ n • g z) z :=
      hz
    _ = (z - x) ^ n • deriv g z + deriv ((· ^ n) ∘ (· - x)) z • g z :=
      deriv_fun_smul (by fun_prop (disch := grind)) hgz.differentiableAt
    _ = (z - x) ^ n • deriv g z + (n * (z - x) ^ (n - 1)) • g z := by
      rw [deriv_comp _ (by fun_prop (disch := grind)) (by fun_prop)]
      simp [deriv_zpow]
    _ = (z - x) ^ (n - 1) • ((n : 𝕜) • g z + (z - x) • deriv g z) := by
      simp [smul_smul, ← zpow_add_one₀ hzx, add_comm, mul_comm]

中文:
引理 meromorphicOrderAt_deriv_eq_sub_one
  结论: [完备空间 E] {f : 𝕜 -> E} {x : 𝕜} {n : 整数}
  证明: by
  have hmero : MeromorphicAt f x := meromorphicAt_of_meromorphicOrderAt_ne_zero (by aesop)
  rw [meromorphicOrderAt_eq_int_iff hmero] at hf
  rw [meromorphicOrderAt_eq_int_iff hmero.deriv]
  obtain ⟨g, hga, hg0, (hg : f =ᶠ[𝓝[!=] x] fun z => (z - x) ^ n • g z)⟩ := hf
  refine ⟨fun z => (n : 𝕜) • g z + (z - x) • deriv g z, by fun_prop, by simpa using ⟨hn, hg0⟩, ?_⟩
  filter_upwards [hga.eventually_analyticAt.filter_mono (nhdsWithin_le_nhds),
    eventually_mem_nhdsWithin, hg.nhdsNE_deriv] with z hgz hmem hz
  have hzx : z - x != 0 := by simpa [sub_eq_zero] using hmem
  calc
    deriv f z = deriv (fun z => (z - x) ^ n • g z) z :=
      hz
    _ = (z - x) ^ n • deriv g z + deriv ((· ^ n) ∘ (· - x)) z • g z :=
      deriv_fun_smul (by fun_prop (disch := grind)) hgz.differentiableAt
    _ = (z - x) ^ n • deriv g z + (n * (z - x) ^ (n - 1)) • g z := by
      rw [deriv_comp _ (by fun_prop (disch := grind)) (by fun_prop)]
      simp [deriv_zpow]
    _ = (z - x) ^ (n - 1) • ((n : 𝕜) • g z + (z - x) • deriv g z) := by
      simp [smul_smul, ← zpow_add_one₀ hzx, add_comm, mul_comm]

Depends on / 依赖: MeromorphicAt, eventually_analyticAt, eventually_mem_nhdsWithin, filter_mono, filter_upwards, fun_prop, hg.nhdsNE_deriv, hga.eventually_analyticAt.filter_mono, hmero.deriv, meromorphicAt_of_meromorphicOrderAt_ne_zero, meromorphicOrderAt_eq_int_iff, nhdsNE_deriv, nhdsWithin_le_nhds
-/
lemma meromorphicOrderAt_deriv_eq_sub_one [CompleteSpace E] {f : 𝕜 -> E} {x : 𝕜} {n : Int}
    (hn : (n : 𝕜) != 0) (hf : meromorphicOrderAt f x = ↑n) :
    meromorphicOrderAt (deriv f) x = ↑(n - 1) := by
  have hmero : MeromorphicAt f x := meromorphicAt_of_meromorphicOrderAt_ne_zero (by aesop)
  rw [meromorphicOrderAt_eq_int_iff hmero] at hf
  rw [meromorphicOrderAt_eq_int_iff hmero.deriv]
  obtain ⟨g, hga, hg0, (hg : f =ᶠ[𝓝[!=] x] fun z => (z - x) ^ n • g z)⟩ := hf
  refine ⟨fun z => (n : 𝕜) • g z + (z - x) • deriv g z, by fun_prop, by simpa using ⟨hn, hg0⟩, ?_⟩
  filter_upwards [hga.eventually_analyticAt.filter_mono (nhdsWithin_le_nhds),
    eventually_mem_nhdsWithin, hg.nhdsNE_deriv] with z hgz hmem hz
  have hzx : z - x != 0 := by simpa [sub_eq_zero] using hmem
  calc
    deriv f z = deriv (fun z => (z - x) ^ n • g z) z :=
      hz
    _ = (z - x) ^ n • deriv g z + deriv ((· ^ n) ∘ (· - x)) z • g z :=
      deriv_fun_smul (by fun_prop (disch := grind)) hgz.differentiableAt
    _ = (z - x) ^ n • deriv g z + (n * (z - x) ^ (n - 1)) • g z := by
      rw [deriv_comp _ (by fun_prop (disch := grind)) (by fun_prop)]
      simp [deriv_zpow]
    _ = (z - x) ^ (n - 1) • ((n : 𝕜) • g z + (z - x) • deriv g z) := by
      simp [smul_smul, ← zpow_add_one₀ hzx, add_comm, mul_comm]

/--
lemma `meromorphicOrderAt_deriv` / 引理 `meromorphicOrderAt_deriv`

English:
lemma meromorphicOrderAt_deriv
  statement: [CompleteSpace E] {f : 𝕜 -> E} {x : 𝕜} {n : Int}
  proof: by
  simpa using meromorphicOrderAt_deriv_eq_sub_one hn hf

中文:
引理 meromorphicOrderAt_deriv
  结论: [完备空间 E] {f : 𝕜 -> E} {x : 𝕜} {n : 整数}
  证明: by
  simpa using meromorphicOrderAt_deriv_eq_sub_one hn hf

Depends on / 依赖: CompleteSpace, meromorphicOrderAt_deriv_eq_sub_one, variable
-/
lemma meromorphicOrderAt_deriv [CompleteSpace E] {f : 𝕜 -> E} {x : 𝕜} {n : Int}
    (hn : (↑(n + 1) : 𝕜) != 0) (hf : meromorphicOrderAt f x = ↑(n + 1)) :
    meromorphicOrderAt (deriv f) x = ↑n := by
  simpa using meromorphicOrderAt_deriv_eq_sub_one hn hf
variable [CompleteSpace 𝕜] {f : 𝕜 -> 𝕜}

/--
theorem `meromorphicOrderAt_logDeriv_eq_neg_one` / 定理 `meromorphicOrderAt_logDeriv_eq_neg_one`

English:
theorem meromorphicOrderAt_logDeriv_eq_neg_one
  statement: [CharZero 𝕜] (hf : MeromorphicAt f x)
  proof: by
  lift meromorphicOrderAt f x to Int using h₂ with n hn
  rw [logDeriv]; rw [meromorphicOrderAt_div hf.deriv hf]; rw [meromorphicOrderAt_deriv_eq_sub_one (Int.cast_ne_zero.mpr (by exact_mod_cast h₁)) hn.symm]; rw [← hn]
  norm_cast
  simp

中文:
定理 meromorphicOrderAt_logDeriv_eq_neg_one
  结论: [特征零 𝕜] (hf : MeromorphicAt f x)
  证明: by
  lift meromorphicOrderAt f x to Int using h₂ with n hn
  rw [logDeriv]; rw [meromorphicOrderAt_div hf.deriv hf]; rw [meromorphicOrderAt_deriv_eq_sub_one (Int.cast_ne_zero.mpr (by exact_mod_cast h₁)) hn.symm]; rw [← hn]
  norm_cast
  simp

Depends on / 依赖: Int.cast_ne_zero.mpr, cast_ne_zero, hf.deriv, hn.symm, logDeriv, meromorphicOrderAt, meromorphicOrderAt_deriv_eq_sub_one, meromorphicOrderAt_div
-/
theorem meromorphicOrderAt_logDeriv_eq_neg_one [CharZero 𝕜] (hf : MeromorphicAt f x)
    (h₁ : meromorphicOrderAt f x != 0) (h₂ : meromorphicOrderAt f x != ⊤) :
    meromorphicOrderAt (logDeriv f) x = -1 := by
  lift meromorphicOrderAt f x to Int using h₂ with n hn
  rw [logDeriv]; rw [meromorphicOrderAt_div hf.deriv hf]; rw [meromorphicOrderAt_deriv_eq_sub_one (Int.cast_ne_zero.mpr (by exact_mod_cast h₁)) hn.symm]; rw [← hn]
  norm_cast
  simp

/--
theorem `meromorphicOrderAt_logDeriv_nonneg` / 定理 `meromorphicOrderAt_logDeriv_nonneg`

English:
theorem meromorphicOrderAt_logDeriv_nonneg
  statement: (hf : MeromorphicAt f x)
  proof: by
  obtain ⟨g, h₁g, h₂g, h₃g⟩ :=
    (meromorphicOrderAt_eq_int_iff (n := 0) hf).1 (by exact_mod_cast h)
  have h₄ : f =ᶠ[𝓝[!=] x] g := by
    filter_upwards [h₃g] with z hz using by simpa using hz
  rw [meromorphicOrderAt_congr (logDeriv_congr_nhdsNE h₄)]
  exact (h₁g.deriv.div h₁g h₂g).meromorphicOrderAt_nonneg

中文:
定理 meromorphicOrderAt_logDeriv_nonneg
  结论: (hf : MeromorphicAt f x)
  证明: by
  obtain ⟨g, h₁g, h₂g, h₃g⟩ :=
    (meromorphicOrderAt_eq_int_iff (n := 0) hf).1 (by exact_mod_cast h)
  have h₄ : f =ᶠ[𝓝[!=] x] g := by
    filter_upwards [h₃g] with z hz using by simpa using hz
  rw [meromorphicOrderAt_congr (logDeriv_congr_nhdsNE h₄)]
  exact (h₁g.deriv.div h₁g h₂g).meromorphicOrderAt_nonneg

Depends on / 依赖: filter_upwards, g.deriv.div, logDeriv_congr_nhdsNE, meromorphicOrderAt_congr, meromorphicOrderAt_eq_int_iff, meromorphicOrderAt_nonneg
-/
theorem meromorphicOrderAt_logDeriv_nonneg (hf : MeromorphicAt f x)
    (h : meromorphicOrderAt f x = 0) :
    0 <= meromorphicOrderAt (logDeriv f) x := by
  obtain ⟨g, h₁g, h₂g, h₃g⟩ :=
    (meromorphicOrderAt_eq_int_iff (n := 0) hf).1 (by exact_mod_cast h)
  have h₄ : f =ᶠ[𝓝[!=] x] g := by
    filter_upwards [h₃g] with z hz using by simpa using hz
  rw [meromorphicOrderAt_congr (logDeriv_congr_nhdsNE h₄)]
  exact (h₁g.deriv.div h₁g h₂g).meromorphicOrderAt_nonneg

end deriv
