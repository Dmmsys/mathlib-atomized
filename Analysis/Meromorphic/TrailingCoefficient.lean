/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Order

/-!
# The Trailing Coefficient of a Meromorphic Function

This file defines the trailing coefficient of a meromorphic function. If `f` is meromorphic at a
point `x`, the trailing coefficient is defined as the (unique!) value `g x` for a presentation of
`f` in the form `(z - x) ^ order • g z` with `g` analytic at `x`.

The lemma `MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt` expresses the trailing coefficient
as a limit.
-/

@[expose] public section

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f g : 𝕜 -> E} {x : 𝕜}

open Filter Topology

variable (f x) in
/--
Definition of `meromorphicTrailingCoeffAt` / `meromorphicTrailingCoeffAt` 的定义

English:
definition meromorphicTrailingCoeffAt
  signature: : E
  body: by
  by_cases h₁ : MeromorphicAt f x
  · by_cases h₂ : meromorphicOrderAt f x = ⊤
    · exact 0
    · exact ((meromorphicOrderAt_ne_top_iff h₁).1 h₂).choose x
  · exact 0

中文:
定义 meromorphicTrailingCoeffAt
  签名: : E
  定义体: by
  by_cases h₁ : MeromorphicAt f x
  · by_cases h₂ : meromorphicOrderAt f x = ⊤
    · exact 0
    · exact ((meromorphicOrderAt_ne_top_iff h₁).1 h₂).choose x
  · exact 0

Depends on / 依赖: MeromorphicAt, meromorphicOrderAt, meromorphicOrderAt_ne_top_iff
-/
noncomputable def meromorphicTrailingCoeffAt : E := by
  by_cases h₁ : MeromorphicAt f x
  · by_cases h₂ : meromorphicOrderAt f x = ⊤
    · exact 0
    · exact ((meromorphicOrderAt_ne_top_iff h₁).1 h₂).choose x
  · exact 0

/--
lemma `meromorphicTrailingCoeffAt_of_not_MeromorphicAt` / 引理 `meromorphicTrailingCoeffAt_of_not_MeromorphicAt`

English:
lemma meromorphicTrailingCoeffAt_of_not_MeromorphicAt
  given: (h : ¬MeromorphicAt f x)
  proof: by simp [meromorphicTrailingCoeffAt, h]

中文:
引理 meromorphicTrailingCoeffAt_of_not_MeromorphicAt
  条件: (h : ¬MeromorphicAt f x)
  证明: by simp [meromorphicTrailingCoeffAt, h]
-/
@[simp] lemma meromorphicTrailingCoeffAt_of_not_MeromorphicAt (h : ¬MeromorphicAt f x) :
    meromorphicTrailingCoeffAt f x = 0 := by simp [meromorphicTrailingCoeffAt, h]

/--
lemma `MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top` / 引理 `MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top`

English:
lemma MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top
  proof: by simp_all [meromorphicTrailingCoeffAt]

中文:
引理 MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top
  证明: by simp_all [meromorphicTrailingCoeffAt]
-/
@[simp] lemma MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top
    (h : meromorphicOrderAt f x = ⊤) :
    meromorphicTrailingCoeffAt f x = 0 := by simp_all [meromorphicTrailingCoeffAt]

/-!
## Characterization of the Trailing Coefficient
-/

/--
lemma `AnalyticAt.meromorphicTrailingCoeffAt_of_eq_nhdsNE` / 引理 `AnalyticAt.meromorphicTrailingCoeffAt_of_eq_nhdsNE`

English:
lemma AnalyticAt.meromorphicTrailingCoeffAt_of_eq_nhdsNE
  statement: (h₁g : AnalyticAt 𝕜 g x)
  proof: by
  have h₁f : MeromorphicAt f x := by
    rw [MeromorphicAt.meromorphicAt_congr h]
    fun_prop
  by_cases h₃ : meromorphicOrderAt f x = ⊤
  · simp only [h₃, WithTop.untop₀_top, zpow_zero, one_smul,
      MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top] at ⊢ h
    apply EventuallyEq.eq_of

中文:
引理 AnalyticAt.meromorphicTrailingCoeffAt_of_eq_nhdsNE
  结论: (h₁g : AnalyticAt 𝕜 g x)
  证明: by
  have h₁f : MeromorphicAt f x := by
    rw [MeromorphicAt.meromorphicAt_congr h]
    fun_prop
  by_cases h₃ : meromorphicOrderAt f x = ⊤
  · simp only [h₃, WithTop.untop₀_top, zpow_zero, one_smul,
      MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top] at ⊢ h
    apply EventuallyEq.eq_of

Depends on / 依赖: ContinuousAt, ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE, EventuallyEq, EventuallyEq.eq_of_nhds, MeromorphicAt, MeromorphicAt.meromorphicAt_congr, MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top, WithTop, WithTop.untop, eq_of_nhds, eventuallyEq_nhds_iff_eventuallyEq_nhdsNE, fun_prop, h.symm.trans, meromorphicAt_congr, meromorphicOrderAt, meromorphicOrderAt_eq_top_iff, meromorphicTrailingCoeffAt, meromorphicTrailingCoeffAt_of_order_eq_top, one_smul, zpow_zero
-/
lemma AnalyticAt.meromorphicTrailingCoeffAt_of_eq_nhdsNE (h₁g : AnalyticAt 𝕜 g x)
    (h : f =ᶠ[𝓝[!=] x] fun z => (z - x) ^ (meromorphicOrderAt f x).untop₀ • g z) :
    meromorphicTrailingCoeffAt f x = g x := by
  have h₁f : MeromorphicAt f x := by
    rw [MeromorphicAt.meromorphicAt_congr h]
    fun_prop
  by_cases h₃ : meromorphicOrderAt f x = ⊤
  · simp only [h₃, WithTop.untop₀_top, zpow_zero, one_smul,
      MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top] at ⊢ h
    apply EventuallyEq.eq_of_nhds (f := 0)
    rw [← ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (by fun_prop) (by fun_prop)]
    apply (h.symm.trans (meromorphicOrderAt_eq_top_iff.1 h₃)).symm
  · unfold meromorphicTrailingCoeffAt
    simp only [h₁f, reduceDIte, h₃, ne_eq]
    obtain ⟨h'₁, h'₂, h'₃⟩ := ((meromorphicOrderAt_ne_top_iff h₁f).1 h₃).choose_spec
    apply Filter.EventuallyEq.eq_of_nhds
    rw [← h'₁.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE h₁g.continuousAt]
    filter_upwards [h, h'₃, self_mem_nhdsWithin] with y h₁y h₂y h₃y
    rw [← sub_eq_zero]
    rwa [h₂y, ← sub_eq_zero, ← smul_sub, smul_eq_zero_iff_right] at h₁y
    simp_all [zpow_ne_zero, sub_ne_zero]

/--
lemma `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE` / 引理 `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE`

English:
lemma AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
  statement: {n : Int} (h₁g : AnalyticAt 𝕜 g x)
  proof: by
  have h₄ : MeromorphicAt f x := by
    rw [MeromorphicAt.meromorphicAt_congr h]
    fun_prop
  have : meromorphicOrderAt f x = n := by
    simp only [meromorphicOrderAt_eq_int_iff h₄, ne_eq]
    use g, h₁g, h₂g
    exact h
  simp_all [meromorphicTrailingCoeffAt_of_eq_nhdsNE h₁g]

中文:
引理 AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
  结论: {n : 整数} (h₁g : AnalyticAt 𝕜 g x)
  证明: by
  have h₄ : MeromorphicAt f x := by
    rw [MeromorphicAt.meromorphicAt_congr h]
    fun_prop
  have : meromorphicOrderAt f x = n := by
    simp only [meromorphicOrderAt_eq_int_iff h₄, ne_eq]
    use g, h₁g, h₂g
    exact h
  simp_all [meromorphicTrailingCoeffAt_of_eq_nhdsNE h₁g]

Depends on / 依赖: MeromorphicAt, MeromorphicAt.meromorphicAt_congr, fun_prop, meromorphicAt_congr, meromorphicOrderAt, meromorphicOrderAt_eq_int_iff, meromorphicTrailingCoeffAt_of_eq_nhdsNE, ne_eq
-/
lemma AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE {n : Int} (h₁g : AnalyticAt 𝕜 g x)
    (h₂g : g x != 0) (h : f =ᶠ[𝓝[!=] x] fun z => (z - x) ^ n • g z) :
    meromorphicTrailingCoeffAt f x = g x := by
  have h₄ : MeromorphicAt f x := by
    rw [MeromorphicAt.meromorphicAt_congr h]
    fun_prop
  have : meromorphicOrderAt f x = n := by
    simp only [meromorphicOrderAt_eq_int_iff h₄, ne_eq]
    use g, h₁g, h₂g
    exact h
  simp_all [meromorphicTrailingCoeffAt_of_eq_nhdsNE h₁g]

/--
If `f` is analytic and does not vanish at `x`, then the trailing coefficient of `f` at `x` is `f x`.
-/
@[simp]
/--
lemma `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero` / 引理 `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero`

English:
lemma AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero
  given: (h₁ : AnalyticAt 𝕜 f x) (h₂ : f x != 0)
  proof: by
  rw [h₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := 0) h₂]
  filter_upwards
  simp

中文:
引理 AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero
  条件: (h₁ : AnalyticAt 𝕜 f x) (h₂ : f x != 0)
  证明: by
  rw [h₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := 0) h₂]
  filter_upwards
  simp

Depends on / 依赖: filter_upwards, meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
-/
lemma AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero (h₁ : AnalyticAt 𝕜 f x) (h₂ : f x != 0) :
    meromorphicTrailingCoeffAt f x = f x := by
  rw [h₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := 0) h₂]
  filter_upwards
  simp

/--
lemma `MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt` / 引理 `MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt`

English:
lemma MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt
  given: (h : MeromorphicAt f x)
  proof: by
  by_cases h₂ : meromorphicOrderAt f x = ⊤
  · simp_all only [WithTop.untop₀_top, neg_zero, zpow_zero, one_smul,
      meromorphicTrailingCoeffAt_of_order_eq_top]
    apply Tendsto.congr' (f₁ := 0)
    · filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₂] with y hy
      simp_all
    · apply Tend

中文:
引理 MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt
  条件: (h : MeromorphicAt f x)
  证明: by
  by_cases h₂ : meromorphicOrderAt f x = ⊤
  · simp_all only [WithTop.untop₀_top, neg_zero, zpow_zero, one_smul,
      meromorphicTrailingCoeffAt_of_order_eq_top]
    apply Tendsto.congr' (f₁ := 0)
    · filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₂] with y hy
      simp_all
    · apply Tend

Depends on / 依赖: Tendsto, Tendsto.congr, WithTop, WithTop.untop, continuousWithinAt_const, continuousWithinAt_const.tendsto, filter_upwards, meromorphicOrderAt, meromorphicOrderAt_eq_top_iff, meromorphicOrderAt_ne_top_iff, meromorphicTrailingCoeffAt_of_order_eq_top, neg_zero, one_smul, self_mem_nhdsWithin, tendsto, zpow_zero
-/
lemma MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt (h : MeromorphicAt f x) :
    Tendsto ((· - x) ^ (-(meromorphicOrderAt f x).untop₀) • f) (𝓝[!=] x)
      (𝓝 (meromorphicTrailingCoeffAt f x)) := by
  by_cases h₂ : meromorphicOrderAt f x = ⊤
  · simp_all only [WithTop.untop₀_top, neg_zero, zpow_zero, one_smul,
      meromorphicTrailingCoeffAt_of_order_eq_top]
    apply Tendsto.congr' (f₁ := 0)
    · filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₂] with y hy
      simp_all
    · apply Tendsto.congr' (f₁ := 0) (by rfl) continuousWithinAt_const.tendsto
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff h).1 h₂
  apply Tendsto.congr' (f₁ := g)
  · filter_upwards [h₃g, self_mem_nhdsWithin] with y h₁y h₂y
    rw [zpow_neg]; rw [Pi.smul_apply']; rw [Pi.inv_apply]; rw [Pi.pow_apply]; rw [h₁y]; rw [← smul_assoc]; rw [smul_eq_mul]; rw [← zpow_neg]; rw [← zpow_add']; rw [neg_add_cancel]; rw [zpow_zero]; rw [one_smul]
    left
    simp_all [sub_ne_zero]
  · rw [h₁g.meromorphicTrailingCoeffAt_of_eq_nhdsNE h₃g]
    apply h₁g.continuousAt.continuousWithinAt

/-!
## Elementary Properties
-/

/--
lemma `MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero` / 引理 `MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero`

English:
lemma MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero
  statement: (h₁ : MeromorphicAt f x)
  proof: by
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff h₁).1 h₂
  simpa [h₁g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g h₃g] using h₂g

中文:
引理 MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero
  结论: (h₁ : MeromorphicAt f x)
  证明: by
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff h₁).1 h₂
  simpa [h₁g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g h₃g] using h₂g

Depends on / 依赖: g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE, meromorphicOrderAt_ne_top_iff, meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero (h₁ : MeromorphicAt f x)
    (h₂ : meromorphicOrderAt f x != ⊤) :
    meromorphicTrailingCoeffAt f x != 0 := by
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff h₁).1 h₂
  simpa [h₁g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g h₃g] using h₂g

/--
The trailing coefficient of a constant function is the constant.
-/
@[simp]
/--
theorem `meromorphicTrailingCoeffAt_const` / 定理 `meromorphicTrailingCoeffAt_const`

English:
theorem meromorphicTrailingCoeffAt_const
  given: {x : 𝕜} {e : 𝕜}
  proof: by
  by_cases he : e = 0
  · rw [he]
    apply MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top
    rw [meromorphicOrderAt_eq_top_iff]
    simp
  · exact analyticAt_const.meromorphicTrailingCoeffAt_of_ne_zero he

中文:
定理 meromorphicTrailingCoeffAt_const
  条件: {x : 𝕜} {e : 𝕜}
  证明: by
  by_cases he : e = 0
  · rw [he]
    apply MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top
    rw [meromorphicOrderAt_eq_top_iff]
    simp
  · exact analyticAt_const.meromorphicTrailingCoeffAt_of_ne_zero he

Depends on / 依赖: MeromorphicAt, MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top, analyticAt_const, analyticAt_const.meromorphicTrailingCoeffAt_of_ne_zero, meromorphicOrderAt_eq_top_iff, meromorphicTrailingCoeffAt_of_ne_zero, meromorphicTrailingCoeffAt_of_order_eq_top
-/
theorem meromorphicTrailingCoeffAt_const {x : 𝕜} {e : 𝕜} :
    meromorphicTrailingCoeffAt (fun _ => e) x = e := by
  by_cases he : e = 0
  · rw [he]
    apply MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top
    rw [meromorphicOrderAt_eq_top_iff]
    simp
  · exact analyticAt_const.meromorphicTrailingCoeffAt_of_ne_zero he

/--
theorem `meromorphicTrailingCoeffAt_id_sub_const` / 定理 `meromorphicTrailingCoeffAt_id_sub_const`

English:
theorem meromorphicTrailingCoeffAt_id_sub_const
  given: [DecidableEq 𝕜] {x y : 𝕜}
  proof: by
  by_cases h : x = y
  · simp_all only [sub_self, ite_true]
    apply AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := 1) (by fun_prop)
      (by apply one_ne_zero)
    simp
  · simp_all only [ite_false]
    apply AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero (by fun_prop)
 

中文:
定理 meromorphicTrailingCoeffAt_id_sub_const
  条件: [DecidableEq 𝕜] {x y : 𝕜}
  证明: by
  by_cases h : x = y
  · simp_all only [sub_self, ite_true]
    apply AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := 1) (by fun_prop)
      (by apply one_ne_zero)
    simp
  · simp_all only [ite_false]
    apply AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero (by fun_prop)
 

Depends on / 依赖: AnalyticAt, AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero, AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE, fun_prop, ite_false, ite_true, meromorphicTrailingCoeffAt_of_ne_zero, meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE, one_ne_zero, sub_ne_zero, sub_self
-/
theorem meromorphicTrailingCoeffAt_id_sub_const [DecidableEq 𝕜] {x y : 𝕜} :
    meromorphicTrailingCoeffAt (· - y) x = if x = y then 1 else x - y := by
  by_cases h : x = y
  · simp_all only [sub_self, ite_true]
    apply AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := 1) (by fun_prop)
      (by apply one_ne_zero)
    simp
  · simp_all only [ite_false]
    apply AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero (by fun_prop)
    simp_all [sub_ne_zero]

/-!
## Congruence Lemma
-/

/--
lemma `meromorphicTrailingCoeffAt_congr_nhdsNE` / 引理 `meromorphicTrailingCoeffAt_congr_nhdsNE`

English:
lemma meromorphicTrailingCoeffAt_congr_nhdsNE
  given: {f₁ f₂ : 𝕜 -> E} (h : f₁ =ᶠ[𝓝[!=] x] f₂)
  proof: by
  by_cases h₁ : ¬MeromorphicAt f₁ x
  · simp [h₁, (MeromorphicAt.meromorphicAt_congr h).not.1 h₁]
  rw [not_not] at h₁
  by_cases h₂ : meromorphicOrderAt f₁ x = ⊤
  · simp_all [meromorphicOrderAt_congr h]
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff h₁).1 h₂
  rw [h₁g.meromorphic

中文:
引理 meromorphicTrailingCoeffAt_congr_nhdsNE
  条件: {f₁ f₂ : 𝕜 -> E} (h : f₁ =ᶠ[𝓝[!=] x] f₂)
  证明: by
  by_cases h₁ : ¬MeromorphicAt f₁ x
  · simp [h₁, (MeromorphicAt.meromorphicAt_congr h).not.1 h₁]
  rw [not_not] at h₁
  by_cases h₂ : meromorphicOrderAt f₁ x = ⊤
  · simp_all [meromorphicOrderAt_congr h]
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff h₁).1 h₂
  rw [h₁g.meromorphic

Depends on / 依赖: MeromorphicAt, MeromorphicAt.meromorphicAt_congr, g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE, h.symm.trans, meromorphicAt_congr, meromorphicOrderAt, meromorphicOrderAt_congr, meromorphicOrderAt_ne_top_iff, meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE, not_not
-/
lemma meromorphicTrailingCoeffAt_congr_nhdsNE {f₁ f₂ : 𝕜 -> E} (h : f₁ =ᶠ[𝓝[!=] x] f₂) :
    meromorphicTrailingCoeffAt f₁ x = meromorphicTrailingCoeffAt f₂ x := by
  by_cases h₁ : ¬MeromorphicAt f₁ x
  · simp [h₁, (MeromorphicAt.meromorphicAt_congr h).not.1 h₁]
  rw [not_not] at h₁
  by_cases h₂ : meromorphicOrderAt f₁ x = ⊤
  · simp_all [meromorphicOrderAt_congr h]
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff h₁).1 h₂
  rw [h₁g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g h₃g]; rw [h₁g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g (h.symm.trans h₃g)]

/-!
## Behavior under Arithmetic Operations
-/

/--
theorem `meromorphicTrailingCoeffAt_neg` / 定理 `meromorphicTrailingCoeffAt_neg`

English:
theorem meromorphicTrailingCoeffAt_neg
  given: {f : 𝕜 -> E}
  proof: by
  by_cases h₁ : ¬ MeromorphicAt f x
  · aesop
  rw [not_not] at h₁
  by_cases h₂ : meromorphicOrderAt f x = ⊤
  · simp_all [← meromorphicOrderAt_neg]
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff h₁).1 h₂
  rw [h₁g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g h₃g]
  rw [

中文:
定理 meromorphicTrailingCoeffAt_neg
  条件: {f : 𝕜 -> E}
  证明: by
  by_cases h₁ : ¬ MeromorphicAt f x
  · aesop
  rw [not_not] at h₁
  by_cases h₂ : meromorphicOrderAt f x = ⊤
  · simp_all [← meromorphicOrderAt_neg]
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff h₁).1 h₂
  rw [h₁g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g h₃g]
  rw [

Depends on / 依赖: AnalyticAt, AnalyticAt.meromorphicTrailingCoeffAt_of_eq_nhdsNE, MeromorphicAt, filter_upwards, fun_prop, g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE, meromorphicOrderAt, meromorphicOrderAt_ne_top_iff, meromorphicOrderAt_neg, meromorphicTrailingCoeffAt_of_eq_nhdsNE, meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE, not_not
-/
theorem meromorphicTrailingCoeffAt_neg {f : 𝕜 -> E} :
    meromorphicTrailingCoeffAt (-f) x = -meromorphicTrailingCoeffAt f x := by
  by_cases h₁ : ¬ MeromorphicAt f x
  · aesop
  rw [not_not] at h₁
  by_cases h₂ : meromorphicOrderAt f x = ⊤
  · simp_all [← meromorphicOrderAt_neg]
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff h₁).1 h₂
  rw [h₁g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g h₃g]
  rw [AnalyticAt.meromorphicTrailingCoeffAt_of_eq_nhdsNE (g := -g)]
  · simp
  · fun_prop
  · filter_upwards [h₃g] with a ha
    simp [ha, ← meromorphicOrderAt_neg]

/--
theorem `meromorphicTrailingCoeffAt_fun_neg` / 定理 `meromorphicTrailingCoeffAt_fun_neg`

English:
theorem meromorphicTrailingCoeffAt_fun_neg
  given: {f : 𝕜 -> E}
  proof: meromorphicTrailingCoeffAt_neg

中文:
定理 meromorphicTrailingCoeffAt_fun_neg
  条件: {f : 𝕜 -> E}
  证明: meromorphicTrailingCoeffAt_neg

Depends on / 依赖: meromorphicTrailingCoeffAt_neg
-/
theorem meromorphicTrailingCoeffAt_fun_neg {f : 𝕜 -> E} :
    meromorphicTrailingCoeffAt (fun z => -f z) x = -meromorphicTrailingCoeffAt f x :=
  meromorphicTrailingCoeffAt_neg

/--
theorem `MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt` / 定理 `MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt`

English:
theorem MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt
  statement: {f₁ f₂ : 𝕜 -> E}
  proof: by
  -- Trivial case: f₁ not meromorphic at x
  by_cases! hf₁ : ¬MeromorphicAt f₁ x
  · have : ¬MeromorphicAt (f₁ + f₂) x := by
      rwa [add_comm, hf₂.meromorphicAt_add_iff_meromorphicAt₁]
    simp_all
  -- Trivial case: f₂ vanishes locally around x
  by_cases h₁f₂ : meromorphicOrderAt f₂ x = ⊤
  

中文:
定理 MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt
  结论: {f₁ f₂ : 𝕜 -> E}
  证明: by
  -- Trivial case: f₁ not meromorphic at x
  by_cases! hf₁ : ¬MeromorphicAt f₁ x
  · have : ¬MeromorphicAt (f₁ + f₂) x := by
      rwa [add_comm, hf₂.meromorphicAt_add_iff_meromorphicAt₁]
    simp_all
  -- Trivial case: f₂ vanishes locally around x
  by_cases h₁f₂ : meromorphicOrderAt f₂ x = ⊤
  
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt {f₁ f₂ : 𝕜 -> E}
    (hf₂ : MeromorphicAt f₂ x) (h : meromorphicOrderAt f₁ x < meromorphicOrderAt f₂ x) :
    meromorphicTrailingCoeffAt (f₁ + f₂) x = meromorphicTrailingCoeffAt f₁ x := by
  -- Trivial case: f₁ not meromorphic at x
  by_cases! hf₁ : ¬MeromorphicAt f₁ x
  · have : ¬MeromorphicAt (f₁ + f₂) x := by
      rwa [add_comm, hf₂.meromorphicAt_add_iff_meromorphicAt₁]
    simp_all
  -- Trivial case: f₂ vanishes locally around x
  by_cases h₁f₂ : meromorphicOrderAt f₂ x = ⊤
  · apply meromorphicTrailingCoeffAt_congr_nhdsNE
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₁f₂]
    simp
  -- General case
  lift meromorphicOrderAt f₂ x to Int using h₁f₂ with n₂ hn₂
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_eq_int_iff hf₂).1 hn₂.symm
  lift meromorphicOrderAt f₁ x to Int using (by aesop) with n₁ hn₁
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 hn₁.symm
  rw [WithTop.coe_lt_coe] at h
  have τ₀ : forallᶠ z in 𝓝[!=] x, (f₁ + f₂) z = (z - x) ^ n₁ • (g₁ + (z - x) ^ (n₂ - n₁) • g₂) z := by
    filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin] with z h₁z h₂z h₃z
    simp only [Pi.add_apply, h₁z, h₂z, Pi.smul_apply, smul_add, ← smul_assoc, smul_eq_mul,
      add_right_inj]
    rw [← zpow_add₀]; rw [add_sub_cancel]
    simp_all [sub_ne_zero]
  have τ₁ : AnalyticAt 𝕜 (fun z => g₁ z + (z - x) ^ (n₂ - n₁) • g₂ z) x :=
    h₁g₁.fun_add (AnalyticAt.fun_smul (AnalyticAt.fun_zpow_nonneg (by fun_prop)
      (sub_nonneg_of_le h.le)) h₁g₂)
  have τ₂ : g₁ x + (x - x) ^ (n₂ - n₁) • g₂ x != 0 := by
    simp_all [zero_zpow _ (sub_ne_zero.2 (ne_of_lt h).symm)]
  rw [h₁g₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₁ h₃g₁]; rw [τ₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE τ₂ τ₀]; rw [sub_self]; rw [add_eq_left]; rw [smul_eq_zero]; rw [zero_zpow _ (sub_ne_zero.2 (ne_of_lt h).symm)]
  tauto

/--
theorem `MeromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_left_of_lt` / 定理 `MeromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_left_of_lt`

English:
theorem MeromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_left_of_lt
  statement: {f₁ f₂ : 𝕜 -> E}
  proof: MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt hf₂ h

中文:
定理 MeromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_left_of_lt
  结论: {f₁ f₂ : 𝕜 -> E}
  证明: MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt hf₂ h

Depends on / 依赖: MeromorphicAt, MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt, meromorphicTrailingCoeffAt_add_eq_left_of_lt
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_left_of_lt {f₁ f₂ : 𝕜 -> E}
    (hf₂ : MeromorphicAt f₂ x) (h : meromorphicOrderAt f₁ x < meromorphicOrderAt f₂ x) :
    meromorphicTrailingCoeffAt (fun z => f₁ z + f₂ z) x = meromorphicTrailingCoeffAt f₁ x :=
  MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt hf₂ h

/--
theorem `MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_left_of_lt` / 定理 `MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_left_of_lt`

English:
theorem MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_left_of_lt
  statement: {f₁ f₂ : 𝕜 -> E}
  proof: by
  rw [sub_eq_add_neg]
  apply MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt (by fun_prop)
  rwa [← meromorphicOrderAt_neg]

中文:
定理 MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_left_of_lt
  结论: {f₁ f₂ : 𝕜 -> E}
  证明: by
  rw [sub_eq_add_neg]
  apply MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt (by fun_prop)
  rwa [← meromorphicOrderAt_neg]

Depends on / 依赖: MeromorphicAt, MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt, fun_prop, meromorphicOrderAt_neg, meromorphicTrailingCoeffAt_add_eq_left_of_lt, sub_eq_add_neg
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_left_of_lt {f₁ f₂ : 𝕜 -> E}
    (hf₂ : MeromorphicAt f₂ x) (h : meromorphicOrderAt f₁ x < meromorphicOrderAt f₂ x) :
    meromorphicTrailingCoeffAt (f₁ - f₂) x = meromorphicTrailingCoeffAt f₁ x := by
  rw [sub_eq_add_neg]
  apply MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt (by fun_prop)
  rwa [← meromorphicOrderAt_neg]

/--
theorem `MeromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt` / 定理 `MeromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt`

English:
theorem MeromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt
  statement: {f₁ f₂ : 𝕜 -> E}
  proof: MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_left_of_lt hf₂ h

中文:
定理 MeromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt
  结论: {f₁ f₂ : 𝕜 -> E}
  证明: MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_left_of_lt hf₂ h

Depends on / 依赖: MeromorphicAt, MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_left_of_lt, meromorphicTrailingCoeffAt_sub_eq_left_of_lt
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt {f₁ f₂ : 𝕜 -> E}
    (hf₂ : MeromorphicAt f₂ x) (h : meromorphicOrderAt f₁ x < meromorphicOrderAt f₂ x) :
    meromorphicTrailingCoeffAt (fun z => f₁ z - f₂ z) x = meromorphicTrailingCoeffAt f₁ x :=
  MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_left_of_lt hf₂ h

/--
theorem `MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_add` / 定理 `MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_add`

English:
theorem MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_add
  statement: {f₁ f₂ : 𝕜 -> E}
  proof: by
  -- Trivial case: f₁ vanishes locally around x
  by_cases h₁f₁ : meromorphicOrderAt f₁ x = ⊤
  · rw [meromorphicTrailingCoeffAt_of_order_eq_top h₁f₁, zero_add]
    apply meromorphicTrailingCoeffAt_congr_nhdsNE
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₁f₁]
    simp
  -- General case
 

中文:
定理 MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_add
  结论: {f₁ f₂ : 𝕜 -> E}
  证明: by
  -- Trivial case: f₁ vanishes locally around x
  by_cases h₁f₁ : meromorphicOrderAt f₁ x = ⊤
  · rw [meromorphicTrailingCoeffAt_of_order_eq_top h₁f₁, zero_add]
    apply meromorphicTrailingCoeffAt_congr_nhdsNE
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₁f₁]
    simp
  -- General case
 
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_add {f₁ f₂ : 𝕜 -> E}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h₁ : meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x)
    (h₂ : meromorphicTrailingCoeffAt f₁ x + meromorphicTrailingCoeffAt f₂ x != 0) :
    meromorphicTrailingCoeffAt (f₁ + f₂) x
      = meromorphicTrailingCoeffAt f₁ x + meromorphicTrailingCoeffAt f₂ x := by
  -- Trivial case: f₁ vanishes locally around x
  by_cases h₁f₁ : meromorphicOrderAt f₁ x = ⊤
  · rw [meromorphicTrailingCoeffAt_of_order_eq_top h₁f₁, zero_add]
    apply meromorphicTrailingCoeffAt_congr_nhdsNE
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₁f₁]
    simp
  -- General case
  lift meromorphicOrderAt f₁ x to Int using (by lia) with n₁ hn₁
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 hn₁.symm
  lift meromorphicOrderAt f₂ x to Int using (by lia) with n₂ hn₂
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_eq_int_iff hf₂).1 hn₂.symm
  rw [WithTop.coe_eq_coe]; rw [h₁g₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₁ h₃g₁]; rw [h₁g₂.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₂ h₃g₂] at *
  have τ₀ : forallᶠ z in 𝓝[!=] x, (f₁ + f₂) z = (z - x) ^ n₁ • (g₁ + g₂) z := by
    filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin] with z h₁z h₂z h₃z
    simp_all
  simp [AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (by fun_prop)
    (by simp_all) τ₀]

/--
theorem `MeromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_add` / 定理 `MeromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_add`

English:
theorem MeromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_add
  statement: {f₁ f₂ : 𝕜 -> E}
  proof: MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_add hf₁ hf₂ h₁ h₂

中文:
定理 MeromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_add
  结论: {f₁ f₂ : 𝕜 -> E}
  证明: MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_add hf₁ hf₂ h₁ h₂

Depends on / 依赖: MeromorphicAt, MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_add, meromorphicTrailingCoeffAt_add_eq_add
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_add {f₁ f₂ : 𝕜 -> E}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h₁ : meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x)
    (h₂ : meromorphicTrailingCoeffAt f₁ x + meromorphicTrailingCoeffAt f₂ x != 0) :
    meromorphicTrailingCoeffAt (fun z => f₁ z + f₂ z) x
      = meromorphicTrailingCoeffAt f₁ x + meromorphicTrailingCoeffAt f₂ x :=
  MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_add hf₁ hf₂ h₁ h₂

/--
theorem `MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_sub` / 定理 `MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_sub`

English:
theorem MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_sub
  statement: {f₁ f₂ : 𝕜 -> E}
  proof: by
  rw [sub_eq_add_neg]; rw [hf₁.meromorphicTrailingCoeffAt_add_eq_add (by fun_prop)]
  · rw [meromorphicTrailingCoeffAt_neg, sub_eq_add_neg]
  · rwa [← meromorphicOrderAt_neg]
  · rwa [meromorphicTrailingCoeffAt_neg, ← sub_eq_add_neg]

中文:
定理 MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_sub
  结论: {f₁ f₂ : 𝕜 -> E}
  证明: by
  rw [sub_eq_add_neg]; rw [hf₁.meromorphicTrailingCoeffAt_add_eq_add (by fun_prop)]
  · rw [meromorphicTrailingCoeffAt_neg, sub_eq_add_neg]
  · rwa [← meromorphicOrderAt_neg]
  · rwa [meromorphicTrailingCoeffAt_neg, ← sub_eq_add_neg]

Depends on / 依赖: fun_prop, meromorphicOrderAt_neg, meromorphicTrailingCoeffAt_add_eq_add, meromorphicTrailingCoeffAt_neg, sub_eq_add_neg
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_sub {f₁ f₂ : 𝕜 -> E}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h₁ : meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x)
    (h₂ : meromorphicTrailingCoeffAt f₁ x - meromorphicTrailingCoeffAt f₂ x != 0) :
    meromorphicTrailingCoeffAt (f₁ - f₂) x
      = meromorphicTrailingCoeffAt f₁ x - meromorphicTrailingCoeffAt f₂ x := by
  rw [sub_eq_add_neg]; rw [hf₁.meromorphicTrailingCoeffAt_add_eq_add (by fun_prop)]
  · rw [meromorphicTrailingCoeffAt_neg, sub_eq_add_neg]
  · rwa [← meromorphicOrderAt_neg]
  · rwa [meromorphicTrailingCoeffAt_neg, ← sub_eq_add_neg]

/--
theorem `MeromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_sub` / 定理 `MeromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_sub`

English:
theorem MeromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_sub
  statement: {f₁ f₂ : 𝕜 -> E}
  proof: MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_sub hf₁ hf₂ h₁ h₂

中文:
定理 MeromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_sub
  结论: {f₁ f₂ : 𝕜 -> E}
  证明: MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_sub hf₁ hf₂ h₁ h₂

Depends on / 依赖: MeromorphicAt, MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_sub, meromorphicTrailingCoeffAt_sub_eq_sub
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_sub {f₁ f₂ : 𝕜 -> E}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h₁ : meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x)
    (h₂ : meromorphicTrailingCoeffAt f₁ x - meromorphicTrailingCoeffAt f₂ x != 0) :
    meromorphicTrailingCoeffAt (fun z => f₁ z - f₂ z) x
      = meromorphicTrailingCoeffAt f₁ x - meromorphicTrailingCoeffAt f₂ x :=
  MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_sub hf₁ hf₂ h₁ h₂

/--
lemma `MeromorphicAt.meromorphicTrailingCoeffAt_smul` / 引理 `MeromorphicAt.meromorphicTrailingCoeffAt_smul`

English:
lemma MeromorphicAt.meromorphicTrailingCoeffAt_smul
  statement: {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 -> E}
  proof: by
  by_cases h₁f₁ : meromorphicOrderAt f₁ x = ⊤
  · simp_all [meromorphicOrderAt_smul hf₁ hf₂]
  by_cases h₁f₂ : meromorphicOrderAt f₂ x = ⊤
  · simp_all [meromorphicOrderAt_smul hf₁ hf₂]
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_ne_top_iff hf₁).1 h₁f₁
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ :

中文:
引理 MeromorphicAt.meromorphicTrailingCoeffAt_smul
  结论: {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 -> E}
  证明: by
  by_cases h₁f₁ : meromorphicOrderAt f₁ x = ⊤
  · simp_all [meromorphicOrderAt_smul hf₁ hf₂]
  by_cases h₁f₂ : meromorphicOrderAt f₂ x = ⊤
  · simp_all [meromorphicOrderAt_smul hf₁ hf₂]
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_ne_top_iff hf₁).1 h₁f₁
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ :

Depends on / 依赖: filter_upwards, meromorphicOrderAt, meromorphicOrderAt_ne_top_iff, meromorphicOrderAt_smul, self_mem_nhdsWithin
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_smul {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 -> E}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x) :
    meromorphicTrailingCoeffAt (f₁ • f₂) x =
      (meromorphicTrailingCoeffAt f₁ x) • (meromorphicTrailingCoeffAt f₂ x) := by
  by_cases h₁f₁ : meromorphicOrderAt f₁ x = ⊤
  · simp_all [meromorphicOrderAt_smul hf₁ hf₂]
  by_cases h₁f₂ : meromorphicOrderAt f₂ x = ⊤
  · simp_all [meromorphicOrderAt_smul hf₁ hf₂]
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_ne_top_iff hf₁).1 h₁f₁
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_ne_top_iff hf₂).1 h₁f₂
  have : f₁ • f₂ =ᶠ[𝓝[!=] x]
      fun z => (z - x) ^ (meromorphicOrderAt (f₁ • f₂) x).untop₀ • (g₁ • g₂) z := by
    filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin] with y h₁y h₂y h₃y
    simp_all [meromorphicOrderAt_smul hf₁ hf₂, zpow_add₀ (sub_ne_zero.2 h₃y)]
    module
  rw [h₁g₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₁ h₃g₁]; rw [h₁g₂.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₂ h₃g₂]; rw [(h₁g₁.smul h₁g₂).meromorphicTrailingCoeffAt_of_eq_nhdsNE this]
  simp

/--
lemma `MeromorphicAt.meromorphicTrailingCoeffAt_fun_smul` / 引理 `MeromorphicAt.meromorphicTrailingCoeffAt_fun_smul`

English:
lemma MeromorphicAt.meromorphicTrailingCoeffAt_fun_smul
  statement: {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 -> E}
  proof: MeromorphicAt.meromorphicTrailingCoeffAt_smul hf₁ hf₂

中文:
引理 MeromorphicAt.meromorphicTrailingCoeffAt_fun_smul
  结论: {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 -> E}
  证明: MeromorphicAt.meromorphicTrailingCoeffAt_smul hf₁ hf₂

Depends on / 依赖: MeromorphicAt, MeromorphicAt.meromorphicTrailingCoeffAt_smul, meromorphicTrailingCoeffAt_smul
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_fun_smul {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 -> E}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x) :
    meromorphicTrailingCoeffAt (fun z => f₁ z • f₂ z) x =
      (meromorphicTrailingCoeffAt f₁ x) • (meromorphicTrailingCoeffAt f₂ x) :=
  MeromorphicAt.meromorphicTrailingCoeffAt_smul hf₁ hf₂

/--
lemma `MeromorphicAt.meromorphicTrailingCoeffAt_mul` / 引理 `MeromorphicAt.meromorphicTrailingCoeffAt_mul`

English:
lemma MeromorphicAt.meromorphicTrailingCoeffAt_mul
  statement: {f₁ f₂ : 𝕜 -> 𝕜} (hf₁ : MeromorphicAt f₁ x)
  proof: meromorphicTrailingCoeffAt_smul hf₁ hf₂

中文:
引理 MeromorphicAt.meromorphicTrailingCoeffAt_mul
  结论: {f₁ f₂ : 𝕜 -> 𝕜} (hf₁ : MeromorphicAt f₁ x)
  证明: meromorphicTrailingCoeffAt_smul hf₁ hf₂

Depends on / 依赖: meromorphicTrailingCoeffAt_smul
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_mul {f₁ f₂ : 𝕜 -> 𝕜} (hf₁ : MeromorphicAt f₁ x)
    (hf₂ : MeromorphicAt f₂ x) :
    meromorphicTrailingCoeffAt (f₁ * f₂) x =
      (meromorphicTrailingCoeffAt f₁ x) * (meromorphicTrailingCoeffAt f₂ x) :=
  meromorphicTrailingCoeffAt_smul hf₁ hf₂

/--
lemma `MeromorphicAt.meromorphicTrailingCoeffAt_fun_mul` / 引理 `MeromorphicAt.meromorphicTrailingCoeffAt_fun_mul`

English:
lemma MeromorphicAt.meromorphicTrailingCoeffAt_fun_mul
  statement: {f₁ f₂ : 𝕜 -> 𝕜}
  proof: meromorphicTrailingCoeffAt_smul hf₁ hf₂

中文:
引理 MeromorphicAt.meromorphicTrailingCoeffAt_fun_mul
  结论: {f₁ f₂ : 𝕜 -> 𝕜}
  证明: meromorphicTrailingCoeffAt_smul hf₁ hf₂

Depends on / 依赖: meromorphicTrailingCoeffAt_smul
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_fun_mul {f₁ f₂ : 𝕜 -> 𝕜}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x) :
    meromorphicTrailingCoeffAt (fun z => f₁ z * f₂ z) x =
      (meromorphicTrailingCoeffAt f₁ x) * (meromorphicTrailingCoeffAt f₂ x) :=
  meromorphicTrailingCoeffAt_smul hf₁ hf₂

/--
theorem `meromorphicTrailingCoeffAt_prod` / 定理 `meromorphicTrailingCoeffAt_prod`

English:
theorem meromorphicTrailingCoeffAt_prod
  statement: {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜}
  proof: by
  classical
  induction s using Finset.induction with
  | empty =>
    apply meromorphicTrailingCoeffAt_const
  | insert σ s₁ hσ hind =>
    have : forall σ₀ in s₁, MeromorphicAt (f σ₀) x := by
      intro τ hτ
      apply h τ (Finset.mem_insert_of_mem hτ)
    rw [Finset.prod_insert hσ]; rw [Fins

中文:
定理 meromorphicTrailingCoeffAt_prod
  结论: {ι : 类型} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜}
  证明: by
  classical
  induction s using Finset.induction with
  | empty =>
    apply meromorphicTrailingCoeffAt_const
  | insert σ s₁ hσ hind =>
    have : forall σ₀ in s₁, MeromorphicAt (f σ₀) x := by
      intro τ hτ
      apply h τ (Finset.mem_insert_of_mem hτ)
    rw [Finset.prod_insert hσ]; rw [Fins

Depends on / 依赖: Finset, Finset.induction, Finset.mem_insert_of_mem, Finset.mem_insert_self, Finset.prod_insert, MeromorphicAt, MeromorphicAt.prod, classical, insert, mem_insert_of_mem, mem_insert_self, meromorphicTrailingCoeffAt_const, meromorphicTrailingCoeffAt_mul, prod_insert
-/
theorem meromorphicTrailingCoeffAt_prod {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜}
    {x : 𝕜} (h : forall σ in s, MeromorphicAt (f σ) x) :
    meromorphicTrailingCoeffAt (∏ n in s, f n) x = ∏ n in s, meromorphicTrailingCoeffAt (f n) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    apply meromorphicTrailingCoeffAt_const
  | insert σ s₁ hσ hind =>
    have : forall σ₀ in s₁, MeromorphicAt (f σ₀) x := by
      intro τ hτ
      apply h τ (Finset.mem_insert_of_mem hτ)
    rw [Finset.prod_insert hσ]; rw [Finset.prod_insert hσ]; rw [(h σ (Finset.mem_insert_self σ s₁)).meromorphicTrailingCoeffAt_mul
      (MeromorphicAt.prod this)]; rw [hind this]

/--
theorem `meromorphicTrailingCoeffAt_fun_prod` / 定理 `meromorphicTrailingCoeffAt_fun_prod`

English:
theorem meromorphicTrailingCoeffAt_fun_prod
  statement: {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜}
  proof: by
  convert! meromorphicTrailingCoeffAt_prod h
  simp

中文:
定理 meromorphicTrailingCoeffAt_fun_prod
  结论: {ι : 类型} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜}
  证明: by
  convert! meromorphicTrailingCoeffAt_prod h
  simp

Depends on / 依赖: convert, meromorphicTrailingCoeffAt_prod
-/
theorem meromorphicTrailingCoeffAt_fun_prod {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜}
    {x : 𝕜} (h : forall σ in s, MeromorphicAt (f σ) x) :
    meromorphicTrailingCoeffAt (fun z => ∏ n in s, f n z) x
      = ∏ n in s, meromorphicTrailingCoeffAt (f n) x := by
  convert! meromorphicTrailingCoeffAt_prod h
  simp

/--
lemma `meromorphicTrailingCoeffAt_inv` / 引理 `meromorphicTrailingCoeffAt_inv`

English:
lemma meromorphicTrailingCoeffAt_inv
  given: {f : 𝕜 -> 𝕜}
  proof: by
  by_cases h₁ : MeromorphicAt f x
  · by_cases h₂ : meromorphicOrderAt f x = ⊤
    · simp_all [meromorphicOrderAt_inv (f := f) (x := x)]
    have : f⁻¹ * f =ᶠ[𝓝[!=] x] 1 := by
      filter_upwards [(meromorphicOrderAt_ne_top_iff_eventually_ne_zero h₁).1 h₂]
      simp_all
    rw [← mul_eq_one_iff

中文:
引理 meromorphicTrailingCoeffAt_inv
  条件: {f : 𝕜 -> 𝕜}
  证明: by
  by_cases h₁ : MeromorphicAt f x
  · by_cases h₂ : meromorphicOrderAt f x = ⊤
    · simp_all [meromorphicOrderAt_inv (f := f) (x := x)]
    have : f⁻¹ * f =ᶠ[𝓝[!=] x] 1 := by
      filter_upwards [(meromorphicOrderAt_ne_top_iff_eventually_ne_zero h₁).1 h₂]
      simp_all
    rw [← mul_eq_one_iff

Depends on / 依赖: MeromorphicAt, analyticAt_const, analyticAt_const.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE, filter_upwards, inv.meromorphicTrailingCoeffAt_mul, meromorphicOrderAt, meromorphicOrderAt_inv, meromorphicOrderAt_ne_top_iff_eventually_ne_zero, meromorphicTrailingCoeffAt_congr_nhdsNE, meromorphicTrailingCoeffAt_mul, meromorphicTrailingCoeffAt_ne_zero, meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
-/
lemma meromorphicTrailingCoeffAt_inv {f : 𝕜 -> 𝕜} :
    meromorphicTrailingCoeffAt f⁻¹ x = (meromorphicTrailingCoeffAt f x)⁻¹ := by
  by_cases h₁ : MeromorphicAt f x
  · by_cases h₂ : meromorphicOrderAt f x = ⊤
    · simp_all [meromorphicOrderAt_inv (f := f) (x := x)]
    have : f⁻¹ * f =ᶠ[𝓝[!=] x] 1 := by
      filter_upwards [(meromorphicOrderAt_ne_top_iff_eventually_ne_zero h₁).1 h₂]
      simp_all
    rw [← mul_eq_one_iff_eq_inv₀ (h₁.meromorphicTrailingCoeffAt_ne_zero h₂)]; rw [← h₁.inv.meromorphicTrailingCoeffAt_mul h₁]; rw [meromorphicTrailingCoeffAt_congr_nhdsNE this]; rw [analyticAt_const.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := 0)]
    · simp
    · simp only [zpow_zero, smul_eq_mul, mul_one]
      exact eventuallyEq_nhdsWithin_of_eqOn fun _ => congrFun rfl
  · simp_all

/--
lemma `meromorphicTrailingCoeffAt_fun_inv` / 引理 `meromorphicTrailingCoeffAt_fun_inv`

English:
lemma meromorphicTrailingCoeffAt_fun_inv
  given: {f : 𝕜 -> 𝕜}
  proof: meromorphicTrailingCoeffAt_inv

中文:
引理 meromorphicTrailingCoeffAt_fun_inv
  条件: {f : 𝕜 -> 𝕜}
  证明: meromorphicTrailingCoeffAt_inv

Depends on / 依赖: meromorphicTrailingCoeffAt_inv
-/
lemma meromorphicTrailingCoeffAt_fun_inv {f : 𝕜 -> 𝕜} :
    meromorphicTrailingCoeffAt (fun z => (f z)⁻¹) x = (meromorphicTrailingCoeffAt f x)⁻¹ :=
  meromorphicTrailingCoeffAt_inv

/--
lemma `MeromorphicAt.meromorphicTrailingCoeffAt_zpow` / 引理 `MeromorphicAt.meromorphicTrailingCoeffAt_zpow`

English:
lemma MeromorphicAt.meromorphicTrailingCoeffAt_zpow
  given: {n : Int} {f : 𝕜 -> 𝕜} (h₁ : MeromorphicAt f x)
  proof: by
  by_cases h₂ : meromorphicOrderAt f x = ⊤
  · by_cases h₃ : n = 0
    · simp only [h₃, zpow_zero]
      apply analyticAt_const.meromorphicTrailingCoeffAt_of_ne_zero (ne_zero_of_eq_one rfl)
    · simp_all [meromorphicOrderAt_zpow h₁, zero_zpow n h₃]
  · obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOr

中文:
引理 MeromorphicAt.meromorphicTrailingCoeffAt_zpow
  条件: {n : 整数} {f : 𝕜 -> 𝕜} (h₁ : MeromorphicAt f x)
  证明: by
  by_cases h₂ : meromorphicOrderAt f x = ⊤
  · by_cases h₃ : n = 0
    · simp only [h₃, zpow_zero]
      apply analyticAt_const.meromorphicTrailingCoeffAt_of_ne_zero (ne_zero_of_eq_one rfl)
    · simp_all [meromorphicOrderAt_zpow h₁, zero_zpow n h₃]
  · obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOr

Depends on / 依赖: analyticAt_const, analyticAt_const.meromorphicTrailingCoeffAt_of_ne_zero, g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE, g.zpow, meromorphicOrderAt, meromorphicOrderAt_ne_top_iff, meromorphicOrderAt_zpow, meromorphicTrailingCoeffAt_of_ne_zero, meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE, ne_zero_of_eq_one, zero_zpow, zpow_zero
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_zpow {n : Int} {f : 𝕜 -> 𝕜} (h₁ : MeromorphicAt f x) :
    meromorphicTrailingCoeffAt (f ^ n) x = (meromorphicTrailingCoeffAt f x) ^ n := by
  by_cases h₂ : meromorphicOrderAt f x = ⊤
  · by_cases h₃ : n = 0
    · simp only [h₃, zpow_zero]
      apply analyticAt_const.meromorphicTrailingCoeffAt_of_ne_zero (ne_zero_of_eq_one rfl)
    · simp_all [meromorphicOrderAt_zpow h₁, zero_zpow n h₃]
  · obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff h₁).1 h₂
    rw [h₁g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
        (n := (meromorphicOrderAt f x).untop₀) h₂g h₃g]; rw [(h₁g.zpow h₂g (n := n)).meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
        (n := (meromorphicOrderAt (f ^ n) x).untop₀)
        (by simp_all [zpow_ne_zero])]
    · simp only [Pi.pow_apply]
    · filter_upwards [h₃g] with a ha
      simp_all [mul_zpow, ← zpow_mul, meromorphicOrderAt_zpow h₁, mul_comm]

/--
lemma `MeromorphicAt.meromorphicTrailingCoeffAt_fun_zpow` / 引理 `MeromorphicAt.meromorphicTrailingCoeffAt_fun_zpow`

English:
lemma MeromorphicAt.meromorphicTrailingCoeffAt_fun_zpow
  statement: {n : Int} {f : 𝕜 -> 𝕜}
  proof: MeromorphicAt.meromorphicTrailingCoeffAt_zpow h₁

中文:
引理 MeromorphicAt.meromorphicTrailingCoeffAt_fun_zpow
  结论: {n : 整数} {f : 𝕜 -> 𝕜}
  证明: MeromorphicAt.meromorphicTrailingCoeffAt_zpow h₁

Depends on / 依赖: MeromorphicAt, MeromorphicAt.meromorphicTrailingCoeffAt_zpow, meromorphicTrailingCoeffAt_zpow
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_fun_zpow {n : Int} {f : 𝕜 -> 𝕜}
    (h₁ : MeromorphicAt f x) :
    meromorphicTrailingCoeffAt (fun z => f z ^ n) x = (meromorphicTrailingCoeffAt f x) ^ n :=
  MeromorphicAt.meromorphicTrailingCoeffAt_zpow h₁

/--
lemma `MeromorphicAt.meromorphicTrailingCoeffAt_pow` / 引理 `MeromorphicAt.meromorphicTrailingCoeffAt_pow`

English:
lemma MeromorphicAt.meromorphicTrailingCoeffAt_pow
  statement: {n : Nat} {f : 𝕜 -> 𝕜}
  proof: by
  convert! h₁.meromorphicTrailingCoeffAt_zpow (n := n) <;> simp

中文:
引理 MeromorphicAt.meromorphicTrailingCoeffAt_pow
  结论: {n : 自然数} {f : 𝕜 -> 𝕜}
  证明: by
  convert! h₁.meromorphicTrailingCoeffAt_zpow (n := n) <;> simp

Depends on / 依赖: convert, meromorphicTrailingCoeffAt_zpow
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_pow {n : Nat} {f : 𝕜 -> 𝕜}
    (h₁ : MeromorphicAt f x) :
    meromorphicTrailingCoeffAt (f ^ n) x = (meromorphicTrailingCoeffAt f x) ^ n := by
  convert! h₁.meromorphicTrailingCoeffAt_zpow (n := n) <;> simp

/--
lemma `MeromorphicAt.meromorphicTrailingCoeffAt_fun_pow` / 引理 `MeromorphicAt.meromorphicTrailingCoeffAt_fun_pow`

English:
lemma MeromorphicAt.meromorphicTrailingCoeffAt_fun_pow
  statement: {n : Nat} {f : 𝕜 -> 𝕜}
  proof: MeromorphicAt.meromorphicTrailingCoeffAt_pow h₁

中文:
引理 MeromorphicAt.meromorphicTrailingCoeffAt_fun_pow
  结论: {n : 自然数} {f : 𝕜 -> 𝕜}
  证明: MeromorphicAt.meromorphicTrailingCoeffAt_pow h₁

Depends on / 依赖: MeromorphicAt, MeromorphicAt.meromorphicTrailingCoeffAt_pow, meromorphicTrailingCoeffAt_pow
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_fun_pow {n : Nat} {f : 𝕜 -> 𝕜}
    (h₁ : MeromorphicAt f x) :
    meromorphicTrailingCoeffAt (fun z => f z ^ n) x = (meromorphicTrailingCoeffAt f x) ^ n :=
  MeromorphicAt.meromorphicTrailingCoeffAt_pow h₁

/-!
## Behavior under Composition
-/

/--
theorem `MeromorphicAt.meromorphicTrailingCoeffAt_comp` / 定理 `MeromorphicAt.meromorphicTrailingCoeffAt_comp`

English:
theorem MeromorphicAt.meromorphicTrailingCoeffAt_comp
  statement: {g : 𝕜 -> 𝕜} (hf : MeromorphicAt f (g x))
  proof: by
  by_cases h : meromorphicOrderAt f (g x) = ⊤
  · have : meromorphicTrailingCoeffAt (f ∘ g) x = 0 := by
      apply MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top
      rw [meromorphicOrderAt_eq_top_iff] at *
      exact (hg.map_nhdsNE hg_nc) h
    aesop
  · set r := (meromorphicOrderAt

中文:
定理 MeromorphicAt.meromorphicTrailingCoeffAt_comp
  结论: {g : 𝕜 -> 𝕜} (hf : MeromorphicAt f (g x))
  证明: by
  by_cases h : meromorphicOrderAt f (g x) = ⊤
  · have : meromorphicTrailingCoeffAt (f ∘ g) x = 0 := by
      apply MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top
      rw [meromorphicOrderAt_eq_top_iff] at *
      exact (hg.map_nhdsNE hg_nc) h
    aesop
  · set r := (meromorphicOrderAt

Depends on / 依赖: MeromorphicAt, MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top, hg.map_nhdsNE, hg_nc, map_nhdsNE, meromorphicOrderAt, meromorphicOrderAt_eq_top_iff, meromorphicOrderAt_ne_top_iff, meromorphicTrailingCoeffA, meromorphicTrailingCoeffAt, meromorphicTrailingCoeffAt_of_order_eq_top
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_comp {g : 𝕜 -> 𝕜} (hf : MeromorphicAt f (g x))
    (hg : AnalyticAt 𝕜 g x) (hg_nc : ¬EventuallyConst g (𝓝 x)) :
    meromorphicTrailingCoeffAt (f ∘ g) x =
      (meromorphicTrailingCoeffAt (g · - g x) x) ^ (meromorphicOrderAt f (g x)).untop₀ •
      meromorphicTrailingCoeffAt f (g x) := by
  by_cases h : meromorphicOrderAt f (g x) = ⊤
  · have : meromorphicTrailingCoeffAt (f ∘ g) x = 0 := by
      apply MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top
      rw [meromorphicOrderAt_eq_top_iff] at *
      exact (hg.map_nhdsNE hg_nc) h
    aesop
  · set r := (meromorphicOrderAt f (g x)).untop₀
    obtain ⟨F, h₁F, h₂F, h₃F⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h
    have h₁ : meromorphicTrailingCoeffAt (f ∘ g) x
        = meromorphicTrailingCoeffAt ((g · - g x) ^ r • (F ∘ g)) x := by
      apply meromorphicTrailingCoeffAt_congr_nhdsNE
      apply Filter.Tendsto.eventually (hg.map_nhdsNE hg_nc) h₃F
    rw [h₁]; rw [MeromorphicAt.meromorphicTrailingCoeffAt_smul (by fun_prop) (by fun_prop)]; rw [(h₁F.comp hg).meromorphicTrailingCoeffAt_of_ne_zero h₂F]; rw [h₁F.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂F h₃F]
    simp_all only [ne_eq, Function.comp_apply, not_false_eq_true, smul_left_inj]
    apply MeromorphicAt.meromorphicTrailingCoeffAt_zpow (by fun_prop)

/-- `meromorphicTrailingCoefficientAt` is invariant under translation. -/
@[to_fun meromorphicTrailingCoeffAt_fun_comp_add_const_eq_meromorphicTrailingCoeffAt]
/--
theorem `meromorphicTrailingCoeffAt_comp_add_const_eq_meromorphicTrailingCoeffAt` / 定理 `meromorphicTrailingCoeffAt_comp_add_const_eq_meromorphicTrailingCoeffAt`

English:
theorem meromorphicTrailingCoeffAt_comp_add_const_eq_meromorphicTrailingCoeffAt
  given: {c : 𝕜}
  proof: by
  classical
  by_cases h : ¬ MeromorphicAt f (x + c)
  · simp_all [meromorphicAt_comp_add_const_iff_meromorphicAt.not.2 h]
  rw [MeromorphicAt.meromorphicTrailingCoeffAt_comp (by simp_all) (by fun_prop)
    (by simp [eventuallyConst_iff_analyticOrderAt_sub_eq_top])]
  simp [meromorphicTrailingCoe

中文:
定理 meromorphicTrailingCoeffAt_comp_add_const_eq_meromorphicTrailingCoeffAt
  条件: {c : 𝕜}
  证明: by
  classical
  by_cases h : ¬ MeromorphicAt f (x + c)
  · simp_all [meromorphicAt_comp_add_const_iff_meromorphicAt.not.2 h]
  rw [MeromorphicAt.meromorphicTrailingCoeffAt_comp (by simp_all) (by fun_prop)
    (by simp [eventuallyConst_iff_analyticOrderAt_sub_eq_top])]
  simp [meromorphicTrailingCoe

Depends on / 依赖: MeromorphicAt, MeromorphicAt.meromorphicTrailingCoeffAt_comp, classical, eventuallyConst_iff_analyticOrderAt_sub_eq_top, fun_prop, meromorphicAt_comp_add_const_iff_meromorphicAt, meromorphicAt_comp_add_const_iff_meromorphicAt.not, meromorphicTrailingCoeffAt_comp, meromorphicTrailingCoeffAt_id_sub_const
-/
theorem meromorphicTrailingCoeffAt_comp_add_const_eq_meromorphicTrailingCoeffAt {c : 𝕜} :
    meromorphicTrailingCoeffAt (f ∘ (· + c)) x = meromorphicTrailingCoeffAt f (x + c) := by
  classical
  by_cases h : ¬ MeromorphicAt f (x + c)
  · simp_all [meromorphicAt_comp_add_const_iff_meromorphicAt.not.2 h]
  rw [MeromorphicAt.meromorphicTrailingCoeffAt_comp (by simp_all) (by fun_prop)
    (by simp [eventuallyConst_iff_analyticOrderAt_sub_eq_top])]
  simp [meromorphicTrailingCoeffAt_id_sub_const]

/-- `meromorphicTrailingCoefficientAt` is invariant under translation. -/
@[to_fun meromorphicTrailingCoeffAt_fun_comp_sub_const_eq_meromorphicTrailingCoeffAt]
/--
theorem `meromorphicTrailingCoeffAt_comp_sub_const_eq_meromorphicTrailingCoeffAt` / 定理 `meromorphicTrailingCoeffAt_comp_sub_const_eq_meromorphicTrailingCoeffAt`

English:
theorem meromorphicTrailingCoeffAt_comp_sub_const_eq_meromorphicTrailingCoeffAt
  given: {c : 𝕜}
  proof: by
  simp [sub_eq_add_neg, ← meromorphicTrailingCoeffAt_comp_add_const_eq_meromorphicTrailingCoeffAt]

中文:
定理 meromorphicTrailingCoeffAt_comp_sub_const_eq_meromorphicTrailingCoeffAt
  条件: {c : 𝕜}
  证明: by
  simp [sub_eq_add_neg, ← meromorphicTrailingCoeffAt_comp_add_const_eq_meromorphicTrailingCoeffAt]

Depends on / 依赖: meromorphicTrailingCoeffAt_comp_add_const_eq_meromorphicTrailingCoeffAt, sub_eq_add_neg
-/
theorem meromorphicTrailingCoeffAt_comp_sub_const_eq_meromorphicTrailingCoeffAt {c : 𝕜} :
    meromorphicTrailingCoeffAt (f ∘ (· - c)) x = meromorphicTrailingCoeffAt f (x - c) := by
  simp [sub_eq_add_neg, ← meromorphicTrailingCoeffAt_comp_add_const_eq_meromorphicTrailingCoeffAt]
