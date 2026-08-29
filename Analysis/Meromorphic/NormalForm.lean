/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor

/-!
# Normal form of meromorphic functions and continuous extension

If a function `f` is meromorphic on `U` and if `g` differs from `f` only along a set that is
codiscrete within `U`, then `g` is likewise meromorphic. The set of meromorphic functions is
therefore huge, and `=ᶠ[codiscreteWithin U]` defines an equivalence relation.

This file implements continuous extension to provide an API that allows picking the 'unique best'
representative of any given equivalence class, where 'best' means that the representative can
locally near any point `x` be written 'in normal form', as `f =ᶠ[𝓝 x] fun z ↦ (z - x) ^ n • g`
where `g` is analytic and does not vanish at `x`.

The relevant notions are `MeromorphicNFAt` and `MeromorphicNFOn`; these guarantee normal
form at a single point and along a set, respectively.
-/

@[expose] public section

open Metric Set Topology WithTop
open scoped Pointwise

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 -> E} {g : 𝕜 -> 𝕜}
  {x : 𝕜}
  {U : Set 𝕜}

/-!
## Normal form of meromorphic functions at a given point

### Definition and characterizations
-/

variable (f x) in
/-- A function is 'meromorphic in normal form' at `x` if it vanishes around `x`
or if it can locally be written as `fun z ↦ (z - x) ^ n • g` where `g` is
analytic and does not vanish at `x`. -/
@[fun_prop]
/--
Definition of `MeromorphicNFAt` / `MeromorphicNFAt` 的定义

English:
definition MeromorphicNFAt
  body: f =ᶠ[𝓝 x] 0 ∨
    exists (n : Int) (g : 𝕜 -> E), AnalyticAt 𝕜 g x ∧ g x != 0 ∧ f =ᶠ[𝓝 x] (· - x) ^ n • g

中文:
定义 MeromorphicNFAt
  定义体: f =ᶠ[𝓝 x] 0 ∨
    exists (n : Int) (g : 𝕜 -> E), AnalyticAt 𝕜 g x ∧ g x != 0 ∧ f =ᶠ[𝓝 x] (· - x) ^ n • g

Depends on / 依赖: AnalyticAt
-/
def MeromorphicNFAt :=
  f =ᶠ[𝓝 x] 0 ∨
    exists (n : Int) (g : 𝕜 -> E), AnalyticAt 𝕜 g x ∧ g x != 0 ∧ f =ᶠ[𝓝 x] (· - x) ^ n • g

/--
theorem `meromorphicNFAt_iff_analyticAt_or` / 定理 `meromorphicNFAt_iff_analyticAt_or`

English:
theorem meromorphicNFAt_iff_analyticAt_or
  proof: by
  constructor
  · rintro (h | ⟨n, g, h₁g, h₂g, h₃g⟩)
    · simp [(analyticAt_congr h).2 analyticAt_const]
    · have hf : MeromorphicAt f x := by
        apply MeromorphicAt.congr _ (h₃g.filter_mono nhdsWithin_le_nhds).symm
        fun_prop
      have : meromorphicOrderAt f x = n := by
        rw

中文:
定理 meromorphicNFAt_iff_analyticAt_or
  证明: by
  constructor
  · rintro (h | ⟨n, g, h₁g, h₂g, h₃g⟩)
    · simp [(analyticAt_congr h).2 analyticAt_const]
    · have hf : MeromorphicAt f x := by
        apply MeromorphicAt.congr _ (h₃g.filter_mono nhdsWithin_le_nhds).symm
        fun_prop
      have : meromorphicOrderAt f x = n := by
        rw

Depends on / 依赖: AnalyticAt, AnalyticAt.zpow_nonneg, MeromorphicAt, MeromorphicAt.congr, analyticAt_congr, analyticAt_const, eventually_nhdsWithin_of_eventually_nhds, filter_mono, fun_prop, g.filter_mono, meromorphicOrderAt, meromorphicOrderAt_eq_int_iff, nhdsWithin_le_nhds, zpow_nonneg
-/
theorem meromorphicNFAt_iff_analyticAt_or :
    MeromorphicNFAt f x ↔
      AnalyticAt 𝕜 f x ∨ (MeromorphicAt f x ∧ meromorphicOrderAt f x < 0 ∧ f x = 0) := by
  constructor
  · rintro (h | ⟨n, g, h₁g, h₂g, h₃g⟩)
    · simp [(analyticAt_congr h).2 analyticAt_const]
    · have hf : MeromorphicAt f x := by
        apply MeromorphicAt.congr _ (h₃g.filter_mono nhdsWithin_le_nhds).symm
        fun_prop
      have : meromorphicOrderAt f x = n := by
        rw [meromorphicOrderAt_eq_int_iff hf]
        use g, h₁g, h₂g
        exact eventually_nhdsWithin_of_eventually_nhds h₃g
      by_cases! hn : 0 <= n
      · left
        rw [analyticAt_congr h₃g]
        apply (AnalyticAt.zpow_nonneg (by fun_prop) hn).smul h₁g
      · right
        use hf
        simp [this, WithTop.coe_lt_zero.2 hn, h₃g.eq_of_nhds,
          zero_zpow n hn.ne]
  · rintro (h | ⟨h₁, h₂, h₃⟩)
    · by_cases h₂f : analyticOrderAt f x = ⊤
      · rw [analyticOrderAt_eq_top] at h₂f
        tauto
      · right
        use analyticOrderNatAt f x
        have : analyticOrderAt f x != ⊤ := h₂f
        rw [← ENat.natCast_toNat_eq_self]; rw [eq_comm]; rw [h.analyticOrderAt_eq_natCast] at this
        obtain ⟨g, h₁g, h₂g, h₃g⟩ := this
        use g, h₁g, h₂g
        simpa
    · right
      lift meromorphicOrderAt f x to Int using LT.lt.ne_top h₂ with n hn
      obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_eq_int_iff h₁).1 hn.symm
      use n, g, h₁g, h₂g
      filter_upwards [eventually_nhdsWithin_iff.1 h₃g]
      intro z hz
      by_cases h₁z : z = x
      · simp only [h₁z, Pi.smul_apply', Pi.pow_apply, sub_self]
        rw [h₃]
        apply (smul_eq_zero_of_left (zero_zpow n _) (g x)).symm
        by_contra hCon
        simp [hCon] at h₂
      · exact hz h₁z

/-!
### Relation to other properties of functions
-/

/--
theorem `MeromorphicNFAt.meromorphicAt` / 定理 `MeromorphicNFAt.meromorphicAt`

English:
theorem MeromorphicNFAt.meromorphicAt
  given: (hf : MeromorphicNFAt f x)
  proof: by
  rw [meromorphicNFAt_iff_analyticAt_or] at hf
  rcases hf with h | h
  · exact h.meromorphicAt
  · obtain ⟨hf, _⟩ := h
    exact hf

中文:
定理 MeromorphicNFAt.meromorphicAt
  条件: (hf : MeromorphicNFAt f x)
  证明: by
  rw [meromorphicNFAt_iff_analyticAt_or] at hf
  rcases hf with h | h
  · exact h.meromorphicAt
  · obtain ⟨hf, _⟩ := h
    exact hf

Depends on / 依赖: h.meromorphicAt, meromorphicAt, meromorphicNFAt_iff_analyticAt_or
-/
theorem MeromorphicNFAt.meromorphicAt (hf : MeromorphicNFAt f x) :
    MeromorphicAt f x := by
  rw [meromorphicNFAt_iff_analyticAt_or] at hf
  rcases hf with h | h
  · exact h.meromorphicAt
  · obtain ⟨hf, _⟩ := h
    exact hf

/--
theorem `MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt` / 定理 `MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt`

English:
theorem MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt
  given: (hf : MeromorphicNFAt f x)
  proof: by
  constructor <;> intro h₂f
  · rw [meromorphicNFAt_iff_analyticAt_or] at hf
    rcases hf with h | ⟨_, h₃f, _⟩
    · exact h
    · by_contra h'
      exact lt_irrefl 0 (lt_of_le_of_lt h₂f h₃f)
  · rw [h₂f.meromorphicOrderAt_eq]
    simp

中文:
定理 MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt
  条件: (hf : MeromorphicNFAt f x)
  证明: by
  constructor <;> intro h₂f
  · rw [meromorphicNFAt_iff_analyticAt_or] at hf
    rcases hf with h | ⟨_, h₃f, _⟩
    · exact h
    · by_contra h'
      exact lt_irrefl 0 (lt_of_le_of_lt h₂f h₃f)
  · rw [h₂f.meromorphicOrderAt_eq]
    simp

Depends on / 依赖: f.meromorphicOrderAt_eq, lt_irrefl, lt_of_le_of_lt, meromorphicNFAt_iff_analyticAt_or, meromorphicOrderAt_eq
-/
theorem MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt (hf : MeromorphicNFAt f x) :
    0 <= meromorphicOrderAt f x ↔ AnalyticAt 𝕜 f x := by
  constructor <;> intro h₂f
  · rw [meromorphicNFAt_iff_analyticAt_or] at hf
    rcases hf with h | ⟨_, h₃f, _⟩
    · exact h
    · by_contra h'
      exact lt_irrefl 0 (lt_of_le_of_lt h₂f h₃f)
  · rw [h₂f.meromorphicOrderAt_eq]
    simp

/--
theorem `AnalyticAt.meromorphicNFAt` / 定理 `AnalyticAt.meromorphicNFAt`

English:
theorem AnalyticAt.meromorphicNFAt
  given: (hf : AnalyticAt 𝕜 f x)
  proof: by
  simp [meromorphicNFAt_iff_analyticAt_or, hf]

中文:
定理 AnalyticAt.meromorphicNFAt
  条件: (hf : AnalyticAt 𝕜 f x)
  证明: by
  simp [meromorphicNFAt_iff_analyticAt_or, hf]

Depends on / 依赖: meromorphicNFAt_iff_analyticAt_or
-/
theorem AnalyticAt.meromorphicNFAt (hf : AnalyticAt 𝕜 f x) :
    MeromorphicNFAt f x := by
  simp [meromorphicNFAt_iff_analyticAt_or, hf]

/--
theorem `MeromorphicOn.meromorphicNFAt_mem_codiscreteWithin` / 定理 `MeromorphicOn.meromorphicNFAt_mem_codiscreteWithin`

English:
theorem MeromorphicOn.meromorphicNFAt_mem_codiscreteWithin
  statement: {U : Set 𝕜}
  proof: by
  filter_upwards [hf.analyticAt_mem_codiscreteWithin] with _ ha
  exact ha.meromorphicNFAt

中文:
定理 MeromorphicOn.meromorphicNFAt_mem_codiscreteWithin
  结论: {U : 集合 𝕜}
  证明: by
  filter_upwards [hf.analyticAt_mem_codiscreteWithin] with _ ha
  exact ha.meromorphicNFAt

Depends on / 依赖: analyticAt_mem_codiscreteWithin, filter_upwards, ha.meromorphicNFAt, hf.analyticAt_mem_codiscreteWithin, meromorphicNFAt
-/
theorem MeromorphicOn.meromorphicNFAt_mem_codiscreteWithin {U : Set 𝕜}
    (hf : MeromorphicOn f U) :
    { x | MeromorphicNFAt f x } in Filter.codiscreteWithin U := by
  filter_upwards [hf.analyticAt_mem_codiscreteWithin] with _ ha
  exact ha.meromorphicNFAt

/-!
### Vanishing and order
-/

/--
theorem `MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff` / 定理 `MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff`

English:
theorem MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff
  given: (hf : MeromorphicNFAt f x)
  proof: by
  constructor
  · intro h₁f
    have h₂f := hf.meromorphicOrderAt_nonneg_iff_analyticAt.1 (le_of_eq h₁f.symm)
    rw [← h₂f.analyticOrderAt_eq_zero]; rw [← ENat.map_natCast_eq_zero (α := Int)]
    rwa [h₂f.meromorphicOrderAt_eq] at h₁f
  · intro h
    rcases id hf with h₁ | ⟨n, g, h₁g, h₂g, h₃g⟩


中文:
定理 MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff
  条件: (hf : MeromorphicNFAt f x)
  证明: by
  constructor
  · intro h₁f
    have h₂f := hf.meromorphicOrderAt_nonneg_iff_analyticAt.1 (le_of_eq h₁f.symm)
    rw [← h₂f.analyticOrderAt_eq_zero]; rw [← ENat.map_natCast_eq_zero (α := Int)]
    rwa [h₂f.meromorphicOrderAt_eq] at h₁f
  · intro h
    rcases id hf with h₁ | ⟨n, g, h₁g, h₂g, h₃g⟩


Depends on / 依赖: ENat.map_natCast_eq_zero, Pi.pow_apply, Pi.smul_apply, analyticOrderAt_eq_zero, eq_of_nhds, f.analyticOrderAt_eq_zero, f.meromorphicOrderAt_eq, f.symm, g.eq_of_nhds, hContra, hf.meromorphicOrderAt_nonneg_iff_analyticAt, le_of_eq, map_natCast_eq_zero, meromorphicOrderAt_eq, meromorphicOrderAt_nonneg_iff_analyticAt, pow_apply, smul_apply, sub_self, zero_smul, zero_zpow
-/
theorem MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff (hf : MeromorphicNFAt f x) :
    meromorphicOrderAt f x = 0 ↔ f x != 0 := by
  constructor
  · intro h₁f
    have h₂f := hf.meromorphicOrderAt_nonneg_iff_analyticAt.1 (le_of_eq h₁f.symm)
    rw [← h₂f.analyticOrderAt_eq_zero]; rw [← ENat.map_natCast_eq_zero (α := Int)]
    rwa [h₂f.meromorphicOrderAt_eq] at h₁f
  · intro h
    rcases id hf with h₁ | ⟨n, g, h₁g, h₂g, h₃g⟩
    · have := h₁.eq_of_nhds
      tauto
    · have : n = 0 := by
        by_contra hContra
        have := h₃g.eq_of_nhds
        simp only [Pi.smul_apply', Pi.pow_apply, sub_self, zero_zpow n hContra, zero_smul] at this
        tauto
      simp only [this, zpow_zero] at h₃g
      apply (meromorphicOrderAt_eq_int_iff hf.meromorphicAt).2
      use g, h₁g, h₂g
      simp only [zpow_zero]
      exact h₃g.filter_mono nhdsWithin_le_nhds

/-!
### Local nature of the definition and local identity theorem
-/

/--
theorem `MeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds` / 定理 `MeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds`

English:
theorem MeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
  statement: {g : 𝕜 -> E}
  proof: by
  constructor
  · intro h
    have t₀ := meromorphicOrderAt_congr h
    by_cases cs : meromorphicOrderAt f x = 0
    · rw [cs] at t₀
      have Z := (hf.meromorphicOrderAt_nonneg_iff_analyticAt.1 (le_of_eq cs.symm)).continuousAt
      have W := (hg.meromorphicOrderAt_nonneg_iff_analyticAt.1 (le_o

中文:
定理 MeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
  结论: {g : 𝕜 -> E}
  证明: by
  constructor
  · intro h
    have t₀ := meromorphicOrderAt_congr h
    by_cases cs : meromorphicOrderAt f x = 0
    · rw [cs] at t₀
      have Z := (hf.meromorphicOrderAt_nonneg_iff_analyticAt.1 (le_of_eq cs.symm)).continuousAt
      have W := (hg.meromorphicOrderAt_nonneg_iff_analyticAt.1 (le_o

Depends on / 依赖: Z.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE, continuousAt, cs.symm, eventuallyEq_nhds_iff_eventuallyEq_nhdsNE, eventuallyEq_nhds_of_eventuallyEq_nhdsNE, hf.meromorphicOrderAt_eq_zero_iff, hf.meromorphicOrderAt_nonneg_iff_analyticAt, hg.meromo, hg.meromorphicOrderAt_nonneg_iff_analyticAt, le_of_eq, meromo, meromorphicOrderAt, meromorphicOrderAt_congr, meromorphicOrderAt_eq_zero_iff, meromorphicOrderAt_nonneg_iff_analyticAt
-/
theorem MeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds {g : 𝕜 -> E}
    (hf : MeromorphicNFAt f x) (hg : MeromorphicNFAt g x) :
    f =ᶠ[𝓝[!=] x] g ↔ f =ᶠ[𝓝 x] g := by
  constructor
  · intro h
    have t₀ := meromorphicOrderAt_congr h
    by_cases cs : meromorphicOrderAt f x = 0
    · rw [cs] at t₀
      have Z := (hf.meromorphicOrderAt_nonneg_iff_analyticAt.1 (le_of_eq cs.symm)).continuousAt
      have W := (hg.meromorphicOrderAt_nonneg_iff_analyticAt.1 (le_of_eq t₀)).continuousAt
      exact (Z.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE W).1 h
    · apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE h
      let h₁f := cs
      rw [hf.meromorphicOrderAt_eq_zero_iff] at h₁f
      let h₁g := cs
      rw [t₀]; rw [hg.meromorphicOrderAt_eq_zero_iff] at h₁g
      simp only [not_not] at *
      rw [h₁f]; rw [h₁g]
  · exact (Filter.EventuallyEq.filter_mono · nhdsWithin_le_nhds)

/--
theorem `meromorphicNFAt_congr` / 定理 `meromorphicNFAt_congr`

English:
theorem meromorphicNFAt_congr
  given: {g : 𝕜 -> E} (hfg : f =ᶠ[𝓝 x] g)
  proof: by
  constructor
  · rintro (h | ⟨n, h, h₁h, h₂h, h₃h⟩)
    · exact .inl (hfg.symm.trans h)
    · exact .inr ⟨n, h, h₁h, h₂h, hfg.symm.trans h₃h⟩
  · rintro (h | ⟨n, h, h₁h, h₂h, h₃h⟩)
    · exact .inl (hfg.trans h)
    · exact .inr ⟨n, h, h₁h, h₂h, hfg.trans h₃h⟩

中文:
定理 meromorphicNFAt_congr
  条件: {g : 𝕜 -> E} (hfg : f =ᶠ[𝓝 x] g)
  证明: by
  constructor
  · rintro (h | ⟨n, h, h₁h, h₂h, h₃h⟩)
    · exact .inl (hfg.symm.trans h)
    · exact .inr ⟨n, h, h₁h, h₂h, hfg.symm.trans h₃h⟩
  · rintro (h | ⟨n, h, h₁h, h₂h, h₃h⟩)
    · exact .inl (hfg.trans h)
    · exact .inr ⟨n, h, h₁h, h₂h, hfg.trans h₃h⟩

Depends on / 依赖: hfg.symm.trans, hfg.trans
-/
theorem meromorphicNFAt_congr {g : 𝕜 -> E} (hfg : f =ᶠ[𝓝 x] g) :
    MeromorphicNFAt f x ↔ MeromorphicNFAt g x := by
  constructor
  · rintro (h | ⟨n, h, h₁h, h₂h, h₃h⟩)
    · exact .inl (hfg.symm.trans h)
    · exact .inr ⟨n, h, h₁h, h₂h, hfg.symm.trans h₃h⟩
  · rintro (h | ⟨n, h, h₁h, h₂h, h₃h⟩)
    · exact .inl (hfg.trans h)
    · exact .inr ⟨n, h, h₁h, h₂h, hfg.trans h₃h⟩

/-!
### Criteria to guarantee normal form
-/

/--
lemma `MeromorphicNFAt.smul_analytic` / 引理 `MeromorphicNFAt.smul_analytic`

English:
lemma MeromorphicNFAt.smul_analytic
  statement: (hf : MeromorphicNFAt f x)
  proof: by
  rcases hf with h₁f | ⟨n, g_f, h₁g_f, h₂g_f, h₃g_f⟩
  · left
    filter_upwards [h₁f]
    simp_all
  · right
    use n, g • g_f, h₁g.smul h₁g_f
    constructor
    · simp [smul_ne_zero h₂g h₂g_f]
    · filter_upwards [h₃g_f]
      intro y hy
      simp only [Pi.smul_apply', hy, Pi.pow_apply]
   

中文:
引理 MeromorphicNFAt.smul_analytic
  结论: (hf : MeromorphicNFAt f x)
  证明: by
  rcases hf with h₁f | ⟨n, g_f, h₁g_f, h₂g_f, h₃g_f⟩
  · left
    filter_upwards [h₁f]
    simp_all
  · right
    use n, g • g_f, h₁g.smul h₁g_f
    constructor
    · simp [smul_ne_zero h₂g h₂g_f]
    · filter_upwards [h₃g_f]
      intro y hy
      simp only [Pi.smul_apply', hy, Pi.pow_apply]
   

Depends on / 依赖: Pi.pow_apply, Pi.smul_apply, filter_upwards, g.smul, pow_apply, smul_apply, smul_comm, smul_ne_zero
-/
lemma MeromorphicNFAt.smul_analytic (hf : MeromorphicNFAt f x)
    (h₁g : AnalyticAt 𝕜 g x) (h₂g : g x != 0) :
    MeromorphicNFAt (g • f) x := by
  rcases hf with h₁f | ⟨n, g_f, h₁g_f, h₂g_f, h₃g_f⟩
  · left
    filter_upwards [h₁f]
    simp_all
  · right
    use n, g • g_f, h₁g.smul h₁g_f
    constructor
    · simp [smul_ne_zero h₂g h₂g_f]
    · filter_upwards [h₃g_f]
      intro y hy
      simp only [Pi.smul_apply', hy, Pi.pow_apply]
      rw [smul_comm]

/--
theorem `meromorphicNFAt_smul_iff_right_of_analyticAt` / 定理 `meromorphicNFAt_smul_iff_right_of_analyticAt`

English:
theorem meromorphicNFAt_smul_iff_right_of_analyticAt
  statement: (h₁g : AnalyticAt 𝕜 g x)
  proof: by
    have : f =ᶠ[𝓝 x] g⁻¹ • g • f := by
      filter_upwards [h₁g.continuousAt.preimage_mem_nhds (compl_singleton_mem_nhds_iff.mpr h₂g)]
      intro y hy
      rw [Set.preimage_compl]; rw [Set.mem_compl_iff]; rw [Set.mem_preimage]; rw [Set.mem_singleton_iff] at hy
      simp [hy]
    rw [meromorph

中文:
定理 meromorphicNFAt_smul_iff_right_of_analyticAt
  结论: (h₁g : AnalyticAt 𝕜 g x)
  证明: by
    have : f =ᶠ[𝓝 x] g⁻¹ • g • f := by
      filter_upwards [h₁g.continuousAt.preimage_mem_nhds (compl_singleton_mem_nhds_iff.mpr h₂g)]
      intro y hy
      rw [Set.preimage_compl]; rw [Set.mem_compl_iff]; rw [Set.mem_preimage]; rw [Set.mem_singleton_iff] at hy
      simp [hy]
    rw [meromorph

Depends on / 依赖: Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.preimage_compl, compl_singleton_mem_nhds_iff, compl_singleton_mem_nhds_iff.mpr, continuousAt, filter_upwards, g.continuousAt.preimage_mem_nhds, g.inv, hf.smul_analytic, hprod.smul_analytic, inv_ne_zero, mem_compl_iff, mem_preimage, mem_singleton_iff, meromorphicNFAt_congr, preimage_compl, preimage_mem_nhds, smul_analytic
-/
theorem meromorphicNFAt_smul_iff_right_of_analyticAt (h₁g : AnalyticAt 𝕜 g x)
    (h₂g : g x != 0) :
    MeromorphicNFAt (g • f) x ↔ MeromorphicNFAt f x where
  mp hprod := by
    have : f =ᶠ[𝓝 x] g⁻¹ • g • f := by
      filter_upwards [h₁g.continuousAt.preimage_mem_nhds (compl_singleton_mem_nhds_iff.mpr h₂g)]
      intro y hy
      rw [Set.preimage_compl]; rw [Set.mem_compl_iff]; rw [Set.mem_preimage]; rw [Set.mem_singleton_iff] at hy
      simp [hy]
    rw [meromorphicNFAt_congr this]
    exact hprod.smul_analytic (h₁g.inv h₂g) (inv_ne_zero h₂g)
  mpr hf := hf.smul_analytic h₁g h₂g

/--
theorem `meromorphicNFAt_mul_iff_right` / 定理 `meromorphicNFAt_mul_iff_right`

English:
theorem meromorphicNFAt_mul_iff_right
  statement: {f : 𝕜 -> 𝕜} (h₁g : AnalyticAt 𝕜 g x)
  proof: meromorphicNFAt_smul_iff_right_of_analyticAt h₁g h₂g

中文:
定理 meromorphicNFAt_mul_iff_right
  结论: {f : 𝕜 -> 𝕜} (h₁g : AnalyticAt 𝕜 g x)
  证明: meromorphicNFAt_smul_iff_right_of_analyticAt h₁g h₂g

Depends on / 依赖: meromorphicNFAt_smul_iff_right_of_analyticAt
-/
theorem meromorphicNFAt_mul_iff_right {f : 𝕜 -> 𝕜} (h₁g : AnalyticAt 𝕜 g x)
    (h₂g : g x != 0) :
    MeromorphicNFAt (g * f) x ↔ MeromorphicNFAt f x :=
  meromorphicNFAt_smul_iff_right_of_analyticAt h₁g h₂g

/--
theorem `meromorphicNFAt_mul_iff_left` / 定理 `meromorphicNFAt_mul_iff_left`

English:
theorem meromorphicNFAt_mul_iff_left
  statement: {f : 𝕜 -> 𝕜} (h₁g : AnalyticAt 𝕜 g x)
  proof: by
  rw [mul_comm]; rw [← smul_eq_mul]
  exact meromorphicNFAt_smul_iff_right_of_analyticAt h₁g h₂g

中文:
定理 meromorphicNFAt_mul_iff_left
  结论: {f : 𝕜 -> 𝕜} (h₁g : AnalyticAt 𝕜 g x)
  证明: by
  rw [mul_comm]; rw [← smul_eq_mul]
  exact meromorphicNFAt_smul_iff_right_of_analyticAt h₁g h₂g

Depends on / 依赖: meromorphicNFAt_smul_iff_right_of_analyticAt, mul_comm, smul_eq_mul
-/
theorem meromorphicNFAt_mul_iff_left {f : 𝕜 -> 𝕜} (h₁g : AnalyticAt 𝕜 g x)
    (h₂g : g x != 0) :
    MeromorphicNFAt (f * g) x ↔ MeromorphicNFAt f x := by
  rw [mul_comm]; rw [← smul_eq_mul]
  exact meromorphicNFAt_smul_iff_right_of_analyticAt h₁g h₂g

/--
theorem `meromorphicNFAt_prod` / 定理 `meromorphicNFAt_prod`

English:
theorem meromorphicNFAt_prod
  statement: {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜}
  proof: by
  classical
  have h₃f {τ : ι} (h₁τ : τ in s) (h₂τ : τ ∉ {σ in s | f σ x = 0}) :
      AnalyticAt 𝕜 (f τ) x := by
    rw [← (h₁f τ h₁τ).meromorphicOrderAt_nonneg_iff_analyticAt]
    apply ((h₁f τ h₁τ).meromorphicOrderAt_eq_zero_iff.2 _).symm.le
    grind
  by_cases h₄f : {σ in s | f σ x = 0} = ∅


中文:
定理 meromorphicNFAt_prod
  结论: {x : 𝕜} {ι : 类型} {s : 有限集 ι} {f : ι -> 𝕜 -> 𝕜}
  证明: by
  classical
  have h₃f {τ : ι} (h₁τ : τ in s) (h₂τ : τ ∉ {σ in s | f σ x = 0}) :
      AnalyticAt 𝕜 (f τ) x := by
    rw [← (h₁f τ h₁τ).meromorphicOrderAt_nonneg_iff_analyticAt]
    apply ((h₁f τ h₁τ).meromorphicOrderAt_eq_zero_iff.2 _).symm.le
    grind
  by_cases h₄f : {σ in s | f σ x = 0} = ∅


Depends on / 依赖: AnalyticAt, Finset, Finset.analyticAt_prod, Finset.filter_eq_empty_iff, analyticAt_prod, by_c, classical, filter_eq_empty_iff, meromorphicNFAt, meromorphicOrderAt_eq_zero_iff, meromorphicOrderAt_nonneg_iff_analyticAt, s.erase, symm.le
-/
theorem meromorphicNFAt_prod {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜}
    (h₁f : forall i in s, MeromorphicNFAt (f i) x)
    (h₂f : Set.Subsingleton {σ in s | f σ x = 0}) :
    MeromorphicNFAt (∏ i in s, f i) x := by
  classical
  have h₃f {τ : ι} (h₁τ : τ in s) (h₂τ : τ ∉ {σ in s | f σ x = 0}) :
      AnalyticAt 𝕜 (f τ) x := by
    rw [← (h₁f τ h₁τ).meromorphicOrderAt_nonneg_iff_analyticAt]
    apply ((h₁f τ h₁τ).meromorphicOrderAt_eq_zero_iff.2 _).symm.le
    grind
  by_cases h₄f : {σ in s | f σ x = 0} = ∅
  · exact (Finset.analyticAt_prod _ (fun σ hσ => h₃f hσ (by aesop))).meromorphicNFAt
  rw [Finset.filter_eq_empty_iff] at h₄f
  push Not at h₄f
  obtain ⟨τ, h₁τ, h₂τ⟩ := h₄f
  have {μ : ι} (hμ : μ in s.erase τ) : f μ x != 0 := by
    by_contra
    have : τ = μ := h₂f (by aesop) (by aesop)
    aesop
  rw [← Finset.mul_prod_erase _ _ h₁τ]; rw [meromorphicNFAt_mul_iff_left]
  · apply h₁f τ h₁τ
  · apply Finset.analyticAt_prod _ (fun μ hμ => h₃f (Finset.mem_of_mem_erase hμ) (by aesop))
  · rw [Finset.prod_apply, Finset.prod_ne_zero_iff]
    aesop

/--
theorem `meromorphicNFAt_fun_prod` / 定理 `meromorphicNFAt_fun_prod`

English:
theorem meromorphicNFAt_fun_prod
  statement: {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜}
  proof: by
  convert! meromorphicNFAt_prod h₁f h₂f
  exact (Finset.prod_apply _ s f).symm

中文:
定理 meromorphicNFAt_fun_prod
  结论: {x : 𝕜} {ι : 类型} {s : 有限集 ι} {f : ι -> 𝕜 -> 𝕜}
  证明: by
  convert! meromorphicNFAt_prod h₁f h₂f
  exact (Finset.prod_apply _ s f).symm

Depends on / 依赖: Finset, Finset.prod_apply, convert, meromorphicNFAt_prod, prod_apply
-/
theorem meromorphicNFAt_fun_prod {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜}
    (h₁f : forall i in s, MeromorphicNFAt (f i) x)
    (h₂f : Set.Subsingleton {σ in s | f σ x = 0}) :
    MeromorphicNFAt (fun a => ∏ i in s, f i a) x := by
  convert! meromorphicNFAt_prod h₁f h₂f
  exact (Finset.prod_apply _ s f).symm

/--
theorem `meromorphicNFAt_finprod` / 定理 `meromorphicNFAt_finprod`

English:
theorem meromorphicNFAt_finprod
  statement: {x : 𝕜} {ι : Type*} {f : ι -> 𝕜 -> 𝕜}
  proof: by
  by_cases h₃f : Function.HasFiniteMulSupport f
  · simp_rw [finprod_eq_prod f h₃f]
    exact meromorphicNFAt_prod (by aesop) (fun _ _ _ _ => by aesop)
  · exact finprod_of_not_hasFiniteMulSupport h₃f ▸ analyticAt_const.meromorphicNFAt

中文:
定理 meromorphicNFAt_finprod
  结论: {x : 𝕜} {ι : 类型} {f : ι -> 𝕜 -> 𝕜}
  证明: by
  by_cases h₃f : Function.HasFiniteMulSupport f
  · simp_rw [finprod_eq_prod f h₃f]
    exact meromorphicNFAt_prod (by aesop) (fun _ _ _ _ => by aesop)
  · exact finprod_of_not_hasFiniteMulSupport h₃f ▸ analyticAt_const.meromorphicNFAt

Depends on / 依赖: Function, Function.HasFiniteMulSupport, HasFiniteMulSupport, analyticAt_const, analyticAt_const.meromorphicNFAt, finprod_eq_prod, finprod_of_not_hasFiniteMulSupport, meromorphicNFAt, meromorphicNFAt_prod, simp_rw
-/
theorem meromorphicNFAt_finprod {x : 𝕜} {ι : Type*} {f : ι -> 𝕜 -> 𝕜}
    (h₁f : forall i, MeromorphicNFAt (f i) x) (h₂f : Set.Subsingleton {σ | f σ x = 0}) :
    MeromorphicNFAt (∏ᶠ i, f i) x := by
  by_cases h₃f : Function.HasFiniteMulSupport f
  · simp_rw [finprod_eq_prod f h₃f]
    exact meromorphicNFAt_prod (by aesop) (fun _ _ _ _ => by aesop)
  · exact finprod_of_not_hasFiniteMulSupport h₃f ▸ analyticAt_const.meromorphicNFAt

/--
Integer powers of meromorphic functions in normal form are in normal form.
-/
@[to_fun]
/--
theorem `MeromorphicNFAt.zpow` / 定理 `MeromorphicNFAt.zpow`

English:
theorem MeromorphicNFAt.zpow
  given: {f : 𝕜 -> 𝕜} {n : Int} {x : 𝕜} (hf : MeromorphicNFAt f x)
  proof: by
  by_cases hn : n = 0
  · simp_all only [zpow_zero]
    apply AnalyticAt.meromorphicNFAt
    apply analyticAt_const
  rcases hf with hf | hf
  · left
    filter_upwards [hf] with z hz
    simp_all only [Pi.zero_apply, Pi.pow_apply, zero_zpow n hn]
  · obtain ⟨m, g, h₁g, h₂g, h₃g⟩ := hf
    right


中文:
定理 MeromorphicNFAt.zpow
  条件: {f : 𝕜 -> 𝕜} {n : 整数} {x : 𝕜} (hf : MeromorphicNFAt f x)
  证明: by
  by_cases hn : n = 0
  · simp_all only [zpow_zero]
    apply AnalyticAt.meromorphicNFAt
    apply analyticAt_const
  rcases hf with hf | hf
  · left
    filter_upwards [hf] with z hz
    simp_all only [Pi.zero_apply, Pi.pow_apply, zero_zpow n hn]
  · obtain ⟨m, g, h₁g, h₂g, h₃g⟩ := hf
    right


Depends on / 依赖: AnalyticAt, AnalyticAt.meromorphicNFAt, Pi.pow_apply, Pi.zero_apply, analyticAt_const, filter_upwards, g.zpow, meromorphicNFAt, mul_zpow, pow_apply, zero_apply, zero_zpow, zpow_mul, zpow_ne_zero, zpow_zero
-/
theorem MeromorphicNFAt.zpow {f : 𝕜 -> 𝕜} {n : Int} {x : 𝕜} (hf : MeromorphicNFAt f x) :
    MeromorphicNFAt (f ^ n) x := by
  by_cases hn : n = 0
  · simp_all only [zpow_zero]
    apply AnalyticAt.meromorphicNFAt
    apply analyticAt_const
  rcases hf with hf | hf
  · left
    filter_upwards [hf] with z hz
    simp_all only [Pi.zero_apply, Pi.pow_apply, zero_zpow n hn]
  · obtain ⟨m, g, h₁g, h₂g, h₃g⟩ := hf
    right
    use n * m, g ^ n, h₁g.zpow h₂g
    constructor
    · rw [Pi.pow_apply]
      exact zpow_ne_zero n h₂g
    · filter_upwards [h₃g] with z hz
      simp [hz, mul_zpow, (zpow_mul' (z - x) n m).symm]

/--
theorem `MeromorphicNFAt.inv` / 定理 `MeromorphicNFAt.inv`

English:
theorem MeromorphicNFAt.inv
  given: {f : 𝕜 -> 𝕜} (hf : MeromorphicNFAt f x)
  proof: by
  rcases hf with h | ⟨n, g, h₁, h₂, h₃⟩
  · left
    filter_upwards [h] with x hx
    simp [hx]
  · right
    use -n, g⁻¹, h₁.inv h₂, (by simp_all)
    filter_upwards [h₃] with y hy
    simp only [Pi.inv_apply, hy, Pi.smul_apply', Pi.pow_apply, smul_eq_mul, mul_inv_rev, zpow_neg]
    ring

中文:
定理 MeromorphicNFAt.inv
  条件: {f : 𝕜 -> 𝕜} (hf : MeromorphicNFAt f x)
  证明: by
  rcases hf with h | ⟨n, g, h₁, h₂, h₃⟩
  · left
    filter_upwards [h] with x hx
    simp [hx]
  · right
    use -n, g⁻¹, h₁.inv h₂, (by simp_all)
    filter_upwards [h₃] with y hy
    simp only [Pi.inv_apply, hy, Pi.smul_apply', Pi.pow_apply, smul_eq_mul, mul_inv_rev, zpow_neg]
    ring

Depends on / 依赖: Pi.inv_apply, Pi.pow_apply, Pi.smul_apply, filter_upwards, inv_apply, mul_inv_rev, pow_apply, smul_apply, smul_eq_mul, zpow_neg
-/
theorem MeromorphicNFAt.inv {f : 𝕜 -> 𝕜} (hf : MeromorphicNFAt f x) :
    MeromorphicNFAt f⁻¹ x := by
  rcases hf with h | ⟨n, g, h₁, h₂, h₃⟩
  · left
    filter_upwards [h] with x hx
    simp [hx]
  · right
    use -n, g⁻¹, h₁.inv h₂, (by simp_all)
    filter_upwards [h₃] with y hy
    simp only [Pi.inv_apply, hy, Pi.smul_apply', Pi.pow_apply, smul_eq_mul, mul_inv_rev, zpow_neg]
    ring

/--
theorem `meromorphicNFAt_inv` / 定理 `meromorphicNFAt_inv`

English:
theorem meromorphicNFAt_inv
  given: {f : 𝕜 -> 𝕜}
  statement: MeromorphicNFAt f⁻¹ x ↔ MeromorphicNFAt f x where
  proof: inv_inv f ▸ hf.inv
  mpr hf := hf.inv

中文:
定理 meromorphicNFAt_inv
  条件: {f : 𝕜 -> 𝕜}
  结论: MeromorphicNFAt f⁻¹ x ↔ MeromorphicNFAt f x where
  证明: inv_inv f ▸ hf.inv
  mpr hf := hf.inv
-/
@[simp] theorem meromorphicNFAt_inv {f : 𝕜 -> 𝕜} : MeromorphicNFAt f⁻¹ x ↔ MeromorphicNFAt f x where
  mp hf := inv_inv f ▸ hf.inv
  mpr hf := hf.inv

/--
theorem `MeromorphicNFOn.div` / 定理 `MeromorphicNFOn.div`

English:
theorem MeromorphicNFOn.div
  statement: {f : 𝕜 -> 𝕜} {g : 𝕜 -> 𝕜} {x : 𝕜} (hf : AnalyticAt 𝕜 f x)
  proof: by
  rw [div_eq_mul_inv]
  rcases hor with hgne | hfne
  · have hf := hf.meromorphicNFAt
    have hgAnalytic : AnalyticAt 𝕜 g x := by grind [meromorphicNFAt_iff_analyticAt_or]
    have hgInvAnalytic : AnalyticAt 𝕜 g⁻¹ x := hgAnalytic.inv hgne
    rwa [← meromorphicNFAt_mul_iff_left hgInvAnalytic (in

中文:
定理 MeromorphicNFOn.div
  结论: {f : 𝕜 -> 𝕜} {g : 𝕜 -> 𝕜} {x : 𝕜} (hf : AnalyticAt 𝕜 f x)
  证明: by
  rw [div_eq_mul_inv]
  rcases hor with hgne | hfne
  · have hf := hf.meromorphicNFAt
    have hgAnalytic : AnalyticAt 𝕜 g x := by grind [meromorphicNFAt_iff_analyticAt_or]
    have hgInvAnalytic : AnalyticAt 𝕜 g⁻¹ x := hgAnalytic.inv hgne
    rwa [← meromorphicNFAt_mul_iff_left hgInvAnalytic (in

Depends on / 依赖: AnalyticAt, div_eq_mul_inv, hf.meromorphicNFAt, hg.inv, hgAnalytic, hgAnalytic.inv, hgInvAnalytic, inv_ne_zero, meromorphicNFAt, meromorphicNFAt_iff_analyticAt_or, meromorphicNFAt_mul_iff_left, meromorphicNFAt_mul_iff_right
-/
theorem MeromorphicNFOn.div {f : 𝕜 -> 𝕜} {g : 𝕜 -> 𝕜} {x : 𝕜} (hf : AnalyticAt 𝕜 f x)
    (hg : MeromorphicNFAt g x) (hor : g x != 0 ∨ f x != 0) : MeromorphicNFAt (f / g) x := by
  rw [div_eq_mul_inv]
  rcases hor with hgne | hfne
  · have hf := hf.meromorphicNFAt
    have hgAnalytic : AnalyticAt 𝕜 g x := by grind [meromorphicNFAt_iff_analyticAt_or]
    have hgInvAnalytic : AnalyticAt 𝕜 g⁻¹ x := hgAnalytic.inv hgne
    rwa [← meromorphicNFAt_mul_iff_left hgInvAnalytic (inv_ne_zero hgne)] at hf
  · grind [meromorphicNFAt_mul_iff_right, hg.inv]

/--
The composition of a meromorphic function in normal form and an analytic
function is meromorphic in normal form.
-/
@[fun_prop]
/--
theorem `MeromorphicNFAt.comp_analyticAt` / 定理 `MeromorphicNFAt.comp_analyticAt`

English:
theorem MeromorphicNFAt.comp_analyticAt
  given: (hf : MeromorphicNFAt f (g x)) (hg : AnalyticAt 𝕜 g x)
  proof: by
  rcases hf with hf | ⟨n, q, hq_an, hq_ne, hf⟩
  · exact Or.inl (hg.continuousAt.tendsto.eventually hf)
  by_cases hord : analyticOrderAt (g · - g x) x = ⊤
  · rw [analyticOrderAt_eq_top] at hord
    by_cases h : f (g x) = 0
    · apply Or.inl
      filter_upwards [hord, hg.continuousAt.preimage_

中文:
定理 MeromorphicNFAt.comp_analyticAt
  条件: (hf : MeromorphicNFAt f (g x)) (hg : AnalyticAt 𝕜 g x)
  证明: by
  rcases hf with hf | ⟨n, q, hq_an, hq_ne, hf⟩
  · exact Or.inl (hg.continuousAt.tendsto.eventually hf)
  by_cases hord : analyticOrderAt (g · - g x) x = ⊤
  · rw [analyticOrderAt_eq_top] at hord
    by_cases h : f (g x) = 0
    · apply Or.inl
      filter_upwards [hord, hg.continuousAt.preimage_

Depends on / 依赖: Or.inl, Or.inr, analyticOrderAt, analyticOrderAt_eq_top, continuousAt, eventually, filter_mono, filter_upwards, fun_prop, hf.filter_mono, hg.continuousAt.preimage_mem_nhds, hg.continuousAt.tendsto.eventually, hq_an, hq_ne, preimage_mem_nhds, sub_eq_zero, tendsto
-/
theorem MeromorphicNFAt.comp_analyticAt (hf : MeromorphicNFAt f (g x)) (hg : AnalyticAt 𝕜 g x) :
    MeromorphicNFAt (f ∘ g) x := by
  rcases hf with hf | ⟨n, q, hq_an, hq_ne, hf⟩
  · exact Or.inl (hg.continuousAt.tendsto.eventually hf)
  by_cases hord : analyticOrderAt (g · - g x) x = ⊤
  · rw [analyticOrderAt_eq_top] at hord
    by_cases h : f (g x) = 0
    · apply Or.inl
      filter_upwards [hord, hg.continuousAt.preimage_mem_nhds (hf.filter_mono (by simp))]
        using by simp_all [sub_eq_zero]
    · refine Or.inr ⟨0, fun _ => f (g x), by fun_prop, h, ?_⟩
      filter_upwards [hord, hg.continuousAt.preimage_mem_nhds (hf.filter_mono (by simp))]
        using by simp_all [sub_eq_zero]
  lift analyticOrderAt (g · - g x) x to Nat using hord with m hm
  obtain ⟨p, h₁p, h₂p, h₃p⟩ := (AnalyticAt.analyticOrderAt_eq_natCast (by fun_prop)).1 hm.symm
  refine Or.inr ⟨n * m, fun z => (p z) ^ n • q (g z), (h₁p.zpow h₂p).smul (by fun_prop), ?_⟩
  simp_all only [ne_eq, smul_eq_mul, isUnit_iff_ne_zero, zpow_ne_zero n h₂p, not_false_eq_true,
    IsUnit.smul_eq_zero, true_and]
  filter_upwards [h₃p, hg.continuousAt.preimage_mem_nhds (hf.filter_mono (by simp))]
    with a h₁a h₂a
  simp_all only [Pi.smul_apply', Pi.pow_apply, Set.preimage_ofPred_eq, Set.mem_ofPred_eq,
    Function.comp_apply, ← smul_assoc, mul_zpow, smul_eq_mul]
  congr 2
  rw [mul_comm]; rw [zpow_mul]; rw [zpow_natCast]

/--
theorem `meromorphicNFAt_comp_iff_of_deriv_ne_zero` / 定理 `meromorphicNFAt_comp_iff_of_deriv_ne_zero`

English:
theorem meromorphicNFAt_comp_iff_of_deriv_ne_zero
  statement: [CompleteSpace 𝕜] [CharZero 𝕜] {x : 𝕜}
  proof: by
  simp [meromorphicNFAt_iff_analyticAt_or, analyticAt_comp_iff_of_deriv_ne_zero hg hg',
    meromorphicAt_comp_iff_of_deriv_ne_zero hg hg',
    meromorphicOrderAt_comp_of_deriv_ne_zero hg hg']

中文:
定理 meromorphicNFAt_comp_iff_of_deriv_ne_zero
  结论: [完备空间 𝕜] [特征零 𝕜] {x : 𝕜}
  证明: by
  simp [meromorphicNFAt_iff_analyticAt_or, analyticAt_comp_iff_of_deriv_ne_zero hg hg',
    meromorphicAt_comp_iff_of_deriv_ne_zero hg hg',
    meromorphicOrderAt_comp_of_deriv_ne_zero hg hg']

Depends on / 依赖: analyticAt_comp_iff_of_deriv_ne_zero, meromorphicAt_comp_iff_of_deriv_ne_zero, meromorphicNFAt_iff_analyticAt_or, meromorphicOrderAt_comp_of_deriv_ne_zero
-/
theorem meromorphicNFAt_comp_iff_of_deriv_ne_zero [CompleteSpace 𝕜] [CharZero 𝕜] {x : 𝕜}
    {g : 𝕜 -> 𝕜} (hg : AnalyticAt 𝕜 g x) (hg' : deriv g x != 0) :
    MeromorphicNFAt (f ∘ g) x ↔ MeromorphicNFAt f (g x) := by
  simp [meromorphicNFAt_iff_analyticAt_or, analyticAt_comp_iff_of_deriv_ne_zero hg hg',
    meromorphicAt_comp_iff_of_deriv_ne_zero hg hg',
    meromorphicOrderAt_comp_of_deriv_ne_zero hg hg']

/-- `MeromorphicNFAt` is invariant under translation. -/
@[to_fun meromorphicNFAt_fun_comp_add_const_iff_meromorphicNFAt]
/--
theorem `meromorphicNFAt_comp_add_const_iff_meromorphicNFAt` / 定理 `meromorphicNFAt_comp_add_const_iff_meromorphicNFAt`

English:
theorem meromorphicNFAt_comp_add_const_iff_meromorphicNFAt
  given: {c : 𝕜} {f : 𝕜 -> E}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [show f = ((f ∘ fun x => x + c) ∘ fun z => z - c) by aesop]
    rw [show x = (x + c) - c by ring] at h
    exact h.comp_analyticAt (g := fun z => z - c) (by fun_prop)
  · exact h.comp_analyticAt (g := fun z => z + c) (by fun_prop)

中文:
定理 meromorphicNFAt_comp_add_const_iff_meromorphicNFAt
  条件: {c : 𝕜} {f : 𝕜 -> E}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [show f = ((f ∘ fun x => x + c) ∘ fun z => z - c) by aesop]
    rw [show x = (x + c) - c by ring] at h
    exact h.comp_analyticAt (g := fun z => z - c) (by fun_prop)
  · exact h.comp_analyticAt (g := fun z => z + c) (by fun_prop)

Depends on / 依赖: comp_analyticAt, fun_prop, h.comp_analyticAt
-/
theorem meromorphicNFAt_comp_add_const_iff_meromorphicNFAt {c : 𝕜} {f : 𝕜 -> E} :
    MeromorphicNFAt (f ∘ (· + c)) x ↔ MeromorphicNFAt f (x + c) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [show f = ((f ∘ fun x => x + c) ∘ fun z => z - c) by aesop]
    rw [show x = (x + c) - c by ring] at h
    exact h.comp_analyticAt (g := fun z => z - c) (by fun_prop)
  · exact h.comp_analyticAt (g := fun z => z + c) (by fun_prop)

/-- `MeromorphicNFAt` is invariant under translation. -/
@[to_fun meromorphicNFAt_fun_comp_sub_const_iff_meromorphicNFAt]
/--
theorem `meromorphicNFAt_comp_sub_const_iff_meromorphicNFAt` / 定理 `meromorphicNFAt_comp_sub_const_iff_meromorphicNFAt`

English:
theorem meromorphicNFAt_comp_sub_const_iff_meromorphicNFAt
  given: {c : 𝕜} {f : 𝕜 -> E}
  proof: by
  simp_rw [sub_eq_add_neg, meromorphicNFAt_comp_add_const_iff_meromorphicNFAt]

中文:
定理 meromorphicNFAt_comp_sub_const_iff_meromorphicNFAt
  条件: {c : 𝕜} {f : 𝕜 -> E}
  证明: by
  simp_rw [sub_eq_add_neg, meromorphicNFAt_comp_add_const_iff_meromorphicNFAt]

Depends on / 依赖: meromorphicNFAt_comp_add_const_iff_meromorphicNFAt, simp_rw, sub_eq_add_neg
-/
theorem meromorphicNFAt_comp_sub_const_iff_meromorphicNFAt {c : 𝕜} {f : 𝕜 -> E} :
    MeromorphicNFAt (f ∘ (· - c)) x ↔ MeromorphicNFAt f (x - c) := by
  simp_rw [sub_eq_add_neg, meromorphicNFAt_comp_add_const_iff_meromorphicNFAt]

/-!
### Continuous extension and conversion to normal form
-/

variable (f x) in
/--
Definition of `toMeromorphicNFAt` / `toMeromorphicNFAt` 的定义

English:
definition toMeromorphicNFAt
  signature: :
  body: by
  by_cases hf : MeromorphicAt f x
  · classical -- do not complain about decidability issues in Function.update
    apply Function.update f x
    by_cases h₁f : meromorphicOrderAt f x = (0 : Int)
    · rw [meromorphicOrderAt_eq_int_iff hf] at h₁f
      exact (Classical.choose h₁f) x
    · exact 0

中文:
定义 toMeromorphicNFAt
  签名: :
  定义体: by
  by_cases hf : MeromorphicAt f x
  · classical -- do not complain about decidability issues in Function.update
    apply Function.update f x
    by_cases h₁f : meromorphicOrderAt f x = (0 : Int)
    · rw [meromorphicOrderAt_eq_int_iff hf] at h₁f
      exact (Classical.choose h₁f) x
    · exact 0

Depends on / 依赖: Classical, Classical.choose, Function, Function.update, MeromorphicAt, classical, complain, decidability, issues, meromorphicOrderAt, meromorphicOrderAt_eq_int_iff, update
-/
noncomputable def toMeromorphicNFAt :
    𝕜 -> E := by
  by_cases hf : MeromorphicAt f x
  · classical -- do not complain about decidability issues in Function.update
    apply Function.update f x
    by_cases h₁f : meromorphicOrderAt f x = (0 : Int)
    · rw [meromorphicOrderAt_eq_int_iff hf] at h₁f
      exact (Classical.choose h₁f) x
    · exact 0
  · exact 0

/--
lemma `MeromorphicAt.eqOn_compl_singleton_toMeromorphicNFAt` / 引理 `MeromorphicAt.eqOn_compl_singleton_toMeromorphicNFAt`

English:
lemma MeromorphicAt.eqOn_compl_singleton_toMeromorphicNFAt
  given: (hf : MeromorphicAt f x)
  proof: fun _ _ => by simp_all [toMeromorphicNFAt]

中文:
引理 MeromorphicAt.eqOn_compl_singleton_toMeromorphicNFAt
  条件: (hf : MeromorphicAt f x)
  证明: fun _ _ => by simp_all [toMeromorphicNFAt]

Depends on / 依赖: toMeromorphicNFAt
-/
lemma MeromorphicAt.eqOn_compl_singleton_toMeromorphicNFAt (hf : MeromorphicAt f x) :
    Set.EqOn f (toMeromorphicNFAt f x) {x}ᶜ :=
  fun _ _ => by simp_all [toMeromorphicNFAt]

/--
lemma `toMeromorphicNFAt_of_not_meromorphicAt` / 引理 `toMeromorphicNFAt_of_not_meromorphicAt`

English:
lemma toMeromorphicNFAt_of_not_meromorphicAt
  given: (hf : ¬MeromorphicAt f x)
  proof: by
  simp [toMeromorphicNFAt, hf]

中文:
引理 toMeromorphicNFAt_of_not_meromorphicAt
  条件: (hf : ¬MeromorphicAt f x)
  证明: by
  simp [toMeromorphicNFAt, hf]
-/
@[simp] lemma toMeromorphicNFAt_of_not_meromorphicAt (hf : ¬MeromorphicAt f x) :
    toMeromorphicNFAt f x = 0 := by
  simp [toMeromorphicNFAt, hf]

/--
lemma `toMeromorphicNFAt_of_meromorphicOrderAt_ne_zero` / 引理 `toMeromorphicNFAt_of_meromorphicOrderAt_ne_zero`

English:
lemma toMeromorphicNFAt_of_meromorphicOrderAt_ne_zero
  proof: by
  simp [toMeromorphicNFAt, meromorphicAt_of_meromorphicOrderAt_ne_zero, horder]

中文:
引理 toMeromorphicNFAt_of_meromorphicOrderAt_ne_zero
  证明: by
  simp [toMeromorphicNFAt, meromorphicAt_of_meromorphicOrderAt_ne_zero, horder]
-/
@[simp] lemma toMeromorphicNFAt_of_meromorphicOrderAt_ne_zero
    (horder : meromorphicOrderAt f x != 0) : toMeromorphicNFAt f x x = 0 := by
  simp [toMeromorphicNFAt, meromorphicAt_of_meromorphicOrderAt_ne_zero, horder]

/--
lemma `MeromorphicAt.eq_nhdsNE_toMeromorphicNFAt` / 引理 `MeromorphicAt.eq_nhdsNE_toMeromorphicNFAt`

English:
lemma MeromorphicAt.eq_nhdsNE_toMeromorphicNFAt
  given: (hf : MeromorphicAt f x)
  proof: eventually_nhdsWithin_of_forall (fun _ hz => hf.eqOn_compl_singleton_toMeromorphicNFAt hz)

中文:
引理 MeromorphicAt.eq_nhdsNE_toMeromorphicNFAt
  条件: (hf : MeromorphicAt f x)
  证明: eventually_nhdsWithin_of_forall (fun _ hz => hf.eqOn_compl_singleton_toMeromorphicNFAt hz)

Depends on / 依赖: eqOn_compl_singleton_toMeromorphicNFAt, eventually_nhdsWithin_of_forall, hf.eqOn_compl_singleton_toMeromorphicNFAt
-/
lemma MeromorphicAt.eq_nhdsNE_toMeromorphicNFAt (hf : MeromorphicAt f x) :
    f =ᶠ[𝓝[!=] x] toMeromorphicNFAt f x :=
  eventually_nhdsWithin_of_forall (fun _ hz => hf.eqOn_compl_singleton_toMeromorphicNFAt hz)

/--
theorem `meromorphicNFAt_toMeromorphicNFAt` / 定理 `meromorphicNFAt_toMeromorphicNFAt`

English:
theorem meromorphicNFAt_toMeromorphicNFAt
  proof: by
  by_cases hf : MeromorphicAt f x
  · by_cases h₂f : meromorphicOrderAt f x = ⊤
    · have : toMeromorphicNFAt f x =ᶠ[𝓝 x] 0 := by
        apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
        · exact hf.eq_nhdsNE_toMeromorphicNFAt.symm.trans (meromorphicOrderAt_eq_top_iff.1 h₂f)
        · simp 

中文:
定理 meromorphicNFAt_toMeromorphicNFAt
  证明: by
  by_cases hf : MeromorphicAt f x
  · by_cases h₂f : meromorphicOrderAt f x = ⊤
    · have : toMeromorphicNFAt f x =ᶠ[𝓝 x] 0 := by
        apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
        · exact hf.eq_nhdsNE_toMeromorphicNFAt.symm.trans (meromorphicOrderAt_eq_top_iff.1 h₂f)
        · simp 

Depends on / 依赖: AnalyticAt, AnalyticAt.meromorphicNFAt, MeromorphicAt, analyticAt_congr, analyticAt_const, eq_nhdsNE_toMeromorphicNFAt, eventuallyEq_nhds_of_eventuallyEq_nhdsNE, hf.eq_nhdsNE_toMeromorphicNFAt.symm.trans, meromorphicNFAt, meromorphicOrderAt, meromorphicOrderAt_eq_int_iff, meromorphicOrderAt_eq_top_iff, toMeromorphicNFAt
-/
theorem meromorphicNFAt_toMeromorphicNFAt :
    MeromorphicNFAt (toMeromorphicNFAt f x) x := by
  by_cases hf : MeromorphicAt f x
  · by_cases h₂f : meromorphicOrderAt f x = ⊤
    · have : toMeromorphicNFAt f x =ᶠ[𝓝 x] 0 := by
        apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
        · exact hf.eq_nhdsNE_toMeromorphicNFAt.symm.trans (meromorphicOrderAt_eq_top_iff.1 h₂f)
        · simp [h₂f, toMeromorphicNFAt, hf]
      apply AnalyticAt.meromorphicNFAt
      rw [analyticAt_congr this]
      exact analyticAt_const
    · lift meromorphicOrderAt f x to Int using h₂f with n hn
      obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hn.symm
      right
      use n, g, h₁g, h₂g
      apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE (hf.eq_nhdsNE_toMeromorphicNFAt.symm.trans h₃g)
      simp only [toMeromorphicNFAt, hf, ↓reduceDIte, ← hn, WithTop.coe_zero,
        WithTop.coe_eq_zero, ne_eq, Function.update_self, sub_self]
      split_ifs with h₃f
      · obtain ⟨h₁G, _, h₃G⟩ :=
          Classical.choose_spec ((meromorphicOrderAt_eq_int_iff hf).1 (h₃f ▸ hn.symm))
        apply Filter.EventuallyEq.eq_of_nhds
        apply (h₁G.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (by fun_prop)).1
        filter_upwards [h₃g, h₃G]
        simp_all
      · simp [h₃f, zero_zpow]
  · simp only [toMeromorphicNFAt, hf, ↓reduceDIte]
    exact analyticAt_const.meromorphicNFAt

@[simp]
/--
lemma `MeromorphicAt.meromorphicOrderAt_toMeromorphicNFAt` / 引理 `MeromorphicAt.meromorphicOrderAt_toMeromorphicNFAt`

English:
lemma MeromorphicAt.meromorphicOrderAt_toMeromorphicNFAt
  given: (hf : MeromorphicAt f x)
  proof: (meromorphicOrderAt_congr hf.eq_nhdsNE_toMeromorphicNFAt).symm

中文:
引理 MeromorphicAt.meromorphicOrderAt_toMeromorphicNFAt
  条件: (hf : MeromorphicAt f x)
  证明: (meromorphicOrderAt_congr hf.eq_nhdsNE_toMeromorphicNFAt).symm

Depends on / 依赖: eq_nhdsNE_toMeromorphicNFAt, hf.eq_nhdsNE_toMeromorphicNFAt, meromorphicOrderAt_congr
-/
lemma MeromorphicAt.meromorphicOrderAt_toMeromorphicNFAt (hf : MeromorphicAt f x) :
    meromorphicOrderAt (toMeromorphicNFAt f x) x = meromorphicOrderAt f x :=
  (meromorphicOrderAt_congr hf.eq_nhdsNE_toMeromorphicNFAt).symm

/--
lemma `MeromorphicAt.meromorphicOrderAt_eq_zero_iff_toMeromorphicNFAt_ne_zero` / 引理 `MeromorphicAt.meromorphicOrderAt_eq_zero_iff_toMeromorphicNFAt_ne_zero`

English:
lemma MeromorphicAt.meromorphicOrderAt_eq_zero_iff_toMeromorphicNFAt_ne_zero
  proof: by
  simp [← meromorphicNFAt_toMeromorphicNFAt.meromorphicOrderAt_eq_zero_iff, hf]

中文:
引理 MeromorphicAt.meromorphicOrderAt_eq_zero_iff_toMeromorphicNFAt_ne_zero
  证明: by
  simp [← meromorphicNFAt_toMeromorphicNFAt.meromorphicOrderAt_eq_zero_iff, hf]

Depends on / 依赖: meromorphicNFAt_toMeromorphicNFAt, meromorphicNFAt_toMeromorphicNFAt.meromorphicOrderAt_eq_zero_iff, meromorphicOrderAt_eq_zero_iff
-/
lemma MeromorphicAt.meromorphicOrderAt_eq_zero_iff_toMeromorphicNFAt_ne_zero
    (hf : MeromorphicAt f x) :
    meromorphicOrderAt f x = 0 ↔ toMeromorphicNFAt f x x != 0 := by
  simp [← meromorphicNFAt_toMeromorphicNFAt.meromorphicOrderAt_eq_zero_iff, hf]

/--
lemma `MeromorphicAt.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt` / 引理 `MeromorphicAt.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt`

English:
lemma MeromorphicAt.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt
  proof: by
  simp [← meromorphicNFAt_toMeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt, hf]

@[gcongr]

中文:
引理 MeromorphicAt.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt
  证明: by
  simp [← meromorphicNFAt_toMeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt, hf]

@[gcongr]

Depends on / 依赖: meromorphicNFAt_toMeromorphicNFAt, meromorphicNFAt_toMeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt, meromorphicOrderAt_nonneg_iff_analyticAt
-/
lemma MeromorphicAt.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt
    (hf : MeromorphicAt f x) :
    0 <= meromorphicOrderAt f x ↔ AnalyticAt 𝕜 (toMeromorphicNFAt f x) x := by
  simp [← meromorphicNFAt_toMeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt, hf]

@[gcongr]
/--
lemma `toMeromorphicNFAt_eventuallyEq_nhds_congr` / 引理 `toMeromorphicNFAt_eventuallyEq_nhds_congr`

English:
lemma toMeromorphicNFAt_eventuallyEq_nhds_congr
  given: {f g : 𝕜 -> E} (hfg : f =ᶠ[𝓝[!=] x] g)
  proof: by
  by_cases hf : MeromorphicAt f x
  · exact meromorphicNFAt_toMeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
.mp hf.eq_nhdsNE_toMeromorphicNFAt.symm.trans meromorphicNFAt_toMeromorphicNFAt
 hfg.trans ((MeromorphicAt.meromorphicAt_congr hfg).mp hf).eq_nhdsNE_toMeromorphicNFAt
  · simp [

中文:
引理 toMeromorphicNFAt_eventuallyEq_nhds_congr
  条件: {f g : 𝕜 -> E} (hfg : f =ᶠ[𝓝[!=] x] g)
  证明: by
  by_cases hf : MeromorphicAt f x
  · exact meromorphicNFAt_toMeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
.mp hf.eq_nhdsNE_toMeromorphicNFAt.symm.trans meromorphicNFAt_toMeromorphicNFAt
 hfg.trans ((MeromorphicAt.meromorphicAt_congr hfg).mp hf).eq_nhdsNE_toMeromorphicNFAt
  · simp [

Depends on / 依赖: MeromorphicAt, MeromorphicAt.meromorphicAt_congr, eq_nhdsNE_toMeromorphicNFAt, eventuallyEq_nhdsNE_iff_eventuallyEq_nhds, hf.eq_nhdsNE_toMeromorphicNFAt.symm.trans, hfg.trans, meromorphicAt_congr, meromorphicNFAt_toMeromorphicNFAt, meromorphicNFAt_toMeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds, not.mp
-/
lemma toMeromorphicNFAt_eventuallyEq_nhds_congr {f g : 𝕜 -> E} (hfg : f =ᶠ[𝓝[!=] x] g) :
    toMeromorphicNFAt f x =ᶠ[𝓝 x] toMeromorphicNFAt g x := by
  by_cases hf : MeromorphicAt f x
  · exact meromorphicNFAt_toMeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
.mp hf.eq_nhdsNE_toMeromorphicNFAt.symm.trans meromorphicNFAt_toMeromorphicNFAt
 hfg.trans ((MeromorphicAt.meromorphicAt_congr hfg).mp hf).eq_nhdsNE_toMeromorphicNFAt
  · simp [hf, MeromorphicAt.meromorphicAt_congr hfg |>.not.mp]

@[simp]
/--
lemma `MeromorphicAt.toMeromorphicNFAt_eventuallyEq_nhds_iff` / 引理 `MeromorphicAt.toMeromorphicNFAt_eventuallyEq_nhds_iff`

English:
lemma MeromorphicAt.toMeromorphicNFAt_eventuallyEq_nhds_iff
  statement: {f g : 𝕜 -> E} (hf : MeromorphicAt f x)
  proof: hf.eq_nhdsNE_toMeromorphicNFAt.trans (h.filter_mono nhdsWithin_le_nhds)
.trans hg.eq_nhdsNE_toMeromorphicNFAt.symm
  mpr := toMeromorphicNFAt_eventuallyEq_nhds_congr

中文:
引理 MeromorphicAt.toMeromorphicNFAt_eventuallyEq_nhds_iff
  结论: {f g : 𝕜 -> E} (hf : MeromorphicAt f x)
  证明: hf.eq_nhdsNE_toMeromorphicNFAt.trans (h.filter_mono nhdsWithin_le_nhds)
.trans hg.eq_nhdsNE_toMeromorphicNFAt.symm
  mpr := toMeromorphicNFAt_eventuallyEq_nhds_congr

Depends on / 依赖: eq_nhdsNE_toMeromorphicNFAt, filter_mono, h.filter_mono, hf.eq_nhdsNE_toMeromorphicNFAt.trans, hg.eq_nhdsNE_toMeromorphicNFAt.symm, nhdsWithin_le_nhds, toMeromorphicNFAt_eventuallyEq_nhds_congr
-/
lemma MeromorphicAt.toMeromorphicNFAt_eventuallyEq_nhds_iff {f g : 𝕜 -> E} (hf : MeromorphicAt f x)
    (hg : MeromorphicAt g x) :
    toMeromorphicNFAt f x =ᶠ[𝓝 x] toMeromorphicNFAt g x ↔ f =ᶠ[𝓝[!=] x] g where
  mp h :=
    hf.eq_nhdsNE_toMeromorphicNFAt.trans (h.filter_mono nhdsWithin_le_nhds)
.trans hg.eq_nhdsNE_toMeromorphicNFAt.symm
  mpr := toMeromorphicNFAt_eventuallyEq_nhds_congr

/--
theorem `toMeromorphicNFAt_eq_self` / 定理 `toMeromorphicNFAt_eq_self`

English:
theorem toMeromorphicNFAt_eq_self
  proof: by
    rw [hf.symm]
    exact meromorphicNFAt_toMeromorphicNFAt
  mpr hf := by
    funext z
    by_cases hz : z = x
    · rw [hz]
      simp only [toMeromorphicNFAt, hf.meromorphicAt, WithTop.coe_zero, ne_eq]
      have h₀f := hf
      rcases hf with h₁f | h₁f
      · simpa [meromorphicOrderAt_eq_to

中文:
定理 toMeromorphicNFAt_eq_self
  证明: by
    rw [hf.symm]
    exact meromorphicNFAt_toMeromorphicNFAt
  mpr hf := by
    funext z
    by_cases hz : z = x
    · rw [hz]
      simp only [toMeromorphicNFAt, hf.meromorphicAt, WithTop.coe_zero, ne_eq]
      have h₀f := hf
      rcases hf with h₁f | h₁f
      · simpa [meromorphicOrderAt_eq_to
-/
@[simp] theorem toMeromorphicNFAt_eq_self :
    toMeromorphicNFAt f x = f ↔ MeromorphicNFAt f x where
  mp hf := by
    rw [hf.symm]
    exact meromorphicNFAt_toMeromorphicNFAt
  mpr hf := by
    funext z
    by_cases hz : z = x
    · rw [hz]
      simp only [toMeromorphicNFAt, hf.meromorphicAt, WithTop.coe_zero, ne_eq]
      have h₀f := hf
      rcases hf with h₁f | h₁f
      · simpa [meromorphicOrderAt_eq_top_iff.2 (h₁f.filter_mono nhdsWithin_le_nhds)]
          using h₁f.eq_of_nhds.symm
      · obtain ⟨n, g, h₁g, h₂g, h₃g⟩ := h₁f
        rw [Filter.EventuallyEq.eq_of_nhds h₃g]
        have : meromorphicOrderAt f x = n := by
          rw [meromorphicOrderAt_eq_int_iff h₀f.meromorphicAt]
          use g, h₁g, h₂g
          exact eventually_nhdsWithin_of_eventually_nhds h₃g
        by_cases h₃f : meromorphicOrderAt f x = 0
        · simp only [Pi.smul_apply', Pi.pow_apply, sub_self, h₃f, ↓reduceDIte]
          have hn : n = (0 : Int) := by
            rw [h₃f] at this
            exact WithTop.coe_eq_zero.mp this.symm
          simp_rw [hn]
          simp only [zpow_zero, one_smul]
          have : g =ᶠ[𝓝 x]
              Classical.choose ((meromorphicOrderAt_eq_int_iff h₀f.meromorphicAt).1 h₃f) := by
            obtain ⟨h₀, h₁, h₂⟩ := Classical.choose_spec
              ((meromorphicOrderAt_eq_int_iff h₀f.meromorphicAt).1 h₃f)
            rw [← h₁g.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE h₀.continuousAt]
            rw [hn] at h₃g
            simp only [zpow_zero, one_smul, ne_eq] at h₃g h₂
            exact (h₃g.filter_mono nhdsWithin_le_nhds).symm.trans h₂
          simp only [Function.update_self]
          exact Filter.EventuallyEq.eq_of_nhds this.symm
        · rw [eq_comm]
          simp only [Pi.smul_apply', Pi.pow_apply, sub_self, h₃f, ↓reduceDIte, smul_eq_zero,
            Function.update_self, smul_eq_zero]
          left
          apply zero_zpow n
          by_contra hn
          rw [hn] at this
          tauto
    · exact (hf.meromorphicAt.eqOn_compl_singleton_toMeromorphicNFAt hz).symm

/-!
## Normal form of meromorphic functions on a given set

### Definition
-/

/--
Definition of `MeromorphicNFOn` / `MeromorphicNFOn` 的定义

English:
definition MeromorphicNFOn
  signature: (f : 𝕜 -> E) (U : Set 𝕜)
  body: forall ⦃z⦄, z in U -> MeromorphicNFAt f z

中文:
定义 MeromorphicNFOn
  签名: (f : 𝕜 -> E) (U : 集合 𝕜)
  定义体: forall ⦃z⦄, z in U -> MeromorphicNFAt f z

Depends on / 依赖: MeromorphicNFAt
-/
def MeromorphicNFOn (f : 𝕜 -> E) (U : Set 𝕜) := forall ⦃z⦄, z in U -> MeromorphicNFAt f z

/-!
### Relation to other properties of functions
-/

/--
theorem `MeromorphicNFOn.meromorphicOn` / 定理 `MeromorphicNFOn.meromorphicOn`

English:
theorem MeromorphicNFOn.meromorphicOn
  given: (hf : MeromorphicNFOn f U)
  proof: fun _ hz => (hf hz).meromorphicAt

中文:
定理 MeromorphicNFOn.meromorphicOn
  条件: (hf : MeromorphicNFOn f U)
  证明: fun _ hz => (hf hz).meromorphicAt

Depends on / 依赖: meromorphicAt
-/
theorem MeromorphicNFOn.meromorphicOn (hf : MeromorphicNFOn f U) :
    MeromorphicOn f U := fun _ hz => (hf hz).meromorphicAt

/--
theorem `MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd` / 定理 `MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd`

English:
theorem MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd
  proof: by
  constructor <;> intro h x
  · intro hx
    rw [← (h₁f hx).meromorphicOrderAt_nonneg_iff_analyticAt]
    have := h x
    simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, h₁f.meromorphicOn, hx,
      MeromorphicOn.divisor_apply, untop₀_nonneg] at this
    assumption
  · by_cases 

中文:
定理 MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd
  证明: by
  constructor <;> intro h x
  · intro hx
    rw [← (h₁f hx).meromorphicOrderAt_nonneg_iff_analyticAt]
    have := h x
    simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, h₁f.meromorphicOn, hx,
      MeromorphicOn.divisor_apply, untop₀_nonneg] at this
    assumption
  · by_cases 

Depends on / 依赖: Function, Function.locallyFinsuppWithin.coe_zero, MeromorphicOn, MeromorphicOn.divisor_apply, Pi.zero_apply, coe_zero, divisor_apply, f.meromorphicOn, locallyFinsuppWithin, meromorphicOn, meromorphicOrderAt_nonneg_iff_analyticAt, zero_apply
-/
theorem MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd
    (h₁f : MeromorphicNFOn f U) :
    0 <= MeromorphicOn.divisor f U ↔ AnalyticOnNhd 𝕜 f U := by
  constructor <;> intro h x
  · intro hx
    rw [← (h₁f hx).meromorphicOrderAt_nonneg_iff_analyticAt]
    have := h x
    simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, h₁f.meromorphicOn, hx,
      MeromorphicOn.divisor_apply, untop₀_nonneg] at this
    assumption
  · by_cases hx : x in U
    · simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, h₁f.meromorphicOn, hx,
        MeromorphicOn.divisor_apply, untop₀_nonneg]
      exact (h₁f hx).meromorphicOrderAt_nonneg_iff_analyticAt.2 (h x hx)
    · simp [hx]

/--
theorem `AnalyticOnNhd.meromorphicNFOn` / 定理 `AnalyticOnNhd.meromorphicNFOn`

English:
theorem AnalyticOnNhd.meromorphicNFOn
  given: (h₁f : AnalyticOnNhd 𝕜 f U)
  proof: fun z hz => (h₁f z hz).meromorphicNFAt

中文:
定理 AnalyticOnNhd.meromorphicNFOn
  条件: (h₁f : AnalyticOnNhd 𝕜 f U)
  证明: fun z hz => (h₁f z hz).meromorphicNFAt

Depends on / 依赖: meromorphicNFAt
-/
theorem AnalyticOnNhd.meromorphicNFOn (h₁f : AnalyticOnNhd 𝕜 f U) :
    MeromorphicNFOn f U := fun z hz => (h₁f z hz).meromorphicNFAt

/-!
### Divisors and zeros of meromorphic functions in normal form.
-/

/--
theorem `MeromorphicNFOn.zero_set_eq_divisor_support` / 定理 `MeromorphicNFOn.zero_set_eq_divisor_support`

English:
theorem MeromorphicNFOn.zero_set_eq_divisor_support
  statement: (h₁f : MeromorphicNFOn f U)
  proof: by
  ext u
  constructor <;> intro hu
  · simp_all only [ne_eq, Subtype.forall, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, Function.mem_support, h₁f.meromorphicOn, MeromorphicOn.divisor_apply,
      WithTop.untop₀_eq_zero, (h₁f hu.1).meromorphicOrderAt_eq_zero_iff, not_true_eq

中文:
定理 MeromorphicNFOn.zero_set_eq_divisor_support
  结论: (h₁f : MeromorphicNFOn f U)
  证明: by
  ext u
  constructor <;> intro hu
  · simp_all only [ne_eq, Subtype.forall, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, Function.mem_support, h₁f.meromorphicOn, MeromorphicOn.divisor_apply,
      WithTop.untop₀_eq_zero, (h₁f hu.1).meromorphicOrderAt_eq_zero_iff, not_true_eq

Depends on / 依赖: Function, Function.mem_support, MeromorphicOn, MeromorphicOn.divisor, MeromorphicOn.divisor_apply, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Subtype, Subtype.forall, WithTop, WithTop.untop, divisor, divisor_apply, f.meromorphicOn, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_support, meromorphicOn
-/
theorem MeromorphicNFOn.zero_set_eq_divisor_support (h₁f : MeromorphicNFOn f U)
    (h₂f : forall u : U, meromorphicOrderAt f u != ⊤) :
    U inter f ⁻¹' {0} = Function.support (MeromorphicOn.divisor f U) := by
  ext u
  constructor <;> intro hu
  · simp_all only [ne_eq, Subtype.forall, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, Function.mem_support, h₁f.meromorphicOn, MeromorphicOn.divisor_apply,
      WithTop.untop₀_eq_zero, (h₁f hu.1).meromorphicOrderAt_eq_zero_iff, not_true_eq_false, or_self,
      not_false_eq_true]
  · simp only [Function.mem_support, ne_eq] at hu
    constructor
    · exact (MeromorphicOn.divisor f U).supportWithinDomain hu
    · rw [Set.mem_preimage, Set.mem_singleton_iff]
      have := h₁f ((MeromorphicOn.divisor f U).supportWithinDomain hu)
.meromorphicOrderAt_eq_zero_iff.not
      simp only [h₁f.meromorphicOn, (MeromorphicOn.divisor f U).supportWithinDomain hu,
        MeromorphicOn.divisor_apply, WithTop.untop₀_eq_zero, not_or] at hu
      simp_all [hu.1]

/-!
### Criteria to guarantee normal form
-/

/--
theorem `meromorphicNFOn_smul_iff_right_of_analyticOnNhd` / 定理 `meromorphicNFOn_smul_iff_right_of_analyticOnNhd`

English:
theorem meromorphicNFOn_smul_iff_right_of_analyticOnNhd
  statement: {g : 𝕜 -> 𝕜} (h₁g : AnalyticOnNhd 𝕜 g U)
  proof: by
  constructor <;> intro h z hz
  · rw [← meromorphicNFAt_smul_iff_right_of_analyticAt (h₁g z hz) (h₂g z hz)]
    exact h hz
  · apply (h hz).smul_analytic (h₁g z hz)
    exact h₂g z hz

中文:
定理 meromorphicNFOn_smul_iff_right_of_analyticOnNhd
  结论: {g : 𝕜 -> 𝕜} (h₁g : AnalyticOnNhd 𝕜 g U)
  证明: by
  constructor <;> intro h z hz
  · rw [← meromorphicNFAt_smul_iff_right_of_analyticAt (h₁g z hz) (h₂g z hz)]
    exact h hz
  · apply (h hz).smul_analytic (h₁g z hz)
    exact h₂g z hz

Depends on / 依赖: meromorphicNFAt_smul_iff_right_of_analyticAt, smul_analytic
-/
theorem meromorphicNFOn_smul_iff_right_of_analyticOnNhd {g : 𝕜 -> 𝕜} (h₁g : AnalyticOnNhd 𝕜 g U)
    (h₂g : forall u in U, g u != 0) :
    MeromorphicNFOn (g • f) U ↔ MeromorphicNFOn f U := by
  constructor <;> intro h z hz
  · rw [← meromorphicNFAt_smul_iff_right_of_analyticAt (h₁g z hz) (h₂g z hz)]
    exact h hz
  · apply (h hz).smul_analytic (h₁g z hz)
    exact h₂g z hz

/--
theorem `meromorphicNFOn_mul_iff_right_of_analyticOnNhd` / 定理 `meromorphicNFOn_mul_iff_right_of_analyticOnNhd`

English:
theorem meromorphicNFOn_mul_iff_right_of_analyticOnNhd
  statement: {f g : 𝕜 -> 𝕜} (h₁g : AnalyticOnNhd 𝕜 g U)
  proof: by
  rw [← smul_eq_mul]
  exact meromorphicNFOn_smul_iff_right_of_analyticOnNhd h₁g h₂g

中文:
定理 meromorphicNFOn_mul_iff_right_of_analyticOnNhd
  结论: {f g : 𝕜 -> 𝕜} (h₁g : AnalyticOnNhd 𝕜 g U)
  证明: by
  rw [← smul_eq_mul]
  exact meromorphicNFOn_smul_iff_right_of_analyticOnNhd h₁g h₂g

Depends on / 依赖: meromorphicNFOn_smul_iff_right_of_analyticOnNhd, smul_eq_mul
-/
theorem meromorphicNFOn_mul_iff_right_of_analyticOnNhd {f g : 𝕜 -> 𝕜} (h₁g : AnalyticOnNhd 𝕜 g U)
    (h₂g : forall u in U, g u != 0) :
    MeromorphicNFOn (g * f) U ↔ MeromorphicNFOn f U := by
  rw [← smul_eq_mul]
  exact meromorphicNFOn_smul_iff_right_of_analyticOnNhd h₁g h₂g

/--
theorem `meromorphicNFOn_mul_iff_left_of_analyticOnNhd` / 定理 `meromorphicNFOn_mul_iff_left_of_analyticOnNhd`

English:
theorem meromorphicNFOn_mul_iff_left_of_analyticOnNhd
  statement: {f g : 𝕜 -> 𝕜} (h₁g : AnalyticOnNhd 𝕜 g U)
  proof: by
  rw [mul_comm]; rw [← smul_eq_mul]
  exact meromorphicNFOn_mul_iff_right_of_analyticOnNhd h₁g h₂g

中文:
定理 meromorphicNFOn_mul_iff_left_of_analyticOnNhd
  结论: {f g : 𝕜 -> 𝕜} (h₁g : AnalyticOnNhd 𝕜 g U)
  证明: by
  rw [mul_comm]; rw [← smul_eq_mul]
  exact meromorphicNFOn_mul_iff_right_of_analyticOnNhd h₁g h₂g

Depends on / 依赖: meromorphicNFOn_mul_iff_right_of_analyticOnNhd, mul_comm, smul_eq_mul
-/
theorem meromorphicNFOn_mul_iff_left_of_analyticOnNhd {f g : 𝕜 -> 𝕜} (h₁g : AnalyticOnNhd 𝕜 g U)
    (h₂g : forall u in U, g u != 0) :
    MeromorphicNFOn (f * g) U ↔ MeromorphicNFOn f U := by
  rw [mul_comm]; rw [← smul_eq_mul]
  exact meromorphicNFOn_mul_iff_right_of_analyticOnNhd h₁g h₂g

/--
theorem `meromorphicNFOn_prod` / 定理 `meromorphicNFOn_prod`

English:
theorem meromorphicNFOn_prod
  statement: {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜}
  proof: fun x hx => meromorphicNFAt_prod (h₁f · · hx) (h₂f x hx)

中文:
定理 meromorphicNFOn_prod
  结论: {ι : 类型} {s : 有限集 ι} {f : ι -> 𝕜 -> 𝕜}
  证明: fun x hx => meromorphicNFAt_prod (h₁f · · hx) (h₂f x hx)

Depends on / 依赖: meromorphicNFAt_prod
-/
theorem meromorphicNFOn_prod {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜}
    (h₁f : forall i in s, MeromorphicNFOn (f i) U)
    (h₂f : forall x in U, Set.Subsingleton {σ in s | f σ x = 0}) :
    MeromorphicNFOn (∏ i in s, f i) U :=
  fun x hx => meromorphicNFAt_prod (h₁f · · hx) (h₂f x hx)

/--
theorem `meromorphicNFOn_fun_prod` / 定理 `meromorphicNFOn_fun_prod`

English:
theorem meromorphicNFOn_fun_prod
  statement: {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜}
  proof: by
  convert! meromorphicNFOn_prod h₁f h₂f
  exact (Finset.prod_apply _ s f).symm

中文:
定理 meromorphicNFOn_fun_prod
  结论: {ι : 类型} {s : 有限集 ι} {f : ι -> 𝕜 -> 𝕜}
  证明: by
  convert! meromorphicNFOn_prod h₁f h₂f
  exact (Finset.prod_apply _ s f).symm

Depends on / 依赖: Finset, Finset.prod_apply, convert, meromorphicNFOn_prod, prod_apply
-/
theorem meromorphicNFOn_fun_prod {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜}
    (h₁f : forall i in s, MeromorphicNFOn (f i) U)
    (h₂f : forall x in U, Set.Subsingleton {σ in s | f σ x = 0}) :
    MeromorphicNFOn (fun x => ∏ i in s, f i x) U := by
  convert! meromorphicNFOn_prod h₁f h₂f
  exact (Finset.prod_apply _ s f).symm

/--
theorem `meromorphicNFOn_finprod` / 定理 `meromorphicNFOn_finprod`

English:
theorem meromorphicNFOn_finprod
  statement: {ι : Type*} {f : ι -> 𝕜 -> 𝕜} (h₁f : forall i, MeromorphicNFOn (f i) U)
  proof: fun x hx => meromorphicNFAt_finprod (h₁f · hx) (h₂f x hx)

中文:
定理 meromorphicNFOn_finprod
  结论: {ι : 类型} {f : ι -> 𝕜 -> 𝕜} (h₁f : 对任意 i, MeromorphicNFOn (f i) U)
  证明: fun x hx => meromorphicNFAt_finprod (h₁f · hx) (h₂f x hx)

Depends on / 依赖: meromorphicNFAt_finprod
-/
theorem meromorphicNFOn_finprod {ι : Type*} {f : ι -> 𝕜 -> 𝕜} (h₁f : forall i, MeromorphicNFOn (f i) U)
    (h₂f : forall x in U, Set.Subsingleton {σ | f σ x = 0}) :
  MeromorphicNFOn (∏ᶠ i, f i) U :=
  fun x hx => meromorphicNFAt_finprod (h₁f · hx) (h₂f x hx)

/--
Integer powers of meromorphic functions in normal form are in normal form.
-/
@[to_fun]
/--
theorem `MeromorphicNFOn.zpow` / 定理 `MeromorphicNFOn.zpow`

English:
theorem MeromorphicNFOn.zpow
  given: {f : 𝕜 -> 𝕜} {n : Int} {U : Set 𝕜} (hf : MeromorphicNFOn f U)
  proof: fun _ hz => (hf hz).zpow

中文:
定理 MeromorphicNFOn.zpow
  条件: {f : 𝕜 -> 𝕜} {n : 整数} {U : 集合 𝕜} (hf : MeromorphicNFOn f U)
  证明: fun _ hz => (hf hz).zpow
-/
theorem MeromorphicNFOn.zpow {f : 𝕜 -> 𝕜} {n : Int} {U : Set 𝕜} (hf : MeromorphicNFOn f U) :
    MeromorphicNFOn (f ^ n) U := fun _ hz => (hf hz).zpow

/--
theorem `meromorphicNFOn_inv` / 定理 `meromorphicNFOn_inv`

English:
theorem meromorphicNFOn_inv
  given: {f : 𝕜 -> 𝕜}
  proof: meromorphicNFAt_inv.1 (h hx)
  mpr h _ hx := meromorphicNFAt_inv.2 (h hx)

中文:
定理 meromorphicNFOn_inv
  条件: {f : 𝕜 -> 𝕜}
  证明: meromorphicNFAt_inv.1 (h hx)
  mpr h _ hx := meromorphicNFAt_inv.2 (h hx)

Depends on / 依赖: meromorphicNFAt_inv
-/
theorem meromorphicNFOn_inv {f : 𝕜 -> 𝕜} :
    MeromorphicNFOn f⁻¹ U ↔ MeromorphicNFOn f U where
  mp h _ hx := meromorphicNFAt_inv.1 (h hx)
  mpr h _ hx := meromorphicNFAt_inv.2 (h hx)

/--
theorem `meromorphicNFOn_fun_inv` / 定理 `meromorphicNFOn_fun_inv`

English:
theorem meromorphicNFOn_fun_inv
  given: {f : 𝕜 -> 𝕜}
  proof: meromorphicNFOn_inv

中文:
定理 meromorphicNFOn_fun_inv
  条件: {f : 𝕜 -> 𝕜}
  证明: meromorphicNFOn_inv

Depends on / 依赖: meromorphicNFOn_inv
-/
theorem meromorphicNFOn_fun_inv {f : 𝕜 -> 𝕜} :
    MeromorphicNFOn (fun x => (f x)⁻¹) U ↔ MeromorphicNFOn f U :=
  meromorphicNFOn_inv

/-- `MeromorphicNFOn` is invariant under translation. -/
@[to_fun meromorphicNFOn_fun_comp_add_const_iff_meromorphicNFOn]
/--
theorem `meromorphicNFOn_comp_add_const_iff_meromorphicNFOn` / 定理 `meromorphicNFOn_comp_add_const_iff_meromorphicNFOn`

English:
theorem meromorphicNFOn_comp_add_const_iff_meromorphicNFOn
  given: {c : 𝕜} {U : Set 𝕜}
  proof: by
  refine ⟨fun h y hy => ?_, fun h y hy => ?_⟩
  · rw [add_singleton, mem_image] at hy
    obtain ⟨x, h₁x, h₂x⟩ := hy
    simpa [← h₂x, ← meromorphicNFAt_comp_add_const_iff_meromorphicNFAt] using h h₁x
  · rw [meromorphicNFAt_comp_add_const_iff_meromorphicNFAt]
    aesop

中文:
定理 meromorphicNFOn_comp_add_const_iff_meromorphicNFOn
  条件: {c : 𝕜} {U : 集合 𝕜}
  证明: by
  refine ⟨fun h y hy => ?_, fun h y hy => ?_⟩
  · rw [add_singleton, mem_image] at hy
    obtain ⟨x, h₁x, h₂x⟩ := hy
    simpa [← h₂x, ← meromorphicNFAt_comp_add_const_iff_meromorphicNFAt] using h h₁x
  · rw [meromorphicNFAt_comp_add_const_iff_meromorphicNFAt]
    aesop

Depends on / 依赖: add_singleton, mem_image, meromorphicNFAt_comp_add_const_iff_meromorphicNFAt
-/
theorem meromorphicNFOn_comp_add_const_iff_meromorphicNFOn {c : 𝕜} {U : Set 𝕜} :
    MeromorphicNFOn (f ∘ (· + c)) U ↔ MeromorphicNFOn f (U + {c}) := by
  refine ⟨fun h y hy => ?_, fun h y hy => ?_⟩
  · rw [add_singleton, mem_image] at hy
    obtain ⟨x, h₁x, h₂x⟩ := hy
    simpa [← h₂x, ← meromorphicNFAt_comp_add_const_iff_meromorphicNFAt] using h h₁x
  · rw [meromorphicNFAt_comp_add_const_iff_meromorphicNFAt]
    aesop

/-- `MeromorphicNFOn` is invariant under translation. -/
@[to_fun meromorphicNFOn_fun_comp_sub_const_iff_meromorphicNFOn]
/--
theorem `meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn` / 定理 `meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn`

English:
theorem meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn
  given: {c : 𝕜} {U : Set 𝕜}
  proof: by
  simp_rw [sub_eq_add_neg, meromorphicNFOn_comp_add_const_iff_meromorphicNFOn, neg_singleton]

中文:
定理 meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn
  条件: {c : 𝕜} {U : 集合 𝕜}
  证明: by
  simp_rw [sub_eq_add_neg, meromorphicNFOn_comp_add_const_iff_meromorphicNFOn, neg_singleton]

Depends on / 依赖: meromorphicNFOn_comp_add_const_iff_meromorphicNFOn, neg_singleton, simp_rw, sub_eq_add_neg
-/
theorem meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn {c : 𝕜} {U : Set 𝕜} :
    MeromorphicNFOn (f ∘ (· - c)) U ↔ MeromorphicNFOn f (U - {c}) := by
  simp_rw [sub_eq_add_neg, meromorphicNFOn_comp_add_const_iff_meromorphicNFOn, neg_singleton]

/-- `MeromorphicNFOn` is invariant under translation, special case where the set is a ball. -/
@[to_fun (attr := simp) meromorphicNFOn_ball_fun_comp_sub_const_iff_meromorphicNFOn_ball]
/--
theorem `meromorphicNFOn_ball_comp_sub_const_iff_meromorphicNFOn_ball` / 定理 `meromorphicNFOn_ball_comp_sub_const_iff_meromorphicNFOn_ball`

English:
theorem meromorphicNFOn_ball_comp_sub_const_iff_meromorphicNFOn_ball
  given: {c : 𝕜} {R : Real}
  proof: by
  rw [meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn]; rw [ball_sub_singleton]; rw [sub_self]

中文:
定理 meromorphicNFOn_ball_comp_sub_const_iff_meromorphicNFOn_ball
  条件: {c : 𝕜} {R : 实数}
  证明: by
  rw [meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn]; rw [ball_sub_singleton]; rw [sub_self]

Depends on / 依赖: ContinuousStar, ball_sub_singleton, meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn, sub_self
-/
theorem meromorphicNFOn_ball_comp_sub_const_iff_meromorphicNFOn_ball {c : 𝕜} {R : Real} :
    MeromorphicNFOn (f ∘ (· - c)) (ball c R) ↔ MeromorphicNFOn f (ball 0 R) := by
  rw [meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn]; rw [ball_sub_singleton]; rw [sub_self]

/--
`MeromorphicNFOn` is invariant under translation, special case where the set is a closed ball.
-/
@[to_fun (attr := simp)
  meromorphicNFOn_closedBall_fun_comp_sub_const_iff_meromorphicNFOn_closedBall]
/--
theorem `meromorphicNFOn_closedBall_comp_sub_const_iff_meromorphicNFOn_closedBall` / 定理 `meromorphicNFOn_closedBall_comp_sub_const_iff_meromorphicNFOn_closedBall`

English:
theorem meromorphicNFOn_closedBall_comp_sub_const_iff_meromorphicNFOn_closedBall
  given: {c : 𝕜} {R : Real}
  proof: by
  rw [meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn]; rw [closedBall_sub_singleton]; rw [sub_self]

中文:
定理 meromorphicNFOn_closedBall_comp_sub_const_iff_meromorphicNFOn_closedBall
  条件: {c : 𝕜} {R : 实数}
  证明: by
  rw [meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn]; rw [closedBall_sub_singleton]; rw [sub_self]

Depends on / 依赖: closedBall_sub_singleton, meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn, sub_self
-/
theorem meromorphicNFOn_closedBall_comp_sub_const_iff_meromorphicNFOn_closedBall {c : 𝕜} {R : Real} :
    MeromorphicNFOn (f ∘ (· - c)) (closedBall c R) ↔ MeromorphicNFOn f (closedBall 0 R) := by
  rw [meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn]; rw [closedBall_sub_singleton]; rw [sub_self]

/-- `MeromorphicNFOn` is invariant under translation, special case where the set is a sphere. -/
@[to_fun (attr := simp) meromorphicNFOn_sphere_fun_comp_sub_const_iff_meromorphicNFOn_sphere]
/--
theorem `meromorphicNFOn_sphere_comp_sub_const_iff_meromorphicNFOn_sphere` / 定理 `meromorphicNFOn_sphere_comp_sub_const_iff_meromorphicNFOn_sphere`

English:
theorem meromorphicNFOn_sphere_comp_sub_const_iff_meromorphicNFOn_sphere
  given: {c : 𝕜} {R : Real}
  proof: by
  rw [meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn]; rw [sphere_sub_singleton]; rw [sub_self]

中文:
定理 meromorphicNFOn_sphere_comp_sub_const_iff_meromorphicNFOn_sphere
  条件: {c : 𝕜} {R : 实数}
  证明: by
  rw [meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn]; rw [sphere_sub_singleton]; rw [sub_self]

Depends on / 依赖: meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn, sphere_sub_singleton, sub_self
-/
theorem meromorphicNFOn_sphere_comp_sub_const_iff_meromorphicNFOn_sphere {c : 𝕜} {R : Real} :
    MeromorphicNFOn (f ∘ (· - c)) (sphere c R) ↔ MeromorphicNFOn f (sphere 0 R) := by
  rw [meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn]; rw [sphere_sub_singleton]; rw [sub_self]

/-!
### Continuous extension and conversion to normal form
-/

variable (f U) in
/--
Definition of `toMeromorphicNFOn` / `toMeromorphicNFOn` 的定义

English:
definition toMeromorphicNFOn
  signature: :
  body: by
  by_cases h₁f : MeromorphicOn f U
  · intro z
    by_cases hz : z in U
    · exact toMeromorphicNFAt f z z
    · exact f z
  · exact 0

中文:
定义 toMeromorphicNFOn
  签名: :
  定义体: by
  by_cases h₁f : MeromorphicOn f U
  · intro z
    by_cases hz : z in U
    · exact toMeromorphicNFAt f z z
    · exact f z
  · exact 0

Depends on / 依赖: MeromorphicOn, toMeromorphicNFAt
-/
noncomputable def toMeromorphicNFOn :
    𝕜 -> E := by
  by_cases h₁f : MeromorphicOn f U
  · intro z
    by_cases hz : z in U
    · exact toMeromorphicNFAt f z z
    · exact f z
  · exact 0

/--
lemma `toMeromorphicNFOn_of_not_meromorphicOn` / 引理 `toMeromorphicNFOn_of_not_meromorphicOn`

English:
lemma toMeromorphicNFOn_of_not_meromorphicOn
  given: (hf : ¬MeromorphicOn f U)
  proof: by
  simp [toMeromorphicNFOn, hf]

中文:
引理 toMeromorphicNFOn_of_not_meromorphicOn
  条件: (hf : ¬MeromorphicOn f U)
  证明: by
  simp [toMeromorphicNFOn, hf]
-/
@[simp] lemma toMeromorphicNFOn_of_not_meromorphicOn (hf : ¬MeromorphicOn f U) :
    toMeromorphicNFOn f U = 0 := by
  simp [toMeromorphicNFOn, hf]

/--
lemma `toMeromorphicNFOn_eq_self_on_compl` / 引理 `toMeromorphicNFOn_eq_self_on_compl`

English:
lemma toMeromorphicNFOn_eq_self_on_compl
  given: (hf : MeromorphicOn f U)
  proof: by
  intro x hx
  simp_all [toMeromorphicNFOn]

中文:
引理 toMeromorphicNFOn_eq_self_on_compl
  条件: (hf : MeromorphicOn f U)
  证明: by
  intro x hx
  simp_all [toMeromorphicNFOn]
-/
@[simp] lemma toMeromorphicNFOn_eq_self_on_compl (hf : MeromorphicOn f U) :
    Set.EqOn (toMeromorphicNFOn f U) f Uᶜ := by
  intro x hx
  simp_all [toMeromorphicNFOn]

/--
theorem `toMeromorphicNFOn_eqOn_codiscrete` / 定理 `toMeromorphicNFOn_eqOn_codiscrete`

English:
theorem toMeromorphicNFOn_eqOn_codiscrete
  given: (hf : MeromorphicOn f U)
  proof: by
  have : U in Filter.codiscreteWithin U := by simp
  filter_upwards [hf.analyticAt_mem_codiscreteWithin, this] with a h₁a h₂a
  simp [toMeromorphicNFOn, hf, ← (toMeromorphicNFAt_eq_self.2 h₁a.meromorphicNFAt).symm]

中文:
定理 toMeromorphicNFOn_eqOn_codiscrete
  条件: (hf : MeromorphicOn f U)
  证明: by
  have : U in Filter.codiscreteWithin U := by simp
  filter_upwards [hf.analyticAt_mem_codiscreteWithin, this] with a h₁a h₂a
  simp [toMeromorphicNFOn, hf, ← (toMeromorphicNFAt_eq_self.2 h₁a.meromorphicNFAt).symm]

Depends on / 依赖: Filter, Filter.codiscreteWithin, a.meromorphicNFAt, analyticAt_mem_codiscreteWithin, codiscreteWithin, filter_upwards, hf.analyticAt_mem_codiscreteWithin, meromorphicNFAt, toMeromorphicNFAt_eq_self, toMeromorphicNFOn
-/
theorem toMeromorphicNFOn_eqOn_codiscrete (hf : MeromorphicOn f U) :
    f =ᶠ[Filter.codiscreteWithin U] toMeromorphicNFOn f U := by
  have : U in Filter.codiscreteWithin U := by simp
  filter_upwards [hf.analyticAt_mem_codiscreteWithin, this] with a h₁a h₂a
  simp [toMeromorphicNFOn, hf, ← (toMeromorphicNFAt_eq_self.2 h₁a.meromorphicNFAt).symm]

/--
theorem `MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE` / 定理 `MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE`

English:
theorem MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE
  proof: by
  filter_upwards [hf.eventually_analyticAt_or_mem_compl hx] with a ha
  rcases ha with ha | ha
  · simp [toMeromorphicNFOn, hf, ← (toMeromorphicNFAt_eq_self.2 ha.meromorphicNFAt).symm]
  · simp only [Set.mem_compl_iff] at ha
    simp [toMeromorphicNFOn, ha, hf]

中文:
定理 MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE
  证明: by
  filter_upwards [hf.eventually_analyticAt_or_mem_compl hx] with a ha
  rcases ha with ha | ha
  · simp [toMeromorphicNFOn, hf, ← (toMeromorphicNFAt_eq_self.2 ha.meromorphicNFAt).symm]
  · simp only [Set.mem_compl_iff] at ha
    simp [toMeromorphicNFOn, ha, hf]

Depends on / 依赖: Set.mem_compl_iff, eventually_analyticAt_or_mem_compl, filter_upwards, ha.meromorphicNFAt, hf.eventually_analyticAt_or_mem_compl, mem_compl_iff, meromorphicNFAt, toMeromorphicNFAt_eq_self, toMeromorphicNFOn
-/
theorem MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE
    (hf : MeromorphicOn f U) (hx : x in U) :
    toMeromorphicNFOn f U =ᶠ[𝓝[!=] x] f := by
  filter_upwards [hf.eventually_analyticAt_or_mem_compl hx] with a ha
  rcases ha with ha | ha
  · simp [toMeromorphicNFOn, hf, ← (toMeromorphicNFAt_eq_self.2 ha.meromorphicNFAt).symm]
  · simp only [Set.mem_compl_iff] at ha
    simp [toMeromorphicNFOn, ha, hf]

/--
theorem `toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds` / 定理 `toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds`

English:
theorem toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds
  statement: (hf : MeromorphicOn f U)
  proof: by
  apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
  · exact (hf.toMeromorphicNFOn_eq_self_on_nhdsNE hx).trans (hf x hx).eq_nhdsNE_toMeromorphicNFAt
  · simp [toMeromorphicNFOn, hf, hx]

中文:
定理 toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds
  结论: (hf : MeromorphicOn f U)
  证明: by
  apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
  · exact (hf.toMeromorphicNFOn_eq_self_on_nhdsNE hx).trans (hf x hx).eq_nhdsNE_toMeromorphicNFAt
  · simp [toMeromorphicNFOn, hf, hx]

Depends on / 依赖: eq_nhdsNE_toMeromorphicNFAt, eventuallyEq_nhds_of_eventuallyEq_nhdsNE, hf.toMeromorphicNFOn_eq_self_on_nhdsNE, toMeromorphicNFOn, toMeromorphicNFOn_eq_self_on_nhdsNE
-/
theorem toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds (hf : MeromorphicOn f U)
    (hx : x in U) :
    toMeromorphicNFOn f U =ᶠ[𝓝 x] toMeromorphicNFAt f x := by
  apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
  · exact (hf.toMeromorphicNFOn_eq_self_on_nhdsNE hx).trans (hf x hx).eq_nhdsNE_toMeromorphicNFAt
  · simp [toMeromorphicNFOn, hf, hx]

/--
theorem `toMeromorphicNFOn_eq_toMeromorphicNFAt` / 定理 `toMeromorphicNFOn_eq_toMeromorphicNFAt`

English:
theorem toMeromorphicNFOn_eq_toMeromorphicNFAt
  statement: (hf : MeromorphicOn f U)
  proof: by
  apply Filter.EventuallyEq.eq_of_nhds (g := toMeromorphicNFAt f x)
  simp [(toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hf hx).trans]

中文:
定理 toMeromorphicNFOn_eq_toMeromorphicNFAt
  结论: (hf : MeromorphicOn f U)
  证明: by
  apply Filter.EventuallyEq.eq_of_nhds (g := toMeromorphicNFAt f x)
  simp [(toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hf hx).trans]

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.eq_of_nhds, eq_of_nhds, toMeromorphicNFAt, toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds
-/
theorem toMeromorphicNFOn_eq_toMeromorphicNFAt (hf : MeromorphicOn f U)
    (hx : x in U) :
    toMeromorphicNFOn f U x = toMeromorphicNFAt f x x := by
  apply Filter.EventuallyEq.eq_of_nhds (g := toMeromorphicNFAt f x)
  simp [(toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hf hx).trans]

variable (f U) in
/--
theorem `meromorphicNFOn_toMeromorphicNFOn` / 定理 `meromorphicNFOn_toMeromorphicNFOn`

English:
theorem meromorphicNFOn_toMeromorphicNFOn
  proof: by
  by_cases hf : MeromorphicOn f U
  · intro z hz
    rw [meromorphicNFAt_congr (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hf hz)]
    exact meromorphicNFAt_toMeromorphicNFAt
  · simpa [hf] using! analyticOnNhd_const.meromorphicNFOn

中文:
定理 meromorphicNFOn_toMeromorphicNFOn
  证明: by
  by_cases hf : MeromorphicOn f U
  · intro z hz
    rw [meromorphicNFAt_congr (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hf hz)]
    exact meromorphicNFAt_toMeromorphicNFAt
  · simpa [hf] using! analyticOnNhd_const.meromorphicNFOn

Depends on / 依赖: MeromorphicOn, analyticOnNhd_const, analyticOnNhd_const.meromorphicNFOn, meromorphicNFAt_congr, meromorphicNFAt_toMeromorphicNFAt, meromorphicNFOn, toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds
-/
theorem meromorphicNFOn_toMeromorphicNFOn :
    MeromorphicNFOn (toMeromorphicNFOn f U) U := by
  by_cases hf : MeromorphicOn f U
  · intro z hz
    rw [meromorphicNFAt_congr (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hf hz)]
    exact meromorphicNFAt_toMeromorphicNFAt
  · simpa [hf] using! analyticOnNhd_const.meromorphicNFOn

/--
theorem `toMeromorphicNFOn_eq_self` / 定理 `toMeromorphicNFOn_eq_self`

English:
theorem toMeromorphicNFOn_eq_self
  proof: by
  constructor <;> intro h
  · rw [h.symm]
    apply meromorphicNFOn_toMeromorphicNFOn
  · ext x
    by_cases hx : x in U
    · simp only [toMeromorphicNFOn, h.meromorphicOn, ↓reduceDIte, hx]
      rw [toMeromorphicNFAt_eq_self.2 (h hx)]
    · simp [toMeromorphicNFOn, h.meromorphicOn, hx]

中文:
定理 toMeromorphicNFOn_eq_self
  证明: by
  constructor <;> intro h
  · rw [h.symm]
    apply meromorphicNFOn_toMeromorphicNFOn
  · ext x
    by_cases hx : x in U
    · simp only [toMeromorphicNFOn, h.meromorphicOn, ↓reduceDIte, hx]
      rw [toMeromorphicNFAt_eq_self.2 (h hx)]
    · simp [toMeromorphicNFOn, h.meromorphicOn, hx]
-/
@[simp] theorem toMeromorphicNFOn_eq_self :
    toMeromorphicNFOn f U = f ↔ MeromorphicNFOn f U := by
  constructor <;> intro h
  · rw [h.symm]
    apply meromorphicNFOn_toMeromorphicNFOn
  · ext x
    by_cases hx : x in U
    · simp only [toMeromorphicNFOn, h.meromorphicOn, ↓reduceDIte, hx]
      rw [toMeromorphicNFAt_eq_self.2 (h hx)]
    · simp [toMeromorphicNFOn, h.meromorphicOn, hx]

/--
theorem `meromorphicOrderAt_toMeromorphicNFOn` / 定理 `meromorphicOrderAt_toMeromorphicNFOn`

English:
theorem meromorphicOrderAt_toMeromorphicNFOn
  given: (hf : MeromorphicOn f U) (hx : x in U)
  proof: by
  apply meromorphicOrderAt_congr
  exact hf.toMeromorphicNFOn_eq_self_on_nhdsNE hx

中文:
定理 meromorphicOrderAt_toMeromorphicNFOn
  条件: (hf : MeromorphicOn f U) (hx : x in U)
  证明: by
  apply meromorphicOrderAt_congr
  exact hf.toMeromorphicNFOn_eq_self_on_nhdsNE hx
-/
@[simp] theorem meromorphicOrderAt_toMeromorphicNFOn (hf : MeromorphicOn f U) (hx : x in U) :
    meromorphicOrderAt (toMeromorphicNFOn f U) x = meromorphicOrderAt f x := by
  apply meromorphicOrderAt_congr
  exact hf.toMeromorphicNFOn_eq_self_on_nhdsNE hx

/--
theorem `MeromorphicOn.divisor_of_toMeromorphicNFOn` / 定理 `MeromorphicOn.divisor_of_toMeromorphicNFOn`

English:
theorem MeromorphicOn.divisor_of_toMeromorphicNFOn
  given: (hf : MeromorphicOn f U)
  proof: by
  ext z
  by_cases hz : z in U <;> simp [hf, (meromorphicNFOn_toMeromorphicNFOn f U).meromorphicOn, hz]

中文:
定理 MeromorphicOn.divisor_of_toMeromorphicNFOn
  条件: (hf : MeromorphicOn f U)
  证明: by
  ext z
  by_cases hz : z in U <;> simp [hf, (meromorphicNFOn_toMeromorphicNFOn f U).meromorphicOn, hz]
-/
@[simp] theorem MeromorphicOn.divisor_of_toMeromorphicNFOn (hf : MeromorphicOn f U) :
    divisor (toMeromorphicNFOn f U) U = divisor f U := by
  ext z
  by_cases hz : z in U <;> simp [hf, (meromorphicNFOn_toMeromorphicNFOn f U).meromorphicOn, hz]
