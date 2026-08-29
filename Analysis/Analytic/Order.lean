/-
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara, Stefan Kebekus
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Vanishing Order of Analytic Functions

This file defines the order of vanishing of an analytic function `f` at a point `z₀`, as an element
of `ℕ∞`.

## TODO

Uniformize API between analytic and meromorphic functions
-/

@[expose] public section

open Filter Set
open scoped Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
## Vanishing Order at a Point: Definition and Characterization
-/

section NormedSpace
variable {f g : 𝕜 -> E} {n : Nat} {z₀ : 𝕜}

open scoped Classical in
/--
Definition of `analyticOrderAt` / `analyticOrderAt` 的定义

English:
definition analyticOrderAt
  signature: (f : 𝕜 -> E) (z₀ : 𝕜)
  body: if hf : AnalyticAt 𝕜 f z₀ then
    if h : forallᶠ z in 𝓝 z₀, f z = 0 then ⊤
    else ↑(hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h).choose
  else 0

中文:
定义 analyticOrderAt
  签名: (f : 𝕜 -> E) (z₀ : 𝕜)
  定义体: if hf : AnalyticAt 𝕜 f z₀ then
    if h : forallᶠ z in 𝓝 z₀, f z = 0 then ⊤
    else ↑(hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h).choose
  else 0

Depends on / 依赖: AnalyticAt, exists_eventuallyEq_pow_smul_nonzero_iff, hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr
-/
noncomputable def analyticOrderAt (f : 𝕜 -> E) (z₀ : 𝕜) : Nat∞ :=
  if hf : AnalyticAt 𝕜 f z₀ then
    if h : forallᶠ z in 𝓝 z₀, f z = 0 then ⊤
    else ↑(hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h).choose
  else 0

/--
Definition of `analyticOrderNatAt` / `analyticOrderNatAt` 的定义

English:
definition analyticOrderNatAt
  signature: (f : 𝕜 -> E) (z₀ : 𝕜)
  body: (analyticOrderAt f z₀).toNat

@[simp]

中文:
定义 analyticOrder自然数At
  签名: (f : 𝕜 -> E) (z₀ : 𝕜)
  定义体: (analyticOrderAt f z₀).toNat

@[simp]

Depends on / 依赖: analyticOrderAt
-/
noncomputable def analyticOrderNatAt (f : 𝕜 -> E) (z₀ : 𝕜) : Nat := (analyticOrderAt f z₀).toNat

@[simp]
/--
lemma `analyticOrderAt_of_not_analyticAt` / 引理 `analyticOrderAt_of_not_analyticAt`

English:
lemma analyticOrderAt_of_not_analyticAt
  given: (hf : ¬ AnalyticAt 𝕜 f z₀)
  statement: analyticOrderAt f z₀ = 0
  proof: dif_neg hf

@[simp]

中文:
引理 analyticOrderAt_of_not_analyticAt
  条件: (hf : ¬ AnalyticAt 𝕜 f z₀)
  结论: analyticOrderAt f z₀ = 0
  证明: dif_neg hf

@[simp]

Depends on / 依赖: dif_neg
-/
lemma analyticOrderAt_of_not_analyticAt (hf : ¬ AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = 0 :=
  dif_neg hf

@[simp]
/--
lemma `analyticOrderNatAt_of_not_analyticAt` / 引理 `analyticOrderNatAt_of_not_analyticAt`

English:
lemma analyticOrderNatAt_of_not_analyticAt
  given: (hf : ¬ AnalyticAt 𝕜 f z₀)
  proof: by simp [analyticOrderNatAt, hf]

中文:
引理 analyticOrder自然数At_of_not_analyticAt
  条件: (hf : ¬ AnalyticAt 𝕜 f z₀)
  证明: by simp [analyticOrderNatAt, hf]

Depends on / 依赖: analyticOrderNatAt
-/
lemma analyticOrderNatAt_of_not_analyticAt (hf : ¬ AnalyticAt 𝕜 f z₀) :
    analyticOrderNatAt f z₀ = 0 := by simp [analyticOrderNatAt, hf]

/--
lemma `Nat.cast_analyticOrderNatAt` / 引理 `Nat.cast_analyticOrderNatAt`

English:
lemma Nat.cast_analyticOrderNatAt
  given: (hf : analyticOrderAt f z₀ != ⊤)
  proof: ENat.natCast_toNat hf

中文:
引理 自然数.cast_analyticOrder自然数At
  条件: (hf : analyticOrderAt f z₀ != ⊤)
  证明: ENat.natCast_toNat hf
-/
@[simp] lemma Nat.cast_analyticOrderNatAt (hf : analyticOrderAt f z₀ != ⊤) :
    analyticOrderNatAt f z₀ = analyticOrderAt f z₀ := ENat.natCast_toNat hf

/--
lemma `analyticOrderAt_eq_top` / 引理 `analyticOrderAt_eq_top`

English:
lemma analyticOrderAt_eq_top
  statement: analyticOrderAt f z₀ = ⊤ ↔ forallᶠ z in 𝓝 z₀, f z = 0 where
  proof: by unfold analyticOrderAt at hf; split_ifs at hf with h <;> simp [*] at *
  mpr hf := by unfold analyticOrderAt; simp [hf, analyticAt_congr hf, analyticAt_const]

中文:
引理 analyticOrderAt_eq_top
  结论: analyticOrderAt f z₀ = ⊤ ↔ 对任意ᶠ z in 𝓝 z₀, f z = 0 where
  证明: by unfold analyticOrderAt at hf; split_ifs at hf with h <;> simp [*] at *
  mpr hf := by unfold analyticOrderAt; simp [hf, analyticAt_congr hf, analyticAt_const]

Depends on / 依赖: analyticAt_congr, analyticAt_const, analyticOrderAt, split_ifs
-/
lemma analyticOrderAt_eq_top : analyticOrderAt f z₀ = ⊤ ↔ forallᶠ z in 𝓝 z₀, f z = 0 where
  mp hf := by unfold analyticOrderAt at hf; split_ifs at hf with h <;> simp [*] at *
  mpr hf := by unfold analyticOrderAt; simp [hf, analyticAt_congr hf, analyticAt_const]

/--
lemma `eventuallyConst_iff_analyticOrderAt_sub_eq_top` / 引理 `eventuallyConst_iff_analyticOrderAt_sub_eq_top`

English:
lemma eventuallyConst_iff_analyticOrderAt_sub_eq_top
  proof: by
  simpa [eventuallyConst_iff_exists_eventuallyEq, analyticOrderAt_eq_top, sub_eq_zero]
    using ⟨fun ⟨c, hc⟩ => (show f z₀ = c from hc.self_of_nhds) ▸ hc, fun h => ⟨_, h⟩⟩

中文:
引理 eventuallyConst_iff_analyticOrderAt_sub_eq_top
  证明: by
  simpa [eventuallyConst_iff_exists_eventuallyEq, analyticOrderAt_eq_top, sub_eq_zero]
    using ⟨fun ⟨c, hc⟩ => (show f z₀ = c from hc.self_of_nhds) ▸ hc, fun h => ⟨_, h⟩⟩

Depends on / 依赖: analyticOrderAt_eq_top, eventuallyConst_iff_exists_eventuallyEq, hc.self_of_nhds, self_of_nhds, sub_eq_zero
-/
lemma eventuallyConst_iff_analyticOrderAt_sub_eq_top :
    EventuallyConst f (𝓝 z₀) ↔ analyticOrderAt (f · - f z₀) z₀ = ⊤ := by
  simpa [eventuallyConst_iff_exists_eventuallyEq, analyticOrderAt_eq_top, sub_eq_zero]
    using ⟨fun ⟨c, hc⟩ => (show f z₀ = c from hc.self_of_nhds) ▸ hc, fun h => ⟨_, h⟩⟩

/--
lemma `AnalyticAt.analyticOrderAt_eq_natCast` / 引理 `AnalyticAt.analyticOrderAt_eq_natCast`

English:
lemma AnalyticAt.analyticOrderAt_eq_natCast
  given: (hf : AnalyticAt 𝕜 f z₀)
  proof: by
  unfold analyticOrderAt
  split_ifs with h
  · simp only [ENat.top_ne_natCast, false_iff]
    contrapose h
    rw [← hf.exists_eventuallyEq_pow_smul_nonzero_iff]
    exact ⟨n, h⟩
  · rw [← hf.exists_eventuallyEq_pow_smul_nonzero_iff] at h
    refine ⟨fun hn => (WithTop.coe_inj.mp hn : h.choose =

中文:
引理 AnalyticAt.analyticOrderAt_eq_natCast
  条件: (hf : AnalyticAt 𝕜 f z₀)
  证明: by
  unfold analyticOrderAt
  split_ifs with h
  · simp only [ENat.top_ne_natCast, false_iff]
    contrapose h
    rw [← hf.exists_eventuallyEq_pow_smul_nonzero_iff]
    exact ⟨n, h⟩
  · rw [← hf.exists_eventuallyEq_pow_smul_nonzero_iff] at h
    refine ⟨fun hn => (WithTop.coe_inj.mp hn : h.choose =

Depends on / 依赖: AnalyticAt, AnalyticAt.unique_eventuallyEq_pow_smul_nonzero, ENat.top_ne_natCast, WithTop, WithTop.coe_inj.mp, analyticOrderAt, choose_spec, coe_inj, contrapose, exists_eventuallyEq_pow_smul_nonzero_iff, false_iff, h.choose, h.choose_spec, hf.exists_eventuallyEq_pow_smul_nonzero_iff, split_ifs, top_ne_natCast, unique_eventuallyEq_pow_smul_nonzero
-/
lemma AnalyticAt.analyticOrderAt_eq_natCast (hf : AnalyticAt 𝕜 f z₀) :
    analyticOrderAt f z₀ = n ↔
      exists (g : 𝕜 -> E), AnalyticAt 𝕜 g z₀ ∧ g z₀ != 0 ∧ forallᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z := by
  unfold analyticOrderAt
  split_ifs with h
  · simp only [ENat.top_ne_natCast, false_iff]
    contrapose h
    rw [← hf.exists_eventuallyEq_pow_smul_nonzero_iff]
    exact ⟨n, h⟩
  · rw [← hf.exists_eventuallyEq_pow_smul_nonzero_iff] at h
    refine ⟨fun hn => (WithTop.coe_inj.mp hn : h.choose = n) ▸ h.choose_spec, fun h' => ?_⟩
    rw [AnalyticAt.unique_eventuallyEq_pow_smul_nonzero h.choose_spec h']

/--
lemma `AnalyticAt.analyticOrderNatAt_eq_iff` / 引理 `AnalyticAt.analyticOrderNatAt_eq_iff`

English:
lemma AnalyticAt.analyticOrderNatAt_eq_iff
  statement: (hf : AnalyticAt 𝕜 f z₀) (hf' : analyticOrderAt f z₀ != ⊤)
  proof: by
  simp [← Nat.cast_inj (R := Nat∞), Nat.cast_analyticOrderNatAt hf', hf.analyticOrderAt_eq_natCast]

中文:
引理 AnalyticAt.analyticOrder自然数At_eq_iff
  结论: (hf : AnalyticAt 𝕜 f z₀) (hf' : analyticOrderAt f z₀ != ⊤)
  证明: by
  simp [← Nat.cast_inj (R := Nat∞), Nat.cast_analyticOrderNatAt hf', hf.analyticOrderAt_eq_natCast]

Depends on / 依赖: Nat.cast_analyticOrderNatAt, Nat.cast_inj, analyticOrderAt_eq_natCast, cast_analyticOrderNatAt, cast_inj, hf.analyticOrderAt_eq_natCast
-/
lemma AnalyticAt.analyticOrderNatAt_eq_iff (hf : AnalyticAt 𝕜 f z₀) (hf' : analyticOrderAt f z₀ != ⊤)
    {n : Nat} :
    analyticOrderNatAt f z₀ = n ↔
      exists (g : 𝕜 -> E), AnalyticAt 𝕜 g z₀ ∧ g z₀ != 0 ∧ forallᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z := by
  simp [← Nat.cast_inj (R := Nat∞), Nat.cast_analyticOrderNatAt hf', hf.analyticOrderAt_eq_natCast]

/--
lemma `AnalyticAt.analyticOrderAt_ne_top` / 引理 `AnalyticAt.analyticOrderAt_ne_top`

English:
lemma AnalyticAt.analyticOrderAt_ne_top
  given: (hf : AnalyticAt 𝕜 f z₀)
  proof: by
  simp only [← ENat.natCast_toNat_eq_self, Eq.comm, EventuallyEq, ← hf.analyticOrderAt_eq_natCast,
    analyticOrderNatAt]

中文:
引理 AnalyticAt.analyticOrderAt_ne_top
  条件: (hf : AnalyticAt 𝕜 f z₀)
  证明: by
  simp only [← ENat.natCast_toNat_eq_self, Eq.comm, EventuallyEq, ← hf.analyticOrderAt_eq_natCast,
    analyticOrderNatAt]

Depends on / 依赖: ENat.natCast_toNat_eq_self, Eq.comm, EventuallyEq, analyticOrderAt_eq_natCast, analyticOrderNatAt, hf.analyticOrderAt_eq_natCast, natCast_toNat_eq_self
-/
lemma AnalyticAt.analyticOrderAt_ne_top (hf : AnalyticAt 𝕜 f z₀) :
    analyticOrderAt f z₀ != ⊤ ↔
      exists (g : 𝕜 -> E), AnalyticAt 𝕜 g z₀ ∧ g z₀ != 0 ∧
        f =ᶠ[𝓝 z₀] fun z => (z - z₀) ^ analyticOrderNatAt f z₀ • g z := by
  simp only [← ENat.natCast_toNat_eq_self, Eq.comm, EventuallyEq, ← hf.analyticOrderAt_eq_natCast,
    analyticOrderNatAt]

/--
lemma `analyticOrderAt_eq_zero` / 引理 `analyticOrderAt_eq_zero`

English:
lemma analyticOrderAt_eq_zero
  statement: analyticOrderAt f z₀ = 0 ↔ ¬ AnalyticAt 𝕜 f z₀ ∨ f z₀ != 0
  proof: by
  by_cases hf : AnalyticAt 𝕜 f z₀
  · rw [← ENat.natCast_zero, hf.analyticOrderAt_eq_natCast]
    constructor
    · intro ⟨g, _, _, hg⟩
      simpa [hf, hg.self_of_nhds]
· exact fun hz => ⟨f, hf, hz.resolve_left not_not_intro hf, by simp⟩
  · simp [hf]

中文:
引理 analyticOrderAt_eq_zero
  结论: analyticOrderAt f z₀ = 0 ↔ ¬ AnalyticAt 𝕜 f z₀ ∨ f z₀ != 0
  证明: by
  by_cases hf : AnalyticAt 𝕜 f z₀
  · rw [← ENat.natCast_zero, hf.analyticOrderAt_eq_natCast]
    constructor
    · intro ⟨g, _, _, hg⟩
      simpa [hf, hg.self_of_nhds]
· exact fun hz => ⟨f, hf, hz.resolve_left not_not_intro hf, by simp⟩
  · simp [hf]

Depends on / 依赖: AnalyticAt, ENat.natCast_zero, analyticOrderAt_eq_natCast, hf.analyticOrderAt_eq_natCast, hg.self_of_nhds, hz.resolve_left, natCast_zero, not_not_intro, resolve_left, self_of_nhds
-/
lemma analyticOrderAt_eq_zero : analyticOrderAt f z₀ = 0 ↔ ¬ AnalyticAt 𝕜 f z₀ ∨ f z₀ != 0 := by
  by_cases hf : AnalyticAt 𝕜 f z₀
  · rw [← ENat.natCast_zero, hf.analyticOrderAt_eq_natCast]
    constructor
    · intro ⟨g, _, _, hg⟩
      simpa [hf, hg.self_of_nhds]
· exact fun hz => ⟨f, hf, hz.resolve_left not_not_intro hf, by simp⟩
  · simp [hf]

/--
lemma `analyticOrderAt_ne_zero` / 引理 `analyticOrderAt_ne_zero`

English:
lemma analyticOrderAt_ne_zero
  statement: analyticOrderAt f z₀ != 0 ↔ AnalyticAt 𝕜 f z₀ ∧ f z₀ = 0
  proof: by
  simp [analyticOrderAt_eq_zero]

中文:
引理 analyticOrderAt_ne_zero
  结论: analyticOrderAt f z₀ != 0 ↔ AnalyticAt 𝕜 f z₀ ∧ f z₀ = 0
  证明: by
  simp [analyticOrderAt_eq_zero]

Depends on / 依赖: analyticOrderAt_eq_zero
-/
lemma analyticOrderAt_ne_zero : analyticOrderAt f z₀ != 0 ↔ AnalyticAt 𝕜 f z₀ ∧ f z₀ = 0 := by
  simp [analyticOrderAt_eq_zero]

/--
lemma `AnalyticAt.analyticOrderAt_eq_zero` / 引理 `AnalyticAt.analyticOrderAt_eq_zero`

English:
lemma AnalyticAt.analyticOrderAt_eq_zero
  given: (hf : AnalyticAt 𝕜 f z₀)
  proof: by simp [hf, analyticOrderAt_eq_zero]

中文:
引理 AnalyticAt.analyticOrderAt_eq_zero
  条件: (hf : AnalyticAt 𝕜 f z₀)
  证明: by simp [hf, analyticOrderAt_eq_zero]
-/
protected lemma AnalyticAt.analyticOrderAt_eq_zero (hf : AnalyticAt 𝕜 f z₀) :
    analyticOrderAt f z₀ = 0 ↔ f z₀ != 0 := by simp [hf, analyticOrderAt_eq_zero]

/--
lemma `AnalyticAt.analyticOrderAt_ne_zero` / 引理 `AnalyticAt.analyticOrderAt_ne_zero`

English:
lemma AnalyticAt.analyticOrderAt_ne_zero
  given: (hf : AnalyticAt 𝕜 f z₀)
  proof: hf.analyticOrderAt_eq_zero.not_left

中文:
引理 AnalyticAt.analyticOrderAt_ne_zero
  条件: (hf : AnalyticAt 𝕜 f z₀)
  证明: hf.analyticOrderAt_eq_zero.not_left
-/
protected lemma AnalyticAt.analyticOrderAt_ne_zero (hf : AnalyticAt 𝕜 f z₀) :
    analyticOrderAt f z₀ != 0 ↔ f z₀ = 0 := hf.analyticOrderAt_eq_zero.not_left

/--
lemma `apply_eq_zero_of_analyticOrderAt_ne_zero` / 引理 `apply_eq_zero_of_analyticOrderAt_ne_zero`

English:
lemma apply_eq_zero_of_analyticOrderAt_ne_zero
  given: (hf : analyticOrderAt f z₀ != 0)
  proof: by
  by_cases hf' : AnalyticAt 𝕜 f z₀ <;> simp_all [analyticOrderAt_eq_zero]

中文:
引理 apply_eq_zero_of_analyticOrderAt_ne_zero
  条件: (hf : analyticOrderAt f z₀ != 0)
  证明: by
  by_cases hf' : AnalyticAt 𝕜 f z₀ <;> simp_all [analyticOrderAt_eq_zero]

Depends on / 依赖: AnalyticAt, analyticOrderAt_eq_zero
-/
lemma apply_eq_zero_of_analyticOrderAt_ne_zero (hf : analyticOrderAt f z₀ != 0) :
    f z₀ = 0 := by
  by_cases hf' : AnalyticAt 𝕜 f z₀ <;> simp_all [analyticOrderAt_eq_zero]

/--
lemma `apply_eq_zero_of_analyticOrderNatAt_ne_zero` / 引理 `apply_eq_zero_of_analyticOrderNatAt_ne_zero`

English:
lemma apply_eq_zero_of_analyticOrderNatAt_ne_zero
  given: (hf : analyticOrderNatAt f z₀ != 0)
  proof: by
  by_cases hf' : AnalyticAt 𝕜 f z₀ <;> simp_all [analyticOrderNatAt, analyticOrderAt_eq_zero]

中文:
引理 apply_eq_zero_of_analyticOrder自然数At_ne_zero
  条件: (hf : analyticOrder自然数At f z₀ != 0)
  证明: by
  by_cases hf' : AnalyticAt 𝕜 f z₀ <;> simp_all [analyticOrderNatAt, analyticOrderAt_eq_zero]

Depends on / 依赖: AnalyticAt, analyticOrderAt_eq_zero, analyticOrderNatAt
-/
lemma apply_eq_zero_of_analyticOrderNatAt_ne_zero (hf : analyticOrderNatAt f z₀ != 0) :
    f z₀ = 0 := by
  by_cases hf' : AnalyticAt 𝕜 f z₀ <;> simp_all [analyticOrderNatAt, analyticOrderAt_eq_zero]

/--
lemma `natCast_le_analyticOrderAt` / 引理 `natCast_le_analyticOrderAt`

English:
lemma natCast_le_analyticOrderAt
  given: (hf : AnalyticAt 𝕜 f z₀) {n : Nat}
  proof: by
  unfold analyticOrderAt
  split_ifs with h
  · simpa using ⟨0, analyticAt_const .., by simpa⟩
  · let m := (hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h).choose
    obtain ⟨g, hg, hg_ne, hm⟩ := (hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h).choose_spec
    rw [ENat.natCast_le_natCast]


中文:
引理 natCast_le_analyticOrderAt
  条件: (hf : AnalyticAt 𝕜 f z₀) {n : 自然数}
  证明: by
  unfold analyticOrderAt
  split_ifs with h
  · simpa using ⟨0, analyticAt_const .., by simpa⟩
  · let m := (hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h).choose
    obtain ⟨g, hg, hg_ne, hm⟩ := (hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h).choose_spec
    rw [ENat.natCast_le_natCast]


Depends on / 依赖: ENat.natCast_le_natCast, Nat.add_sub_of_le, add_sub_of_le, analyticAt_const, analyticOrderAt, choose_spec, contrapose, exists_eventuallyEq_pow_smul_nonzero_iff, filter_upwards, fun_prop, hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr, hg_ne, mul_smul, natCast_le_natCast, pow_add, split_ifs
-/
lemma natCast_le_analyticOrderAt (hf : AnalyticAt 𝕜 f z₀) {n : Nat} :
    n <= analyticOrderAt f z₀ ↔
      exists g, AnalyticAt 𝕜 g z₀ ∧ forallᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z := by
  unfold analyticOrderAt
  split_ifs with h
  · simpa using ⟨0, analyticAt_const .., by simpa⟩
  · let m := (hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h).choose
    obtain ⟨g, hg, hg_ne, hm⟩ := (hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h).choose_spec
    rw [ENat.natCast_le_natCast]
    refine ⟨fun hmn => ⟨fun z => (z - z₀) ^ (m - n) • g z, by fun_prop, ?_⟩, fun ⟨h, hh, hfh⟩ => ?_⟩
    · filter_upwards [hm] with z hz using by rwa [← mul_smul, ← pow_add, Nat.add_sub_of_le hmn]
    · contrapose! hg_ne
      have : ContinuousAt (fun z => (z - z₀) ^ (n - m) • h z) z₀ := by fun_prop
      rw [tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[!=] z₀)
        hg.continuousAt.continuousWithinAt this.continuousWithinAt ?_]
      · simp [m, Nat.sub_ne_zero_of_lt hg_ne]
      · filter_upwards [self_mem_nhdsWithin, hm.filter_mono nhdsWithin_le_nhds,
          hfh.filter_mono nhdsWithin_le_nhds] with z hz hf' hf''
        rw [← inv_smul_eq_iff₀ (pow_ne_zero _ <| sub_ne_zero_of_ne hz)]; rw [hf'']; rw [smul_comm]; rw [← mul_smul] at hf'
        rw [pow_sub₀ _ (sub_ne_zero_of_ne hz) (by lia)]; rw [← hf']

/--
lemma `analyticOrderAt_congr` / 引理 `analyticOrderAt_congr`

English:
lemma analyticOrderAt_congr
  given: (hfg : f =ᶠ[𝓝 z₀] g)
  proof: by
  by_cases hf : AnalyticAt 𝕜 f z₀
  · refine ENat.eq_of_forall_natCast_le_iff fun n => ?_
    simp only [natCast_le_analyticOrderAt, hf, hf.congr hfg]
    congr! 3
    exact hfg.congr_left
  · rw [analyticOrderAt_of_not_analyticAt hf,
analyticOrderAt_of_not_analyticAt fun hg => hf hg.congr hfg.sy

中文:
引理 analyticOrderAt_congr
  条件: (hfg : f =ᶠ[𝓝 z₀] g)
  证明: by
  by_cases hf : AnalyticAt 𝕜 f z₀
  · refine ENat.eq_of_forall_natCast_le_iff fun n => ?_
    simp only [natCast_le_analyticOrderAt, hf, hf.congr hfg]
    congr! 3
    exact hfg.congr_left
  · rw [analyticOrderAt_of_not_analyticAt hf,
analyticOrderAt_of_not_analyticAt fun hg => hf hg.congr hfg.sy

Depends on / 依赖: AnalyticAt, ENat.eq_of_forall_natCast_le_iff, analyticOrderAt_of_not_analyticAt, congr_left, eq_of_forall_natCast_le_iff, hf.congr, hfg.congr_left, hfg.symm, hg.congr, natCast_le_analyticOrderAt
-/
lemma analyticOrderAt_congr (hfg : f =ᶠ[𝓝 z₀] g) :
    analyticOrderAt f z₀ = analyticOrderAt g z₀ := by
  by_cases hf : AnalyticAt 𝕜 f z₀
  · refine ENat.eq_of_forall_natCast_le_iff fun n => ?_
    simp only [natCast_le_analyticOrderAt, hf, hf.congr hfg]
    congr! 3
    exact hfg.congr_left
  · rw [analyticOrderAt_of_not_analyticAt hf,
analyticOrderAt_of_not_analyticAt fun hg => hf hg.congr hfg.symm]

/--
lemma `analyticOrderAt_id` / 引理 `analyticOrderAt_id`

English:
lemma analyticOrderAt_id
  statement: analyticOrderAt (𝕜 := 𝕜) id 0 = 1
  proof: analyticAt_id.analyticOrderAt_eq_natCast.mpr ⟨fun _ => 1, by fun_prop, by simp, by simp⟩

中文:
引理 analyticOrderAt_id
  结论: analyticOrderAt (𝕜 := 𝕜) id 0 = 1
  证明: analyticAt_id.analyticOrderAt_eq_natCast.mpr ⟨fun _ => 1, by fun_prop, by simp, by simp⟩
-/
@[simp] lemma analyticOrderAt_id : analyticOrderAt (𝕜 := 𝕜) id 0 = 1 :=
  analyticAt_id.analyticOrderAt_eq_natCast.mpr ⟨fun _ => 1, by fun_prop, by simp, by simp⟩

/--
lemma `analyticOrderAt_neg` / 引理 `analyticOrderAt_neg`

English:
lemma analyticOrderAt_neg
  statement: analyticOrderAt (-f) z₀ = analyticOrderAt f z₀
  proof: by
  by_cases hf : AnalyticAt 𝕜 f z₀
  · refine ENat.eq_of_forall_natCast_le_iff fun n => ?_
    simp only [natCast_le_analyticOrderAt, hf, hf.neg]
exact (Equiv.neg _).exists_congr by simp [neg_eq_iff_eq_neg]
  · rw [analyticOrderAt_of_not_analyticAt hf,
analyticOrderAt_of_not_analyticAt analyticAt_

中文:
引理 analyticOrderAt_neg
  结论: analyticOrderAt (-f) z₀ = analyticOrderAt f z₀
  证明: by
  by_cases hf : AnalyticAt 𝕜 f z₀
  · refine ENat.eq_of_forall_natCast_le_iff fun n => ?_
    simp only [natCast_le_analyticOrderAt, hf, hf.neg]
exact (Equiv.neg _).exists_congr by simp [neg_eq_iff_eq_neg]
  · rw [analyticOrderAt_of_not_analyticAt hf,
analyticOrderAt_of_not_analyticAt analyticAt_
-/
@[simp] lemma analyticOrderAt_neg : analyticOrderAt (-f) z₀ = analyticOrderAt f z₀ := by
  by_cases hf : AnalyticAt 𝕜 f z₀
  · refine ENat.eq_of_forall_natCast_le_iff fun n => ?_
    simp only [natCast_le_analyticOrderAt, hf, hf.neg]
exact (Equiv.neg _).exists_congr by simp [neg_eq_iff_eq_neg]
  · rw [analyticOrderAt_of_not_analyticAt hf,
analyticOrderAt_of_not_analyticAt analyticAt_neg.not.2 hf]

/--
theorem `le_analyticOrderAt_add` / 定理 `le_analyticOrderAt_add`

English:
theorem le_analyticOrderAt_add
  proof: by
  by_cases hf : AnalyticAt 𝕜 f z₀
  · by_cases hg : AnalyticAt 𝕜 g z₀
    · refine ENat.forall_natCast_le_iff_le.mp fun n => ?_
      simp only [le_min_iff, natCast_le_analyticOrderAt, hf, hg, hf.add hg]
      refine fun ⟨⟨F, hF, hF'⟩, ⟨G, hG, hG'⟩⟩ => ⟨F + G, hF.add hG, ?_⟩
      filter_upwards 

中文:
定理 le_analyticOrderAt_add
  证明: by
  by_cases hf : AnalyticAt 𝕜 f z₀
  · by_cases hg : AnalyticAt 𝕜 g z₀
    · refine ENat.forall_natCast_le_iff_le.mp fun n => ?_
      simp only [le_min_iff, natCast_le_analyticOrderAt, hf, hg, hf.add hg]
      refine fun ⟨⟨F, hF, hF'⟩, ⟨G, hG, hG'⟩⟩ => ⟨F + G, hF.add hG, ?_⟩
      filter_upwards 

Depends on / 依赖: AnalyticAt, ENat.forall_natCast_le_iff_le.mp, contextual, filter_upwards, forall_natCast_le_iff_le, hF.add, hf.add, le_min_iff, natCast_le_analyticOrderAt
-/
theorem le_analyticOrderAt_add :
    min (analyticOrderAt f z₀) (analyticOrderAt g z₀) <= analyticOrderAt (f + g) z₀ := by
  by_cases hf : AnalyticAt 𝕜 f z₀
  · by_cases hg : AnalyticAt 𝕜 g z₀
    · refine ENat.forall_natCast_le_iff_le.mp fun n => ?_
      simp only [le_min_iff, natCast_le_analyticOrderAt, hf, hg, hf.add hg]
      refine fun ⟨⟨F, hF, hF'⟩, ⟨G, hG, hG'⟩⟩ => ⟨F + G, hF.add hG, ?_⟩
      filter_upwards [hF', hG'] with z using by simp +contextual
    · simp [*]
  · simp [*]

/--
lemma `le_analyticOrderAt_sub` / 引理 `le_analyticOrderAt_sub`

English:
lemma le_analyticOrderAt_sub
  proof: by
  simpa [sub_eq_add_neg] using le_analyticOrderAt_add (f := f) (g := -g)

中文:
引理 le_analyticOrderAt_sub
  证明: by
  simpa [sub_eq_add_neg] using le_analyticOrderAt_add (f := f) (g := -g)

Depends on / 依赖: le_analyticOrderAt_add, sub_eq_add_neg
-/
lemma le_analyticOrderAt_sub :
    min (analyticOrderAt f z₀) (analyticOrderAt g z₀) <= analyticOrderAt (f - g) z₀ := by
  simpa [sub_eq_add_neg] using le_analyticOrderAt_add (f := f) (g := -g)

/--
lemma `analyticOrderAt_add_eq_left_of_lt` / 引理 `analyticOrderAt_add_eq_left_of_lt`

English:
lemma analyticOrderAt_add_eq_left_of_lt
  given: (hfg : analyticOrderAt f z₀ < analyticOrderAt g z₀)
  proof: le_antisymm (by simpa [hfg.not_ge] using le_analyticOrderAt_sub (f := f + g) (g := g) (z₀ := z₀))
    (by simpa [hfg.le] using le_analyticOrderAt_add (f := f) (g := g) (z₀ := z₀))

中文:
引理 analyticOrderAt_add_eq_left_of_lt
  条件: (hfg : analyticOrderAt f z₀ < analyticOrderAt g z₀)
  证明: le_antisymm (by simpa [hfg.not_ge] using le_analyticOrderAt_sub (f := f + g) (g := g) (z₀ := z₀))
    (by simpa [hfg.le] using le_analyticOrderAt_add (f := f) (g := g) (z₀ := z₀))

Depends on / 依赖: hfg.le, hfg.not_ge, le_analyticOrderAt_add, le_analyticOrderAt_sub, le_antisymm, not_ge
-/
lemma analyticOrderAt_add_eq_left_of_lt (hfg : analyticOrderAt f z₀ < analyticOrderAt g z₀) :
    analyticOrderAt (f + g) z₀ = analyticOrderAt f z₀ :=
  le_antisymm (by simpa [hfg.not_ge] using le_analyticOrderAt_sub (f := f + g) (g := g) (z₀ := z₀))
    (by simpa [hfg.le] using le_analyticOrderAt_add (f := f) (g := g) (z₀ := z₀))

/--
lemma `analyticOrderAt_add_eq_right_of_lt` / 引理 `analyticOrderAt_add_eq_right_of_lt`

English:
lemma analyticOrderAt_add_eq_right_of_lt
  given: (hgf : analyticOrderAt g z₀ < analyticOrderAt f z₀)
  proof: by
  rw [add_comm]; rw [analyticOrderAt_add_eq_left_of_lt hgf]

中文:
引理 analyticOrderAt_add_eq_right_of_lt
  条件: (hgf : analyticOrderAt g z₀ < analyticOrderAt f z₀)
  证明: by
  rw [add_comm]; rw [analyticOrderAt_add_eq_left_of_lt hgf]

Depends on / 依赖: add_comm, analyticOrderAt_add_eq_left_of_lt
-/
lemma analyticOrderAt_add_eq_right_of_lt (hgf : analyticOrderAt g z₀ < analyticOrderAt f z₀) :
    analyticOrderAt (f + g) z₀ = analyticOrderAt g z₀ := by
  rw [add_comm]; rw [analyticOrderAt_add_eq_left_of_lt hgf]

/--
lemma `analyticOrderAt_add_of_ne` / 引理 `analyticOrderAt_add_of_ne`

English:
lemma analyticOrderAt_add_of_ne
  given: (hfg : analyticOrderAt f z₀ != analyticOrderAt g z₀)
  proof: by
  obtain hfg | hgf := hfg.lt_or_gt
  · simpa [hfg.le] using analyticOrderAt_add_eq_left_of_lt hfg
  · simpa [hgf.le] using analyticOrderAt_add_eq_right_of_lt hgf

中文:
引理 analyticOrderAt_add_of_ne
  条件: (hfg : analyticOrderAt f z₀ != analyticOrderAt g z₀)
  证明: by
  obtain hfg | hgf := hfg.lt_or_gt
  · simpa [hfg.le] using analyticOrderAt_add_eq_left_of_lt hfg
  · simpa [hgf.le] using analyticOrderAt_add_eq_right_of_lt hgf

Depends on / 依赖: analyticOrderAt_add_eq_left_of_lt, analyticOrderAt_add_eq_right_of_lt, hfg.le, hfg.lt_or_gt, hgf.le, lt_or_gt
-/
lemma analyticOrderAt_add_of_ne (hfg : analyticOrderAt f z₀ != analyticOrderAt g z₀) :
    analyticOrderAt (f + g) z₀ = min (analyticOrderAt f z₀) (analyticOrderAt g z₀) := by
  obtain hfg | hgf := hfg.lt_or_gt
  · simpa [hfg.le] using analyticOrderAt_add_eq_left_of_lt hfg
  · simpa [hgf.le] using analyticOrderAt_add_eq_right_of_lt hgf

/--
lemma `analyticOrderAt_smul_eq_top_of_left` / 引理 `analyticOrderAt_smul_eq_top_of_left`

English:
lemma analyticOrderAt_smul_eq_top_of_left
  given: {f : 𝕜 -> 𝕜} (hf : analyticOrderAt f z₀ = ⊤)
  proof: by
  rw [analyticOrderAt_eq_top]; rw [eventually_nhds_iff] at *
  obtain ⟨t, h₁t, h₂t, h₃t⟩ := hf
  exact ⟨t, fun y hy => by simp [h₁t y hy], h₂t, h₃t⟩

中文:
引理 analyticOrderAt_smul_eq_top_of_left
  条件: {f : 𝕜 -> 𝕜} (hf : analyticOrderAt f z₀ = ⊤)
  证明: by
  rw [analyticOrderAt_eq_top]; rw [eventually_nhds_iff] at *
  obtain ⟨t, h₁t, h₂t, h₃t⟩ := hf
  exact ⟨t, fun y hy => by simp [h₁t y hy], h₂t, h₃t⟩

Depends on / 依赖: analyticOrderAt_eq_top, eventually_nhds_iff
-/
lemma analyticOrderAt_smul_eq_top_of_left {f : 𝕜 -> 𝕜} (hf : analyticOrderAt f z₀ = ⊤) :
     analyticOrderAt (f • g) z₀ = ⊤ := by
  rw [analyticOrderAt_eq_top]; rw [eventually_nhds_iff] at *
  obtain ⟨t, h₁t, h₂t, h₃t⟩ := hf
  exact ⟨t, fun y hy => by simp [h₁t y hy], h₂t, h₃t⟩

/--
lemma `analyticOrderAt_smul_eq_top_of_right` / 引理 `analyticOrderAt_smul_eq_top_of_right`

English:
lemma analyticOrderAt_smul_eq_top_of_right
  given: {f : 𝕜 -> 𝕜} (hg : analyticOrderAt g z₀ = ⊤)
  proof: by
  rw [analyticOrderAt_eq_top]; rw [eventually_nhds_iff] at *
  obtain ⟨t, h₁t, h₂t, h₃t⟩ := hg
  exact ⟨t, fun y hy => by simp [h₁t y hy], h₂t, h₃t⟩

中文:
引理 analyticOrderAt_smul_eq_top_of_right
  条件: {f : 𝕜 -> 𝕜} (hg : analyticOrderAt g z₀ = ⊤)
  证明: by
  rw [analyticOrderAt_eq_top]; rw [eventually_nhds_iff] at *
  obtain ⟨t, h₁t, h₂t, h₃t⟩ := hg
  exact ⟨t, fun y hy => by simp [h₁t y hy], h₂t, h₃t⟩

Depends on / 依赖: analyticOrderAt_eq_top, eventually_nhds_iff
-/
lemma analyticOrderAt_smul_eq_top_of_right {f : 𝕜 -> 𝕜} (hg : analyticOrderAt g z₀ = ⊤) :
    analyticOrderAt (f • g) z₀ = ⊤ := by
  rw [analyticOrderAt_eq_top]; rw [eventually_nhds_iff] at *
  obtain ⟨t, h₁t, h₂t, h₃t⟩ := hg
  exact ⟨t, fun y hy => by simp [h₁t y hy], h₂t, h₃t⟩

/--
lemma `analyticOrderAt_smul` / 引理 `analyticOrderAt_smul`

English:
lemma analyticOrderAt_smul
  given: {f : 𝕜 -> 𝕜} (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀)
  proof: by
  -- Trivial cases: one of the functions vanishes around z₀
  by_cases hf' : analyticOrderAt f z₀ = ⊤
  · simp [analyticOrderAt_smul_eq_top_of_left, *]
  by_cases hg' : analyticOrderAt g z₀ = ⊤
  · simp [analyticOrderAt_smul_eq_top_of_right, *]
  -- Non-trivial case: both functions do not vanish 

中文:
引理 analyticOrderAt_smul
  条件: {f : 𝕜 -> 𝕜} (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀)
  证明: by
  -- Trivial cases: one of the functions vanishes around z₀
  by_cases hf' : analyticOrderAt f z₀ = ⊤
  · simp [analyticOrderAt_smul_eq_top_of_left, *]
  by_cases hg' : analyticOrderAt g z₀ = ⊤
  · simp [analyticOrderAt_smul_eq_top_of_right, *]
  -- Non-trivial case: both functions do not vanish 
-/
lemma analyticOrderAt_smul {f : 𝕜 -> 𝕜} (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    analyticOrderAt (f • g) z₀ = analyticOrderAt f z₀ + analyticOrderAt g z₀ := by
  -- Trivial cases: one of the functions vanishes around z₀
  by_cases hf' : analyticOrderAt f z₀ = ⊤
  · simp [analyticOrderAt_smul_eq_top_of_left, *]
  by_cases hg' : analyticOrderAt g z₀ = ⊤
  · simp [analyticOrderAt_smul_eq_top_of_right, *]
  -- Non-trivial case: both functions do not vanish around z₀
  obtain ⟨f', h₁f', h₂f', h₃f'⟩ := hf.analyticOrderAt_ne_top.1 hf'
  obtain ⟨g', h₁g', h₂g', h₃g'⟩ := hg.analyticOrderAt_ne_top.1 hg'
  rw [← Nat.cast_analyticOrderNatAt hf']; rw [← Nat.cast_analyticOrderNatAt hg']; rw [← ENat.natCast_add]; rw [(hf.smul hg).analyticOrderAt_eq_natCast]
  refine ⟨f' • g', h₁f'.smul h₁g', ?_, ?_⟩
  · simp
    tauto
  · obtain ⟨t, h₁t, h₂t, h₃t⟩ := eventually_nhds_iff.1 h₃f'
    obtain ⟨s, h₁s, h₂s, h₃s⟩ := eventually_nhds_iff.1 h₃g'
    exact eventually_nhds_iff.2
      ⟨t inter s, fun y hy => (by simp [h₁t y hy.1, h₁s y hy.2]; module), h₂t.inter h₂s, h₃t, h₃s⟩

/--
theorem `AnalyticAt.analyticOrderAt_deriv_add_one` / 定理 `AnalyticAt.analyticOrderAt_deriv_add_one`

English:
theorem AnalyticAt.analyticOrderAt_deriv_add_one
  statement: {x : 𝕜} (hf : AnalyticAt 𝕜 f x)
  proof: by
  generalize h : analyticOrderAt (f · - f x) x = r
  cases r with
  | top =>
    suffices analyticOrderAt (deriv f) x = ⊤ by simp_all
    simp only [analyticOrderAt_eq_top, sub_eq_zero] at h ⊢
    obtain ⟨U, hUf, hUo, hUx⟩ := eventually_nhds_iff.mp h
    filter_upwards [hUo.mem_nhds hUx] with y h

中文:
定理 AnalyticAt.analyticOrderAt_deriv_add_one
  结论: {x : 𝕜} (hf : AnalyticAt 𝕜 f x)
  证明: by
  generalize h : analyticOrderAt (f · - f x) x = r
  cases r with
  | top =>
    suffices analyticOrderAt (deriv f) x = ⊤ by simp_all
    simp only [analyticOrderAt_eq_top, sub_eq_zero] at h ⊢
    obtain ⟨U, hUf, hUo, hUx⟩ := eventually_nhds_iff.mp h
    filter_upwards [hUo.mem_nhds hUx] with y h

Depends on / 依赖: AnalyticAt, AnalyticAt.analyticOrderAt_eq_zero, ENat.natCast_zero, analyticOrderAt, analyticOrderAt_eq_top, analyticOrderAt_eq_zero, deriv_eq, eventuallyEq_of_mem, eventually_nhds_iff, eventually_nhds_iff.mp, filter_upwards, fun_prop, generalize, hUo.mem_nhds, mem_nhds, natCast_zero, sub_eq_zero
-/
theorem AnalyticAt.analyticOrderAt_deriv_add_one {x : 𝕜} (hf : AnalyticAt 𝕜 f x)
    [CompleteSpace E] [CharZero 𝕜] :
    analyticOrderAt (deriv f) x + 1 = analyticOrderAt (f · - f x) x := by
  generalize h : analyticOrderAt (f · - f x) x = r
  cases r with
  | top =>
    suffices analyticOrderAt (deriv f) x = ⊤ by simp_all
    simp only [analyticOrderAt_eq_top, sub_eq_zero] at h ⊢
    obtain ⟨U, hUf, hUo, hUx⟩ := eventually_nhds_iff.mp h
    filter_upwards [hUo.mem_nhds hUx] with y hy
    simp [(eventuallyEq_of_mem (hUo.mem_nhds hy) hUf).deriv_eq]
  | coe r =>
    have hrne : r != 0 := by
      intro hr
      rw [hr]; rw [ENat.natCast_zero]; rw [AnalyticAt.analyticOrderAt_eq_zero (by fun_prop)] at h
      grind
    obtain ⟨s, rfl⟩ := Nat.exists_add_one_eq.mpr (Nat.pos_of_ne_zero hrne)
    rw [Nat.cast_succ]
    congr 1
    rw [analyticOrderAt_eq_natCast (by fun_prop)] at h
    obtain ⟨F, hFa, hFne, hfF⟩ := h
    simp only [sub_eq_iff_eq_add] at hfF
    obtain ⟨U, hUf, hUo, hUx⟩ := eventually_nhds_iff.mp (hfF.and hFa.eventually_analyticAt)
    have : forall y in U, deriv f y =
        (y - x) ^ (s + 1) • deriv F y + (s + 1) • (y - x) ^ s • F y := by
      intro y hy
      rw [EventuallyEq.deriv_eq (eventually_of_mem (hUo.mem_nhds hy) (fun u hu => (hUf u hu).1))]; rw [deriv_add_const]; rw [deriv_fun_smul (by fun_prop) (hUf y hy).2.differentiableAt]
      simp [mul_smul, add_smul, Nat.cast_smul_eq_nsmul]
    rw [analyticOrderAt_congr (eventually_of_mem (hUo.mem_nhds hUx) this)]
    have : analyticOrderAt (fun y => (s + 1) • (y - x) ^ s • F y) x = s := by
      rw [analyticOrderAt_eq_natCast]
      · refine ⟨fun z => (↑(s + 1) : 𝕜) • F z, hFa.fun_const_smul, ?_, .of_forall fun y => ?_⟩
        · simpa using ⟨by norm_cast, hFne⟩
        · simpa only [Nat.cast_smul_eq_nsmul] using smul_comm ..
      · simp_rw [← Nat.cast_smul_eq_nsmul 𝕜]
        fun_prop
    rwa [← Pi.add_def, analyticOrderAt_add_eq_right_of_lt]
    rw [this]; rw [← ENat.add_one_le_iff (ENat.natCast_ne_top _)]; rw [← Nat.cast_add_one]; rw [natCast_le_analyticOrderAt (by fun_prop)]
    exact ⟨deriv F, hFa.deriv, by simp⟩

/--
theorem `AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero` / 定理 `AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero`

English:
theorem AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero
  statement: {x : 𝕜} (hf : AnalyticAt 𝕜 f x)
  proof: by
  generalize h : analyticOrderAt (f · - f x) x = r
  cases r with
  | top =>
    simp_rw [analyticOrderAt_eq_top, sub_eq_zero] at h
    refine (hf' ?_).elim
    rw [EventuallyEq.deriv_eq h]; rw [deriv_const]
  | coe r =>
    norm_cast
    obtain ⟨F, hFa, hFne, hfF⟩ := (analyticOrderAt_eq_natCast 

中文:
定理 AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero
  结论: {x : 𝕜} (hf : AnalyticAt 𝕜 f x)
  证明: by
  generalize h : analyticOrderAt (f · - f x) x = r
  cases r with
  | top =>
    simp_rw [analyticOrderAt_eq_top, sub_eq_zero] at h
    refine (hf' ?_).elim
    rw [EventuallyEq.deriv_eq h]; rw [deriv_const]
  | coe r =>
    norm_cast
    obtain ⟨F, hFa, hFne, hfF⟩ := (analyticOrderAt_eq_natCast 

Depends on / 依赖: EventuallyEq, EventuallyEq.deriv_eq, analyticOrderAt, analyticOrderAt_eq_natCast, analyticOrderAt_eq_top, contrapose, deriv_add_const, deriv_const, deriv_eq, deriv_fun_smul, eq_of_ge_of_le, fun_pro, fun_prop, generalize, hfF.self_of_nhds, self_of_nhds, simp_rw, sub_eq_iff_eq_add, sub_eq_zero
-/
theorem AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero {x : 𝕜} (hf : AnalyticAt 𝕜 f x)
    (hf' : deriv f x != 0) : analyticOrderAt (f · - f x) x = 1 := by
  generalize h : analyticOrderAt (f · - f x) x = r
  cases r with
  | top =>
    simp_rw [analyticOrderAt_eq_top, sub_eq_zero] at h
    refine (hf' ?_).elim
    rw [EventuallyEq.deriv_eq h]; rw [deriv_const]
  | coe r =>
    norm_cast
    obtain ⟨F, hFa, hFne, hfF⟩ := (analyticOrderAt_eq_natCast (by fun_prop)).mp h
    apply eq_of_ge_of_le
    · by_contra! hr
      have := hfF.self_of_nhds
      simp_all
    · contrapose! hf'
      simp_rw [sub_eq_iff_eq_add] at hfF
      rw [EventuallyEq.deriv_eq hfF]; rw [deriv_add_const]; rw [deriv_fun_smul (by fun_prop) (by fun_prop)]; rw [deriv_fun_pow (by fun_prop)]; rw [sub_self]; rw [zero_pow (by lia)]; rw [zero_pow (by lia)]; rw [mul_zero]; rw [zero_mul]; rw [zero_smul]; rw [zero_smul]; rw [add_zero]

/--
theorem `AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero` / 定理 `AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero`

English:
theorem AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  statement: {x : 𝕜}
  proof: by
  simpa [hfx] using hf.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hf'

中文:
定理 AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  结论: {x : 𝕜}
  证明: by
  simpa [hfx] using hf.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hf'

Depends on / 依赖: analyticOrderAt_sub_eq_one_of_deriv_ne_zero, hf.analyticOrderAt_sub_eq_one_of_deriv_ne_zero
-/
theorem AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero {x : 𝕜}
    (hf : AnalyticAt 𝕜 f x) (hfx : f x = 0) (hf' : deriv f x != 0) :
    analyticOrderAt f x = 1 := by
  simpa [hfx] using hf.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hf'

/--
lemma `natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero` / 引理 `natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero`

English:
lemma natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
  statement: [CharZero 𝕜] [CompleteSpace E]
  proof: by
  induction n generalizing f with
  | zero => simp
  | succ n IH =>
    by_cases hfz : f z₀ = 0; swap
    · simpa [analyticOrderAt_eq_zero.mpr (.inr hfz)] using ⟨0, by simp, by simpa⟩
    have : analyticOrderAt (deriv f) z₀ + 1 = analyticOrderAt f z₀ := by
      simpa [hfz] using hf.analyticOrder

中文:
引理 natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
  结论: [特征零 𝕜] [完备空间 E]
  证明: by
  induction n generalizing f with
  | zero => simp
  | succ n IH =>
    by_cases hfz : f z₀ = 0; swap
    · simpa [analyticOrderAt_eq_zero.mpr (.inr hfz)] using ⟨0, by simp, by simpa⟩
    have : analyticOrderAt (deriv f) z₀ + 1 = analyticOrderAt f z₀ := by
      simpa [hfz] using hf.analyticOrder

Depends on / 依赖: Nat.forall_lt_succ_left, Order.lt_add_one_iff, analyticOrderAt, analyticOrderAt_deriv_add_one, analyticOrderAt_eq_zero, analyticOrderAt_eq_zero.mpr, forall_lt_succ_left, generalizing, hf.analyticOrderAt_deriv_add_one, hf.deriv, iteratedDeriv_succ, lt_add_one_iff
-/
lemma natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero [CharZero 𝕜] [CompleteSpace E]
    (hf : AnalyticAt 𝕜 f z₀) :
    n <= analyticOrderAt f z₀ ↔ forall i < n, iteratedDeriv i f z₀ = 0 := by
  induction n generalizing f with
  | zero => simp
  | succ n IH =>
    by_cases hfz : f z₀ = 0; swap
    · simpa [analyticOrderAt_eq_zero.mpr (.inr hfz)] using ⟨0, by simp, by simpa⟩
    have : analyticOrderAt (deriv f) z₀ + 1 = analyticOrderAt f z₀ := by
      simpa [hfz] using hf.analyticOrderAt_deriv_add_one
    simp [← this, IH hf.deriv, iteratedDeriv_succ',
      -Order.lt_add_one_iff, Nat.forall_lt_succ_left, hfz]

/--
lemma `analyticOrderAt_deriv_of_pos` / 引理 `analyticOrderAt_deriv_of_pos`

English:
lemma analyticOrderAt_deriv_of_pos
  statement: {𝕜 : Type*} {E : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
  proof: by
  have ⟨g, hg, hg₀, hfg⟩ := (AnalyticAt.analyticOrderAt_eq_natCast hf).1 horder
  have hz₀ : f z₀ = 0 := by
    simpa [sub_self, zero_pow, zero_smul] using Filter.Eventually.self_of_nhds hfg
  simpa [hz₀, sub_zero, horder] using hf.analyticOrderAt_deriv_add_one

中文:
引理 analyticOrderAt_deriv_of_pos
  结论: {𝕜 : 类型} {E : 类型} [NontriviallyNormedField 𝕜] [特征零 𝕜]
  证明: by
  have ⟨g, hg, hg₀, hfg⟩ := (AnalyticAt.analyticOrderAt_eq_natCast hf).1 horder
  have hz₀ : f z₀ = 0 := by
    simpa [sub_self, zero_pow, zero_smul] using Filter.Eventually.self_of_nhds hfg
  simpa [hz₀, sub_zero, horder] using hf.analyticOrderAt_deriv_add_one

Depends on / 依赖: AnalyticAt, AnalyticAt.analyticOrderAt_eq_natCast, Eventually, Filter, Filter.Eventually.self_of_nhds, analyticOrderAt_deriv_add_one, analyticOrderAt_eq_natCast, hf.analyticOrderAt_deriv_add_one, horder, self_of_nhds, sub_self, sub_zero, zero_pow, zero_smul
-/
lemma analyticOrderAt_deriv_of_pos {𝕜 : Type*} {E : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {f : 𝕜 -> E} {z₀ : 𝕜}
    (hf : AnalyticAt 𝕜 f z₀) {n : Nat} (horder : analyticOrderAt f z₀ = n + 1) :
    analyticOrderAt (deriv f) z₀ = n := by
  have ⟨g, hg, hg₀, hfg⟩ := (AnalyticAt.analyticOrderAt_eq_natCast hf).1 horder
  have hz₀ : f z₀ = 0 := by
    simpa [sub_self, zero_pow, zero_smul] using Filter.Eventually.self_of_nhds hfg
  simpa [hz₀, sub_zero, horder] using hf.analyticOrderAt_deriv_add_one

/--
lemma `analyticOrderAt_iterated_deriv` / 引理 `analyticOrderAt_iterated_deriv`

English:
lemma analyticOrderAt_iterated_deriv
  statement: {𝕜 : Type*} {E : Type*} [NontriviallyNormedField 𝕜]
  proof: by
  induction k generalizing n with
  | zero => exact fun Hn Hpos Hk => Hn.symm
  | succ n' hk =>
    intro Hn Hpos Hk
    rw [Function.iterate_succ']
    have horder : analyticOrderAt (deriv^[n'] f) z₀ = (n - n'.succ) + 1 := by
      refine (hk Hn Hpos (by lia)).trans ?_
      have : (n - n'.succ)

中文:
引理 analyticOrderAt_iterated_deriv
  结论: {𝕜 : 类型} {E : 类型} [NontriviallyNormedField 𝕜]
  证明: by
  induction k generalizing n with
  | zero => exact fun Hn Hpos Hk => Hn.symm
  | succ n' hk =>
    intro Hn Hpos Hk
    rw [Function.iterate_succ']
    have horder : analyticOrderAt (deriv^[n'] f) z₀ = (n - n'.succ) + 1 := by
      refine (hk Hn Hpos (by lia)).trans ?_
      have : (n - n'.succ)

Depends on / 依赖: AnalyticAt, AnalyticAt.iterated_deriv, Function, Function.iterate_succ, Hn.symm, analyticOrderAt, analyticOrderAt_deriv_of_pos, generalizing, horder, iterate_succ, iterated_deriv
-/
lemma analyticOrderAt_iterated_deriv {𝕜 : Type*} {E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {f : 𝕜 -> E} {z₀ : 𝕜}
    (hf : AnalyticAt 𝕜 f z₀) {k n : Nat} [CharZero 𝕜] :
    n = analyticOrderAt f z₀ -> n != 0 -> k <= n -> analyticOrderAt (deriv^[k] f) z₀ = (n - k : Nat) := by
  induction k generalizing n with
  | zero => exact fun Hn Hpos Hk => Hn.symm
  | succ n' hk =>
    intro Hn Hpos Hk
    rw [Function.iterate_succ']
    have horder : analyticOrderAt (deriv^[n'] f) z₀ = (n - n'.succ) + 1 := by
      refine (hk Hn Hpos (by lia)).trans ?_
      have : (n - n'.succ) + 1 = n - n' := by grind
      rw [← this]
      simp
    simpa using (analyticOrderAt_deriv_of_pos (hf := AnalyticAt.iterated_deriv hf n')
      (n := n - n'.succ) horder)

attribute [local simp] Nat.factorial_ne_zero in
/--
lemma `AnalyticAt.exists_eventuallyEq_sum_add_pow_mul` / 引理 `AnalyticAt.exists_eventuallyEq_sum_add_pow_mul`

English:
lemma AnalyticAt.exists_eventuallyEq_sum_add_pow_mul
  statement: [CharZero 𝕜] [CompleteSpace E]
  proof: by
  simp only [← sub_eq_iff_eq_add']
  have : AnalyticAt 𝕜
      (fun z : 𝕜 => ∑ i in .range n, (z ^ i / i.factorial) • iteratedDeriv i f 0) 0 := by
    refine Finset.analyticAt_fun_sum _ fun i hi => ?_
    fun_prop
  convert! (natCast_le_analyticOrderAt (hf.fun_sub this)).mp ?_
  · simp
  · rw [na

中文:
引理 AnalyticAt.存在_eventuallyEq_sum_add_pow_mul
  结论: [特征零 𝕜] [完备空间 E]
  证明: by
  simp only [← sub_eq_iff_eq_add']
  have : AnalyticAt 𝕜
      (fun z : 𝕜 => ∑ i in .range n, (z ^ i / i.factorial) • iteratedDeriv i f 0) 0 := by
    refine Finset.analyticAt_fun_sum _ fun i hi => ?_
    fun_prop
  convert! (natCast_le_analyticOrderAt (hf.fun_sub this)).mp ?_
  · simp
  · rw [na

Depends on / 依赖: AnalyticAt, AnalyticAt.contDiffAt, Finset, Finset.analyticAt_fun_sum, analyticAt_fun_sum, contDiffAt, convert, factorial, fun_prop, fun_sub, hf.fun_sub, i.factorial, iterate, iteratedDeriv, iteratedDeriv_fun_sub, iteratedDeriv_fun_sum, natCast_le_analyticOrderAt, natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero, sub_eq_iff_eq_add, this.contDiffAt
-/
lemma AnalyticAt.exists_eventuallyEq_sum_add_pow_mul [CharZero 𝕜] [CompleteSpace E]
    {f : 𝕜 -> E} (hf : AnalyticAt 𝕜 f 0) (n : Nat) :
    exists F : 𝕜 -> E, AnalyticAt 𝕜 F 0 ∧ forallᶠ z in 𝓝 0,
      f z = (∑ i in .range n, (z ^ i / i.factorial) • iteratedDeriv i f 0) + z ^ n • F z := by
  simp only [← sub_eq_iff_eq_add']
  have : AnalyticAt 𝕜
      (fun z : 𝕜 => ∑ i in .range n, (z ^ i / i.factorial) • iteratedDeriv i f 0) 0 := by
    refine Finset.analyticAt_fun_sum _ fun i hi => ?_
    fun_prop
  convert! (natCast_le_analyticOrderAt (hf.fun_sub this)).mp ?_
  · simp
  · rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf.fun_sub this)]
    intro i hi
    rw [iteratedDeriv_fun_sub (AnalyticAt.contDiffAt <| by fun_prop) this.contDiffAt]
    simp (disch := fun_prop) only [iteratedDeriv_fun_sum, iteratedDeriv_smul_const,
      iteratedDeriv_div_const, iteratedDeriv_fun_pow_zero]
    simp [ite_div, Finset.sum_ite_eq_of_mem _ _ _ (Finset.mem_range.mpr hi)]

attribute [local simp] Nat.factorial_ne_zero in
/--
lemma `AnalyticAt.exists_eq_sum_add_pow_mul` / 引理 `AnalyticAt.exists_eq_sum_add_pow_mul`

English:
lemma AnalyticAt.exists_eq_sum_add_pow_mul
  statement: [CharZero 𝕜] [CompleteSpace E]
  proof: by
  classical
  obtain ⟨F, hFa, hF⟩ := hf.exists_eventuallyEq_sum_add_pow_mul n
  obtain ⟨U, hU0, hU'⟩ := by rwa [eventually_iff_exists_mem] at hF
  refine ⟨fun z => if z in U then F z else (z ^ n)⁻¹ • (f z
      - (∑ i in .range n, (z ^ i / i.factorial) • iteratedDeriv i f 0)), ?_, fun z => ?_⟩
  

中文:
引理 AnalyticAt.存在_eq_sum_add_pow_mul
  结论: [特征零 𝕜] [完备空间 E]
  证明: by
  classical
  obtain ⟨F, hFa, hF⟩ := hf.exists_eventuallyEq_sum_add_pow_mul n
  obtain ⟨U, hU0, hU'⟩ := by rwa [eventually_iff_exists_mem] at hF
  refine ⟨fun z => if z in U then F z else (z ^ n)⁻¹ • (f z
      - (∑ i in .range n, (z ^ i / i.factorial) • iteratedDeriv i f 0)), ?_, fun z => ?_⟩
  

Depends on / 依赖: classical, contextual, contrapose, eventually_iff_exists_mem, exists_eventuallyEq_sum_add_pow_mul, factorial, filter_upwards, hFa.congr, hf.exists_eventuallyEq_sum_add_pow_mul, i.factorial, if_neg, iteratedDeriv, module, pow_eq_zero_iff
-/
lemma AnalyticAt.exists_eq_sum_add_pow_mul [CharZero 𝕜] [CompleteSpace E]
    {f : 𝕜 -> E} (hf : AnalyticAt 𝕜 f 0) (n : Nat) :
    exists F : 𝕜 -> E, AnalyticAt 𝕜 F 0 ∧ forall z,
      f z = (∑ i in .range n, (z ^ i / i.factorial) • iteratedDeriv i f 0) + z ^ n • F z := by
  classical
  obtain ⟨F, hFa, hF⟩ := hf.exists_eventuallyEq_sum_add_pow_mul n
  obtain ⟨U, hU0, hU'⟩ := by rwa [eventually_iff_exists_mem] at hF
  refine ⟨fun z => if z in U then F z else (z ^ n)⁻¹ • (f z
      - (∑ i in .range n, (z ^ i / i.factorial) • iteratedDeriv i f 0)), ?_, fun z => ?_⟩
  · exact hFa.congr (by filter_upwards [hU0] using by simp +contextual)
  · by_cases hz : z in U
    · simpa [hz] using hU' z hz
    · simp only [if_neg hz]
      rw [smul_inv_smul₀]
      · module
      · contrapose hz
        exact (pow_eq_zero_iff'.mp hz).1 ▸ mem_of_mem_nhds hU0

variable [CharZero 𝕜] [CompleteSpace E] {z₀ : 𝕜} {f : 𝕜 -> E}
  (hf : AnalyticAt 𝕜 f z₀) (hzero : f z₀ = 0)

include hf hzero

/--
lemma `analyticOrderAt_deriv_ge_iff` / 引理 `analyticOrderAt_deriv_ge_iff`

English:
lemma analyticOrderAt_deriv_ge_iff
  given: {n : Nat}
  proof: by
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf.deriv]; rw [← Nat.cast_add_one]; rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf]
  simp only [← iteratedDeriv_succ']
refine ⟨fun h k hk => ?_, fun h k hk => h (k + 1) by lia⟩
  cases k with
  | zero => simpa
| succ k => ex

中文:
引理 analyticOrderAt_deriv_ge_iff
  条件: {n : 自然数}
  证明: by
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf.deriv]; rw [← Nat.cast_add_one]; rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf]
  simp only [← iteratedDeriv_succ']
refine ⟨fun h k hk => ?_, fun h k hk => h (k + 1) by lia⟩
  cases k with
  | zero => simpa
| succ k => ex

Depends on / 依赖: Nat.cast_add_one, cast_add_one, hf.deriv, iteratedDeriv_succ, natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
-/
lemma analyticOrderAt_deriv_ge_iff {n : Nat} :
    n <= analyticOrderAt (deriv f) z₀ ↔ n + 1 <= analyticOrderAt f z₀ := by
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf.deriv]; rw [← Nat.cast_add_one]; rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf]
  simp only [← iteratedDeriv_succ']
refine ⟨fun h k hk => ?_, fun h k hk => h (k + 1) by lia⟩
  cases k with
  | zero => simpa
| succ k => exact h k by lia

/--
lemma `analyticOrderAt_deriv_eq_top_iff_of_eq_zero` / 引理 `analyticOrderAt_deriv_eq_top_iff_of_eq_zero`

English:
lemma analyticOrderAt_deriv_eq_top_iff_of_eq_zero
  proof: by
  simp_rw [ENat.eq_top_iff_forall_ge, analyticOrderAt_deriv_ge_iff hf hzero]
  exact ⟨fun h m => le_self_add.trans (h m), fun h m => h (m + 1)⟩

中文:
引理 analyticOrderAt_deriv_eq_top_iff_of_eq_zero
  证明: by
  simp_rw [ENat.eq_top_iff_forall_ge, analyticOrderAt_deriv_ge_iff hf hzero]
  exact ⟨fun h m => le_self_add.trans (h m), fun h m => h (m + 1)⟩

Depends on / 依赖: ENat.eq_top_iff_forall_ge, analyticOrderAt_deriv_ge_iff, eq_top_iff_forall_ge, le_self_add, le_self_add.trans, simp_rw
-/
lemma analyticOrderAt_deriv_eq_top_iff_of_eq_zero :
    analyticOrderAt (deriv f) z₀ = ⊤ ↔ analyticOrderAt f z₀ = ⊤ := by
  simp_rw [ENat.eq_top_iff_forall_ge, analyticOrderAt_deriv_ge_iff hf hzero]
  exact ⟨fun h m => le_self_add.trans (h m), fun h m => h (m + 1)⟩

/--
lemma `analyticOrderAt_deriv_eq_iff` / 引理 `analyticOrderAt_deriv_eq_iff`

English:
lemma analyticOrderAt_deriv_eq_iff
  given: {n : Nat}
  proof: by
  have H {m : Nat} {n : Nat∞} : n = m ↔ m <= n ∧ ¬ m + 1 <= n := by
    cases n with | top => simp | coe _ => norm_cast; lia
  rw [← Nat.cast_add_one n]; rw [H]; rw [H]; rw [analyticOrderAt_deriv_ge_iff hf hzero]; rw [← Nat.cast_add_one n]; rw [analyticOrderAt_deriv_ge_iff hf hzero]

omit hzero i

中文:
引理 analyticOrderAt_deriv_eq_iff
  条件: {n : 自然数}
  证明: by
  have H {m : Nat} {n : Nat∞} : n = m ↔ m <= n ∧ ¬ m + 1 <= n := by
    cases n with | top => simp | coe _ => norm_cast; lia
  rw [← Nat.cast_add_one n]; rw [H]; rw [H]; rw [analyticOrderAt_deriv_ge_iff hf hzero]; rw [← Nat.cast_add_one n]; rw [analyticOrderAt_deriv_ge_iff hf hzero]

omit hzero i

Depends on / 依赖: Nat.cast_add_one, analyticOrderAt_deriv_ge_iff, cast_add_one
-/
lemma analyticOrderAt_deriv_eq_iff {n : Nat} :
    analyticOrderAt f z₀ = n + 1 ↔ analyticOrderAt (deriv f) z₀ = n := by
  have H {m : Nat} {n : Nat∞} : n = m ↔ m <= n ∧ ¬ m + 1 <= n := by
    cases n with | top => simp | coe _ => norm_cast; lia
  rw [← Nat.cast_add_one n]; rw [H]; rw [H]; rw [analyticOrderAt_deriv_ge_iff hf hzero]; rw [← Nat.cast_add_one n]; rw [analyticOrderAt_deriv_ge_iff hf hzero]

omit hzero in
/--
lemma `analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero` / 引理 `analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero`

English:
lemma analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
  given: {n : Nat}
  proof: by
  induction n generalizing f with
  | zero => simp [hf.analyticOrderAt_eq_zero]
  | succ n IH =>
    specialize IH hf.deriv
    simp_rw [← iteratedDeriv_succ'] at IH
    refine ⟨fun ho => ?_, fun ⟨hz, hnz⟩ => ?_⟩
    · have ⟨h_zero, h_nz⟩ := IH.mp (analyticOrderAt_deriv_of_pos hf ho)
      refine

中文:
引理 analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
  条件: {n : 自然数}
  证明: by
  induction n generalizing f with
  | zero => simp [hf.analyticOrderAt_eq_zero]
  | succ n IH =>
    specialize IH hf.deriv
    simp_rw [← iteratedDeriv_succ'] at IH
    refine ⟨fun ho => ?_, fun ⟨hz, hnz⟩ => ?_⟩
    · have ⟨h_zero, h_nz⟩ := IH.mp (analyticOrderAt_deriv_of_pos hf ho)
      refine

Depends on / 依赖: IH.mp, Nat.cast_add_one, Nat.cast_add_one_ne_zero, analyticOrderAt_deriv_eq_iff, analyticOrderAt_deriv_of_pos, analyticOrderAt_eq_zero, analyticOrderAt_ne_zero, cast_add_one, cast_add_one_ne_zero, generalizing, h_nz, h_zero, hf.analyticOrderAt_eq_zero, hf.analyticOrderAt_ne_zero, hf.deriv, iteratedDeriv_succ, iteratedDeriv_zero, simp_rw, specialize
-/
lemma analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero {n : Nat} :
    analyticOrderAt f z₀ = n ↔ (forall k < n, iteratedDeriv k f z₀ = 0) ∧ iteratedDeriv n f z₀ != 0 := by
  induction n generalizing f with
  | zero => simp [hf.analyticOrderAt_eq_zero]
  | succ n IH =>
    specialize IH hf.deriv
    simp_rw [← iteratedDeriv_succ'] at IH
    refine ⟨fun ho => ?_, fun ⟨hz, hnz⟩ => ?_⟩
    · have ⟨h_zero, h_nz⟩ := IH.mp (analyticOrderAt_deriv_of_pos hf ho)
      refine ⟨fun k hk => ?_, h_nz⟩
      match k with
      | 0 => rw [iteratedDeriv_zero, ← hf.analyticOrderAt_ne_zero, ho, Nat.cast_add_one]
             exact Nat.cast_add_one_ne_zero _
      | k + 1 => exact h_zero k (by lia)
· exact (analyticOrderAt_deriv_eq_iff hf <| by simpa using hz 0 (by lia)).mpr
        IH.mpr ⟨fun j _ => hz (j + 1) (by lia), hnz⟩

end NormedSpace

/-!
## Vanishing Order at a Point: Elementary Computations
-/

/-- Simplifier lemma for the order of a centered monomial -/
@[simp]
/--
lemma `analyticOrderAt_centeredMonomial` / 引理 `analyticOrderAt_centeredMonomial`

English:
lemma analyticOrderAt_centeredMonomial
  given: {z₀ : 𝕜} {n : Nat}
  proof: by
  rw [AnalyticAt.analyticOrderAt_eq_natCast (by fun_prop)]
  exact ⟨1, by simp [Pi.one_def, analyticAt_const]⟩

中文:
引理 analyticOrderAt_centeredMonomial
  条件: {z₀ : 𝕜} {n : 自然数}
  证明: by
  rw [AnalyticAt.analyticOrderAt_eq_natCast (by fun_prop)]
  exact ⟨1, by simp [Pi.one_def, analyticAt_const]⟩

Depends on / 依赖: AnalyticAt, AnalyticAt.analyticOrderAt_eq_natCast, Pi.one_def, analyticAt_const, analyticOrderAt_eq_natCast, fun_prop, one_def
-/
lemma analyticOrderAt_centeredMonomial {z₀ : 𝕜} {n : Nat} :
    analyticOrderAt ((· - z₀) ^ n) z₀ = n := by
  rw [AnalyticAt.analyticOrderAt_eq_natCast (by fun_prop)]
  exact ⟨1, by simp [Pi.one_def, analyticAt_const]⟩

/--
theorem `analyticOrderAt_id_sub_const_self` / 定理 `analyticOrderAt_id_sub_const_self`

English:
theorem analyticOrderAt_id_sub_const_self
  given: {c : 𝕜}
  proof: by
  have := analyticOrderAt_centeredMonomial (n := 1) (z₀ := c)
  simp_all [pow_one]

中文:
定理 analyticOrderAt_id_sub_const_self
  条件: {c : 𝕜}
  证明: by
  have := analyticOrderAt_centeredMonomial (n := 1) (z₀ := c)
  simp_all [pow_one]
-/
@[simp] theorem analyticOrderAt_id_sub_const_self {c : 𝕜} :
    analyticOrderAt (· - c) c = 1 := by
  have := analyticOrderAt_centeredMonomial (n := 1) (z₀ := c)
  simp_all [pow_one]

/--
theorem `analyticOrderAt_id_sub_const_of_ne` / 定理 `analyticOrderAt_id_sub_const_of_ne`

English:
theorem analyticOrderAt_id_sub_const_of_ne
  given: {c x : 𝕜} (h : x != c)
  proof: by
  apply analyticOrderAt_eq_zero.2
  grind

中文:
定理 analyticOrderAt_id_sub_const_of_ne
  条件: {c x : 𝕜} (h : x != c)
  证明: by
  apply analyticOrderAt_eq_zero.2
  grind
-/
@[simp] theorem analyticOrderAt_id_sub_const_of_ne {c x : 𝕜} (h : x != c) :
    analyticOrderAt (· - c) x = 0 := by
  apply analyticOrderAt_eq_zero.2
  grind

section NontriviallyNormedField
variable {f g : 𝕜 -> 𝕜} {z₀ : 𝕜}

/--
lemma `analyticOrderAt_mul_eq_top_of_left` / 引理 `analyticOrderAt_mul_eq_top_of_left`

English:
lemma analyticOrderAt_mul_eq_top_of_left
  given: (hf : analyticOrderAt f z₀ = ⊤)
  proof: analyticOrderAt_smul_eq_top_of_left hf

中文:
引理 analyticOrderAt_mul_eq_top_of_left
  条件: (hf : analyticOrderAt f z₀ = ⊤)
  证明: analyticOrderAt_smul_eq_top_of_left hf

Depends on / 依赖: analyticOrderAt_smul_eq_top_of_left
-/
lemma analyticOrderAt_mul_eq_top_of_left (hf : analyticOrderAt f z₀ = ⊤) :
    analyticOrderAt (f * g) z₀ = ⊤ := analyticOrderAt_smul_eq_top_of_left hf

/--
lemma `analyticOrderAt_mul_eq_top_of_right` / 引理 `analyticOrderAt_mul_eq_top_of_right`

English:
lemma analyticOrderAt_mul_eq_top_of_right
  given: (hg : analyticOrderAt g z₀ = ⊤)
  proof: analyticOrderAt_smul_eq_top_of_right hg

中文:
引理 analyticOrderAt_mul_eq_top_of_right
  条件: (hg : analyticOrderAt g z₀ = ⊤)
  证明: analyticOrderAt_smul_eq_top_of_right hg

Depends on / 依赖: analyticOrderAt_smul_eq_top_of_right
-/
lemma analyticOrderAt_mul_eq_top_of_right (hg : analyticOrderAt g z₀ = ⊤) :
    analyticOrderAt (f * g) z₀ = ⊤ := analyticOrderAt_smul_eq_top_of_right hg

/--
theorem `analyticOrderAt_mul` / 定理 `analyticOrderAt_mul`

English:
theorem analyticOrderAt_mul
  given: (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀)
  proof: analyticOrderAt_smul hf hg

中文:
定理 analyticOrderAt_mul
  条件: (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀)
  证明: analyticOrderAt_smul hf hg

Depends on / 依赖: analyticOrderAt_smul
-/
theorem analyticOrderAt_mul (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    analyticOrderAt (f * g) z₀ = analyticOrderAt f z₀ + analyticOrderAt g z₀ :=
  analyticOrderAt_smul hf hg

/--
theorem `analyticOrderNatAt_mul` / 定理 `analyticOrderNatAt_mul`

English:
theorem analyticOrderNatAt_mul
  statement: (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀)
  proof: by
  simp [analyticOrderNatAt, analyticOrderAt_mul, ENat.toNat_add, *]

中文:
定理 analyticOrder自然数At_mul
  结论: (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀)
  证明: by
  simp [analyticOrderNatAt, analyticOrderAt_mul, ENat.toNat_add, *]

Depends on / 依赖: ENat.toNat_add, analyticOrderAt_mul, analyticOrderNatAt, toNat_add
-/
theorem analyticOrderNatAt_mul (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀)
    (hf' : analyticOrderAt f z₀ != ⊤) (hg' : analyticOrderAt g z₀ != ⊤) :
    analyticOrderNatAt (f * g) z₀ = analyticOrderNatAt f z₀ + analyticOrderNatAt g z₀ := by
  simp [analyticOrderNatAt, analyticOrderAt_mul, ENat.toNat_add, *]

/--
theorem `analyticOrderAt_pow` / 定理 `analyticOrderAt_pow`

English:
theorem analyticOrderAt_pow
  given: (hf : AnalyticAt 𝕜 f z₀)

中文:
定理 analyticOrderAt_pow
  条件: (hf : AnalyticAt 𝕜 f z₀)
-/
theorem analyticOrderAt_pow (hf : AnalyticAt 𝕜 f z₀) :
    forall n, analyticOrderAt (f ^ n) z₀ = n • analyticOrderAt f z₀
  | 0 => by simp [analyticOrderAt_eq_zero]
  | n + 1 => by simp [add_mul, pow_add, analyticOrderAt_mul (hf.pow n), analyticOrderAt_pow, hf]

/--
theorem `analyticOrderNatAt_pow` / 定理 `analyticOrderNatAt_pow`

English:
theorem analyticOrderNatAt_pow
  given: (hf : AnalyticAt 𝕜 f z₀) (n : Nat)
  proof: by
  simp [analyticOrderNatAt, analyticOrderAt_pow, hf]

中文:
定理 analyticOrder自然数At_pow
  条件: (hf : AnalyticAt 𝕜 f z₀) (n : 自然数)
  证明: by
  simp [analyticOrderNatAt, analyticOrderAt_pow, hf]

Depends on / 依赖: analyticOrderAt_pow, analyticOrderNatAt
-/
theorem analyticOrderNatAt_pow (hf : AnalyticAt 𝕜 f z₀) (n : Nat) :
    analyticOrderNatAt (f ^ n) z₀ = n • analyticOrderNatAt f z₀ := by
  simp [analyticOrderNatAt, analyticOrderAt_pow, hf]

end NontriviallyNormedField

section comp

/-!
## Vanishing Order at a Point: Composition
-/
variable {f : 𝕜 -> E} {g : 𝕜 -> 𝕜} {z₀ : 𝕜}

/--
lemma `AnalyticAt.analyticOrderAt_comp` / 引理 `AnalyticAt.analyticOrderAt_comp`

English:
lemma AnalyticAt.analyticOrderAt_comp
  given: (hf : AnalyticAt 𝕜 f (g z₀)) (hg : AnalyticAt 𝕜 g z₀)
  proof: by
  by_cases hg_nc : EventuallyConst g (𝓝 z₀)
  · -- If `g` is eventually constant, both sides are either `⊤` or `0`.
    have := hg_nc.comp f
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top] at hg_nc this
    rw [hg_nc]
    by_cases hf' : f (g z₀) = 0
    · simpa [hf', show analyticOrderAt 

中文:
引理 AnalyticAt.analyticOrderAt_comp
  条件: (hf : AnalyticAt 𝕜 f (g z₀)) (hg : AnalyticAt 𝕜 g z₀)
  证明: by
  by_cases hg_nc : EventuallyConst g (𝓝 z₀)
  · -- If `g` is eventually constant, both sides are either `⊤` or `0`.
    have := hg_nc.comp f
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top] at hg_nc this
    rw [hg_nc]
    by_cases hf' : f (g z₀) = 0
    · simpa [hf', show analyticOrderAt 

Depends on / 依赖: AnalyticAt, AnalyticAt.analyticOrderAt_eq_zero, EventuallyConst, analyticOrderAt, analyticOrderAt_eq_zero, analyticOrderAt_ne_zero, constant, either, eventually, eventuallyConst_iff_analyticOrderAt_sub_eq_top, hf.comp, hg_nc, hg_nc.comp, zero_mul
-/
lemma AnalyticAt.analyticOrderAt_comp (hf : AnalyticAt 𝕜 f (g z₀)) (hg : AnalyticAt 𝕜 g z₀) :
    analyticOrderAt (f ∘ g) z₀ = analyticOrderAt f (g z₀) * analyticOrderAt (g · - g z₀) z₀ := by
  by_cases hg_nc : EventuallyConst g (𝓝 z₀)
  · -- If `g` is eventually constant, both sides are either `⊤` or `0`.
    have := hg_nc.comp f
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top] at hg_nc this
    rw [hg_nc]
    by_cases hf' : f (g z₀) = 0
    · simpa [hf', show analyticOrderAt f (g z₀) != 0 by grind [analyticOrderAt_ne_zero]]
    · rw [show analyticOrderAt f (g z₀) = 0 from ?_, zero_mul] <;>
      grind [hf.comp hg, AnalyticAt.analyticOrderAt_eq_zero]
  by_cases hf' : analyticOrderAt f (g z₀) = ⊤
  · -- If `f` is eventually constant but `g` is not, we have `⊤ = ⊤ * (non-zero thing)`
    rw [hf']; rw [analyticOrderAt_eq_top.mpr
      (EventuallyEq.comp_tendsto (analyticOrderAt_eq_top.mp hf') hg.continuousAt)]; rw [ENat.top_mul]
    rw [AnalyticAt.analyticOrderAt_ne_zero (by fun_prop)]; rw [sub_eq_zero]
  · -- The interesting case: both orders are finite. First unpack the data:
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top] at hg_nc
    obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp hf'
    obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp hg_nc
    rw [← hr]; rw [← hs]; rw [← ENat.natCast_mul]; rw [(hf.comp hg).analyticOrderAt_eq_natCast]
    rw [Eq.comm]; rw [hf.analyticOrderAt_eq_natCast] at hr
    rcases hr with ⟨F, hFa, hFne, hfF⟩
    rw [Eq.comm]; rw [AnalyticAt.analyticOrderAt_eq_natCast (by fun_prop)] at hs
    rcases hs with ⟨G, hGa, hGne, hgG⟩
    -- Now write `f ∘ g` locally as the product of `(z - z₀) ^ (r * s)` and the
    -- non-vanishing analytic function `fun z ↦ (G z) ^ r • F (g z)`.
    refine ⟨fun z => (G z) ^ r • F (g z), by fun_prop, by aesop, ?_⟩
    filter_upwards [EventuallyEq.comp_tendsto hfF hg.continuousAt, hgG] with z hfz hgz
    simp only [hfz, Function.comp_def, hgz, smul_eq_mul, mul_pow, mul_smul, mul_comm r s, pow_mul]

/--
lemma `analyticOrderAt_comp_of_deriv_ne_zero` / 引理 `analyticOrderAt_comp_of_deriv_ne_zero`

English:
lemma analyticOrderAt_comp_of_deriv_ne_zero
  statement: (hg : AnalyticAt 𝕜 g z₀) (hg' : deriv g z₀ != 0)
  proof: by
  by_cases hf : AnalyticAt 𝕜 f (g z₀)
  · simp [hf.analyticOrderAt_comp hg, hg.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hg']
  · rw [analyticOrderAt_of_not_analyticAt hf, analyticOrderAt_of_not_analyticAt]
    rwa [analyticAt_comp_iff_of_deriv_ne_zero hg hg']

中文:
引理 analyticOrderAt_comp_of_deriv_ne_zero
  结论: (hg : AnalyticAt 𝕜 g z₀) (hg' : deriv g z₀ != 0)
  证明: by
  by_cases hf : AnalyticAt 𝕜 f (g z₀)
  · simp [hf.analyticOrderAt_comp hg, hg.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hg']
  · rw [analyticOrderAt_of_not_analyticAt hf, analyticOrderAt_of_not_analyticAt]
    rwa [analyticAt_comp_iff_of_deriv_ne_zero hg hg']

Depends on / 依赖: AnalyticAt, analyticAt_comp_iff_of_deriv_ne_zero, analyticOrderAt_comp, analyticOrderAt_of_not_analyticAt, analyticOrderAt_sub_eq_one_of_deriv_ne_zero, hf.analyticOrderAt_comp, hg.analyticOrderAt_sub_eq_one_of_deriv_ne_zero
-/
lemma analyticOrderAt_comp_of_deriv_ne_zero (hg : AnalyticAt 𝕜 g z₀) (hg' : deriv g z₀ != 0)
    [CompleteSpace 𝕜] [CharZero 𝕜] :
    analyticOrderAt (f ∘ g) z₀ = analyticOrderAt f (g z₀) := by
  by_cases hf : AnalyticAt 𝕜 f (g z₀)
  · simp [hf.analyticOrderAt_comp hg, hg.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hg']
  · rw [analyticOrderAt_of_not_analyticAt hf, analyticOrderAt_of_not_analyticAt]
    rwa [analyticAt_comp_iff_of_deriv_ne_zero hg hg']

end comp

/-!
## Level Sets of the Order Function
-/

namespace AnalyticOnNhd

variable {U : Set 𝕜} {f : 𝕜 -> E}

/--
theorem `isClopen_setOfPred_analyticOrderAt_eq_top` / 定理 `isClopen_setOfPred_analyticOrderAt_eq_top`

English:
theorem isClopen_setOfPred_analyticOrderAt_eq_top
  given: (hf : AnalyticOnNhd 𝕜 f U)
  proof: by
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    rcases (hf z.1 z.2).eventually_eq_zero_or_eventually_ne_zero with h | h
    · -- Case: f is locally zero in a punctured neighborhood of z
      rw [← analyticOrderAt_eq_top] at h
      tauto
    · -- Case: f 

中文:
定理 isClopen_setOfPred_analyticOrderAt_eq_top
  条件: (hf : AnalyticOnNhd 𝕜 f U)
  证明: by
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    rcases (hf z.1 z.2).eventually_eq_zero_or_eventually_ne_zero with h | h
    · -- Case: f is locally zero in a punctured neighborhood of z
      rw [← analyticOrderAt_eq_top] at h
      tauto
    · -- Case: f 

Depends on / 依赖: Subtype, Subtype.val, analyticOrderAt_eq_top, eventually_eq_zero_or_eventually_ne_zero, eventually_nhdsWithin_iff, eventually_nhds_iff, isOpen_compl_iff, isOpen_iff_forall_mem_open, locally, neighborhood, nonzero, punctured
-/
theorem isClopen_setOfPred_analyticOrderAt_eq_top (hf : AnalyticOnNhd 𝕜 f U) :
    IsClopen {u : U | analyticOrderAt f u = ⊤} := by
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    rcases (hf z.1 z.2).eventually_eq_zero_or_eventually_ne_zero with h | h
    · -- Case: f is locally zero in a punctured neighborhood of z
      rw [← analyticOrderAt_eq_top] at h
      tauto
    · -- Case: f is locally nonzero in a punctured neighborhood of z
      obtain ⟨t', h₁t', h₂t', h₃t'⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h)
      use Subtype.val ⁻¹' t'
      constructor
      · intro w hw
        push _ in _
        by_cases h₁w : w = z
        · rwa [h₁w]
        · rw [(hf _ w.2).analyticOrderAt_eq_zero.2 ((h₁t' w hw) (Subtype.coe_ne_coe.mpr h₁w))]
          exact ENat.zero_ne_top
      · exact ⟨isOpen_induced h₂t', h₃t'⟩
  · apply isOpen_iff_forall_mem_open.mpr
    intro z hz
    conv =>
      arg 1; intro; left; right; arg 1; intro
      rw [analyticOrderAt_eq_top]; rw [eventually_nhds_iff]
    simp only [mem_ofPred_eq] at hz
    rw [analyticOrderAt_eq_top]; rw [eventually_nhds_iff] at hz
    obtain ⟨t', h₁t', h₂t', h₃t'⟩ := hz
    use Subtype.val ⁻¹' t'
    simp only [isOpen_induced h₂t', mem_preimage, h₃t', and_self, and_true]
    grind

@[deprecated (since := "2026-07-09")]
alias isClopen_setOf_analyticOrderAt_eq_top := isClopen_setOfPred_analyticOrderAt_eq_top

/--
theorem `exists_analyticOrderAt_ne_top_iff_forall` / 定理 `exists_analyticOrderAt_ne_top_iff_forall`

English:
theorem exists_analyticOrderAt_ne_top_iff_forall
  given: (hf : AnalyticOnNhd 𝕜 f U) (hU : IsConnected U)
  proof: by
  have : ConnectedSpace U := Subtype.connectedSpace hU
  obtain ⟨v⟩ : Nonempty U := inferInstance
  suffices (forall (u : U), analyticOrderAt f u != ⊤) ∨ forall (u : U), analyticOrderAt f u = ⊤ by tauto
  simpa [Set.eq_empty_iff_forall_notMem, Set.eq_univ_iff_forall] using
      isClopen_iff.1 hf

中文:
定理 存在_analyticOrderAt_ne_top_iff_对任意
  条件: (hf : AnalyticOnNhd 𝕜 f U) (hU : 是连通 U)
  证明: by
  have : ConnectedSpace U := Subtype.connectedSpace hU
  obtain ⟨v⟩ : Nonempty U := inferInstance
  suffices (forall (u : U), analyticOrderAt f u != ⊤) ∨ forall (u : U), analyticOrderAt f u = ⊤ by tauto
  simpa [Set.eq_empty_iff_forall_notMem, Set.eq_univ_iff_forall] using
      isClopen_iff.1 hf

Depends on / 依赖: ConnectedSpace, Nonempty, Set.eq_empty_iff_forall_notMem, Set.eq_univ_iff_forall, Subtype, Subtype.connectedSpace, analyticOrderAt, connectedSpace, eq_empty_iff_forall_notMem, eq_univ_iff_forall, hf.isClopen_setOfPred_analyticOrderAt_eq_top, isClopen_iff, isClopen_setOfPred_analyticOrderAt_eq_top
-/
theorem exists_analyticOrderAt_ne_top_iff_forall (hf : AnalyticOnNhd 𝕜 f U) (hU : IsConnected U) :
    (exists u : U, analyticOrderAt f u != ⊤) ↔ (forall u : U, analyticOrderAt f u != ⊤) := by
  have : ConnectedSpace U := Subtype.connectedSpace hU
  obtain ⟨v⟩ : Nonempty U := inferInstance
  suffices (forall (u : U), analyticOrderAt f u != ⊤) ∨ forall (u : U), analyticOrderAt f u = ⊤ by tauto
  simpa [Set.eq_empty_iff_forall_notMem, Set.eq_univ_iff_forall] using
      isClopen_iff.1 hf.isClopen_setOfPred_analyticOrderAt_eq_top

/--
theorem `analyticOrderAt_ne_top_of_isPreconnected` / 定理 `analyticOrderAt_ne_top_of_isPreconnected`

English:
theorem analyticOrderAt_ne_top_of_isPreconnected
  statement: {x y : 𝕜} (hf : AnalyticOnNhd 𝕜 f U)
  proof: (hf.exists_analyticOrderAt_ne_top_iff_forall ⟨nonempty_of_mem h₁x, hU⟩).1 (by use ⟨x, h₁x⟩)
    ⟨y, hy⟩

中文:
定理 analyticOrderAt_ne_top_of_isPreconnected
  结论: {x y : 𝕜} (hf : AnalyticOnNhd 𝕜 f U)
  证明: (hf.exists_analyticOrderAt_ne_top_iff_forall ⟨nonempty_of_mem h₁x, hU⟩).1 (by use ⟨x, h₁x⟩)
    ⟨y, hy⟩

Depends on / 依赖: exists_analyticOrderAt_ne_top_iff_forall, hf.exists_analyticOrderAt_ne_top_iff_forall, nonempty_of_mem
-/
theorem analyticOrderAt_ne_top_of_isPreconnected {x y : 𝕜} (hf : AnalyticOnNhd 𝕜 f U)
    (hU : IsPreconnected U) (h₁x : x in U) (hy : y in U) (h₂x : analyticOrderAt f x != ⊤) :
    analyticOrderAt f y != ⊤ :=
  (hf.exists_analyticOrderAt_ne_top_iff_forall ⟨nonempty_of_mem h₁x, hU⟩).1 (by use ⟨x, h₁x⟩)
    ⟨y, hy⟩

/--
theorem `codiscrete_setOfPred_analyticOrderAt_eq_zero_or_top` / 定理 `codiscrete_setOfPred_analyticOrderAt_eq_zero_or_top`

English:
theorem codiscrete_setOfPred_analyticOrderAt_eq_zero_or_top
  given: (hf : AnalyticOnNhd 𝕜 f U)
  proof: by
  simp_rw [mem_codiscrete_subtype_iff_mem_codiscreteWithin, mem_codiscreteWithin,
    disjoint_principal_right]
  intro x hx
  rcases (hf x hx).eventually_eq_zero_or_eventually_ne_zero with h₁f | h₁f
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds h₁f.eventually_nhds] with a ha
    s

中文:
定理 codiscrete_setOfPred_analyticOrderAt_eq_zero_or_top
  条件: (hf : AnalyticOnNhd 𝕜 f U)
  证明: by
  simp_rw [mem_codiscrete_subtype_iff_mem_codiscreteWithin, mem_codiscreteWithin,
    disjoint_principal_right]
  intro x hx
  rcases (hf x hx).eventually_eq_zero_or_eventually_ne_zero with h₁f | h₁f
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds h₁f.eventually_nhds] with a ha
    s

Depends on / 依赖: analyticOrderAt_eq_top, analyticOrderAt_eq_zero, contextual, disjoint_principal_right, eventually_eq_zero_or_eventually_ne_zero, eventually_nhds, eventually_nhdsWithin_of_eventually_nhds, f.eventually_nhds, filter_upwards, mem_codiscreteWithin, mem_codiscrete_subtype_iff_mem_codiscreteWithin, simp_rw
-/
theorem codiscrete_setOfPred_analyticOrderAt_eq_zero_or_top (hf : AnalyticOnNhd 𝕜 f U) :
    {u : U | analyticOrderAt f u = 0 ∨ analyticOrderAt f u = ⊤} in Filter.codiscrete U := by
  simp_rw [mem_codiscrete_subtype_iff_mem_codiscreteWithin, mem_codiscreteWithin,
    disjoint_principal_right]
  intro x hx
  rcases (hf x hx).eventually_eq_zero_or_eventually_ne_zero with h₁f | h₁f
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds h₁f.eventually_nhds] with a ha
    simp [analyticOrderAt_eq_top, ha]
  · filter_upwards [h₁f] with a ha
    simp +contextual [(hf a _).analyticOrderAt_eq_zero, ha]

@[deprecated (since := "2026-07-09")]
alias codiscrete_setOf_analyticOrderAt_eq_zero_or_top :=
  codiscrete_setOfPred_analyticOrderAt_eq_zero_or_top

/--
theorem `codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top` / 定理 `codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top`

English:
theorem codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top
  given: (hf : AnalyticOnNhd 𝕜 f U)
  proof: by
  simp_rw [mem_codiscreteWithin, disjoint_principal_right]
  intro x hx
  rcases (hf x hx).eventually_eq_zero_or_eventually_ne_zero with h₁f | h₁f
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds h₁f.eventually_nhds] with a ha
    simp [analyticOrderAt_eq_top, ha]
  · filter_upwards [

中文:
定理 codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top
  条件: (hf : AnalyticOnNhd 𝕜 f U)
  证明: by
  simp_rw [mem_codiscreteWithin, disjoint_principal_right]
  intro x hx
  rcases (hf x hx).eventually_eq_zero_or_eventually_ne_zero with h₁f | h₁f
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds h₁f.eventually_nhds] with a ha
    simp [analyticOrderAt_eq_top, ha]
  · filter_upwards [

Depends on / 依赖: analyticOrderAt_eq_top, analyticOrderAt_eq_zero, contextual, disjoint_principal_right, eventually_eq_zero_or_eventually_ne_zero, eventually_nhds, eventually_nhdsWithin_of_eventually_nhds, f.eventually_nhds, filter_upwards, mem_codiscreteWithin, simp_rw
-/
theorem codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top (hf : AnalyticOnNhd 𝕜 f U) :
    {u : 𝕜 | analyticOrderAt f u = 0 ∨ analyticOrderAt f u = ⊤} in codiscreteWithin U := by
  simp_rw [mem_codiscreteWithin, disjoint_principal_right]
  intro x hx
  rcases (hf x hx).eventually_eq_zero_or_eventually_ne_zero with h₁f | h₁f
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds h₁f.eventually_nhds] with a ha
    simp [analyticOrderAt_eq_top, ha]
  · filter_upwards [h₁f] with a ha
    simp +contextual [(hf a _).analyticOrderAt_eq_zero, ha]

@[deprecated (since := "2026-07-09")]
alias codiscreteWithin_setOf_analyticOrderAt_eq_zero_or_top :=
  codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top

/--
theorem `preimage_zero_mem_codiscreteWithin` / 定理 `preimage_zero_mem_codiscreteWithin`

English:
theorem preimage_zero_mem_codiscreteWithin
  statement: {x : 𝕜} (h₁f : AnalyticOnNhd 𝕜 f U) (h₂f : f x != 0)
  proof: by
  rcases h₁f.eqOn_zero_or_eventually_ne_zero_of_preconnected hU.isPreconnected with hzero | hne
  · exact (h₂f (hzero hx)).elim
  · exact hne

中文:
定理 preimage_zero_mem_codiscreteWithin
  结论: {x : 𝕜} (h₁f : AnalyticOnNhd 𝕜 f U) (h₂f : f x != 0)
  证明: by
  rcases h₁f.eqOn_zero_or_eventually_ne_zero_of_preconnected hU.isPreconnected with hzero | hne
  · exact (h₂f (hzero hx)).elim
  · exact hne

Depends on / 依赖: eqOn_zero_or_eventually_ne_zero_of_preconnected, f.eqOn_zero_or_eventually_ne_zero_of_preconnected, hU.isPreconnected, isPreconnected
-/
theorem preimage_zero_mem_codiscreteWithin {x : 𝕜} (h₁f : AnalyticOnNhd 𝕜 f U) (h₂f : f x != 0)
    (hx : x in U) (hU : IsConnected U) :
    f ⁻¹' {0}ᶜ in codiscreteWithin U := by
  rcases h₁f.eqOn_zero_or_eventually_ne_zero_of_preconnected hU.isPreconnected with hzero | hne
  · exact (h₂f (hzero hx)).elim
  · exact hne

/--
theorem `preimage_zero_mem_codiscrete` / 定理 `preimage_zero_mem_codiscrete`

English:
theorem preimage_zero_mem_codiscrete
  statement: [ConnectedSpace 𝕜] {x : 𝕜} (hf : AnalyticOnNhd 𝕜 f Set.univ)
  proof: hf.preimage_zero_mem_codiscreteWithin hx trivial isConnected_univ

中文:
定理 preimage_zero_mem_codiscrete
  结论: [连通空间 𝕜] {x : 𝕜} (hf : AnalyticOnNhd 𝕜 f 集合.univ)
  证明: hf.preimage_zero_mem_codiscreteWithin hx trivial isConnected_univ

Depends on / 依赖: hf.preimage_zero_mem_codiscreteWithin, isConnected_univ, preimage_zero_mem_codiscreteWithin
-/
theorem preimage_zero_mem_codiscrete [ConnectedSpace 𝕜] {x : 𝕜} (hf : AnalyticOnNhd 𝕜 f Set.univ)
    (hx : f x != 0) :
    f ⁻¹' {0}ᶜ in codiscrete 𝕜 :=
  hf.preimage_zero_mem_codiscreteWithin hx trivial isConnected_univ

/--
lemma `analyticOrderAt_eq_top_iff_eq_zero` / 引理 `analyticOrderAt_eq_top_iff_eq_zero`

English:
lemma analyticOrderAt_eq_top_iff_eq_zero
  statement: [PreconnectedSpace 𝕜] {f : 𝕜 -> E} (z : 𝕜)
  proof: by
.mp ?_, by simp +contextual⟩ refine analyticOrderAt_eq_top.trans ⟨fun h => eqOn_univ ..
  apply eqOn_zero_of_preconnected_of_frequently_eq_zero (fun z _ => hf z) isPreconnected_univ trivial
.mpr h .frequently_eq_iff_eventually_eq analyticAt_const exact hf z

中文:
引理 analyticOrderAt_eq_top_iff_eq_zero
  结论: [预连通空间 𝕜] {f : 𝕜 -> E} (z : 𝕜)
  证明: by
.mp ?_, by simp +contextual⟩ refine analyticOrderAt_eq_top.trans ⟨fun h => eqOn_univ ..
  apply eqOn_zero_of_preconnected_of_frequently_eq_zero (fun z _ => hf z) isPreconnected_univ trivial
.mpr h .frequently_eq_iff_eventually_eq analyticAt_const exact hf z

Depends on / 依赖: analyticAt_const, analyticOrderAt_eq_top, analyticOrderAt_eq_top.trans, contextual, eqOn_univ, eqOn_zero_of_preconnected_of_frequently_eq_zero, frequently_eq_iff_eventually_eq, isPreconnected_univ
-/
lemma analyticOrderAt_eq_top_iff_eq_zero [PreconnectedSpace 𝕜] {f : 𝕜 -> E} (z : 𝕜)
    (hf : forall z₀, AnalyticAt 𝕜 f z₀) : analyticOrderAt f z = ⊤ ↔ f = 0 := by
.mp ?_, by simp +contextual⟩ refine analyticOrderAt_eq_top.trans ⟨fun h => eqOn_univ ..
  apply eqOn_zero_of_preconnected_of_frequently_eq_zero (fun z _ => hf z) isPreconnected_univ trivial
.mpr h .frequently_eq_iff_eventually_eq analyticAt_const exact hf z

/--
lemma `_root_.IsOpen.forall_analyticOrderAt_eq_top_iff_eqOn_zero` / 引理 `_root_.IsOpen.forall_analyticOrderAt_eq_top_iff_eqOn_zero`

English:
lemma _root_.IsOpen.forall_analyticOrderAt_eq_top_iff_eqOn_zero
  statement: {s : Set 𝕜} (hs : IsOpen s)
  proof: by
  refine ⟨(EventuallyEq.eq_of_nhds <| analyticOrderAt_eq_top.mp <| · · ·), fun hzero z hz => ?_⟩
  apply analyticOrderAt_eq_top.mpr
  filter_upwards [hs.mem_nhds hz]
  exact fun _ => hzero.eq_of_mem

中文:
引理 _root_.是开集.对任意_analyticOrderAt_eq_top_iff_eqOn_zero
  结论: {s : 集合 𝕜} (hs : 是开集 s)
  证明: by
  refine ⟨(EventuallyEq.eq_of_nhds <| analyticOrderAt_eq_top.mp <| · · ·), fun hzero z hz => ?_⟩
  apply analyticOrderAt_eq_top.mpr
  filter_upwards [hs.mem_nhds hz]
  exact fun _ => hzero.eq_of_mem

Depends on / 依赖: EventuallyEq, EventuallyEq.eq_of_nhds, analyticOrderAt_eq_top, analyticOrderAt_eq_top.mp, analyticOrderAt_eq_top.mpr, eq_of_mem, eq_of_nhds, filter_upwards, hs.mem_nhds, hzero.eq_of_mem, mem_nhds
-/
lemma _root_.IsOpen.forall_analyticOrderAt_eq_top_iff_eqOn_zero {s : Set 𝕜} (hs : IsOpen s)
    (f : 𝕜 -> E) : (forall z in s, analyticOrderAt f z = ⊤) ↔ EqOn f 0 s := by
  refine ⟨(EventuallyEq.eq_of_nhds <| analyticOrderAt_eq_top.mp <| · · ·), fun hzero z hz => ?_⟩
  apply analyticOrderAt_eq_top.mpr
  filter_upwards [hs.mem_nhds hz]
  exact fun _ => hzero.eq_of_mem

end AnalyticOnNhd
