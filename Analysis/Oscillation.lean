/-
Copyright (c) 2024 James Sundstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Sundstrom
-/
module

public import Mathlib.Data.ENNReal.Real
public import Mathlib.Order.WellFoundedSet
public import Mathlib.Topology.EMetricSpace.Diam

/-!
# Oscillation

In this file we define the oscillation of a function `f: E → F` at a point `x` of `E`. (`E` is
required to be a TopologicalSpace and `F` a PseudoEMetricSpace.) The oscillation of `f` at `x` is
defined to be the infimum of `diam f '' N` for all neighborhoods `N` of `x`. We also define
`oscillationWithin f D x`, which is the oscillation at `x` of `f` restricted to `D`.

We also prove some simple facts about oscillation, most notably that the oscillation of `f`
at `x` is 0 if and only if `f` is continuous at `x`, with versions for both `oscillation` and
`oscillationWithin`.

## Tags

oscillation, oscillationWithin
-/

@[expose] public section

open Topology Metric Set ENNReal

universe u v

variable {E : Type u} {F : Type v} [PseudoEMetricSpace F]

/--
Definition of `oscillation` / `oscillation` 的定义

English:
definition oscillation
  signature: [TopologicalSpace E] (f : E -> F) (x : E)
  body: ⨅ S in (𝓝 x).map f, ediam S

中文:
定义 oscillation
  签名: [TopologicalSpace E] (f : E -> F) (x : E)
  定义体: ⨅ S in (𝓝 x).map f, ediam S
-/
noncomputable def oscillation [TopologicalSpace E] (f : E -> F) (x : E) : ENNReal :=
  ⨅ S in (𝓝 x).map f, ediam S

/--
Definition of `oscillationWithin` / `oscillationWithin` 的定义

English:
definition oscillationWithin
  signature: [TopologicalSpace E] (f : E -> F) (D : Set E) (x : E)
  body: ⨅ S in (𝓝[D] x).map f, ediam S

中文:
定义 oscillationWithin
  签名: [TopologicalSpace E] (f : E -> F) (D : Set E) (x : E)
  定义体: ⨅ S in (𝓝[D] x).map f, ediam S
-/
noncomputable def oscillationWithin [TopologicalSpace E] (f : E -> F) (D : Set E) (x : E) :
    ENNReal :=
  ⨅ S in (𝓝[D] x).map f, ediam S

/--
theorem `oscillationWithin_nhds_eq_oscillation` / 定理 `oscillationWithin_nhds_eq_oscillation`

English:
theorem oscillationWithin_nhds_eq_oscillation
  statement: [TopologicalSpace E] (f : E -> F) (D : Set E) (x : E)
  proof: by
  rw [oscillation]; rw [oscillationWithin]; rw [nhdsWithin_eq_nhds.2 hD]

中文:
定理 oscillationWithin_nhds_eq_oscillation
  结论: [TopologicalSpace E] (f : E -> F) (D : Set E) (x : E)
  证明: by
  rw [oscillation]; rw [oscillationWithin]; rw [nhdsWithin_eq_nhds.2 hD]

Depends on / 依赖: nhdsWithin_eq_nhds, oscillation, oscillationWithin
-/
theorem oscillationWithin_nhds_eq_oscillation [TopologicalSpace E] (f : E -> F) (D : Set E) (x : E)
    (hD : D in 𝓝 x) : oscillationWithin f D x = oscillation f x := by
  rw [oscillation]; rw [oscillationWithin]; rw [nhdsWithin_eq_nhds.2 hD]

/--
theorem `oscillationWithin_univ_eq_oscillation` / 定理 `oscillationWithin_univ_eq_oscillation`

English:
theorem oscillationWithin_univ_eq_oscillation
  given: [TopologicalSpace E] (f : E -> F) (x : E)
  proof: oscillationWithin_nhds_eq_oscillation f univ x Filter.univ_mem

中文:
定理 oscillationWithin_univ_eq_oscillation
  条件: [TopologicalSpace E] (f : E -> F) (x : E)
  证明: oscillationWithin_nhds_eq_oscillation f univ x Filter.univ_mem

Depends on / 依赖: Filter, Filter.univ_mem, oscillationWithin_nhds_eq_oscillation, univ_mem
-/
theorem oscillationWithin_univ_eq_oscillation [TopologicalSpace E] (f : E -> F) (x : E) :
    oscillationWithin f univ x = oscillation f x :=
  oscillationWithin_nhds_eq_oscillation f univ x Filter.univ_mem

namespace ContinuousWithinAt

/--
theorem `oscillationWithin_eq_zero` / 定理 `oscillationWithin_eq_zero`

English:
theorem oscillationWithin_eq_zero
  statement: [TopologicalSpace E] {f : E -> F} {D : Set E}
  proof: by
  rw [← nonpos_iff_eq_zero]
  refine _root_.le_of_forall_pos_le_add fun ε hε => ?_
  rw [zero_add]
  have : eball (f x) (ε / 2) in (𝓝[D] x).map f :=
hf eball_mem_nhds _ (by simp [ne_of_gt hε])
  refine (biInf_le ediam this).trans (le_of_le_of_eq ediam_eball_le ?_)
  exact (ENNReal.mul_div_cancel 

中文:
定理 oscillationWithin_eq_zero
  结论: [TopologicalSpace E] {f : E -> F} {D : Set E}
  证明: by
  rw [← nonpos_iff_eq_zero]
  refine _root_.le_of_forall_pos_le_add fun ε hε => ?_
  rw [zero_add]
  have : eball (f x) (ε / 2) in (𝓝[D] x).map f :=
hf eball_mem_nhds _ (by simp [ne_of_gt hε])
  refine (biInf_le ediam this).trans (le_of_le_of_eq ediam_eball_le ?_)
  exact (ENNReal.mul_div_cancel 

Depends on / 依赖: ENNReal, ENNReal.mul_div_cancel, _root_, _root_.le_of_forall_pos_le_add, biInf_le, eball_mem_nhds, ediam_eball_le, le_of_forall_pos_le_add, le_of_le_of_eq, mul_div_cancel, ne_of_gt, nonpos_iff_eq_zero, zero_add
-/
theorem oscillationWithin_eq_zero [TopologicalSpace E] {f : E -> F} {D : Set E}
    {x : E} (hf : ContinuousWithinAt f D x) : oscillationWithin f D x = 0 := by
  rw [← nonpos_iff_eq_zero]
  refine _root_.le_of_forall_pos_le_add fun ε hε => ?_
  rw [zero_add]
  have : eball (f x) (ε / 2) in (𝓝[D] x).map f :=
hf eball_mem_nhds _ (by simp [ne_of_gt hε])
  refine (biInf_le ediam this).trans (le_of_le_of_eq ediam_eball_le ?_)
  exact (ENNReal.mul_div_cancel (by simp) (by simp))

end ContinuousWithinAt

namespace ContinuousAt

/--
theorem `oscillation_eq_zero` / 定理 `oscillation_eq_zero`

English:
theorem oscillation_eq_zero
  given: [TopologicalSpace E] {f : E -> F} {x : E} (hf : ContinuousAt f x)
  proof: by
  rw [← continuousWithinAt_univ f x] at hf
  exact oscillationWithin_univ_eq_oscillation f x ▸ hf.oscillationWithin_eq_zero

中文:
定理 oscillation_eq_zero
  条件: [TopologicalSpace E] {f : E -> F} {x : E} (hf : ContinuousAt f x)
  证明: by
  rw [← continuousWithinAt_univ f x] at hf
  exact oscillationWithin_univ_eq_oscillation f x ▸ hf.oscillationWithin_eq_zero

Depends on / 依赖: continuousWithinAt_univ, hf.oscillationWithin_eq_zero, oscillationWithin_eq_zero, oscillationWithin_univ_eq_oscillation
-/
theorem oscillation_eq_zero [TopologicalSpace E] {f : E -> F} {x : E} (hf : ContinuousAt f x) :
    oscillation f x = 0 := by
  rw [← continuousWithinAt_univ f x] at hf
  exact oscillationWithin_univ_eq_oscillation f x ▸ hf.oscillationWithin_eq_zero

end ContinuousAt

namespace OscillationWithin

/--
theorem `eq_zero_iff_continuousWithinAt` / 定理 `eq_zero_iff_continuousWithinAt`

English:
theorem eq_zero_iff_continuousWithinAt
  statement: [TopologicalSpace E] (f : E -> F) {D : Set E}
  proof: by
  refine ⟨fun hf => EMetric.tendsto_nhds.mpr (fun ε ε0 => ?_), fun hf => hf.oscillationWithin_eq_zero⟩
  simp_rw [← hf, oscillationWithin, iInf_lt_iff] at ε0
  obtain ⟨S, hS, Sε⟩ := ε0
  refine Filter.mem_of_superset hS (fun y hy => lt_of_le_of_lt ?_ Sε)
exact edist_le_ediam_of_mem (mem_preimage.

中文:
定理 eq_zero_iff_continuousWithinAt
  结论: [TopologicalSpace E] (f : E -> F) {D : Set E}
  证明: by
  refine ⟨fun hf => EMetric.tendsto_nhds.mpr (fun ε ε0 => ?_), fun hf => hf.oscillationWithin_eq_zero⟩
  simp_rw [← hf, oscillationWithin, iInf_lt_iff] at ε0
  obtain ⟨S, hS, Sε⟩ := ε0
  refine Filter.mem_of_superset hS (fun y hy => lt_of_le_of_lt ?_ Sε)
exact edist_le_ediam_of_mem (mem_preimage.

Depends on / 依赖: EMetric, EMetric.tendsto_nhds.mpr, Filter, Filter.mem_of_superset, edist_le_ediam_of_mem, hf.oscillationWithin_eq_zero, iInf_lt_iff, lt_of_le_of_lt, mem_of_mem_nhdsWithin, mem_of_superset, mem_preimage, oscillationWithin, oscillationWithin_eq_zero, simp_rw, tendsto_nhds
-/
theorem eq_zero_iff_continuousWithinAt [TopologicalSpace E] (f : E -> F) {D : Set E}
    {x : E} (xD : x in D) : oscillationWithin f D x = 0 ↔ ContinuousWithinAt f D x := by
  refine ⟨fun hf => EMetric.tendsto_nhds.mpr (fun ε ε0 => ?_), fun hf => hf.oscillationWithin_eq_zero⟩
  simp_rw [← hf, oscillationWithin, iInf_lt_iff] at ε0
  obtain ⟨S, hS, Sε⟩ := ε0
  refine Filter.mem_of_superset hS (fun y hy => lt_of_le_of_lt ?_ Sε)
exact edist_le_ediam_of_mem (mem_preimage.1 hy) mem_preimage.1 (mem_of_mem_nhdsWithin xD hS)

end OscillationWithin

namespace Oscillation

/--
theorem `eq_zero_iff_continuousAt` / 定理 `eq_zero_iff_continuousAt`

English:
theorem eq_zero_iff_continuousAt
  given: [TopologicalSpace E] (f : E -> F) (x : E)
  proof: by
  rw [← oscillationWithin_univ_eq_oscillation]; rw [← continuousWithinAt_univ f x]
  exact OscillationWithin.eq_zero_iff_continuousWithinAt f (mem_univ x)

中文:
定理 eq_zero_iff_continuousAt
  条件: [TopologicalSpace E] (f : E -> F) (x : E)
  证明: by
  rw [← oscillationWithin_univ_eq_oscillation]; rw [← continuousWithinAt_univ f x]
  exact OscillationWithin.eq_zero_iff_continuousWithinAt f (mem_univ x)

Depends on / 依赖: OscillationWithin, OscillationWithin.eq_zero_iff_continuousWithinAt, continuousWithinAt_univ, eq_zero_iff_continuousWithinAt, mem_univ, oscillationWithin_univ_eq_oscillation
-/
theorem eq_zero_iff_continuousAt [TopologicalSpace E] (f : E -> F) (x : E) :
    oscillation f x = 0 ↔ ContinuousAt f x := by
  rw [← oscillationWithin_univ_eq_oscillation]; rw [← continuousWithinAt_univ f x]
  exact OscillationWithin.eq_zero_iff_continuousWithinAt f (mem_univ x)

end Oscillation

namespace IsCompact

variable [PseudoEMetricSpace E] {K : Set E}
variable {f : E -> F} {D : Set E} {ε : ENNReal}

/--
theorem `uniform_oscillationWithin` / 定理 `uniform_oscillationWithin`

English:
theorem uniform_oscillationWithin
  given: (comp : IsCompact K) (hK : forall x in K, oscillationWithin f D x < ε)
  proof: by
  let S := fun r =>
    {x : E | exists (a : Real), (a > r ∧ ediam (f '' (eball x (ENNReal.ofReal a) inter D)) <= ε)}
  have S_open : forall r > 0, IsOpen (S r) := by
    refine fun r _ => EMetric.isOpen_iff.mpr fun x ⟨a, ar, ha⟩ =>
      ⟨ENNReal.ofReal ((a - r) / 2), by simp [ar], ?_⟩
    refin

中文:
定理 uniform_oscillationWithin
  条件: (comp : IsCompact K) (hK : 对任意 x in K, oscillationWithin f D x < ε)
  证明: by
  let S := fun r =>
    {x : E | exists (a : Real), (a > r ∧ ediam (f '' (eball x (ENNReal.ofReal a) inter D)) <= ε)}
  have S_open : forall r > 0, IsOpen (S r) := by
    refine fun r _ => EMetric.isOpen_iff.mpr fun x ⟨a, ar, ha⟩ =>
      ⟨ENNReal.ofReal ((a - r) / 2), by simp [ar], ?_⟩
    refin

Depends on / 依赖: EMetric, EMetric.isOpen_iff.mpr, ENNReal, ENNReal.add_lt_add, ENNReal.ofReal, IsOpen, S_open, add_lt_add, ediam_mono, edist_triangle, image_mono, isOpen_iff, le_trans, lt_of_le_of_lt, lt_of_lt_of_eq, ofReal, ofReal_add
-/
theorem uniform_oscillationWithin (comp : IsCompact K) (hK : forall x in K, oscillationWithin f D x < ε) :
    exists δ > 0, forall x in K, ediam (f '' (eball x (ENNReal.ofReal δ) inter D)) <= ε := by
  let S := fun r =>
    {x : E | exists (a : Real), (a > r ∧ ediam (f '' (eball x (ENNReal.ofReal a) inter D)) <= ε)}
  have S_open : forall r > 0, IsOpen (S r) := by
    refine fun r _ => EMetric.isOpen_iff.mpr fun x ⟨a, ar, ha⟩ =>
      ⟨ENNReal.ofReal ((a - r) / 2), by simp [ar], ?_⟩
    refine fun y hy => ⟨a - (a - r) / 2, by linarith,
      le_trans (ediam_mono (image_mono fun z hz => ?_)) ha⟩
    refine ⟨lt_of_le_of_lt (edist_triangle z y x) (lt_of_lt_of_eq (ENNReal.add_lt_add hz.1 hy) ?_),
      hz.2⟩
    rw [← ofReal_add (by linarith) (by linarith)]; rw [sub_add_cancel]
  have S_cover : K subseteq ⋃ r > 0, S r := by
    intro x hx
    have : oscillationWithin f D x < ε := hK x hx
    simp only [oscillationWithin, Filter.mem_map, iInf_lt_iff] at this
    obtain ⟨n, hn₁, hn₂⟩ := this
    obtain ⟨r, r0, hr⟩ := EMetric.mem_nhdsWithin_iff.1 hn₁
    simp only [gt_iff_lt, mem_iUnion, exists_prop]
    have : forall r', (ENNReal.ofReal r') <= r ->
        ediam (f '' (eball x (ENNReal.ofReal r') inter D)) <= ε := by
      intro r' hr'
      grw [← hn₂, ← image_subset_iff.2 hr, hr']
    by_cases r_top : r = ⊤
    · exact ⟨1, one_pos, 2, by simp, this 2 (by simp only [r_top, le_top])⟩
    · obtain ⟨r', hr'⟩ := exists_between (toReal_pos (ne_of_gt r0) r_top)
      use r', hr'.1, r.toReal, hr'.2, this r.toReal ofReal_toReal_le
  have S_antitone : forall (r₁ r₂ : Real), r₁ <= r₂ -> S r₂ subseteq S r₁ :=
    fun r₁ r₂ hr x ⟨a, ar₂, ha⟩ => ⟨a, lt_of_le_of_lt hr ar₂, ha⟩
  obtain ⟨δ, δ0, hδ⟩ : exists r > 0, K subseteq S r := by
    obtain ⟨T, Tb, Tfin, hT⟩ := comp.elim_finite_subcover_image S_open S_cover
    by_cases T_nonempty : T.Nonempty
    · use Tfin.isWF.min T_nonempty, Tb (Tfin.isWF.min_mem T_nonempty)
      intro x hx
      obtain ⟨r, hr⟩ := mem_iUnion.1 (hT hx)
      simp only [mem_iUnion, exists_prop] at hr
      exact (S_antitone _ r (IsWF.min_le Tfin.isWF T_nonempty hr.1)) hr.2
    · rw [not_nonempty_iff_eq_empty] at T_nonempty
      use 1, one_pos, subset_trans hT (by simp [T_nonempty])
  use δ, δ0
  intro x xK
  obtain ⟨a, δa, ha⟩ := hδ xK
  grw [← ha]
  gcongr

/--
theorem `uniform_oscillation` / 定理 `uniform_oscillation`

English:
theorem uniform_oscillation
  statement: {K : Set E} (comp : IsCompact K)
  proof: by
  simp only [← oscillationWithin_univ_eq_oscillation] at hK
  convert! ← comp.uniform_oscillationWithin hK
  exact inter_univ _

中文:
定理 uniform_oscillation
  结论: {K : Set E} (comp : IsCompact K)
  证明: by
  simp only [← oscillationWithin_univ_eq_oscillation] at hK
  convert! ← comp.uniform_oscillationWithin hK
  exact inter_univ _

Depends on / 依赖: comp.uniform_oscillationWithin, convert, inter_univ, oscillationWithin_univ_eq_oscillation, uniform_oscillationWithin
-/
theorem uniform_oscillation {K : Set E} (comp : IsCompact K)
    {f : E -> F} {ε : ENNReal} (hK : forall x in K, oscillation f x < ε) :
    exists δ > 0, forall x in K, ediam (f '' (eball x (ENNReal.ofReal δ))) <= ε := by
  simp only [← oscillationWithin_univ_eq_oscillation] at hK
  convert! ← comp.uniform_oscillationWithin hK
  exact inter_univ _

end IsCompact
