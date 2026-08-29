/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Tangent cone points as limits of sequences

This file contains a few ways to describe `tangentConeAt`
as the set of limits of certain sequences.

In many cases, one can generalize results about the tangent cone
by using `mem_tangentConeAt_of_seq` and `exists_fun_of_mem_tangentConeAt`
instead of these lemmas.
-/

public section

open Filter
open scoped Topology

/--
theorem `mem_tangentConeAt_iff_exists_seq` / 定理 `mem_tangentConeAt_iff_exists_seq`

English:
theorem mem_tangentConeAt_iff_exists_seq
  statement: {R E : Type*} [AddCommGroup E] [SMul R E]
  proof: by
  constructor
  · intro h
    simp only [tangentConeAt_def, Set.mem_ofPred, ← map₂_smul, ← map_prod_eq_map₂, ClusterPt,
      ← neBot_inf_comap_iff_map'] at h
    rcases @exists_seq_tendsto _ _ _ h with ⟨cd, hcd⟩
    simp only [tendsto_inf, tendsto_comap_iff, tendsto_prod_iff', tendsto_nhdsWithin

中文:
定理 mem_tangentConeAt_iff_存在_seq
  结论: {R E : 类型} [加法交换群 E] [标量乘法 R E]
  证明: by
  constructor
  · intro h
    simp only [tangentConeAt_def, Set.mem_ofPred, ← map₂_smul, ← map_prod_eq_map₂, ClusterPt,
      ← neBot_inf_comap_iff_map'] at h
    rcases @exists_seq_tendsto _ _ _ h with ⟨cd, hcd⟩
    simp only [tendsto_inf, tendsto_comap_iff, tendsto_prod_iff', tendsto_nhdsWithin

Depends on / 依赖: ClusterPt, Prod.fst, Prod.snd, Set.mem_ofPred, exists_seq_tendsto, mem_ofPred, mem_tangentConeAt_of_seq, neBot_inf_comap_iff_map, tangentConeAt_def, tendsto_comap_iff, tendsto_inf, tendsto_nhdsWithin_iff, tendsto_prod_iff
-/
theorem mem_tangentConeAt_iff_exists_seq {R E : Type*} [AddCommGroup E] [SMul R E]
    [TopologicalSpace E] [FirstCountableTopology E] {s : Set E} {x y : E} :
    y in tangentConeAt R s x ↔ exists (c : Nat -> R) (d : Nat -> E), Tendsto d atTop (𝓝 0) ∧
      (forallᶠ n in atTop, x + d n in s) ∧ Tendsto (fun n => c n • d n) atTop (𝓝 y) := by
  constructor
  · intro h
    simp only [tangentConeAt_def, Set.mem_ofPred, ← map₂_smul, ← map_prod_eq_map₂, ClusterPt,
      ← neBot_inf_comap_iff_map'] at h
    rcases @exists_seq_tendsto _ _ _ h with ⟨cd, hcd⟩
    simp only [tendsto_inf, tendsto_comap_iff, tendsto_prod_iff', tendsto_nhdsWithin_iff] at hcd
    exact ⟨Prod.fst ∘ cd, Prod.snd ∘ cd, hcd.2.2.1, hcd.2.2.2, hcd.1⟩
  · rintro ⟨c, d, hd₀, hds, hcd⟩
    exact mem_tangentConeAt_of_seq atTop c d hd₀ hds hcd

section
variable {𝕜 E : Type*} [NormedDivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [ContinuousSMul 𝕜 E] {s : Set E} {x y : E} {r : 𝕜}

/--
theorem `tangentConeAt.lim_zero` / 定理 `tangentConeAt.lim_zero`

English:
theorem tangentConeAt.lim_zero
  statement: {α : Type*} (l : Filter α) {c : α -> 𝕜} {d : α -> E} {y : E}
  proof: by
  have : forallᶠ n in l, (c n)⁻¹ • c n • d n = d n :=
    (eventually_ne_of_tendsto_norm_atTop hc 0).mono fun n hn => inv_smul_smul₀ hn (d n)
  rw [tendsto_norm_atTop_iff_cobounded] at hc
simpa using Tendsto.congr' this (tendsto_inv₀_cobounded.comp hc).smul hd

中文:
定理 tangentConeAt.lim_zero
  结论: {α : 类型} (l : 滤子 α) {c : α -> 𝕜} {d : α -> E} {y : E}
  证明: by
  have : forallᶠ n in l, (c n)⁻¹ • c n • d n = d n :=
    (eventually_ne_of_tendsto_norm_atTop hc 0).mono fun n hn => inv_smul_smul₀ hn (d n)
  rw [tendsto_norm_atTop_iff_cobounded] at hc
simpa using Tendsto.congr' this (tendsto_inv₀_cobounded.comp hc).smul hd

Depends on / 依赖: Tendsto, Tendsto.congr, _cobounded.comp, eventually_ne_of_tendsto_norm_atTop, tendsto_norm_atTop_iff_cobounded
-/
theorem tangentConeAt.lim_zero {α : Type*} (l : Filter α) {c : α -> 𝕜} {d : α -> E} {y : E}
    (hc : Tendsto (fun n => ‖c n‖) l atTop) (hd : Tendsto (fun n => c n • d n) l (𝓝 y)) :
    Tendsto d l (𝓝 0) := by
  have : forallᶠ n in l, (c n)⁻¹ • c n • d n = d n :=
    (eventually_ne_of_tendsto_norm_atTop hc 0).mono fun n hn => inv_smul_smul₀ hn (d n)
  rw [tendsto_norm_atTop_iff_cobounded] at hc
simpa using Tendsto.congr' this (tendsto_inv₀_cobounded.comp hc).smul hd

/--
theorem `mem_tangentConeAt_of_pow_smul` / 定理 `mem_tangentConeAt_of_pow_smul`

English:
theorem mem_tangentConeAt_of_pow_smul
  statement: (hr₀ : r != 0) (hr : ‖r‖ < 1)
  proof: by
  refine mem_tangentConeAt_of_add_smul_mem
    (tendsto_nhdsWithin_iff.mpr ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr, ?_⟩) hs
  simp [hr₀]

中文:
定理 mem_tangentConeAt_of_pow_smul
  结论: (hr₀ : r != 0) (hr : ‖r‖ < 1)
  证明: by
  refine mem_tangentConeAt_of_add_smul_mem
    (tendsto_nhdsWithin_iff.mpr ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr, ?_⟩) hs
  simp [hr₀]

Depends on / 依赖: mem_tangentConeAt_of_add_smul_mem, tendsto_nhdsWithin_iff, tendsto_nhdsWithin_iff.mpr, tendsto_pow_atTop_nhds_zero_of_norm_lt_one
-/
theorem mem_tangentConeAt_of_pow_smul (hr₀ : r != 0) (hr : ‖r‖ < 1)
    (hs : forallᶠ n : Nat in atTop, x + r ^ n • y in s) :
    y in tangentConeAt 𝕜 s x := by
  refine mem_tangentConeAt_of_add_smul_mem
    (tendsto_nhdsWithin_iff.mpr ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr, ?_⟩) hs
  simp [hr₀]

end

/--
theorem `mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop` / 定理 `mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop`

English:
theorem mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop
  statement: {𝕜 E : Type*}
  proof: by
  constructor
  · rcases eq_or_ne y 0 with rfl | hy₀
    · rw [zero_mem_tangentConeAt_iff]
      intro hx
      obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 1
      have (n : Nat) : exists d : E, x + d in s ∧ ‖d‖ < (1 / (2 * ‖c‖)) ^ n := by
        rw [Metric.mem_closure_iff] at hx
        rcas

中文:
定理 mem_tangentConeAt_iff_存在_seq_norm_tendsto_atTop
  结论: {𝕜 E : 类型}
  证明: by
  constructor
  · rcases eq_or_ne y 0 with rfl | hy₀
    · rw [zero_mem_tangentConeAt_iff]
      intro hx
      obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 1
      have (n : Nat) : exists d : E, x + d in s ∧ ‖d‖ < (1 / (2 * ‖c‖)) ^ n := by
        rw [Metric.mem_closure_iff] at hx
        rcas

Depends on / 依赖: Metric, Metric.mem_closure_iff, NormedField, NormedField.exists_lt_norm, dist_eq_norm_sub, eq_or_ne, exists_lt_norm, mem_closure_iff, norm_pow, of_forall, tendsto_, tendsto_c, tendsto_cd, zero_mem_tangentConeAt_iff
-/
theorem mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {s : Set E} {x y : E} :
    y in tangentConeAt 𝕜 s x ↔
      exists (c : Nat -> 𝕜) (d : Nat -> E), Tendsto (‖c ·‖) atTop atTop ∧ (forallᶠ n in atTop, x + d n in s) ∧
        Tendsto (fun n => c n • d n) atTop (𝓝 y) := by
  constructor
  · rcases eq_or_ne y 0 with rfl | hy₀
    · rw [zero_mem_tangentConeAt_iff]
      intro hx
      obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 1
      have (n : Nat) : exists d : E, x + d in s ∧ ‖d‖ < (1 / (2 * ‖c‖)) ^ n := by
        rw [Metric.mem_closure_iff] at hx
        rcases hx ((1 / (2 * ‖c‖)) ^ n) (by positivity) with ⟨v, hvs, hv⟩
        use v - x
        simp_all [dist_eq_norm_sub']
      choose d hds hd using this
      refine ⟨(c ^ ·), d, ?tendsto_c, .of_forall hds, ?tendsto_cd⟩
      case tendsto_c =>
        simp only [norm_pow]
        exact tendsto_pow_atTop_atTop_of_one_lt hc
      case tendsto_cd =>
        rw [atTop_basis.tendsto_iff (Metric.nhds_basis_ball_pow one_half_pos one_half_lt_one)]
        refine fun N _ => ⟨N, trivial, fun n hn => ?_⟩
        rw [Set.mem_Ici] at hn
        suffices ‖c‖ ^ n * ‖d n‖ < 1 / (2 ^ N) by simpa [norm_smul]
        rw [← lt_div_iff₀' (by positivity)]
        refine (hd n).trans_le ?_
        grw [hn]
        · simp [mul_pow, div_eq_inv_mul]
        · norm_num1
    · rw [mem_tangentConeAt_iff_exists_seq]
      rintro ⟨c, d, hd₀, hds, hcd⟩
      refine ⟨c, d, ?_, hds, hcd⟩
      replace hd₀ := hd₀.norm
      have hd₀' : forallᶠ n in .atTop, d n != 0 :=
.mono fun _ => right_ne_zero_of_smul hcd.eventually_ne hy₀
      replace hcd := hcd.norm
      simp only [norm_smul, norm_zero, ← div_inv_eq_mul] at hd₀ hcd
      refine .num ?_ (by simpa) hcd
      rw [← inv_nhdsGT_zero (𝕜 := Real)]; rw [← Filter.comap_inv]; rw [Filter.tendsto_comap_iff]
      simpa [Function.comp_def, tendsto_nhdsWithin_iff, hd₀] using hd₀'
  · rintro ⟨c, d, hc, hds, hcd⟩
    exact mem_tangentConeAt_of_seq atTop c d (tangentConeAt.lim_zero atTop hc hcd) hds hcd
