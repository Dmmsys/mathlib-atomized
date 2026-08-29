/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The logarithm as a limit of powers

This file shows that the logarithm can be expressed as a limit of powers, namely that
`p⁻¹ * (x ^ p - 1)` tends to `log x` as `p` tends to zero for positive `x`.

## Main declarations

* `Real.tendstoLocallyUniformlyOn_rpow_sub_one_log`: `p⁻¹ * (x ^ p - 1)` tends uniformly to
  `log x` on compact subsets of `Ioi 0` as `p` tends to zero
* `tendsto_rpow_sub_one_log`: `p⁻¹ * (x ^ p - 1)`: the analogous statement for pointwise
  convergence.
-/

public section

open scoped Topology
open Real Filter

/--
lemma `Real.norm_inv_mul_rpow_sub_one_sub_log_le` / 引理 `Real.norm_inv_mul_rpow_sub_one_sub_log_le`

English:
lemma Real.norm_inv_mul_rpow_sub_one_sub_log_le
  statement: {p x : Real} (p_pos : 0 < p) (x_pos : 0 < x)
  proof: by
  have pinv_nonneg : 0 <= p⁻¹ := by grind [_root_.inv_nonneg]
  calc
    _ = ‖p⁻¹ * ((x ^ p - 1) - p * log x)‖ := by grind
    _ = p⁻¹ * ‖(rexp (p * log x) - 1) - p * log x‖ := by
          simp only [norm_mul, Real.norm_of_nonneg (r := p⁻¹) pinv_nonneg]
          congr
          rw [mul_comm]; r

中文:
引理 实数.norm_inv_mul_rpow_sub_one_sub_log_le
  结论: {p x : 实数} (p_pos : 0 < p) (x_pos : 0 < x)
  证明: by
  have pinv_nonneg : 0 <= p⁻¹ := by grind [_root_.inv_nonneg]
  calc
    _ = ‖p⁻¹ * ((x ^ p - 1) - p * log x)‖ := by grind
    _ = p⁻¹ * ‖(rexp (p * log x) - 1) - p * log x‖ := by
          simp only [norm_mul, Real.norm_of_nonneg (r := p⁻¹) pinv_nonneg]
          congr
          rw [mul_comm]; r

Depends on / 依赖: Real.exp_log, Real.exp_mul, Real.norm_exp_sub_one_sub_id_le, Real.norm_of_nonneg, _root_, _root_.inv_nonneg, exp_log, exp_mul, inv_nonneg, mul_comm, norm_exp_sub_one_sub_id_le, norm_mul, norm_of_nonneg, pinv_nonneg
-/
lemma Real.norm_inv_mul_rpow_sub_one_sub_log_le {p x : Real} (p_pos : 0 < p) (x_pos : 0 < x)
    (hx : ‖p * log x‖ <= 1) : ‖p⁻¹ * (x ^ p - 1) - log x‖ <= p * ‖log x‖ ^ 2 := by
  have pinv_nonneg : 0 <= p⁻¹ := by grind [_root_.inv_nonneg]
  calc
    _ = ‖p⁻¹ * ((x ^ p - 1) - p * log x)‖ := by grind
    _ = p⁻¹ * ‖(rexp (p * log x) - 1) - p * log x‖ := by
          simp only [norm_mul, Real.norm_of_nonneg (r := p⁻¹) pinv_nonneg]
          congr
          rw [mul_comm]; rw [Real.exp_mul]; rw [Real.exp_log (by grind)]
    _ <= p⁻¹ * ‖p * log x‖ ^ 2 := by
          gcongr
          refine Real.norm_exp_sub_one_sub_id_le ?_
          simp only [hx]
    _ = p * ‖log x‖ ^ 2 := by
          simp only [norm_mul]
          grind [Real.norm_of_nonneg]

open Set in
/--
lemma `Real.tendstoLocallyUniformlyOn_rpow_sub_one_log` / 引理 `Real.tendstoLocallyUniformlyOn_rpow_sub_one_log`

English:
lemma Real.tendstoLocallyUniformlyOn_rpow_sub_one_log
  proof: by
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioi).mpr ?_
  intro s hs hs'
  rw [Metric.uniformity_basis_dist_le.tendstoUniformlyOn_iff_of_uniformity]
  intro ε hε
  let pbound : Real := ε / (sSup ((fun x => ‖log x‖ ^ 2) '' s) + 1)
  have hxs : forall x in s, x != 0 := by grind


中文:
引理 实数.tendstoLocallyUniformlyOn_rpow_sub_one_log
  证明: by
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioi).mpr ?_
  intro s hs hs'
  rw [Metric.uniformity_basis_dist_le.tendstoUniformlyOn_iff_of_uniformity]
  intro ε hε
  let pbound : Real := ε / (sSup ((fun x => ‖log x‖ ^ 2) '' s) + 1)
  have hxs : forall x in s, x != 0 := by grind


Depends on / 依赖: Metric, Metric.uniformity_basis_dist_le.tendstoUniformlyOn_iff_of_uniformity, Real.sSup_nonneg, isOpen_Ioi, pbound, sSup_nonneg, sq_nonneg, tendstoLocallyUniformlyOn_iff_forall_isCompact, tendstoUniformlyOn_iff_of_uniformity, uniformity_basis_dist_le
-/
lemma Real.tendstoLocallyUniformlyOn_rpow_sub_one_log :
    TendstoLocallyUniformlyOn (fun (p : Real) (x : Real) => p⁻¹ * (x ^ p - 1)) log (𝓝[>] 0) (Ioi 0) := by
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioi).mpr ?_
  intro s hs hs'
  rw [Metric.uniformity_basis_dist_le.tendstoUniformlyOn_iff_of_uniformity]
  intro ε hε
  let pbound : Real := ε / (sSup ((fun x => ‖log x‖ ^ 2) '' s) + 1)
  have hxs : forall x in s, x != 0 := by grind
  have sSup_nonneg : 0 <= sSup ((fun x => ‖log x‖ ^ 2) '' s) := by
    refine Real.sSup_nonneg ?_
    grind [← sq_nonneg]
  have sSup_nonneg' : 0 <= sSup ((fun x => ‖log x‖) '' s) := by
    refine Real.sSup_nonneg ?_
    grind [← sq_nonneg]
  have pbound_pos : 0 < pbound := by positivity
.mem_of_mem pbound_pos have h₁ : forallᶠ p : Real in 𝓝[>] 0, 0 < p ∧ p < pbound := nhdsGT_basis 0
  have h₂ : forallᶠ p : Real in 𝓝[>] 0, p <= 1 / (sSup ((fun x => ‖log x‖) '' s) + 1) :=
Eventually.filter_mono nhdsWithin_le_nhds eventually_le_nhds (by positivity)
  have hcont : ContinuousOn (fun x => ‖log x‖ ^ 2) s := by fun_prop
  have hcont' : ContinuousOn (fun x => ‖log x‖) s := by fun_prop
  filter_upwards [h₁, h₂] with p ⟨hp₁,hp₂⟩ hp₃
  intro x hx
  have hx' : ‖p * log x‖ <= 1 := calc
    _ = p * ‖log x‖ := by grind [norm_mul, Real.norm_of_nonneg]
    _ <= 1 / (sSup ((fun y => ‖log y‖) '' s) + 1) * ‖log x‖ := by gcongr
    _ <= 1 / (‖log x‖ + 1) * ‖log x‖ := by
        gcongr
        refine le_csSup ?_ (by grind)
        grind [IsCompact.bddAbove, ← IsCompact.image_of_continuousOn]
    _ = ‖log x‖ / (‖log x‖ + 1) := by grind
    _ <= 1 := by rw [div_le_one₀] <;> grind [norm_nonneg]
  have pinv_nonneg : 0 <= p⁻¹ := by grind [_root_.inv_nonneg]
  rw [dist_eq_norm']
  calc
    _ <= p * ‖log x‖ ^ 2 := Real.norm_inv_mul_rpow_sub_one_sub_log_le hp₁ (hs hx) hx'
    _ <= p * sSup ((fun x => ‖log x‖ ^ 2) '' s) := by
          gcongr
          refine le_csSup ?_ (by grind)
          grind [IsCompact.bddAbove, ← IsCompact.image_of_continuousOn]
    _ <= pbound * (sSup ((fun x => ‖log x‖ ^ 2) '' s) + 1) := by gcongr; grind
    _ = ε := by grind

/--
lemma `tendsto_rpow_sub_one_log` / 引理 `tendsto_rpow_sub_one_log`

English:
lemma tendsto_rpow_sub_one_log
  given: {x : Real} (hx : 0 < x)
  proof: TendstoLocallyUniformlyOn.tendsto_at
    tendstoLocallyUniformlyOn_rpow_sub_one_log (by grind)

中文:
引理 tendsto_rpow_sub_one_log
  条件: {x : 实数} (hx : 0 < x)
  证明: TendstoLocallyUniformlyOn.tendsto_at
    tendstoLocallyUniformlyOn_rpow_sub_one_log (by grind)

Depends on / 依赖: TendstoLocallyUniformlyOn, TendstoLocallyUniformlyOn.tendsto_at, tendstoLocallyUniformlyOn_rpow_sub_one_log, tendsto_at
-/
lemma tendsto_rpow_sub_one_log {x : Real} (hx : 0 < x) :
    Tendsto (fun p => p⁻¹ * (x ^ p - 1)) (𝓝[>] 0) (𝓝 (log x)) :=
  TendstoLocallyUniformlyOn.tendsto_at
    tendstoLocallyUniformlyOn_rpow_sub_one_log (by grind)
