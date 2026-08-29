/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.SqrtDeriv
public import Mathlib.Analysis.Normed.Ring.InfiniteProd
public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# The modular discriminant Δ

This file defines the modular discriminant `Δ(z) = η(z) ^ 24`, where `η` is the Dedekind eta
function, and proves its key properties including invariance under the generators of `SL(2, ℤ)`.

## Main definitions

* `ModularForm.discriminant`: The modular discriminant function `Δ(z) = η(z) ^ 24`, which can also
  be expressed as `q * ∏' (1 - q ^ (n + 1)) ^ 24` where `q = e ^ (2πiz)`.

## Main results

* `ModularForm.discriminant_ne_zero`: The discriminant is non-vanishing on the upper half-plane.
* `ModularForm.discriminant_T_invariant`: Invariance under the translation `T : z ↦ z + 1`.
* `ModularForm.discriminant_S_invariant`: Invariance under the inversion `S : z ↦ -1 / z`,
  showing `Δ(-1 / z) = z ^ 12 · Δ(z)`.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], section 1.2
-/

open Function Complex SlashInvariantForm MatrixGroups Filter

open UpperHalfPlane hiding I

open scoped Real Topology

noncomputable section

namespace ModularForm

/-- The modular discriminant `Δ(z) = η(z) ^ 24`, where `η` is the Dedekind eta function. -/
@[expose] public def discriminant (z : ℍ) := (eta z) ^ 24

local notation "Δ" => discriminant

local notation "𝕢" => Periodic.qParam

section auxiliary

/--
lemma `csqrt_pow_24_eq` / 引理 `csqrt_pow_24_eq`

English:
lemma csqrt_pow_24_eq
  given: {z : Complex} (hz : z != 0)
  statement: sqrt z ^ 24 = z ^ 12
  proof: by
  rw [sqrt_eq_exp hz]; rw [← exp_nat_mul]
  ring_nf
  rw [show (log z * 12) = (12 : Nat) * log z by ring]; rw [exp_nat_mul]; rw [exp_log hz]

中文:
引理 csqrt_pow_24_eq
  条件: {z : 复形} (hz : z != 0)
  结论: sqrt z ^ 24 = z ^ 12
  证明: by
  rw [sqrt_eq_exp hz]; rw [← exp_nat_mul]
  ring_nf
  rw [show (log z * 12) = (12 : Nat) * log z by ring]; rw [exp_nat_mul]; rw [exp_log hz]

Depends on / 依赖: exp_log, exp_nat_mul, ring_nf, sqrt_eq_exp
-/
lemma csqrt_pow_24_eq {z : Complex} (hz : z != 0) : sqrt z ^ 24 = z ^ 12 := by
  rw [sqrt_eq_exp hz]; rw [← exp_nat_mul]
  ring_nf
  rw [show (log z * 12) = (12 : Nat) * log z by ring]; rw [exp_nat_mul]; rw [exp_log hz]

/--
lemma `csqrt_I_pow_24` / 引理 `csqrt_I_pow_24`

English:
lemma csqrt_I_pow_24
  statement: sqrt I ^ 24 = 1
  proof: by
  rw [csqrt_pow_24_eq I_ne_zero]; rw [show 12 = 4 * 3 by lia]; rw [pow_mul]; rw [I_pow_four]; rw [one_pow]

中文:
引理 csqrt_I_pow_24
  结论: sqrt I ^ 24 = 1
  证明: by
  rw [csqrt_pow_24_eq I_ne_zero]; rw [show 12 = 4 * 3 by lia]; rw [pow_mul]; rw [I_pow_four]; rw [one_pow]

Depends on / 依赖: I_ne_zero, I_pow_four, csqrt_pow_24_eq, one_pow, pow_mul
-/
lemma csqrt_I_pow_24 : sqrt I ^ 24 = 1 := by
  rw [csqrt_pow_24_eq I_ne_zero]; rw [show 12 = 4 * 3 by lia]; rw [pow_mul]; rw [I_pow_four]; rw [one_pow]

/--
lemma `logDeriv_eta_comp_div_eq` / 引理 `logDeriv_eta_comp_div_eq`

English:
lemma logDeriv_eta_comp_div_eq
  given: (z : ℍ)
  proof: by
  simp only [neg_div, one_div, inv_neg]
  rw [logDeriv_comp]; rw [mul_comm]
  · simp [zpow_ofNat]
  · exact differentiableAt_eta_of_mem_upperHalfPlaneSet (by grind [im_pnat_div_pos 1 z])
  · fun_prop (disch := exact z.ne_zero)

中文:
引理 logDeriv_eta_comp_div_eq
  条件: (z : ℍ)
  证明: by
  simp only [neg_div, one_div, inv_neg]
  rw [logDeriv_comp]; rw [mul_comm]
  · simp [zpow_ofNat]
  · exact differentiableAt_eta_of_mem_upperHalfPlaneSet (by grind [im_pnat_div_pos 1 z])
  · fun_prop (disch := exact z.ne_zero)

Depends on / 依赖: differentiableAt_eta_of_mem_upperHalfPlaneSet, fun_prop, im_pnat_div_pos, inv_neg, logDeriv_comp, mul_comm, ne_zero, neg_div, one_div, z.ne_zero, zpow_ofNat
-/
lemma logDeriv_eta_comp_div_eq (z : ℍ) :
    logDeriv (η ∘ (-1 / ·)) z = ((z : Complex) ^ (2 : Int))⁻¹ * logDeriv η (-z)⁻¹ := by
  simp only [neg_div, one_div, inv_neg]
  rw [logDeriv_comp]; rw [mul_comm]
  · simp [zpow_ofNat]
  · exact differentiableAt_eta_of_mem_upperHalfPlaneSet (by grind [im_pnat_div_pos 1 z])
  · fun_prop (disch := exact z.ne_zero)

open EisensteinSeries in
/--
lemma `logDeriv_eta_comp_eq_logDeriv_csqrt_eta` / 引理 `logDeriv_eta_comp_eq_logDeriv_csqrt_eta`

English:
lemma logDeriv_eta_comp_eq_logDeriv_csqrt_eta
  given: (z : ℍ)
  proof: by
  rw [logDeriv_eta_comp_div_eq z]; rw [Pi.mul_def]; rw [logDeriv_mul _ (by simp [sqrt]; rw [ne_zero z]) (eta_ne_zero z.2)
      (differentiableAt_sqrt (mem_slitPlane z))
      (differentiableAt_eta_of_mem_upperHalfPlaneSet z.2), logDeriv_apply sqrt]
  have hE2 := congrFun (E2_slash_action Modular

中文:
引理 logDeriv_eta_comp_eq_logDeriv_csqrt_eta
  条件: (z : ℍ)
  证明: by
  rw [logDeriv_eta_comp_div_eq z]; rw [Pi.mul_def]; rw [logDeriv_mul _ (by simp [sqrt]; rw [ne_zero z]) (eta_ne_zero z.2)
      (differentiableAt_sqrt (mem_slitPlane z))
      (differentiableAt_eta_of_mem_upperHalfPlaneSet z.2), logDeriv_apply sqrt]
  have hE2 := congrFun (E2_slash_action Modular

Depends on / 依赖: E2_slash_action, Int.reduceNeg, ModularGroup, ModularGroup.S, ModularGroup.denom_S, Pi.mul_def, Pi.smul_apply, Pi.sub_apply, SL_slash_def, denom_S, differentiableAt_eta_of_mem_upperHalfPlaneSet, differentiableAt_sqrt, eta_ne_zero, inv_div, logDeriv_apply, logDeriv_eta_comp_div_eq, logDeriv_mul, mem_slitPlane, modular_S_smul, mul_def
-/
lemma logDeriv_eta_comp_eq_logDeriv_csqrt_eta (z : ℍ) :
    logDeriv (η ∘ (-1 / ·)) z = logDeriv (sqrt * η) z := by
  rw [logDeriv_eta_comp_div_eq z]; rw [Pi.mul_def]; rw [logDeriv_mul _ (by simp [sqrt]; rw [ne_zero z]) (eta_ne_zero z.2)
      (differentiableAt_sqrt (mem_slitPlane z))
      (differentiableAt_eta_of_mem_upperHalfPlaneSet z.2), logDeriv_apply sqrt]
  have hE2 := congrFun (E2_slash_action ModularGroup.S) z
  simp only [one_div, SL_slash_def, modular_S_smul, ModularGroup.denom_S,
    Int.reduceNeg, zpow_neg, riemannZeta_two, mul_inv_rev, inv_div, Pi.sub_apply, Pi.smul_apply,
    D2, ModularGroup.denom_S, smul_eq_mul] at hE2
  rw [deriv_sqrt (mem_slitPlane z)]; rw [div_eq_mul_inv]; rw [logDeriv_eta_eq_E2 z]; rw [logDeriv_eta_eq_E2 (.mk _ z.im_inv_neg_coe_pos)]; rw [← mul_assoc]; rw [mul_comm]; rw [← mul_assoc]; rw [hE2]; rw [sqrt]; rw [show ModularGroup.S 1 0 = 1 by simp [ModularGroup.S]]
  transitivity 1 / z / 2 + π * I / 12 * E2 z
  · field_simp
    grind [I_sq]
  · rw [div_mul_eq_mul_div₀ _ _ (2 : Complex), neg_div, cpow_neg, ← mul_inv, ← cpow_add _ _ z.ne_zero]
    norm_num

/--
lemma `eta_comp_eqOn_const_mul_csqrt_eta` / 引理 `eta_comp_eqOn_const_mul_csqrt_eta`

English:
lemma eta_comp_eqOn_const_mul_csqrt_eta
  proof: by
  rw [← logDeriv_eqOn_iff]
  · exact fun z hz => logDeriv_eta_comp_eq_logDeriv_csqrt_eta ⟨z, hz⟩
  · apply DifferentiableOn.comp (t := upperHalfPlaneSet)
    · exact fun x hx => (differentiableAt_eta_of_mem_upperHalfPlaneSet hx).differentiableWithinAt
    · exact DifferentiableOn.div (by fun_prop

中文:
引理 eta_comp_eqOn_const_mul_csqrt_eta
  证明: by
  rw [← logDeriv_eqOn_iff]
  · exact fun z hz => logDeriv_eta_comp_eq_logDeriv_csqrt_eta ⟨z, hz⟩
  · apply DifferentiableOn.comp (t := upperHalfPlaneSet)
    · exact fun x hx => (differentiableAt_eta_of_mem_upperHalfPlaneSet hx).differentiableWithinAt
    · exact DifferentiableOn.div (by fun_prop

Depends on / 依赖: DifferentiableOn, DifferentiableOn.comp, DifferentiableOn.div, differentiableAt_eta_of_m, differentiableAt_eta_of_mem_upperHalfPlaneSet, differentiableAt_sqrt, differentiableWithinAt, fun_prop, im_pnat_div_pos, logDeriv_eqOn_iff, logDeriv_eta_comp_eq_logDeriv_csqrt_eta, mem_slitPlane, ne_zero, upperHalfPlaneSet
-/
lemma eta_comp_eqOn_const_mul_csqrt_eta :
    exists c : Complex, c != 0 ∧ upperHalfPlaneSet.EqOn (η ∘ (fun z : Complex => -1 / z)) (c • (sqrt * η)) := by
  rw [← logDeriv_eqOn_iff]
  · exact fun z hz => logDeriv_eta_comp_eq_logDeriv_csqrt_eta ⟨z, hz⟩
  · apply DifferentiableOn.comp (t := upperHalfPlaneSet)
    · exact fun x hx => (differentiableAt_eta_of_mem_upperHalfPlaneSet hx).differentiableWithinAt
    · exact DifferentiableOn.div (by fun_prop) (by fun_prop)
        (fun x hx => ne_zero (⟨x, hx⟩ : ℍ))
    · exact fun y hy => by grind [im_pnat_div_pos 1 (⟨y, hy⟩ : ℍ)]
  · exact fun x hx => ((differentiableAt_sqrt (mem_slitPlane ⟨x, hx⟩)).mul
     (differentiableAt_eta_of_mem_upperHalfPlaneSet hx)).differentiableWithinAt
  · exact isOpen_upperHalfPlaneSet
  · exact Convex.isPreconnected (convex_halfSpace_im_gt 0)
  · exact fun x hx => mul_ne_zero (by simp [sqrt, ne_zero ⟨x, hx⟩]) (eta_ne_zero hx)
  · exact fun x hx => eta_ne_zero (by grind [im_pnat_div_pos 1 ⟨x, hx⟩])

end auxiliary

public section

/--
lemma `discriminant_eq_q_prod` / 引理 `discriminant_eq_q_prod`

English:
lemma discriminant_eq_q_prod
  given: (z : ℍ)
  statement: Δ z = 𝕢 1 z * ∏' n, (1 - eta_q n z) ^ 24
  proof: by
  simp only [discriminant, eta, mul_pow]
  congr
  · simp [Periodic.qParam, ← exp_nsmul, nsmul_eq_mul, Nat.cast_ofNat]
    grind
  · exact ((multipliableLocallyUniformlyOn_eta.multipliable z.2).tprod_pow _).symm

中文:
引理 discriminant_eq_q_prod
  条件: (z : ℍ)
  结论: Δ z = 𝕢 1 z * ∏' n, (1 - eta_q n z) ^ 24
  证明: by
  simp only [discriminant, eta, mul_pow]
  congr
  · simp [Periodic.qParam, ← exp_nsmul, nsmul_eq_mul, Nat.cast_ofNat]
    grind
  · exact ((multipliableLocallyUniformlyOn_eta.multipliable z.2).tprod_pow _).symm

Depends on / 依赖: Nat.cast_ofNat, Periodic, Periodic.qParam, cast_ofNat, discriminant, exp_nsmul, mul_pow, multipliable, multipliableLocallyUniformlyOn_eta, multipliableLocallyUniformlyOn_eta.multipliable, nsmul_eq_mul, qParam, tprod_pow
-/
lemma discriminant_eq_q_prod (z : ℍ) : Δ z = 𝕢 1 z * ∏' n, (1 - eta_q n z) ^ 24 := by
  simp only [discriminant, eta, mul_pow]
  congr
  · simp [Periodic.qParam, ← exp_nsmul, nsmul_eq_mul, Nat.cast_ofNat]
    grind
  · exact ((multipliableLocallyUniformlyOn_eta.multipliable z.2).tprod_pow _).symm

/--
lemma `discriminant_ne_zero` / 引理 `discriminant_ne_zero`

English:
lemma discriminant_ne_zero
  given: (z : ℍ)
  statement: Δ z != 0
  proof: by
  simpa [discriminant] using eta_ne_zero z.2

中文:
引理 discriminant_ne_zero
  条件: (z : ℍ)
  结论: Δ z != 0
  证明: by
  simpa [discriminant] using eta_ne_zero z.2

Depends on / 依赖: discriminant, eta_ne_zero
-/
lemma discriminant_ne_zero (z : ℍ) : Δ z != 0 := by
  simpa [discriminant] using eta_ne_zero z.2

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `discriminant_T_invariant` / 引理 `discriminant_T_invariant`

English:
lemma discriminant_T_invariant
  statement: (Δ ∣[(12 : Int)] ModularGroup.T) = Δ
  proof: by
  ext z
  rw [SL_slash_apply]; rw [denom]; rw [modular_T_smul]; rw [ModularGroup.T]
  simp [discriminant_eq_q_prod, eta_q, Periodic.qParam, ← exp_periodic (2 * π * I * z)]
  ring_nf

中文:
引理 discriminant_T_invariant
  结论: (Δ ∣[(12 : 整数)] ModularGroup.T) = Δ
  证明: by
  ext z
  rw [SL_slash_apply]; rw [denom]; rw [modular_T_smul]; rw [ModularGroup.T]
  simp [discriminant_eq_q_prod, eta_q, Periodic.qParam, ← exp_periodic (2 * π * I * z)]
  ring_nf

Depends on / 依赖: ModularGroup, ModularGroup.T, Periodic, Periodic.qParam, SL_slash_apply, discriminant_eq_q_prod, eta_q, exp_periodic, modular_T_smul, qParam, ring_nf
-/
lemma discriminant_T_invariant : (Δ ∣[(12 : Int)] ModularGroup.T) = Δ := by
  ext z
  rw [SL_slash_apply]; rw [denom]; rw [modular_T_smul]; rw [ModularGroup.T]
  simp [discriminant_eq_q_prod, eta_q, Periodic.qParam, ← exp_periodic (2 * π * I * z)]
  ring_nf

/--
lemma `eta_comp_eq_csqrt_I_inv` / 引理 `eta_comp_eq_csqrt_I_inv`

English:
lemma eta_comp_eq_csqrt_I_inv
  statement: upperHalfPlaneSet.EqOn
  proof: by
  obtain ⟨z, hz, h⟩ := eta_comp_eqOn_const_mul_csqrt_eta
  have h3 : η I = z * sqrt I * η I := by simpa [← mul_assoc] using h (show I in _ by simp)
  grind [sqrt, eta_ne_zero (show 0 < I.im by simp)]

中文:
引理 eta_comp_eq_csqrt_I_inv
  结论: upperHalfPlaneSet.EqOn
  证明: by
  obtain ⟨z, hz, h⟩ := eta_comp_eqOn_const_mul_csqrt_eta
  have h3 : η I = z * sqrt I * η I := by simpa [← mul_assoc] using h (show I in _ by simp)
  grind [sqrt, eta_ne_zero (show 0 < I.im by simp)]

Depends on / 依赖: I.im, eta_comp_eqOn_const_mul_csqrt_eta, eta_ne_zero, mul_assoc
-/
lemma eta_comp_eq_csqrt_I_inv : upperHalfPlaneSet.EqOn
    (η ∘ (-1 / ·)) ((sqrt I)⁻¹ • (sqrt * η)) := by
  obtain ⟨z, hz, h⟩ := eta_comp_eqOn_const_mul_csqrt_eta
  have h3 : η I = z * sqrt I * η I := by simpa [← mul_assoc] using h (show I in _ by simp)
  grind [sqrt, eta_ne_zero (show 0 < I.im by simp)]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `discriminant_S_invariant` / 引理 `discriminant_S_invariant`

English:
lemma discriminant_S_invariant
  statement: (Δ ∣[(12 : Int)] ModularGroup.S) = Δ
  proof: by
  ext z
  suffices η (-(↑z)⁻¹) ^ 24 * ((z : Complex) ^ 12)⁻¹ = η z ^ 24 by
    rw [SL_slash_apply]; rw [UpperHalfPlane.modular_S_smul]
    simpa [denom, ModularGroup.S]
  have he : η (-(↑z)⁻¹) = (sqrt I)⁻¹ * (sqrt z * η z) := by
    simpa [neg_div] using eta_comp_eq_csqrt_I_inv z.2
  simp only [h

中文:
引理 discriminant_S_invariant
  结论: (Δ ∣[(12 : 整数)] ModularGroup.S) = Δ
  证明: by
  ext z
  suffices η (-(↑z)⁻¹) ^ 24 * ((z : Complex) ^ 12)⁻¹ = η z ^ 24 by
    rw [SL_slash_apply]; rw [UpperHalfPlane.modular_S_smul]
    simpa [denom, ModularGroup.S]
  have he : η (-(↑z)⁻¹) = (sqrt I)⁻¹ * (sqrt z * η z) := by
    simpa [neg_div] using eta_comp_eq_csqrt_I_inv z.2
  simp only [h

Depends on / 依赖: ModularGroup, ModularGroup.S, SL_slash_apply, UpperHalfPlane, UpperHalfPlane.modular_S_smul, csqrt_I_pow_24, csqrt_pow_24_eq, eta_comp_eq_csqrt_I_inv, inv_pow, modular_S_smul, mul_pow, ne_zero, neg_div, z.ne_zero
-/
lemma discriminant_S_invariant : (Δ ∣[(12 : Int)] ModularGroup.S) = Δ := by
  ext z
  suffices η (-(↑z)⁻¹) ^ 24 * ((z : Complex) ^ 12)⁻¹ = η z ^ 24 by
    rw [SL_slash_apply]; rw [UpperHalfPlane.modular_S_smul]
    simpa [denom, ModularGroup.S]
  have he : η (-(↑z)⁻¹) = (sqrt I)⁻¹ * (sqrt z * η z) := by
    simpa [neg_div] using eta_comp_eq_csqrt_I_inv z.2
  simp only [he, mul_pow, mul_pow, inv_pow, csqrt_I_pow_24, csqrt_pow_24_eq (ne_zero z)]
  field_simp [z.ne_zero]

/--
lemma `tendsto_atImInfty_tprod_one_sub_eta_q_pow` / 引理 `tendsto_atImInfty_tprod_one_sub_eta_q_pow`

English:
lemma tendsto_atImInfty_tprod_one_sub_eta_q_pow
  proof: by
  have htprod : Tendsto (fun q : Complex => ∏' (n : Nat), (1 - q ^ (n + 1))) (𝓝 0) (𝓝 1) := by
    have := tendsto_tprod_one_add_of_dominated_convergence (𝓕 := 𝓝 0) (g := 0)
      (f := fun (q : Complex) (n : Nat) => -q ^ (n + 1)) (bound := fun n => (1 / 2 : Real) ^ (n + 1))
    simp only [Pi.zer

中文:
引理 tendsto_atImInfty_tprod_one_sub_eta_q_pow
  证明: by
  have htprod : Tendsto (fun q : Complex => ∏' (n : Nat), (1 - q ^ (n + 1))) (𝓝 0) (𝓝 1) := by
    have := tendsto_tprod_one_add_of_dominated_convergence (𝓕 := 𝓝 0) (g := 0)
      (f := fun (q : Complex) (n : Nat) => -q ^ (n + 1)) (bound := fun n => (1 / 2 : Real) ^ (n + 1))
    simp only [Pi.zer

Depends on / 依赖: Pi.zero_apply, Tendsto, add_zero, htprod, mul_left, norm_neg, norm_pow, pow_succ, simp_rw, sub_eq_add_neg, summable_geometric_of_abs_lt_one, tendsto_tprod_one_add_of_dominated_convergence, tprod_one, zero_apply
-/
lemma tendsto_atImInfty_tprod_one_sub_eta_q_pow :
    Tendsto (fun x : ℍ => ∏' (n : Nat), (1 - eta_q n x) ^ 24) atImInfty (𝓝 1) := by
  have htprod : Tendsto (fun q : Complex => ∏' (n : Nat), (1 - q ^ (n + 1))) (𝓝 0) (𝓝 1) := by
    have := tendsto_tprod_one_add_of_dominated_convergence (𝓕 := 𝓝 0) (g := 0)
      (f := fun (q : Complex) (n : Nat) => -q ^ (n + 1)) (bound := fun n => (1 / 2 : Real) ^ (n + 1))
    simp only [Pi.zero_apply, norm_neg, norm_pow, add_zero, tprod_one] at this
    simp_rw [sub_eq_add_neg]
    refine this
      (by simpa only [pow_succ'] using (summable_geometric_of_abs_lt_one (by norm_num)).mul_left _)
      (fun k => by simpa using ((continuous_pow (M := Complex) (k + 1)).tendsto 0).neg) ?_
    filter_upwards [Metric.ball_mem_nhds (0 : Complex) (by norm_num : (0 : Real) < 1 / 2)] with q hq k
    exact pow_le_pow_left₀ (norm_nonneg _) (mem_ball_zero_iff.mp hq).le _
  have := (htprod.comp (UpperHalfPlane.qParam_tendsto_atImInfty zero_lt_one)).pow 24
  simp only [Periodic.qParam, ofReal_one, div_one, comp_apply, one_pow, eta_q] at *
  convert! this using 2 with τ
  rw [Multipliable.tprod_pow]
  apply (multipliableLocallyUniformlyOn_eta.multipliable τ.2).congr
  simp [eta_q, Periodic.qParam, ← exp_nat_mul]

@[deprecated (since := "2026-04-30")]
alias discriminant_bounded_factor := tendsto_atImInfty_tprod_one_sub_eta_q_pow

/--
lemma `discriminant_isZeroAtImInfty` / 引理 `discriminant_isZeroAtImInfty`

English:
lemma discriminant_isZeroAtImInfty
  statement: IsZeroAtImInfty Δ
  proof: by
  apply Tendsto.congr (fun z => (discriminant_eq_q_prod z).symm)
  rw [show (0 : Complex) = 0 * 1 by ring]
  exact (qParam_tendsto_atImInfty zero_lt_one).mul
    (tendsto_atImInfty_tprod_one_sub_eta_q_pow.congr fun z => by congr 1)

中文:
引理 discriminant_isZeroAtImInfty
  结论: IsZeroAtImInfty Δ
  证明: by
  apply Tendsto.congr (fun z => (discriminant_eq_q_prod z).symm)
  rw [show (0 : Complex) = 0 * 1 by ring]
  exact (qParam_tendsto_atImInfty zero_lt_one).mul
    (tendsto_atImInfty_tprod_one_sub_eta_q_pow.congr fun z => by congr 1)

Depends on / 依赖: Tendsto, Tendsto.congr, discriminant_eq_q_prod, qParam_tendsto_atImInfty, tendsto_atImInfty_tprod_one_sub_eta_q_pow, tendsto_atImInfty_tprod_one_sub_eta_q_pow.congr, zero_lt_one
-/
lemma discriminant_isZeroAtImInfty : IsZeroAtImInfty Δ := by
  apply Tendsto.congr (fun z => (discriminant_eq_q_prod z).symm)
  rw [show (0 : Complex) = 0 * 1 by ring]
  exact (qParam_tendsto_atImInfty zero_lt_one).mul
    (tendsto_atImInfty_tprod_one_sub_eta_q_pow.congr fun z => by congr 1)

/--
lemma `exp_isBigO_discriminant` / 引理 `exp_isBigO_discriminant`

English:
lemma exp_isBigO_discriminant
  statement: (fun τ => Real.exp (-2 * π * τ.im)) =O[atImInfty] Δ
  proof: by
  refine .of_bound 2 ?_
  have hprod := tendsto_atImInfty_tprod_one_sub_eta_q_pow.eventually
    (Metric.ball_mem_nhds 1 (by norm_num : (0 : Real) < 1/2))
  filter_upwards [hprod] with τ hτ
  rw [discriminant_eq_q_prod]; rw [norm_mul]; rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  have hq_norm :

中文:
引理 exp_isBigO_discriminant
  结论: (fun τ => 实数.exp (-2 * π * τ.im)) =O[atImInfty] Δ
  证明: by
  refine .of_bound 2 ?_
  have hprod := tendsto_atImInfty_tprod_one_sub_eta_q_pow.eventually
    (Metric.ball_mem_nhds 1 (by norm_num : (0 : Real) < 1/2))
  filter_upwards [hprod] with τ hτ
  rw [discriminant_eq_q_prod]; rw [norm_mul]; rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  have hq_norm :

Depends on / 依赖: Complex.norm_exp, Metric, Metric.ball_mem_nhds, Periodic, Periodic.qParam, Real.exp, Real.exp_pos, Real.norm_of_nonneg, ball_mem_nhds, discriminant_eq_q_prod, eta_q, eventually, exp_pos, filter_upwards, hprod_bound, hq_norm, norm_exp, norm_mul, norm_of_nonneg, of_bound
-/
lemma exp_isBigO_discriminant : (fun τ => Real.exp (-2 * π * τ.im)) =O[atImInfty] Δ := by
  refine .of_bound 2 ?_
  have hprod := tendsto_atImInfty_tprod_one_sub_eta_q_pow.eventually
    (Metric.ball_mem_nhds 1 (by norm_num : (0 : Real) < 1/2))
  filter_upwards [hprod] with τ hτ
  rw [discriminant_eq_q_prod]; rw [norm_mul]; rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  have hq_norm : ‖𝕢 1 τ‖ = Real.exp (-2 * π * τ.im) := by simp [Periodic.qParam, Complex.norm_exp]
  rw [← hq_norm]
  have hprod_bound : 1 / 2 <= ‖∏' n, (1 - eta_q n τ) ^ 24‖ := by
    have hsub : ‖∏' n, (1 - eta_q n τ) ^ 24 - 1‖ < 1 / 2 := by rwa [Complex.dist_eq] at hτ
    have h1 := norm_sub_norm_le 1 (∏' n, (1 - eta_q n τ) ^ 24)
    grind [norm_one, norm_sub_rev]
  linarith [norm_nonneg (𝕢 1 τ), mul_le_mul_of_nonneg_left hprod_bound (norm_nonneg (𝕢 1 τ))]

/--
lemma `discriminant_cuspFunction_eqOn` / 引理 `discriminant_cuspFunction_eqOn`

English:
lemma discriminant_cuspFunction_eqOn
  statement: Set.EqOn (cuspFunction 1 Δ)
  proof: by
  intro q hq
  by_cases hq0 : q = 0
  · simpa [hq0] using! Periodic.cuspFunction_zero_of_zero_at_inf one_pos
      discriminant_isZeroAtImInfty.zero_at_infty_comp_ofComplex
  · have him := Periodic.im_invQParam_pos_of_norm_lt_one one_pos
      (by simpa [dist_zero_right] using hq) hq0
    simp [c

中文:
引理 discriminant_cuspFunction_eqOn
  结论: 集合.EqOn (cuspFunction 1 Δ)
  证明: by
  intro q hq
  by_cases hq0 : q = 0
  · simpa [hq0] using! Periodic.cuspFunction_zero_of_zero_at_inf one_pos
      discriminant_isZeroAtImInfty.zero_at_infty_comp_ofComplex
  · have him := Periodic.im_invQParam_pos_of_norm_lt_one one_pos
      (by simpa [dist_zero_right] using hq) hq0
    simp [c

Depends on / 依赖: Periodic, Periodic.cuspFunction_eq_of_nonzero, Periodic.cuspFunction_zero_of_zero_at_inf, Periodic.im_invQParam_pos_of_norm_lt_one, Periodic.qParam_right_inv, cuspFunction, cuspFunction_eq_of_nonzero, cuspFunction_zero_of_zero_at_inf, discriminant_eq_q_prod, discriminant_isZeroAtImInfty, discriminant_isZeroAtImInfty.zero_at_infty_comp_ofComplex, dist_zero_right, eta_q, im_invQParam_pos_of_norm_lt_one, ofComplex_apply_of_im_pos, one_ne_zero, one_pos, qParam_right_inv, zero_at_infty_comp_ofComplex
-/
lemma discriminant_cuspFunction_eqOn : Set.EqOn (cuspFunction 1 Δ)
    (fun q => q * ∏' i, (1 - q ^ (i + 1)) ^ 24) (Metric.ball 0 1) := by
  intro q hq
  by_cases hq0 : q = 0
  · simpa [hq0] using! Periodic.cuspFunction_zero_of_zero_at_inf one_pos
      discriminant_isZeroAtImInfty.zero_at_infty_comp_ofComplex
  · have him := Periodic.im_invQParam_pos_of_norm_lt_one one_pos
      (by simpa [dist_zero_right] using hq) hq0
    simp [cuspFunction, Periodic.cuspFunction_eq_of_nonzero 1 _ hq0,
      ofComplex_apply_of_im_pos him, discriminant_eq_q_prod ⟨_, him⟩,
      Periodic.qParam_right_inv one_ne_zero hq0, eta_q]

/--
lemma `discriminant_qExpansion_coeff_one` / 引理 `discriminant_qExpansion_coeff_one`

English:
lemma discriminant_qExpansion_coeff_one
  statement: (qExpansion 1 Δ).coeff 1 = 1
  proof: by
  have hmem : (0 : Complex) in Metric.ball (0 : Complex) 1 := Metric.mem_ball_self one_pos
  calc (qExpansion 1 Δ).coeff 1
      = derivWithin (cuspFunction 1 Δ) (Metric.ball 0 1) 0 := by
        simp [qExpansion_coeff, ← derivWithin_of_isOpen Metric.isOpen_ball hmem]
    _ = derivWithin (fun q =

中文:
引理 discriminant_qExpansion_coeff_one
  结论: (qExpansion 1 Δ).coeff 1 = 1
  证明: by
  have hmem : (0 : Complex) in Metric.ball (0 : Complex) 1 := Metric.mem_ball_self one_pos
  calc (qExpansion 1 Δ).coeff 1
      = derivWithin (cuspFunction 1 Δ) (Metric.ball 0 1) 0 := by
        simp [qExpansion_coeff, ← derivWithin_of_isOpen Metric.isOpen_ball hmem]
    _ = derivWithin (fun q =

Depends on / 依赖: Metric, Metric.ball, Metric.isOpen_ball, Metric.mem_ball_self, cuspFunction, derivWithin, derivWithin_congr, derivWithin_fun_mul, derivWithin_of_isOpen, differe, differentiableWithinAt_fun_id, discriminant_cuspFunction_eqOn, isOpen_ball, mem_ball_self, one_pos, qExpansion, qExpansion_coeff
-/
lemma discriminant_qExpansion_coeff_one : (qExpansion 1 Δ).coeff 1 = 1 := by
  have hmem : (0 : Complex) in Metric.ball (0 : Complex) 1 := Metric.mem_ball_self one_pos
  calc (qExpansion 1 Δ).coeff 1
      = derivWithin (cuspFunction 1 Δ) (Metric.ball 0 1) 0 := by
        simp [qExpansion_coeff, ← derivWithin_of_isOpen Metric.isOpen_ball hmem]
    _ = derivWithin (fun q => q * ∏' i, (1 - q ^ (i + 1)) ^ 24) (Metric.ball 0 1) 0 :=
        derivWithin_congr discriminant_cuspFunction_eqOn (discriminant_cuspFunction_eqOn hmem)
    _ = 1 := by
        simp [derivWithin_fun_mul differentiableWithinAt_fun_id
          (differentiableOn_tprod_one_sub_pow_pow 24 _ hmem),
          derivWithin_id' _ _ (Metric.isOpen_ball.uniqueDiffWithinAt hmem)]

end

end ModularForm

public section

namespace CuspForm

open ModularForm

local notation "Δ" => ModularForm.discriminant

/--
Definition of `discriminant` / `discriminant` 的定义

English:
definition discriminant
  signature: : CuspForm 𝒮ℒ 12 where
  body: Δ
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact slash_action_generators_SL2Z discriminant_S_invariant discriminant_T_invariant A
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine .congr (fun z hz => (differentiableAt_eta_of_mem_upperHalfPlaneSet hz).pow
.differ

中文:
定义 discriminant
  签名: : 尖点形式 𝒮ℒ 12 where
  定义体: Δ
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact slash_action_generators_SL2Z discriminant_S_invariant discriminant_T_invariant A
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine .congr (fun z hz => (differentiableAt_eta_of_mem_upperHalfPlaneSet hz).pow
.differ
-/
@[expose] def discriminant : CuspForm 𝒮ℒ 12 where
  toFun := Δ
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact slash_action_generators_SL2Z discriminant_S_invariant discriminant_T_invariant A
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine .congr (fun z hz => (differentiableAt_eta_of_mem_upperHalfPlaneSet hz).pow
.differentiableWithinAt) fun z hz => ?_ 24
    simp [ModularForm.discriminant, ofComplex_apply_of_im_pos hz]
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [slash_action_generators_SL2Z discriminant_S_invariant discriminant_T_invariant]
    exact discriminant_isZeroAtImInfty

@[simp]
/--
lemma `coe_discriminant` / 引理 `coe_discriminant`

English:
lemma coe_discriminant
  statement: discriminant = Δ
  proof: rfl

中文:
引理 coe_discriminant
  结论: discriminant = Δ
  证明: rfl
-/
lemma coe_discriminant : discriminant = Δ := rfl

variable {k : Int}

/--
lemma `exp_decay_isBigO_discriminant` / 引理 `exp_decay_isBigO_discriminant`

English:
lemma exp_decay_isBigO_discriminant
  given: (f : CuspForm 𝒮ℒ k)
  proof: (CuspFormClass.exp_decay_atImInfty (h := 1) f one_pos one_mem_strictPeriods_SL).trans
    (by simpa using exp_isBigO_discriminant)

中文:
引理 exp_decay_isBigO_discriminant
  条件: (f : 尖点形式 𝒮ℒ k)
  证明: (CuspFormClass.exp_decay_atImInfty (h := 1) f one_pos one_mem_strictPeriods_SL).trans
    (by simpa using exp_isBigO_discriminant)

Depends on / 依赖: CuspFormClass, CuspFormClass.exp_decay_atImInfty, exp_decay_atImInfty, exp_isBigO_discriminant, one_mem_strictPeriods_SL, one_pos
-/
lemma exp_decay_isBigO_discriminant (f : CuspForm 𝒮ℒ k) :
    f =O[atImInfty] ModularForm.discriminant :=
  (CuspFormClass.exp_decay_atImInfty (h := 1) f one_pos one_mem_strictPeriods_SL).trans
    (by simpa using exp_isBigO_discriminant)

end CuspForm

@[deprecated CuspForm.discriminant (since := "2026-04-30")]
alias ModularForm.discriminantCuspForm := CuspForm.discriminant

end
