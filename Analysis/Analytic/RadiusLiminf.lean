/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Representation of `FormalMultilinearSeries.radius` as a `liminf`

In this file we prove that the radius of convergence of a `FormalMultilinearSeries` is equal to
$\liminf_{n\to\infty} \frac{1}{\sqrt[n]{‖p n‖}}$. This lemma can't go to `Analysis.Analytic.Basic`
because this would create a circular dependency once we redefine `exp` using
`FormalMultilinearSeries`.
-/

public section


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open scoped Topology NNReal ENNReal

open Filter Asymptotics

namespace FormalMultilinearSeries

variable (p : FormalMultilinearSeries 𝕜 E F)

/--
theorem `radius_eq_liminf` / 定理 `radius_eq_liminf`

English:
theorem radius_eq_liminf
  proof: by
  have :
    forall (r : Real>=0) {n},
      0 < n -> ((r : Real>=0∞) <= 1 / ↑(‖p n‖₊ ^ (1 / (n : Real))) ↔ ‖p n‖₊ * r ^ n <= 1) := by
    intro r n hn
    have : 0 < (n : Real) := Nat.cast_pos.2 hn
    conv_lhs =>
      rw [one_div]; rw [ENNReal.le_inv_iff_mul_le]; rw [← ENNReal.coe_mul]; rw [ENNReal.coe_le_one_iff]; rw [one_div]; rw [←
        NNReal.rpow_one r]; rw [← mul_inv_cancel₀ this.ne']; rw [NNReal.rpow_mul]; rw [← NNReal.mul_rpow]; rw [←
        NNReal.one_rpow n⁻¹]; rw [NNReal.rpow_le_rpow_iff (inv_pos.2 this)]; rw [mul_comm]; rw [NNReal.rpow_natCast]
  apply le_antisymm <;> refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  · have := ((TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * r ^ n) 1).out 1 7).1
      (p.isLittleO_of_lt_radius hr)
    obtain ⟨a, ha, H⟩ := this
    apply le_liminf_of_le
    · infer_param
    · rw [← eventually_map]
      refine
        H.mp ((eventually_gt_atTop 0).mono fun n hn₀ hn => (this _ hn₀).2 (NNReal.coe_le_coe.1 ?_))
      push_cast
      exact (le_abs_self _).trans (hn.trans (pow_le_one₀ ha.1.le ha.2.le))
· refine p.le_radius_of_isBigO .of_norm_eventuallyLE ?_
    filter_upwards [eventually_lt_of_lt_liminf hr, eventually_gt_atTop 0] with n hn hn₀
    simpa using NNReal.coe_le_coe.2 ((this _ hn₀).1 hn.le)

中文:
定理 radius_eq_liminf
  证明: by
  have :
    forall (r : Real>=0) {n},
      0 < n -> ((r : Real>=0∞) <= 1 / ↑(‖p n‖₊ ^ (1 / (n : Real))) ↔ ‖p n‖₊ * r ^ n <= 1) := by
    intro r n hn
    have : 0 < (n : Real) := Nat.cast_pos.2 hn
    conv_lhs =>
      rw [one_div]; rw [ENNReal.le_inv_iff_mul_le]; rw [← ENNReal.coe_mul]; rw [ENNReal.coe_le_one_iff]; rw [one_div]; rw [←
        NNReal.rpow_one r]; rw [← mul_inv_cancel₀ this.ne']; rw [NNReal.rpow_mul]; rw [← NNReal.mul_rpow]; rw [←
        NNReal.one_rpow n⁻¹]; rw [NNReal.rpow_le_rpow_iff (inv_pos.2 this)]; rw [mul_comm]; rw [NNReal.rpow_natCast]
  apply le_antisymm <;> refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  · have := ((TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * r ^ n) 1).out 1 7).1
      (p.isLittleO_of_lt_radius hr)
    obtain ⟨a, ha, H⟩ := this
    apply le_liminf_of_le
    · infer_param
    · rw [← eventually_map]
      refine
        H.mp ((eventually_gt_atTop 0).mono fun n hn₀ hn => (this _ hn₀).2 (NNReal.coe_le_coe.1 ?_))
      push_cast
      exact (le_abs_self _).trans (hn.trans (pow_le_one₀ ha.1.le ha.2.le))
· refine p.le_radius_of_isBigO .of_norm_eventuallyLE ?_
    filter_upwards [eventually_lt_of_lt_liminf hr, eventually_gt_atTop 0] with n hn hn₀
    simpa using NNReal.coe_le_coe.2 ((this _ hn₀).1 hn.le)

Depends on / 依赖: ENNReal, ENNReal.coe_le_one_iff, ENNReal.coe_mul, ENNReal.le_inv_iff_mul_le, NNReal, NNReal.mul_rpow, NNReal.one_rpow, NNReal.rpow_le_rpow_iff, NNReal.rpow_mul, NNReal.rpow_one, Nat.cast_pos, cast_pos, coe_le_one_iff, coe_mul, conv_lhs, inv_pos, le_inv_iff_mul_le, mul_comm, mul_rpow, one_div
-/
theorem radius_eq_liminf :
    p.radius = liminf (fun n => (1 / (‖p n‖₊ ^ (1 / (n : Real)) : Real>=0) : Real>=0∞)) atTop := by
  have :
    forall (r : Real>=0) {n},
      0 < n -> ((r : Real>=0∞) <= 1 / ↑(‖p n‖₊ ^ (1 / (n : Real))) ↔ ‖p n‖₊ * r ^ n <= 1) := by
    intro r n hn
    have : 0 < (n : Real) := Nat.cast_pos.2 hn
    conv_lhs =>
      rw [one_div]; rw [ENNReal.le_inv_iff_mul_le]; rw [← ENNReal.coe_mul]; rw [ENNReal.coe_le_one_iff]; rw [one_div]; rw [←
        NNReal.rpow_one r]; rw [← mul_inv_cancel₀ this.ne']; rw [NNReal.rpow_mul]; rw [← NNReal.mul_rpow]; rw [←
        NNReal.one_rpow n⁻¹]; rw [NNReal.rpow_le_rpow_iff (inv_pos.2 this)]; rw [mul_comm]; rw [NNReal.rpow_natCast]
  apply le_antisymm <;> refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  · have := ((TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * r ^ n) 1).out 1 7).1
      (p.isLittleO_of_lt_radius hr)
    obtain ⟨a, ha, H⟩ := this
    apply le_liminf_of_le
    · infer_param
    · rw [← eventually_map]
      refine
        H.mp ((eventually_gt_atTop 0).mono fun n hn₀ hn => (this _ hn₀).2 (NNReal.coe_le_coe.1 ?_))
      push_cast
      exact (le_abs_self _).trans (hn.trans (pow_le_one₀ ha.1.le ha.2.le))
· refine p.le_radius_of_isBigO .of_norm_eventuallyLE ?_
    filter_upwards [eventually_lt_of_lt_liminf hr, eventually_gt_atTop 0] with n hn hn₀
    simpa using NNReal.coe_le_coe.2 ((this _ hn₀).1 hn.le)

/--
theorem `radius_inv_eq_limsup` / 定理 `radius_inv_eq_limsup`

English:
theorem radius_inv_eq_limsup
  proof: by
  simpa [ENNReal.inv_liminf] using congr($(p.radius_eq_liminf)⁻¹)

中文:
定理 radius_inv_eq_limsup
  证明: by
  simpa [ENNReal.inv_liminf] using congr($(p.radius_eq_liminf)⁻¹)

Depends on / 依赖: ENNReal, ENNReal.inv_liminf, inv_liminf, p.radius_eq_liminf, radius_eq_liminf
-/
theorem radius_inv_eq_limsup :
    p.radius⁻¹ = limsup (fun n => ((‖p n‖₊ ^ (1 / (n : Real)) : Real>=0) : Real>=0∞)) atTop := by
  simpa [ENNReal.inv_liminf] using congr($(p.radius_eq_liminf)⁻¹)

end FormalMultilinearSeries
