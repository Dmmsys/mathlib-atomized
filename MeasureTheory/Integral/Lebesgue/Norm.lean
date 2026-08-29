/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Interactions between the Lebesgue integral and norms
-/

public section

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/--
theorem `lintegral_ofReal_le_lintegral_enorm` / 定理 `lintegral_ofReal_le_lintegral_enorm`

English:
theorem lintegral_ofReal_le_lintegral_enorm
  given: (f : α -> Real)
  proof: by
  simp_rw [← ofReal_norm]
  refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
  rw [Real.norm_eq_abs]
  exact le_abs_self (f x)

中文:
定理 lintegral_ofReal_le_lintegral_enorm
  条件: (f : α -> 实数)
  证明: by
  simp_rw [← ofReal_norm]
  refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
  rw [Real.norm_eq_abs]
  exact le_abs_self (f x)

Depends on / 依赖: ENNReal, ENNReal.ofReal_le_ofReal, Real.norm_eq_abs, le_abs_self, lintegral_mono, norm_eq_abs, ofReal_le_ofReal, ofReal_norm, simp_rw
-/
theorem lintegral_ofReal_le_lintegral_enorm (f : α -> Real) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ <= ∫⁻ x, ‖f x‖ₑ ∂μ := by
  simp_rw [← ofReal_norm]
  refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
  rw [Real.norm_eq_abs]
  exact le_abs_self (f x)

/--
theorem `lintegral_enorm_of_ae_nonneg` / 定理 `lintegral_enorm_of_ae_nonneg`

English:
theorem lintegral_enorm_of_ae_nonneg
  given: {f : α -> Real} (h_nonneg : 0 <=ᵐ[μ] f)
  proof: by
  apply lintegral_congr_ae
  filter_upwards [h_nonneg] with x hx
  rw [Real.enorm_eq_ofReal hx]

中文:
定理 lintegral_enorm_of_ae_nonneg
  条件: {f : α -> 实数} (h_nonneg : 0 <=ᵐ[μ] f)
  证明: by
  apply lintegral_congr_ae
  filter_upwards [h_nonneg] with x hx
  rw [Real.enorm_eq_ofReal hx]

Depends on / 依赖: Real.enorm_eq_ofReal, enorm_eq_ofReal, filter_upwards, h_nonneg, lintegral_congr_ae
-/
theorem lintegral_enorm_of_ae_nonneg {f : α -> Real} (h_nonneg : 0 <=ᵐ[μ] f) :
    ∫⁻ x, ‖f x‖ₑ ∂μ = ∫⁻ x, .ofReal (f x) ∂μ := by
  apply lintegral_congr_ae
  filter_upwards [h_nonneg] with x hx
  rw [Real.enorm_eq_ofReal hx]

/--
theorem `lintegral_enorm_of_nonneg` / 定理 `lintegral_enorm_of_nonneg`

English:
theorem lintegral_enorm_of_nonneg
  given: {f : α -> Real} (h_nonneg : 0 <= f)
  proof: lintegral_enorm_of_ae_nonneg .of_forall h_nonneg

中文:
定理 lintegral_enorm_of_nonneg
  条件: {f : α -> 实数} (h_nonneg : 0 <= f)
  证明: lintegral_enorm_of_ae_nonneg .of_forall h_nonneg

Depends on / 依赖: h_nonneg, lintegral_enorm_of_ae_nonneg, of_forall
-/
theorem lintegral_enorm_of_nonneg {f : α -> Real} (h_nonneg : 0 <= f) :
    ∫⁻ x, ‖f x‖ₑ ∂μ = ∫⁻ x, .ofReal (f x) ∂μ :=
lintegral_enorm_of_ae_nonneg .of_forall h_nonneg

end MeasureTheory
