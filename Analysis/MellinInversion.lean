/-
Copyright (c) 2024 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/
module

public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.MellinTransform

/-!
# Mellin inversion formula

We derive the Mellin inversion formula as a consequence of the Fourier inversion formula.

## Main results
- `mellin_inversion`: The inverse Mellin transform of the Mellin transform applied to `x > 0` is x.
-/

public section

open Real Complex Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E]

open scoped FourierTransform

/--
theorem `rexp_neg_deriv_aux` / 定理 `rexp_neg_deriv_aux`

English:
theorem rexp_neg_deriv_aux
  proof: fun x _ => mul_neg_one (rexp (-x)) ▸
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt

中文:
定理 rexp_neg_deriv_aux
  证明: fun x _ => mul_neg_one (rexp (-x)) ▸
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt
-/
private theorem rexp_neg_deriv_aux :
    forall x in univ, HasDerivWithinAt (rexp ∘ Neg.neg) (-rexp (-x)) univ x :=
  fun x _ => mul_neg_one (rexp (-x)) ▸
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt

/--
theorem `rexp_neg_image_aux` / 定理 `rexp_neg_image_aux`

English:
theorem rexp_neg_image_aux
  statement: rexp ∘ Neg.neg '' univ = Ioi 0
  proof: by
  rw [Set.image_comp]; rw [Set.image_univ_of_surjective neg_surjective]; rw [Set.image_univ]; rw [Real.range_exp]

中文:
定理 rexp_neg_image_aux
  结论: rexp ∘ Neg.neg '' univ = Ioi 0
  证明: by
  rw [Set.image_comp]; rw [Set.image_univ_of_surjective neg_surjective]; rw [Set.image_univ]; rw [Real.range_exp]
-/
private theorem rexp_neg_image_aux : rexp ∘ Neg.neg '' univ = Ioi 0 := by
  rw [Set.image_comp]; rw [Set.image_univ_of_surjective neg_surjective]; rw [Set.image_univ]; rw [Real.range_exp]

/--
theorem `rexp_neg_injOn_aux` / 定理 `rexp_neg_injOn_aux`

English:
theorem rexp_neg_injOn_aux
  statement: univ.InjOn (rexp ∘ Neg.neg)
  proof: Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)

中文:
定理 rexp_neg_injOn_aux
  结论: univ.InjOn (rexp ∘ Neg.neg)
  证明: Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)
-/
private theorem rexp_neg_injOn_aux : univ.InjOn (rexp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)

/--
theorem `rexp_cexp_aux` / 定理 `rexp_cexp_aux`

English:
theorem rexp_cexp_aux
  given: (x : Real) (s : Complex) (f : E)
  proof: by
  change (rexp (-x) : Complex) • _ = _ • f
  rw [← smul_assoc]; rw [smul_eq_mul]
  push_cast
  conv in cexp _ * _ => lhs; rw [← cpow_one (cexp _)]
  rw [← cpow_add _ _ (Complex.exp_ne_zero _)]; rw [cpow_def_of_ne_zero (Complex.exp_ne_zero _)]; rw [Complex.log_exp (by simp [pi_pos]) (by simpa usin

中文:
定理 rexp_cexp_aux
  条件: (x : 实数) (s : Complex) (f : E)
  证明: by
  change (rexp (-x) : Complex) • _ = _ • f
  rw [← smul_assoc]; rw [smul_eq_mul]
  push_cast
  conv in cexp _ * _ => lhs; rw [← cpow_one (cexp _)]
  rw [← cpow_add _ _ (Complex.exp_ne_zero _)]; rw [cpow_def_of_ne_zero (Complex.exp_ne_zero _)]; rw [Complex.log_exp (by simp [pi_pos]) (by simpa usin
-/
private theorem rexp_cexp_aux (x : Real) (s : Complex) (f : E) :
    rexp (-x) • cexp (-↑x) ^ (s - 1) • f = cexp (-s * ↑x) • f := by
  change (rexp (-x) : Complex) • _ = _ • f
  rw [← smul_assoc]; rw [smul_eq_mul]
  push_cast
  conv in cexp _ * _ => lhs; rw [← cpow_one (cexp _)]
  rw [← cpow_add _ _ (Complex.exp_ne_zero _)]; rw [cpow_def_of_ne_zero (Complex.exp_ne_zero _)]; rw [Complex.log_exp (by simp [pi_pos]) (by simpa using pi_nonneg)]
  ring_nf

/--
theorem `mellin_eq_fourier` / 定理 `mellin_eq_fourier`

English:
theorem mellin_eq_fourier
  given: (f : Real -> E) {s : Complex}
  proof: calc
    mellin f s
      = ∫ (u : Real), Complex.exp (-s * u) • f (Real.exp (-u)) := by
      rw [mellin]; rw [← rexp_neg_image_aux]; rw [integral_image_eq_integral_abs_deriv_smul
        MeasurableSet.univ rexp_neg_deriv_aux rexp_neg_injOn_aux]
      simp [rexp_cexp_aux]
    _ = ∫ (u : Real), Comp

中文:
定理 mellin_eq_fourier
  条件: (f : 实数 -> E) {s : Complex}
  证明: calc
    mellin f s
      = ∫ (u : Real), Complex.exp (-s * u) • f (Real.exp (-u)) := by
      rw [mellin]; rw [← rexp_neg_image_aux]; rw [integral_image_eq_integral_abs_deriv_smul
        MeasurableSet.univ rexp_neg_deriv_aux rexp_neg_injOn_aux]
      simp [rexp_cexp_aux]
    _ = ∫ (u : Real), Comp

Depends on / 依赖: Complex.exp, MeasurableSet, MeasurableSet.univ, Real.exp, integral_image_eq_integral_abs_deriv_smul, mellin, neg_a, re_add_im, rexp_cexp_aux, rexp_neg_deriv_aux, rexp_neg_image_aux, rexp_neg_injOn_aux, s.im, s.re
-/
theorem mellin_eq_fourier (f : Real -> E) {s : Complex} :
    mellin f s = 𝓕 (fun (u : Real) => (Real.exp (-s.re * u) • f (Real.exp (-u)))) (s.im / (2 * π)) :=
  calc
    mellin f s
      = ∫ (u : Real), Complex.exp (-s * u) • f (Real.exp (-u)) := by
      rw [mellin]; rw [← rexp_neg_image_aux]; rw [integral_image_eq_integral_abs_deriv_smul
        MeasurableSet.univ rexp_neg_deriv_aux rexp_neg_injOn_aux]
      simp [rexp_cexp_aux]
    _ = ∫ (u : Real), Complex.exp (↑(-2 * π * (u * (s.im / (2 * π)))) * I) •
        (Real.exp (-s.re * u) • f (Real.exp (-u))) := by
      congr
      ext u
      trans Complex.exp (-s.im * u * I) • (Real.exp (-s.re * u) • f (Real.exp (-u)))
      · conv => lhs; rw [← re_add_im s]
        rw [neg_add]; rw [add_mul]; rw [Complex.exp_add]; rw [mul_comm]; rw [← smul_eq_mul]; rw [smul_assoc]
        norm_cast
        push_cast
        ring_nf
      congr
      simp [field]
    _ = 𝓕 (fun (u : Real) => (Real.exp (-s.re * u) • f (Real.exp (-u)))) (s.im / (2 * π)) := by
      simp [fourier_eq', mul_comm (_ / _)]

/--
theorem `mellinInv_eq_fourierInv` / 定理 `mellinInv_eq_fourierInv`

English:
theorem mellinInv_eq_fourierInv
  given: (σ : Real) (f : Complex -> E) {x : Real} (hx : 0 < x)
  proof: calc
  mellinInv σ f x
    = (x : Complex) ^ (-σ : Complex) •
      (∫ (y : Real), Complex.exp (2 * π * (y * (-Real.log x)) * I) • f (σ + 2 * π * y * I)) := by
    rw [mellinInv]; rw [one_div]; rw [← abs_of_pos (show 0 < (2 * π)⁻¹ by simp [pi_pos])]
    have hx0 : (x : Complex) != 0 := ofReal_ne_zer

中文:
定理 mellinInv_eq_fourierInv
  条件: (σ : 实数) (f : Complex -> E) {x : 实数} (hx : 0 < x)
  证明: calc
  mellinInv σ f x
    = (x : Complex) ^ (-σ : Complex) •
      (∫ (y : Real), Complex.exp (2 * π * (y * (-Real.log x)) * I) • f (σ + 2 * π * y * I)) := by
    rw [mellinInv]; rw [one_div]; rw [← abs_of_pos (show 0 < (2 * π)⁻¹ by simp [pi_pos])]
    have hx0 : (x : Complex) != 0 := ofReal_ne_zer
-/
theorem mellinInv_eq_fourierInv (σ : Real) (f : Complex -> E) {x : Real} (hx : 0 < x) :
    mellinInv σ f x =
    (x : Complex) ^ (-σ : Complex) • 𝓕⁻ (fun (y : Real) => f (σ + 2 * π * y * I)) (-Real.log x) := calc
  mellinInv σ f x
    = (x : Complex) ^ (-σ : Complex) •
      (∫ (y : Real), Complex.exp (2 * π * (y * (-Real.log x)) * I) • f (σ + 2 * π * y * I)) := by
    rw [mellinInv]; rw [one_div]; rw [← abs_of_pos (show 0 < (2 * π)⁻¹ by simp [pi_pos])]
    have hx0 : (x : Complex) != 0 := ofReal_ne_zero.mpr (ne_of_gt hx)
    simp_rw [neg_add, cpow_add _ _ hx0, mul_smul, integral_smul]
    rw [smul_comm]; rw [← Measure.integral_comp_mul_left]
    congr! 3
    rw [cpow_def_of_ne_zero hx0]; rw [← Complex.ofReal_log hx.le]
    push_cast
    ring_nf
  _ = (x : Complex) ^ (-σ : Complex) • 𝓕⁻ (fun (y : Real) => f (σ + 2 * π * y * I)) (-Real.log x) := by
    simp [fourierInv_eq', mul_comm (Real.log _)]

variable [CompleteSpace E]

/--
theorem `mellinInv_mellin_eq` / 定理 `mellinInv_mellin_eq`

English:
theorem mellinInv_mellin_eq
  statement: (σ : Real) (f : Real -> E) {x : Real} (hx : 0 < x) (hf : MellinConvergent f σ)
  proof: by
  let g := fun (u : Real) => Real.exp (-σ * u) • f (Real.exp (-u))
  replace hf : Integrable g := by
    rw [MellinConvergent]; rw [← rexp_neg_image_aux]; rw [integrableOn_image_iff_integrableOn_abs_deriv_smul
      MeasurableSet.univ rexp_neg_deriv_aux rexp_neg_injOn_aux] at hf
    replace hf : 

中文:
定理 mellinInv_mellin_eq
  结论: (σ : 实数) (f : 实数 -> E) {x : 实数} (hx : 0 < x) (hf : MellinConvergent f σ)
  证明: by
  let g := fun (u : Real) => Real.exp (-σ * u) • f (Real.exp (-u))
  replace hf : Integrable g := by
    rw [MellinConvergent]; rw [← rexp_neg_image_aux]; rw [integrableOn_image_iff_integrableOn_abs_deriv_smul
      MeasurableSet.univ rexp_neg_deriv_aux rexp_neg_injOn_aux] at hf
    replace hf : 

Depends on / 依赖: Integrable, MeasurableSet, MeasurableSet.univ, MellinConvergent, Real.exp, integrableOn_image_iff_integrableOn_abs_deriv_smul, replace, rexp_cexp_aux, rexp_neg_deriv_aux, rexp_neg_image_aux, rexp_neg_injOn_aux
-/
theorem mellinInv_mellin_eq (σ : Real) (f : Real -> E) {x : Real} (hx : 0 < x) (hf : MellinConvergent f σ)
    (hFf : VerticalIntegrable (mellin f) σ) (hfx : ContinuousAt f x) :
    mellinInv σ (mellin f) x = f x := by
  let g := fun (u : Real) => Real.exp (-σ * u) • f (Real.exp (-u))
  replace hf : Integrable g := by
    rw [MellinConvergent]; rw [← rexp_neg_image_aux]; rw [integrableOn_image_iff_integrableOn_abs_deriv_smul
      MeasurableSet.univ rexp_neg_deriv_aux rexp_neg_injOn_aux] at hf
    replace hf : Integrable fun (x : Real) => cexp (-↑σ * ↑x) • f (rexp (-x)) := by
      simpa [rexp_cexp_aux] using hf
    norm_cast at hf
  replace hFf : Integrable (𝓕 g) := by
    have h2π : 2 * π != 0 := by simp
    have : Integrable (𝓕 (fun u => rexp (-(σ * u)) • f (rexp (-u)))) := by
      simpa [mellin_eq_fourier, mul_div_cancel_right₀ _ h2π] using hFf.comp_mul_right' h2π
    simp_rw [neg_mul_eq_neg_mul] at this
    exact this
  replace hfx : ContinuousAt g (-Real.log x) := by
    refine ContinuousAt.fun_smul (by fun_prop) (ContinuousAt.comp ?_ (by fun_prop))
    simpa [Real.exp_log hx] using hfx
  calc
    mellinInv σ (mellin f) x
      = mellinInv σ (fun s => 𝓕 g (s.im / (2 * π))) x := by
      simp [g, mellinInv, mellin_eq_fourier]
    _ = (x : Complex) ^ (-σ : Complex) • g (-Real.log x) := by
      rw [mellinInv_eq_fourierInv _ _ hx]; rw [← hf.fourierInv_fourier_eq hFf hfx]
      simp [mul_div_cancel_left₀ _ (show 2 * π != 0 by simp)]
    _ = (x : Complex) ^ (-σ : Complex) • rexp (σ * Real.log x) • f (rexp (Real.log x)) := by simp [g]
    _ = f x := by
      norm_cast
      rw [mul_comm σ]; rw [← rpow_def_of_pos hx]; rw [Real.exp_log hx]; rw [← Complex.ofReal_cpow hx.le]
      norm_cast
      rw [← smul_assoc]; rw [smul_eq_mul]; rw [Real.rpow_neg hx.le]; rw [inv_mul_cancel₀ (ne_of_gt (rpow_pos_of_pos hx σ))]; rw [one_smul]
