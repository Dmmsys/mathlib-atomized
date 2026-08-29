/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mihai Iancu, Stefan Kebekus, Sebastian Schleissinger, Aristotle AI
-/
module

public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Poisson Integral Formula

We present two versions of the **Poisson Integral Formula** for ℂ-differentiable functions on
arbitrary disks in the complex plane, formulated with the real part of the Herglotz–Riesz kernel of
integration and with the Poisson kernel, respectively.
-/

public section

open Complex MeasureTheory Metric Real Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E]
  {f : Complex -> E} {R : Real} {w c : Complex} {s : Set Complex}

/-!
## Kernels of Integration

For convenience, this preliminary section discussed the kernels on integration that appear in the
various versions of the Poisson Formula.
-/

/--
Definition of `herglotzRieszKernel` / `herglotzRieszKernel` 的定义

English:
definition herglotzRieszKernel
  signature: (c w z : Complex)
  body: ((z - c) + (w - c)) / ((z - c) - (w - c))

中文:
定义 herglotzRieszKernel
  签名: (c w z : 复形)
  定义体: ((z - c) + (w - c)) / ((z - c) - (w - c))
-/
noncomputable def herglotzRieszKernel (c w z : Complex) : Complex :=
  ((z - c) + (w - c)) / ((z - c) - (w - c))

/--
lemma `herglotzRieszKernel_def` / 引理 `herglotzRieszKernel_def`

English:
lemma herglotzRieszKernel_def
  given: (c w z : Complex)
  proof: by rfl

中文:
引理 herglotzRieszKernel_def
  条件: (c w z : 复形)
  证明: by rfl
-/
lemma herglotzRieszKernel_def (c w z : Complex) :
    herglotzRieszKernel c w z = ((z - c) + (w - c)) / ((z - c) - (w - c)) := by rfl

/--
lemma `herglotzRieszKernel_fun_def` / 引理 `herglotzRieszKernel_fun_def`

English:
lemma herglotzRieszKernel_fun_def
  given: (c w : Complex)
  proof: by
  ext z
  exact herglotzRieszKernel_def c w z

中文:
引理 herglotzRieszKernel_fun_def
  条件: (c w : 复形)
  证明: by
  ext z
  exact herglotzRieszKernel_def c w z

Depends on / 依赖: herglotzRieszKernel_def
-/
lemma herglotzRieszKernel_fun_def (c w : Complex) :
    herglotzRieszKernel c w = fun z => ((z - c) + (w - c)) / ((z - c) - (w - c)) := by
  ext z
  exact herglotzRieszKernel_def c w z

/--
lemma `herglotzRieszKernel_add_const` / 引理 `herglotzRieszKernel_add_const`

English:
lemma herglotzRieszKernel_add_const
  given: (c w z : Complex)
  proof: by
  simp [herglotzRieszKernel_fun_def]

中文:
引理 herglotzRieszKernel_add_const
  条件: (c w z : 复形)
  证明: by
  simp [herglotzRieszKernel_fun_def]

Depends on / 依赖: herglotzRieszKernel_fun_def
-/
lemma herglotzRieszKernel_add_const (c w z : Complex) :
    herglotzRieszKernel c w (z + c) = herglotzRieszKernel 0 (w - c) z := by
  simp [herglotzRieszKernel_fun_def]

/--
Definition of `poissonKernel` / `poissonKernel` 的定义

English:
definition poissonKernel
  signature: (c w z : Complex)
  body: (‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) / ‖(z - c) - (w - c)‖ ^ 2

中文:
定义 poissonKernel
  签名: (c w z : 复形)
  定义体: (‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) / ‖(z - c) - (w - c)‖ ^ 2
-/
noncomputable def poissonKernel (c w z : Complex) : Real :=
  (‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) / ‖(z - c) - (w - c)‖ ^ 2

/--
lemma `poissonKernel_def` / 引理 `poissonKernel_def`

English:
lemma poissonKernel_def
  given: (c w z : Complex)
  proof: by rfl

中文:
引理 poissonKernel_def
  条件: (c w z : 复形)
  证明: by rfl
-/
lemma poissonKernel_def (c w z : Complex) :
    poissonKernel c w z = (‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) / ‖(z - c) - (w - c)‖ ^ 2 := by rfl

/--
lemma `poissonKernel_eq_re_herglotzRieszKernel_aux` / 引理 `poissonKernel_eq_re_herglotzRieszKernel_aux`

English:
lemma poissonKernel_eq_re_herglotzRieszKernel_aux
  given: {a b : Complex}
  proof: by
  rw [div_re]; rw [normSq_eq_norm_sq (a - b)]; rw [← add_div]; rw [add_re]; rw [sub_re]; rw [add_im]; rw [sub_im]
  calc ((a.re + b.re) * (a.re - b.re) + (a.im + b.im) * (a.im - b.im)) / ‖a - b‖ ^ 2
    _ = ((a.re * a.re + a.im * a.im) - (b.re * b.re + b.im * b.im)) / ‖a - b‖ ^ 2 := by
      congr! 1; ring
    _ = (‖a‖ ^ 2 - ‖b‖ ^ 2) / ‖a - b‖ ^ 2 := by
      simp [← normSq_apply, normSq_eq_norm_sq]

中文:
引理 poissonKernel_eq_re_herglotzRieszKernel_aux
  条件: {a b : 复形}
  证明: by
  rw [div_re]; rw [normSq_eq_norm_sq (a - b)]; rw [← add_div]; rw [add_re]; rw [sub_re]; rw [add_im]; rw [sub_im]
  calc ((a.re + b.re) * (a.re - b.re) + (a.im + b.im) * (a.im - b.im)) / ‖a - b‖ ^ 2
    _ = ((a.re * a.re + a.im * a.im) - (b.re * b.re + b.im * b.im)) / ‖a - b‖ ^ 2 := by
      congr! 1; ring
    _ = (‖a‖ ^ 2 - ‖b‖ ^ 2) / ‖a - b‖ ^ 2 := by
      simp [← normSq_apply, normSq_eq_norm_sq]
-/
private lemma poissonKernel_eq_re_herglotzRieszKernel_aux {a b : Complex} :
    ((a + b) / (a - b)).re = (‖a‖ ^ 2 - ‖b‖ ^ 2) / ‖a - b‖ ^ 2 := by
  rw [div_re]; rw [normSq_eq_norm_sq (a - b)]; rw [← add_div]; rw [add_re]; rw [sub_re]; rw [add_im]; rw [sub_im]
  calc ((a.re + b.re) * (a.re - b.re) + (a.im + b.im) * (a.im - b.im)) / ‖a - b‖ ^ 2
    _ = ((a.re * a.re + a.im * a.im) - (b.re * b.re + b.im * b.im)) / ‖a - b‖ ^ 2 := by
      congr! 1; ring
    _ = (‖a‖ ^ 2 - ‖b‖ ^ 2) / ‖a - b‖ ^ 2 := by
      simp [← normSq_apply, normSq_eq_norm_sq]

/--
lemma `poissonKernel_eq_re_herglotzRieszKernel` / 引理 `poissonKernel_eq_re_herglotzRieszKernel`

English:
lemma poissonKernel_eq_re_herglotzRieszKernel
  given: {c w : Complex}
  proof: by
  ext z
  rw [Function.comp_apply]; rw [poissonKernel]; rw [herglotzRieszKernel]; rw [poissonKernel_eq_re_herglotzRieszKernel_aux]

中文:
引理 poissonKernel_eq_re_herglotzRieszKernel
  条件: {c w : 复形}
  证明: by
  ext z
  rw [Function.comp_apply]; rw [poissonKernel]; rw [herglotzRieszKernel]; rw [poissonKernel_eq_re_herglotzRieszKernel_aux]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, herglotzRieszKernel, poissonKernel, poissonKernel_eq_re_herglotzRieszKernel_aux
-/
lemma poissonKernel_eq_re_herglotzRieszKernel {c w : Complex} :
    poissonKernel c w = Complex.re ∘ herglotzRieszKernel c w := by
  ext z
  rw [Function.comp_apply]; rw [poissonKernel]; rw [herglotzRieszKernel]; rw [poissonKernel_eq_re_herglotzRieszKernel_aux]

/--
lemma `re_herglotzRieszKernel_le_aux` / 引理 `re_herglotzRieszKernel_le_aux`

English:
lemma re_herglotzRieszKernel_le_aux
  given: (φ θ r R : Real) (h₁ : 0 < r) (h₂ : r < R)
  proof: by
  rw [div_eq_mul_inv]
  have h_cos : (R ^ 2 + r ^ 2 - 2 * R * r * Real.cos (θ - φ)) >= (R - r) ^ 2 := by
    nlinarith [mul_pos h₁ (sub_pos.mpr h₂), Real.cos_le_one (θ - φ)]
  have h_subst :
      (R ^ 2 - r ^ 2) / (R ^ 2 + r ^ 2 - 2 * R * r * Real.cos (θ - φ)) <= (R + r) / (R - r) := by
    rw [div_le_div_iff₀] <;> nlinarith [mul_pos h₁ (sub_pos.mpr h₂)]
  convert h_subst
  rw [← div_eq_mul_inv]; rw [poissonKernel_eq_re_herglotzRieszKernel_aux]
  suffices (R * R * normSq (cexp (θ * I)) + r * r * normSq (cexp (φ * I)) -
      2 * (R * Real.cos θ * (r * Real.cos φ) + R * Real.sin θ * (r * Real.sin φ))) =
      (R ^ 2 + r ^ 2 - 2 * R * r * Real.cos (θ - φ)) by
    rw [← this]; simp [← normSq_eq_norm_sq, Complex.normSq_sub]
  simp [normSq_eq_norm_sq, Real.cos_sub]
  ring

中文:
引理 re_herglotzRieszKernel_le_aux
  条件: (φ θ r R : 实数) (h₁ : 0 < r) (h₂ : r < R)
  证明: by
  rw [div_eq_mul_inv]
  have h_cos : (R ^ 2 + r ^ 2 - 2 * R * r * Real.cos (θ - φ)) >= (R - r) ^ 2 := by
    nlinarith [mul_pos h₁ (sub_pos.mpr h₂), Real.cos_le_one (θ - φ)]
  have h_subst :
      (R ^ 2 - r ^ 2) / (R ^ 2 + r ^ 2 - 2 * R * r * Real.cos (θ - φ)) <= (R + r) / (R - r) := by
    rw [div_le_div_iff₀] <;> nlinarith [mul_pos h₁ (sub_pos.mpr h₂)]
  convert h_subst
  rw [← div_eq_mul_inv]; rw [poissonKernel_eq_re_herglotzRieszKernel_aux]
  suffices (R * R * normSq (cexp (θ * I)) + r * r * normSq (cexp (φ * I)) -
      2 * (R * Real.cos θ * (r * Real.cos φ) + R * Real.sin θ * (r * Real.sin φ))) =
      (R ^ 2 + r ^ 2 - 2 * R * r * Real.cos (θ - φ)) by
    rw [← this]; simp [← normSq_eq_norm_sq, Complex.normSq_sub]
  simp [normSq_eq_norm_sq, Real.cos_sub]
  ring
-/
private lemma re_herglotzRieszKernel_le_aux (φ θ r R : Real) (h₁ : 0 < r) (h₂ : r < R) :
    ((R * exp (θ * I) + r * exp (φ * I)) / (R * exp (θ * I) - r * exp (φ * I))).re
      <= (R + r) / (R - r) := by
  rw [div_eq_mul_inv]
  have h_cos : (R ^ 2 + r ^ 2 - 2 * R * r * Real.cos (θ - φ)) >= (R - r) ^ 2 := by
    nlinarith [mul_pos h₁ (sub_pos.mpr h₂), Real.cos_le_one (θ - φ)]
  have h_subst :
      (R ^ 2 - r ^ 2) / (R ^ 2 + r ^ 2 - 2 * R * r * Real.cos (θ - φ)) <= (R + r) / (R - r) := by
    rw [div_le_div_iff₀] <;> nlinarith [mul_pos h₁ (sub_pos.mpr h₂)]
  convert h_subst
  rw [← div_eq_mul_inv]; rw [poissonKernel_eq_re_herglotzRieszKernel_aux]
  suffices (R * R * normSq (cexp (θ * I)) + r * r * normSq (cexp (φ * I)) -
      2 * (R * Real.cos θ * (r * Real.cos φ) + R * Real.sin θ * (r * Real.sin φ))) =
      (R ^ 2 + r ^ 2 - 2 * R * r * Real.cos (θ - φ)) by
    rw [← this]; simp [← normSq_eq_norm_sq, Complex.normSq_sub]
  simp [normSq_eq_norm_sq, Real.cos_sub]
  ring

/--
theorem `re_herglotzRieszKernel_le` / 定理 `re_herglotzRieszKernel_le`

English:
theorem re_herglotzRieszKernel_le
  given: {c z : Complex} (hz : z in sphere c R) (hw : w in ball c R)
  proof: by
  obtain ⟨η₀, rfl, η₂⟩ : 0 < R ∧ R = ‖z - c‖ ∧ z - c != 0 := by
    grind [ball_eq_empty, mem_sphere, dist_eq_norm, norm_pos_iff]
  by_cases h₁w : ‖w - c‖ = 0
  · aesop
  simpa using re_herglotzRieszKernel_le_aux (w - c).arg (z - c).arg ‖w - c‖ ‖z - c‖
    (by simpa using h₁w) (mem_ball_iff_norm.1 hw)

中文:
定理 re_herglotzRieszKernel_le
  条件: {c z : 复形} (hz : z in sphere c R) (hw : w in ball c R)
  证明: by
  obtain ⟨η₀, rfl, η₂⟩ : 0 < R ∧ R = ‖z - c‖ ∧ z - c != 0 := by
    grind [ball_eq_empty, mem_sphere, dist_eq_norm, norm_pos_iff]
  by_cases h₁w : ‖w - c‖ = 0
  · aesop
  simpa using re_herglotzRieszKernel_le_aux (w - c).arg (z - c).arg ‖w - c‖ ‖z - c‖
    (by simpa using h₁w) (mem_ball_iff_norm.1 hw)

Depends on / 依赖: ball_eq_empty, dist_eq_norm, mem_ball_iff_norm, mem_sphere, norm_pos_iff, re_herglotzRieszKernel_le_aux
-/
theorem re_herglotzRieszKernel_le {c z : Complex} (hz : z in sphere c R) (hw : w in ball c R) :
    ((z - c + (w - c)) / ((z - c) - (w - c))).re <= (R + ‖w - c‖) / (R - ‖w - c‖) := by
  obtain ⟨η₀, rfl, η₂⟩ : 0 < R ∧ R = ‖z - c‖ ∧ z - c != 0 := by
    grind [ball_eq_empty, mem_sphere, dist_eq_norm, norm_pos_iff]
  by_cases h₁w : ‖w - c‖ = 0
  · aesop
  simpa using re_herglotzRieszKernel_le_aux (w - c).arg (z - c).arg ‖w - c‖ ‖z - c‖
    (by simpa using h₁w) (mem_ball_iff_norm.1 hw)

/--
lemma `le_re_herglotzRieszKernel_aux` / 引理 `le_re_herglotzRieszKernel_aux`

English:
lemma le_re_herglotzRieszKernel_aux
  given: (θ φ r R : Real) (h₁ : 0 < r) (h₂ : r < R)
  proof: by
  rw [poissonKernel_eq_re_herglotzRieszKernel_aux]
  simp only [Complex.norm_mul, norm_real, norm_eq_abs, norm_exp_ofReal_mul_I, mul_one, sq_abs,
    sq_sub_sq]
  field_simp [sub_pos.mpr h₂]
  simp only [mul_comm I] -- make sure exponents are in the form `?angle * I` for the simplification
  rw [div_le_div_iff₀ (by positivity [h₁.trans h₂]) ?hpos, ← normSq_eq_norm_sq, normSq_sub,
    normSq_eq_norm_sq, normSq_eq_norm_sq]
  case hpos => simpa [sq_pos_iff, sub_eq_zero] using
(mt <| congr_arg (‖·‖)) by simpa [abs_of_pos, h₁, h₁.trans h₂] using h₂.ne'
  have key := calc
    (-(R * cexp (θ * I) * (starRingEnd Complex) (r * cexp (φ * I)))).re <= _ := re_le_norm _
    _ <= R * r := by simp [abs_of_pos, h₁, h₁.trans h₂]
  simpa using calc
    R ^ 2 + r ^ 2 - 2 * (R * cexp (θ * I) * (starRingEnd Complex) (r * cexp (φ * I))).re
    _ <= R ^ 2 + r ^ 2 + 2 * (R * r) := by rw [sub_eq_add_neg, ← mul_neg, ← neg_re]; gcongr
    _ = (R + r) * (R + r) := by ring

中文:
引理 le_re_herglotzRieszKernel_aux
  条件: (θ φ r R : 实数) (h₁ : 0 < r) (h₂ : r < R)
  证明: by
  rw [poissonKernel_eq_re_herglotzRieszKernel_aux]
  simp only [Complex.norm_mul, norm_real, norm_eq_abs, norm_exp_ofReal_mul_I, mul_one, sq_abs,
    sq_sub_sq]
  field_simp [sub_pos.mpr h₂]
  simp only [mul_comm I] -- make sure exponents are in the form `?angle * I` for the simplification
  rw [div_le_div_iff₀ (by positivity [h₁.trans h₂]) ?hpos, ← normSq_eq_norm_sq, normSq_sub,
    normSq_eq_norm_sq, normSq_eq_norm_sq]
  case hpos => simpa [sq_pos_iff, sub_eq_zero] using
(mt <| congr_arg (‖·‖)) by simpa [abs_of_pos, h₁, h₁.trans h₂] using h₂.ne'
  have key := calc
    (-(R * cexp (θ * I) * (starRingEnd Complex) (r * cexp (φ * I)))).re <= _ := re_le_norm _
    _ <= R * r := by simp [abs_of_pos, h₁, h₁.trans h₂]
  simpa using calc
    R ^ 2 + r ^ 2 - 2 * (R * cexp (θ * I) * (starRingEnd Complex) (r * cexp (φ * I))).re
    _ <= R ^ 2 + r ^ 2 + 2 * (R * r) := by rw [sub_eq_add_neg, ← mul_neg, ← neg_re]; gcongr
    _ = (R + r) * (R + r) := by ring
-/
private lemma le_re_herglotzRieszKernel_aux (θ φ r R : Real) (h₁ : 0 < r) (h₂ : r < R) :
    (R - r) / (R + r)
      <= ((R * exp (θ * I) + r * exp (φ * I)) / (R * exp (θ * I) - r * exp (φ * I))).re := by
  rw [poissonKernel_eq_re_herglotzRieszKernel_aux]
  simp only [Complex.norm_mul, norm_real, norm_eq_abs, norm_exp_ofReal_mul_I, mul_one, sq_abs,
    sq_sub_sq]
  field_simp [sub_pos.mpr h₂]
  simp only [mul_comm I] -- make sure exponents are in the form `?angle * I` for the simplification
  rw [div_le_div_iff₀ (by positivity [h₁.trans h₂]) ?hpos, ← normSq_eq_norm_sq, normSq_sub,
    normSq_eq_norm_sq, normSq_eq_norm_sq]
  case hpos => simpa [sq_pos_iff, sub_eq_zero] using
(mt <| congr_arg (‖·‖)) by simpa [abs_of_pos, h₁, h₁.trans h₂] using h₂.ne'
  have key := calc
    (-(R * cexp (θ * I) * (starRingEnd Complex) (r * cexp (φ * I)))).re <= _ := re_le_norm _
    _ <= R * r := by simp [abs_of_pos, h₁, h₁.trans h₂]
  simpa using calc
    R ^ 2 + r ^ 2 - 2 * (R * cexp (θ * I) * (starRingEnd Complex) (r * cexp (φ * I))).re
    _ <= R ^ 2 + r ^ 2 + 2 * (R * r) := by rw [sub_eq_add_neg, ← mul_neg, ← neg_re]; gcongr
    _ = (R + r) * (R + r) := by ring

/--
theorem `le_re_herglotzRieszKernel` / 定理 `le_re_herglotzRieszKernel`

English:
theorem le_re_herglotzRieszKernel
  given: {c z : Complex} (hz : z in sphere c R) (hw : w in ball c R)
  proof: by
  obtain ⟨η₀, rfl, η₂⟩ : 0 < R ∧ R = ‖z - c‖ ∧ z - c != 0 := by
    grind [ball_eq_empty, mem_sphere, dist_eq_norm, norm_pos_iff]
  by_cases h₁w : ‖w - c‖ = 0
  · aesop
  simpa using le_re_herglotzRieszKernel_aux (z - c).arg (w - c).arg ‖w - c‖ ‖z - c‖
    (by simpa using h₁w) (mem_ball_iff_norm.1 hw)

中文:
定理 le_re_herglotzRieszKernel
  条件: {c z : 复形} (hz : z in sphere c R) (hw : w in ball c R)
  证明: by
  obtain ⟨η₀, rfl, η₂⟩ : 0 < R ∧ R = ‖z - c‖ ∧ z - c != 0 := by
    grind [ball_eq_empty, mem_sphere, dist_eq_norm, norm_pos_iff]
  by_cases h₁w : ‖w - c‖ = 0
  · aesop
  simpa using le_re_herglotzRieszKernel_aux (z - c).arg (w - c).arg ‖w - c‖ ‖z - c‖
    (by simpa using h₁w) (mem_ball_iff_norm.1 hw)

Depends on / 依赖: ball_eq_empty, dist_eq_norm, le_re_herglotzRieszKernel_aux, mem_ball_iff_norm, mem_sphere, norm_pos_iff
-/
theorem le_re_herglotzRieszKernel {c z : Complex} (hz : z in sphere c R) (hw : w in ball c R) :
    (R - ‖w - c‖) / (R + ‖w - c‖) <= ((z - c + (w - c)) / ((z - c) - (w - c))).re := by
  obtain ⟨η₀, rfl, η₂⟩ : 0 < R ∧ R = ‖z - c‖ ∧ z - c != 0 := by
    grind [ball_eq_empty, mem_sphere, dist_eq_norm, norm_pos_iff]
  by_cases h₁w : ‖w - c‖ = 0
  · aesop
  simpa using le_re_herglotzRieszKernel_aux (z - c).arg (w - c).arg ‖w - c‖ ‖z - c‖
    (by simpa using h₁w) (mem_ball_iff_norm.1 hw)

/--
lemma `continuousOn_herglotzRieszKernel_sphere` / 引理 `continuousOn_herglotzRieszKernel_sphere`

English:
lemma continuousOn_herglotzRieszKernel_sphere
  given: (hw : w in ball c R)
  proof: by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  grind [mem_sphere, mem_ball, le_abs_self R]

中文:
引理 continuousOn_herglotzRieszKernel_sphere
  条件: (hw : w in ball c R)
  证明: by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  grind [mem_sphere, mem_ball, le_abs_self R]
-/
@[fun_prop] lemma continuousOn_herglotzRieszKernel_sphere (hw : w in ball c R) :
    ContinuousOn (herglotzRieszKernel c w) (sphere c |R|) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  grind [mem_sphere, mem_ball, le_abs_self R]

/--
theorem `re_circleAverage_herglotzRieszKernel_smul` / 定理 `re_circleAverage_herglotzRieszKernel_smul`

English:
theorem re_circleAverage_herglotzRieszKernel_smul
  statement: {g : Complex -> Real}
  proof: by
  have h₁ : CircleIntegrable (fun ζ => (g ζ : Complex)) 0 R := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hg ⊢
    exact Complex.ofRealCLM.integrable_comp hg
  have h₂ : CircleIntegrable (fun ζ => herglotzRieszKernel 0 w ζ • (g ζ : Complex)) 0 R :=
    h₁.continuousOn_smul (continuousOn_herglotzRieszKernel_sphere hw)
  calc (circleAverage (fun ζ => herglotzRieszKernel 0 w ζ • (g ζ : Complex)) 0 R).re
      = circleAverage (Complex.reCLM ∘ fun ζ => herglotzRieszKernel 0 w ζ • (g ζ : Complex)) 0 R :=
        (Complex.reCLM.circleAverage_comp_comm h₂).symm
    _ = circleAverage ((Complex.re ∘ herglotzRieszKernel 0 w) • g) 0 R := by
        simp [Function.comp_def, Complex.mul_re, Pi.mul_def]

中文:
定理 re_circleAverage_herglotzRieszKernel_smul
  结论: {g : 复形 -> 实数}
  证明: by
  have h₁ : CircleIntegrable (fun ζ => (g ζ : Complex)) 0 R := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hg ⊢
    exact Complex.ofRealCLM.integrable_comp hg
  have h₂ : CircleIntegrable (fun ζ => herglotzRieszKernel 0 w ζ • (g ζ : Complex)) 0 R :=
    h₁.continuousOn_smul (continuousOn_herglotzRieszKernel_sphere hw)
  calc (circleAverage (fun ζ => herglotzRieszKernel 0 w ζ • (g ζ : Complex)) 0 R).re
      = circleAverage (Complex.reCLM ∘ fun ζ => herglotzRieszKernel 0 w ζ • (g ζ : Complex)) 0 R :=
        (Complex.reCLM.circleAverage_comp_comm h₂).symm
    _ = circleAverage ((Complex.re ∘ herglotzRieszKernel 0 w) • g) 0 R := by
        simp [Function.comp_def, Complex.mul_re, Pi.mul_def]

Depends on / 依赖: CircleIntegrable, Complex.ofRealCLM.integrable_comp, Complex.reCLM, circleAverage, continuousOn_herglotzRieszKernel_sphere, continuousOn_smul, herglotzRieszKernel, integrable_comp, intervalIntegrable_iff, ofRealCLM
-/
theorem re_circleAverage_herglotzRieszKernel_smul {g : Complex -> Real}
    (hg : CircleIntegrable g 0 R) (hw : w in ball 0 R) :
    (circleAverage (fun ζ => herglotzRieszKernel 0 w ζ • (g ζ : Complex)) 0 R).re
      = circleAverage ((Complex.re ∘ herglotzRieszKernel 0 w) • g) 0 R := by
  have h₁ : CircleIntegrable (fun ζ => (g ζ : Complex)) 0 R := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hg ⊢
    exact Complex.ofRealCLM.integrable_comp hg
  have h₂ : CircleIntegrable (fun ζ => herglotzRieszKernel 0 w ζ • (g ζ : Complex)) 0 R :=
    h₁.continuousOn_smul (continuousOn_herglotzRieszKernel_sphere hw)
  calc (circleAverage (fun ζ => herglotzRieszKernel 0 w ζ • (g ζ : Complex)) 0 R).re
      = circleAverage (Complex.reCLM ∘ fun ζ => herglotzRieszKernel 0 w ζ • (g ζ : Complex)) 0 R :=
        (Complex.reCLM.circleAverage_comp_comm h₂).symm
    _ = circleAverage ((Complex.re ∘ herglotzRieszKernel 0 w) • g) 0 R := by
        simp [Function.comp_def, Complex.mul_re, Pi.mul_def]


-- Trigonometric identity used in the computation of
-- `DiffContOnCl.circleAverage_re_smul_on_ball_zero`.
/--
lemma `circleAverage_re_smul_on_ball_zero_aux` / 引理 `circleAverage_re_smul_on_ball_zero_aux`

English:
lemma circleAverage_re_smul_on_ball_zero_aux
  given: {φ θ : Real} {r : Real}
  proof: by
  simp only [Complex.ext_iff, exp_ofReal_mul_I, add_re, sub_re, mul_re, div_re, ofReal_re,
    I_re, I_im, add_im, sub_im, mul_im, div_im, ofReal_im, normSq_apply]
  grind [Real.sin_sq]

中文:
引理 circleAverage_re_smul_on_ball_zero_aux
  条件: {φ θ : 实数} {r : 实数}
  证明: by
  simp only [Complex.ext_iff, exp_ofReal_mul_I, add_re, sub_re, mul_re, div_re, ofReal_re,
    I_re, I_im, add_im, sub_im, mul_im, div_im, ofReal_im, normSq_apply]
  grind [Real.sin_sq]
-/
private lemma circleAverage_re_smul_on_ball_zero_aux {φ θ : Real} {r : Real} :
    (R * exp (θ * I)) / (R * exp (θ * I) - r * exp (φ * I)) - (r * exp (θ * I))
      / (r * exp (θ * I) - R * exp (φ * I))
      = ((R * exp (θ * I) + r * exp (φ * I)) / (R * exp (θ * I) - r * exp (φ * I))).re := by
  simp only [Complex.ext_iff, exp_ofReal_mul_I, add_re, sub_re, mul_re, div_re, ofReal_re,
    I_re, I_im, add_im, sub_im, mul_im, div_im, ofReal_im, normSq_apply]
  grind [Real.sin_sq]

-- Version of `DiffContOnCl.circleAverage_re_smul` in case where the center of the ball is zero.
/--
lemma `DiffContOnCl.circleAverage_re_smul_on_ball_zero` / 引理 `DiffContOnCl.circleAverage_re_smul_on_ball_zero`

English:
lemma DiffContOnCl.circleAverage_re_smul_on_ball_zero
  statement: [CompleteSpace E]
  proof: by
  -- Trivial case: nonpositive radius
  rcases le_or_gt R 0 with hR | hR
  · simp_all [ball_eq_empty.2 hR]
  -- Trivial case: w is at the center
  obtain rfl | h₁w := eq_or_ne w 0
  · refine (circleAverage_congr_sphere fun z hz => ?_).trans (abs_of_pos hR ▸ hf |>.circleAverage)
    rw [abs_of_pos hR] at hz
    simp [div_self (a := z) (by aesop)]
  -- General case: positive radius, w is not at the center
  let W := R * exp (w.arg * I)
  let q := ‖w‖ / R
  have h₁q : 0 < q := by positivity
  have h₂q : q < 1 := by simpa [← div_lt_one hR] using hw
  -- Lemma used by automatisation tactics to ensure that quotients are non-zero.
  have η₀ {x : Complex} (h : ‖x‖ <= R) : q * x - W != 0 := by
    suffices ‖q * x‖ < ‖W‖ by grind
    calc
      ‖q * x‖ = q * ‖x‖ := by simp [abs_of_pos h₁q]
      _ <= q * R := by gcongr
      _ < 1 * R := by gcongr
      _ = ‖W‖ := by simp [W, abs_of_pos hR]
  have h0 : ∮ (z : Complex) in C(0, R), z⁻¹ • ((q * z) / (q * z - W)) • f z = 0 := calc
    ∮ (z : Complex) in C(0, R), z⁻¹ • ((q * z) / (q * z - W)) • f z
    _ = ∮ (z : Complex) in C(0, R), (q / (q * z - W)) • f z := by
      apply circleIntegral.integral_congr hR.le fun z hz => ?_
      have hz : z != 0 := by aesop
      match_scalars
      field
    _ = 0 := by
.circleIntegral_eq_zero hR.le .smul hf apply DifferentiableOn.diffContOnCl ?_
      rw [closure_ball 0 hR.ne']
      fun_prop (disch := aesop)
  -- Main computation starts here
  calc Real.circleAverage (fun z => ((z + w) / (z - w)).re • f z) 0 R
    _ = Real.circleAverage (fun z => (z / (z - w) - (q • z) / (q • z - W)) • f z) 0 R := by
      apply circleAverage_congr_sphere fun z hz => ?_
      have hzR : ‖z‖ = R := by simpa [abs_of_pos hR] using hz
      match_scalars
      simp only [q, W, real_smul, ofReal_div, coe_algebraMap, mul_one]
      rw [← norm_mul_exp_arg_mul_I w]; rw [← norm_mul_exp_arg_mul_I z]; rw [hzR]; rw [← circleAverage_re_smul_on_ball_zero_aux]; rw [norm_mul_exp_arg_mul_I w]
      field [hR.ne.symm]
    _ = Real.circleAverage (fun z => (z / (z - w)) • f z) 0 R
        - Real.circleAverage (fun z => ((q • z) / (q • z - W)) • f z) 0 R := by
      simp_rw [sub_smul]
      have h₁ : forall z in sphere 0 R, z - w != 0 := by aesop (add simp sub_eq_zero)
      have h₃ : ContinuousOn f (sphere 0 R) :=
hf.2.mono sphere_subset_closedBall.trans_eq (closure_ball 0 hR.ne').symm
      rw [circleAverage_fun_sub]
      all_goals
        apply ContinuousOn.circleIntegrable hR.le
        fun_prop (disch := aesop)
    _ = f w := by
      rw [← abs_of_pos hR] at hw hf
      simp [← hf.circleAverage_smul_div hw, circleAverage_eq_circleIntegral (ne_of_lt hR).symm, h0]

中文:
引理 DiffContOnCl.circleAverage_re_smul_on_ball_zero
  结论: [完备空间 E]
  证明: by
  -- Trivial case: nonpositive radius
  rcases le_or_gt R 0 with hR | hR
  · simp_all [ball_eq_empty.2 hR]
  -- Trivial case: w is at the center
  obtain rfl | h₁w := eq_or_ne w 0
  · refine (circleAverage_congr_sphere fun z hz => ?_).trans (abs_of_pos hR ▸ hf |>.circleAverage)
    rw [abs_of_pos hR] at hz
    simp [div_self (a := z) (by aesop)]
  -- General case: positive radius, w is not at the center
  let W := R * exp (w.arg * I)
  let q := ‖w‖ / R
  have h₁q : 0 < q := by positivity
  have h₂q : q < 1 := by simpa [← div_lt_one hR] using hw
  -- Lemma used by automatisation tactics to ensure that quotients are non-zero.
  have η₀ {x : Complex} (h : ‖x‖ <= R) : q * x - W != 0 := by
    suffices ‖q * x‖ < ‖W‖ by grind
    calc
      ‖q * x‖ = q * ‖x‖ := by simp [abs_of_pos h₁q]
      _ <= q * R := by gcongr
      _ < 1 * R := by gcongr
      _ = ‖W‖ := by simp [W, abs_of_pos hR]
  have h0 : ∮ (z : Complex) in C(0, R), z⁻¹ • ((q * z) / (q * z - W)) • f z = 0 := calc
    ∮ (z : Complex) in C(0, R), z⁻¹ • ((q * z) / (q * z - W)) • f z
    _ = ∮ (z : Complex) in C(0, R), (q / (q * z - W)) • f z := by
      apply circleIntegral.integral_congr hR.le fun z hz => ?_
      have hz : z != 0 := by aesop
      match_scalars
      field
    _ = 0 := by
.circleIntegral_eq_zero hR.le .smul hf apply DifferentiableOn.diffContOnCl ?_
      rw [closure_ball 0 hR.ne']
      fun_prop (disch := aesop)
  -- Main computation starts here
  calc Real.circleAverage (fun z => ((z + w) / (z - w)).re • f z) 0 R
    _ = Real.circleAverage (fun z => (z / (z - w) - (q • z) / (q • z - W)) • f z) 0 R := by
      apply circleAverage_congr_sphere fun z hz => ?_
      have hzR : ‖z‖ = R := by simpa [abs_of_pos hR] using hz
      match_scalars
      simp only [q, W, real_smul, ofReal_div, coe_algebraMap, mul_one]
      rw [← norm_mul_exp_arg_mul_I w]; rw [← norm_mul_exp_arg_mul_I z]; rw [hzR]; rw [← circleAverage_re_smul_on_ball_zero_aux]; rw [norm_mul_exp_arg_mul_I w]
      field [hR.ne.symm]
    _ = Real.circleAverage (fun z => (z / (z - w)) • f z) 0 R
        - Real.circleAverage (fun z => ((q • z) / (q • z - W)) • f z) 0 R := by
      simp_rw [sub_smul]
      have h₁ : forall z in sphere 0 R, z - w != 0 := by aesop (add simp sub_eq_zero)
      have h₃ : ContinuousOn f (sphere 0 R) :=
hf.2.mono sphere_subset_closedBall.trans_eq (closure_ball 0 hR.ne').symm
      rw [circleAverage_fun_sub]
      all_goals
        apply ContinuousOn.circleIntegrable hR.le
        fun_prop (disch := aesop)
    _ = f w := by
      rw [← abs_of_pos hR] at hw hf
      simp [← hf.circleAverage_smul_div hw, circleAverage_eq_circleIntegral (ne_of_lt hR).symm, h0]
-/
private lemma DiffContOnCl.circleAverage_re_smul_on_ball_zero [CompleteSpace E]
    (hf : DiffContOnCl Complex f (ball 0 R)) (hw : w in ball 0 R) :
    Real.circleAverage (fun z => ((z + w) / (z - w)).re • f z) 0 R = f w := by
  -- Trivial case: nonpositive radius
  rcases le_or_gt R 0 with hR | hR
  · simp_all [ball_eq_empty.2 hR]
  -- Trivial case: w is at the center
  obtain rfl | h₁w := eq_or_ne w 0
  · refine (circleAverage_congr_sphere fun z hz => ?_).trans (abs_of_pos hR ▸ hf |>.circleAverage)
    rw [abs_of_pos hR] at hz
    simp [div_self (a := z) (by aesop)]
  -- General case: positive radius, w is not at the center
  let W := R * exp (w.arg * I)
  let q := ‖w‖ / R
  have h₁q : 0 < q := by positivity
  have h₂q : q < 1 := by simpa [← div_lt_one hR] using hw
  -- Lemma used by automatisation tactics to ensure that quotients are non-zero.
  have η₀ {x : Complex} (h : ‖x‖ <= R) : q * x - W != 0 := by
    suffices ‖q * x‖ < ‖W‖ by grind
    calc
      ‖q * x‖ = q * ‖x‖ := by simp [abs_of_pos h₁q]
      _ <= q * R := by gcongr
      _ < 1 * R := by gcongr
      _ = ‖W‖ := by simp [W, abs_of_pos hR]
  have h0 : ∮ (z : Complex) in C(0, R), z⁻¹ • ((q * z) / (q * z - W)) • f z = 0 := calc
    ∮ (z : Complex) in C(0, R), z⁻¹ • ((q * z) / (q * z - W)) • f z
    _ = ∮ (z : Complex) in C(0, R), (q / (q * z - W)) • f z := by
      apply circleIntegral.integral_congr hR.le fun z hz => ?_
      have hz : z != 0 := by aesop
      match_scalars
      field
    _ = 0 := by
.circleIntegral_eq_zero hR.le .smul hf apply DifferentiableOn.diffContOnCl ?_
      rw [closure_ball 0 hR.ne']
      fun_prop (disch := aesop)
  -- Main computation starts here
  calc Real.circleAverage (fun z => ((z + w) / (z - w)).re • f z) 0 R
    _ = Real.circleAverage (fun z => (z / (z - w) - (q • z) / (q • z - W)) • f z) 0 R := by
      apply circleAverage_congr_sphere fun z hz => ?_
      have hzR : ‖z‖ = R := by simpa [abs_of_pos hR] using hz
      match_scalars
      simp only [q, W, real_smul, ofReal_div, coe_algebraMap, mul_one]
      rw [← norm_mul_exp_arg_mul_I w]; rw [← norm_mul_exp_arg_mul_I z]; rw [hzR]; rw [← circleAverage_re_smul_on_ball_zero_aux]; rw [norm_mul_exp_arg_mul_I w]
      field [hR.ne.symm]
    _ = Real.circleAverage (fun z => (z / (z - w)) • f z) 0 R
        - Real.circleAverage (fun z => ((q • z) / (q • z - W)) • f z) 0 R := by
      simp_rw [sub_smul]
      have h₁ : forall z in sphere 0 R, z - w != 0 := by aesop (add simp sub_eq_zero)
      have h₃ : ContinuousOn f (sphere 0 R) :=
hf.2.mono sphere_subset_closedBall.trans_eq (closure_ball 0 hR.ne').symm
      rw [circleAverage_fun_sub]
      all_goals
        apply ContinuousOn.circleIntegrable hR.le
        fun_prop (disch := aesop)
    _ = f w := by
      rw [← abs_of_pos hR] at hw hf
      simp [← hf.circleAverage_smul_div hw, circleAverage_eq_circleIntegral (ne_of_lt hR).symm, h0]

/--
theorem `DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul` / 定理 `DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul`

English:
theorem DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul
  statement: [CompleteSpace E] {c : Complex}
  proof: by
  rcases le_or_gt R 0 with hR | hR
  · simp_all [ball_eq_empty.2 hR]
  have h₁g : DiffContOnCl Complex (fun z => f (z + c)) (ball 0 R) :=
    hf.comp (DifferentiableOn.diffContOnCl <| by fun_prop) (by intro; aesop)
  have h₂g : w - c in ball 0 R := by simpa using mem_ball_iff_norm.1 hw
  simpa [← circleAverage_map_add_const, herglotzRieszKernel_def]
    using circleAverage_re_smul_on_ball_zero h₁g h₂g

中文:
定理 DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul
  结论: [完备空间 E] {c : 复形}
  证明: by
  rcases le_or_gt R 0 with hR | hR
  · simp_all [ball_eq_empty.2 hR]
  have h₁g : DiffContOnCl Complex (fun z => f (z + c)) (ball 0 R) :=
    hf.comp (DifferentiableOn.diffContOnCl <| by fun_prop) (by intro; aesop)
  have h₂g : w - c in ball 0 R := by simpa using mem_ball_iff_norm.1 hw
  simpa [← circleAverage_map_add_const, herglotzRieszKernel_def]
    using circleAverage_re_smul_on_ball_zero h₁g h₂g

Depends on / 依赖: DiffContOnCl, DifferentiableOn, DifferentiableOn.diffContOnCl, ball_eq_empty, circleAverage_map_add_const, circleAverage_re_smul_on_ball_zero, diffContOnCl, fun_prop, herglotzRieszKernel_def, hf.comp, le_or_gt, mem_ball_iff_norm
-/
theorem DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul [CompleteSpace E] {c : Complex}
    (hf : DiffContOnCl Complex f (ball c R)) (hw : w in ball c R) :
    Real.circleAverage ((re ∘ herglotzRieszKernel c w) • f) c R = f w := by
  rcases le_or_gt R 0 with hR | hR
  · simp_all [ball_eq_empty.2 hR]
  have h₁g : DiffContOnCl Complex (fun z => f (z + c)) (ball 0 R) :=
    hf.comp (DifferentiableOn.diffContOnCl <| by fun_prop) (by intro; aesop)
  have h₂g : w - c in ball 0 R := by simpa using mem_ball_iff_norm.1 hw
  simpa [← circleAverage_map_add_const, herglotzRieszKernel_def]
    using circleAverage_re_smul_on_ball_zero h₁g h₂g

/--
theorem `DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul'` / 定理 `DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul'`

English:
theorem DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul'
  statement: [CompleteSpace E] {c : Complex}
  proof: hf.circleAverage_re_herglotzRieszKernel_smul hw

中文:
定理 DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul'
  结论: [完备空间 E] {c : 复形}
  证明: hf.circleAverage_re_herglotzRieszKernel_smul hw

Depends on / 依赖: circleAverage_re_herglotzRieszKernel_smul, hf.circleAverage_re_herglotzRieszKernel_smul
-/
theorem DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul' [CompleteSpace E] {c : Complex}
    (hf : DiffContOnCl Complex f (ball c R)) (hw : w in ball c R) :
    Real.circleAverage (fun z => ((z - c + (w - c)) / ((z - c) - (w - c))).re • f z) c R = f w :=
  hf.circleAverage_re_herglotzRieszKernel_smul hw

/--
theorem `DiffContOnCl.circleAverage_poissonKernel_smul` / 定理 `DiffContOnCl.circleAverage_poissonKernel_smul`

English:
theorem DiffContOnCl.circleAverage_poissonKernel_smul
  statement: [CompleteSpace E] {c : Complex}
  proof: by
  simp_rw [poissonKernel_eq_re_herglotzRieszKernel]
  apply hf.circleAverage_re_herglotzRieszKernel_smul hw

中文:
定理 DiffContOnCl.circleAverage_poissonKernel_smul
  结论: [完备空间 E] {c : 复形}
  证明: by
  simp_rw [poissonKernel_eq_re_herglotzRieszKernel]
  apply hf.circleAverage_re_herglotzRieszKernel_smul hw

Depends on / 依赖: circleAverage_re_herglotzRieszKernel_smul, hf.circleAverage_re_herglotzRieszKernel_smul, poissonKernel_eq_re_herglotzRieszKernel, simp_rw
-/
theorem DiffContOnCl.circleAverage_poissonKernel_smul [CompleteSpace E] {c : Complex}
    (hf : DiffContOnCl Complex f (ball c R)) (hw : w in ball c R) :
    Real.circleAverage (poissonKernel c w • f) c R = f w := by
  simp_rw [poissonKernel_eq_re_herglotzRieszKernel]
  apply hf.circleAverage_re_herglotzRieszKernel_smul hw

/--
theorem `DiffContOnCl.circleAverage_poissonKernel_smul'` / 定理 `DiffContOnCl.circleAverage_poissonKernel_smul'`

English:
theorem DiffContOnCl.circleAverage_poissonKernel_smul'
  statement: [CompleteSpace E] {c : Complex}
  proof: by
  apply hf.circleAverage_poissonKernel_smul hw

中文:
定理 DiffContOnCl.circleAverage_poissonKernel_smul'
  结论: [完备空间 E] {c : 复形}
  证明: by
  apply hf.circleAverage_poissonKernel_smul hw

Depends on / 依赖: circleAverage_poissonKernel_smul, hf.circleAverage_poissonKernel_smul
-/
theorem DiffContOnCl.circleAverage_poissonKernel_smul' [CompleteSpace E] {c : Complex}
    (hf : DiffContOnCl Complex f (ball c R)) (hw : w in ball c R) :
    Real.circleAverage (fun z => ((‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) / ‖(z - c) - (w - c)‖ ^ 2) • f z) c R
      = f w := by
  apply hf.circleAverage_poissonKernel_smul hw

/-!
## Derivative of the Herglotz–Riesz Kernel Integral
-/

/--
lemma `exists_ball_subset_forall_le_norm_circleMap_sub` / 引理 `exists_ball_subset_forall_le_norm_circleMap_sub`

English:
lemma exists_ball_subset_forall_le_norm_circleMap_sub
  given: (hw : w in ball c R)
  proof: by
  have : Disjoint {w} (ball c R)ᶜ := by simpa
  obtain ⟨d, hd, h_disj⟩ := this.exists_thickenings isCompact_singleton isOpen_ball.isClosed_compl
  refine ⟨d, hd, ?_, ?_⟩ <;> grw [thickening_singleton] at h_disj
  · simpa using (h_disj.mono_right (self_subset_thickening hd _)).subset_compl_left
  · intro x hx θ
    have := h_disj.subset_compl_right hx
    simp only [mem_compl_iff, mem_thickening_iff, mem_ball, not_lt, not_exists, not_and] at this
    simpa [← dist_eq_norm'] using this (circleMap c R θ) (by simp [dist_eq_norm, le_abs_self])

中文:
引理 存在_ball_subset_对任意_le_norm_circleMap_sub
  条件: (hw : w in ball c R)
  证明: by
  have : Disjoint {w} (ball c R)ᶜ := by simpa
  obtain ⟨d, hd, h_disj⟩ := this.exists_thickenings isCompact_singleton isOpen_ball.isClosed_compl
  refine ⟨d, hd, ?_, ?_⟩ <;> grw [thickening_singleton] at h_disj
  · simpa using (h_disj.mono_right (self_subset_thickening hd _)).subset_compl_left
  · intro x hx θ
    have := h_disj.subset_compl_right hx
    simp only [mem_compl_iff, mem_thickening_iff, mem_ball, not_lt, not_exists, not_and] at this
    simpa [← dist_eq_norm'] using this (circleMap c R θ) (by simp [dist_eq_norm, le_abs_self])
-/
private lemma exists_ball_subset_forall_le_norm_circleMap_sub (hw : w in ball c R) :
    exists d > 0, ball w d subseteq ball c R ∧ forall x in ball w d, forall θ : Real, d <= ‖circleMap c R θ - x‖ := by
  have : Disjoint {w} (ball c R)ᶜ := by simpa
  obtain ⟨d, hd, h_disj⟩ := this.exists_thickenings isCompact_singleton isOpen_ball.isClosed_compl
  refine ⟨d, hd, ?_, ?_⟩ <;> grw [thickening_singleton] at h_disj
  · simpa using (h_disj.mono_right (self_subset_thickening hd _)).subset_compl_left
  · intro x hx θ
    have := h_disj.subset_compl_right hx
    simp only [mem_compl_iff, mem_thickening_iff, mem_ball, not_lt, not_exists, not_and] at this
    simpa [← dist_eq_norm'] using this (circleMap c R θ) (by simp [dist_eq_norm, le_abs_self])

/--
theorem `hasDerivAt_circleAverage_herglotzRieszKernel_smul` / 定理 `hasDerivAt_circleAverage_herglotzRieszKernel_smul`

English:
theorem hasDerivAt_circleAverage_herglotzRieszKernel_smul
  statement: (hg : CircleIntegrable f 0 R)
  proof: by
  have hR : 0 < R := pos_of_mem_ball hw
  obtain ⟨d, hd, hsub, hdist⟩ := exists_ball_subset_forall_le_norm_circleMap_sub hw
  have hgm : AEStronglyMeasurable (fun θ => f (circleMap 0 R θ))
      (volume.restrict (uIoc 0 (2 * π))) := (intervalIntegrable_iff.1 hg).aestronglyMeasurable
  simp only [circleAverage_def]
  apply HasDerivAt.const_smul
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun x θ => (2 * circleMap 0 R θ / (circleMap 0 R θ - x) ^ 2) • f (circleMap 0 R θ))
    (bound := fun θ => 2 * R * (d ^ 2)⁻¹ * ‖f (circleMap 0 R θ)‖)
    (ball_mem_nhds w hd) ?meas1 ?int ?meas2 ?bound ?int_bound ?diff).2
  -- Measurability of the integrand, for `x` near `w`
  case meas1 =>
    filter_upwards with x
    apply AEStronglyMeasurable.smul _ hgm
    simp only [herglotzRieszKernel_def, sub_zero]
    exact Measurable.aestronglyMeasurable (by fun_prop)
  -- Integrability of the integrand at `w`
  case int =>
    have h₁ : CircleIntegrable (herglotzRieszKernel 0 w • f) 0 R :=
      hg.continuousOn_smul (continuousOn_herglotzRieszKernel_sphere hw)
    simpa only [CircleIntegrable, Pi.smul_apply'] using h₁
  -- Measurability of the differentiated integrand
  case meas2 =>
    exact (Measurable.aestronglyMeasurable (by fun_prop)).smul hgm
  -- Uniform bound for the differentiated integrand near `w`
  case bound =>
    filter_upwards with θ _ x hx
    have h₁ : ‖(2 : Complex)‖ = 2 := by norm_num
    rw [norm_smul]; rw [norm_div]; rw [norm_mul]; rw [norm_circleMap_zero]; rw [abs_of_pos hR]; rw [norm_pow]; rw [div_eq_mul_inv]; rw [h₁]
    gcongr
    exact hdist x hx θ
  -- Integrability of the bound
  case int_bound =>
    exact (IntervalIntegrable.norm hg).const_mul _
  -- Differentiability of the integrand in `x`, for `x` near `w`
  case diff =>
    filter_upwards with θ _ x hx
    have h₁ : circleMap 0 R θ - x != 0 := sub_ne_zero.2 (circleMap_ne_mem_ball (hsub hx) θ)
    have h₂ : HasDerivAt (fun x => herglotzRieszKernel 0 x (circleMap 0 R θ))
        (2 * circleMap 0 R θ / (circleMap 0 R θ - x) ^ 2) x := by
      have h₃ := ((hasDerivAt_id' x).const_add (circleMap 0 R θ)).div
        ((hasDerivAt_id' x).const_sub (circleMap 0 R θ)) h₁
      simpa [herglotzRieszKernel_def, sub_zero, sub_sub, ← two_mul, Pi.div_def] using h₃
    exact h₂.smul_const (f (circleMap 0 R θ))

中文:
定理 hasDerivAt_circleAverage_herglotzRieszKernel_smul
  结论: (hg : Circle整数egrable f 0 R)
  证明: by
  have hR : 0 < R := pos_of_mem_ball hw
  obtain ⟨d, hd, hsub, hdist⟩ := exists_ball_subset_forall_le_norm_circleMap_sub hw
  have hgm : AEStronglyMeasurable (fun θ => f (circleMap 0 R θ))
      (volume.restrict (uIoc 0 (2 * π))) := (intervalIntegrable_iff.1 hg).aestronglyMeasurable
  simp only [circleAverage_def]
  apply HasDerivAt.const_smul
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun x θ => (2 * circleMap 0 R θ / (circleMap 0 R θ - x) ^ 2) • f (circleMap 0 R θ))
    (bound := fun θ => 2 * R * (d ^ 2)⁻¹ * ‖f (circleMap 0 R θ)‖)
    (ball_mem_nhds w hd) ?meas1 ?int ?meas2 ?bound ?int_bound ?diff).2
  -- Measurability of the integrand, for `x` near `w`
  case meas1 =>
    filter_upwards with x
    apply AEStronglyMeasurable.smul _ hgm
    simp only [herglotzRieszKernel_def, sub_zero]
    exact Measurable.aestronglyMeasurable (by fun_prop)
  -- Integrability of the integrand at `w`
  case int =>
    have h₁ : CircleIntegrable (herglotzRieszKernel 0 w • f) 0 R :=
      hg.continuousOn_smul (continuousOn_herglotzRieszKernel_sphere hw)
    simpa only [CircleIntegrable, Pi.smul_apply'] using h₁
  -- Measurability of the differentiated integrand
  case meas2 =>
    exact (Measurable.aestronglyMeasurable (by fun_prop)).smul hgm
  -- Uniform bound for the differentiated integrand near `w`
  case bound =>
    filter_upwards with θ _ x hx
    have h₁ : ‖(2 : Complex)‖ = 2 := by norm_num
    rw [norm_smul]; rw [norm_div]; rw [norm_mul]; rw [norm_circleMap_zero]; rw [abs_of_pos hR]; rw [norm_pow]; rw [div_eq_mul_inv]; rw [h₁]
    gcongr
    exact hdist x hx θ
  -- Integrability of the bound
  case int_bound =>
    exact (IntervalIntegrable.norm hg).const_mul _
  -- Differentiability of the integrand in `x`, for `x` near `w`
  case diff =>
    filter_upwards with θ _ x hx
    have h₁ : circleMap 0 R θ - x != 0 := sub_ne_zero.2 (circleMap_ne_mem_ball (hsub hx) θ)
    have h₂ : HasDerivAt (fun x => herglotzRieszKernel 0 x (circleMap 0 R θ))
        (2 * circleMap 0 R θ / (circleMap 0 R θ - x) ^ 2) x := by
      have h₃ := ((hasDerivAt_id' x).const_add (circleMap 0 R θ)).div
        ((hasDerivAt_id' x).const_sub (circleMap 0 R θ)) h₁
      simpa [herglotzRieszKernel_def, sub_zero, sub_sub, ← two_mul, Pi.div_def] using h₃
    exact h₂.smul_const (f (circleMap 0 R θ))

Depends on / 依赖: AEStronglyMeasurable, HasDerivAt, HasDerivAt.const_smul, aestronglyMeasurable, circleAverage_def, circleMap, const_smul, exists_ball_subset_forall_le_norm_circleMap_sub, hasDerivAt_integral_of_dominated_loc_of_deriv_le, intervalIntegrable_iff, intervalIntegral, intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le, pos_of_mem_ball, restrict, volume, volume.restrict
-/
theorem hasDerivAt_circleAverage_herglotzRieszKernel_smul (hg : CircleIntegrable f 0 R)
    (hw : w in ball 0 R) :
    HasDerivAt (fun w => circleAverage (fun ζ => herglotzRieszKernel 0 w ζ • f ζ) 0 R)
      (circleAverage (fun ζ => (2 * ζ / (ζ - w) ^ 2) • f ζ) 0 R) w := by
  have hR : 0 < R := pos_of_mem_ball hw
  obtain ⟨d, hd, hsub, hdist⟩ := exists_ball_subset_forall_le_norm_circleMap_sub hw
  have hgm : AEStronglyMeasurable (fun θ => f (circleMap 0 R θ))
      (volume.restrict (uIoc 0 (2 * π))) := (intervalIntegrable_iff.1 hg).aestronglyMeasurable
  simp only [circleAverage_def]
  apply HasDerivAt.const_smul
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun x θ => (2 * circleMap 0 R θ / (circleMap 0 R θ - x) ^ 2) • f (circleMap 0 R θ))
    (bound := fun θ => 2 * R * (d ^ 2)⁻¹ * ‖f (circleMap 0 R θ)‖)
    (ball_mem_nhds w hd) ?meas1 ?int ?meas2 ?bound ?int_bound ?diff).2
  -- Measurability of the integrand, for `x` near `w`
  case meas1 =>
    filter_upwards with x
    apply AEStronglyMeasurable.smul _ hgm
    simp only [herglotzRieszKernel_def, sub_zero]
    exact Measurable.aestronglyMeasurable (by fun_prop)
  -- Integrability of the integrand at `w`
  case int =>
    have h₁ : CircleIntegrable (herglotzRieszKernel 0 w • f) 0 R :=
      hg.continuousOn_smul (continuousOn_herglotzRieszKernel_sphere hw)
    simpa only [CircleIntegrable, Pi.smul_apply'] using h₁
  -- Measurability of the differentiated integrand
  case meas2 =>
    exact (Measurable.aestronglyMeasurable (by fun_prop)).smul hgm
  -- Uniform bound for the differentiated integrand near `w`
  case bound =>
    filter_upwards with θ _ x hx
    have h₁ : ‖(2 : Complex)‖ = 2 := by norm_num
    rw [norm_smul]; rw [norm_div]; rw [norm_mul]; rw [norm_circleMap_zero]; rw [abs_of_pos hR]; rw [norm_pow]; rw [div_eq_mul_inv]; rw [h₁]
    gcongr
    exact hdist x hx θ
  -- Integrability of the bound
  case int_bound =>
    exact (IntervalIntegrable.norm hg).const_mul _
  -- Differentiability of the integrand in `x`, for `x` near `w`
  case diff =>
    filter_upwards with θ _ x hx
    have h₁ : circleMap 0 R θ - x != 0 := sub_ne_zero.2 (circleMap_ne_mem_ball (hsub hx) θ)
    have h₂ : HasDerivAt (fun x => herglotzRieszKernel 0 x (circleMap 0 R θ))
        (2 * circleMap 0 R θ / (circleMap 0 R θ - x) ^ 2) x := by
      have h₃ := ((hasDerivAt_id' x).const_add (circleMap 0 R θ)).div
        ((hasDerivAt_id' x).const_sub (circleMap 0 R θ)) h₁
      simpa [herglotzRieszKernel_def, sub_zero, sub_sub, ← two_mul, Pi.div_def] using h₃
    exact h₂.smul_const (f (circleMap 0 R θ))

/--
theorem `differentiableOn_circleAverage_herglotzRieszKernel_smul` / 定理 `differentiableOn_circleAverage_herglotzRieszKernel_smul`

English:
theorem differentiableOn_circleAverage_herglotzRieszKernel_smul
  given: (hg : CircleIntegrable f 0 R)
  proof: fun _ hw => hasDerivAt_circleAverage_herglotzRieszKernel_smul hg hw
.differentiableAt.differentiableWithinAt

中文:
定理 differentiableOn_circleAverage_herglotzRieszKernel_smul
  条件: (hg : Circle整数egrable f 0 R)
  证明: fun _ hw => hasDerivAt_circleAverage_herglotzRieszKernel_smul hg hw
.differentiableAt.differentiableWithinAt

Depends on / 依赖: differentiableAt, differentiableAt.differentiableWithinAt, differentiableWithinAt, hasDerivAt_circleAverage_herglotzRieszKernel_smul
-/
theorem differentiableOn_circleAverage_herglotzRieszKernel_smul (hg : CircleIntegrable f 0 R) :
    DifferentiableOn Complex
      (fun w => circleAverage (fun ζ => herglotzRieszKernel 0 w ζ • f ζ) 0 R) (ball 0 R) :=
  fun _ hw => hasDerivAt_circleAverage_herglotzRieszKernel_smul hg hw
.differentiableAt.differentiableWithinAt

/--
theorem `analyticOnNhd_circleAverage_herglotzRieszKernel_smul` / 定理 `analyticOnNhd_circleAverage_herglotzRieszKernel_smul`

English:
theorem analyticOnNhd_circleAverage_herglotzRieszKernel_smul
  statement: [CompleteSpace E]
  proof: (differentiableOn_circleAverage_herglotzRieszKernel_smul hg).analyticOnNhd isOpen_ball

中文:
定理 analyticOnNhd_circleAverage_herglotzRieszKernel_smul
  结论: [完备空间 E]
  证明: (differentiableOn_circleAverage_herglotzRieszKernel_smul hg).analyticOnNhd isOpen_ball

Depends on / 依赖: analyticOnNhd, differentiableOn_circleAverage_herglotzRieszKernel_smul, isOpen_ball
-/
theorem analyticOnNhd_circleAverage_herglotzRieszKernel_smul [CompleteSpace E]
    (hg : CircleIntegrable f 0 R) :
    AnalyticOnNhd Complex
      (fun w => circleAverage (fun ζ => herglotzRieszKernel 0 w ζ • f ζ) 0 R) (ball 0 R) :=
  (differentiableOn_circleAverage_herglotzRieszKernel_smul hg).analyticOnNhd isOpen_ball
