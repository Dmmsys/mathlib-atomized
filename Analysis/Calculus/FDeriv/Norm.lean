/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Differentiability of the norm in a real normed vector space

This file provides basic results about the differentiability of the norm in a real vector space.
Most are of the following kind: if the norm has some differentiability property
(`DifferentiableAt`, `ContDiffAt`, `HasStrictFDerivAt`, `HasFDerivAt`) at `x`, then so it has
at `t • x` when `t ≠ 0`.

## Main statements

* `ContDiffAt.contDiffAt_norm_smul`: If the norm is continuously differentiable up to order `n`
  at `x`, then so it is at `t • x` when `t ≠ 0`.
* `differentiableAt_norm_smul`: If `t ≠ 0`, the norm is differentiable at `x` if and only if
  it is at `t • x`.
* `HasFDerivAt.hasFDerivAt_norm_smul`: If the norm has a Fréchet derivative `f` at `x` and `t ≠ 0`,
  then it has `(SignType t) • f` as a Fréchet derivative at `t · x`.
* `fderiv_norm_smul` : `fderiv ℝ (‖·‖) (t • x) = (SignType.sign t : ℝ) • (fderiv ℝ (‖·‖) x)`,
  this holds without any differentiability assumptions.
* `DifferentiableAt.fderiv_norm_self`: if the norm is differentiable at `x`,
  then `fderiv ℝ (‖·‖) x x = ‖x‖`.
* `norm_fderiv_norm`: if the norm is differentiable at `x` then the operator norm of its derivative
  is `1` (on a non-trivial space).

## Tags

differentiability, norm

-/

public section

open ContinuousLinearMap Filter NNReal Real Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {n : WithTop Nat∞} {f : StrongDual Real E} {x : E} {t : Real}

variable (E) in
/--
theorem `not_differentiableAt_norm_zero` / 定理 `not_differentiableAt_norm_zero`

English:
theorem not_differentiableAt_norm_zero
  given: [Nontrivial E]
  proof: by
  obtain ⟨x, hx⟩ := NormedSpace.exists_lt_norm Real E 0
  intro h
  have : DifferentiableAt Real (fun t : Real => ‖t • x‖) 0 := DifferentiableAt.comp _ (by simpa) (by simp)
  have : DifferentiableAt Real (|·|) (0 : Real) := by
    simp_rw [norm_smul, norm_eq_abs] at this
    have aux : abs = fun t => (1 / ‖x‖) * (|t| * ‖x‖) := by field_simp
    rw [aux]
    exact this.const_mul _
  exact not_differentiableAt_abs_zero this

中文:
定理 not_differentiableAt_norm_zero
  条件: [非平凡 E]
  证明: by
  obtain ⟨x, hx⟩ := NormedSpace.exists_lt_norm Real E 0
  intro h
  have : DifferentiableAt Real (fun t : Real => ‖t • x‖) 0 := DifferentiableAt.comp _ (by simpa) (by simp)
  have : DifferentiableAt Real (|·|) (0 : Real) := by
    simp_rw [norm_smul, norm_eq_abs] at this
    have aux : abs = fun t => (1 / ‖x‖) * (|t| * ‖x‖) := by field_simp
    rw [aux]
    exact this.const_mul _
  exact not_differentiableAt_abs_zero this

Depends on / 依赖: DifferentiableAt, DifferentiableAt.comp, NormedSpace, NormedSpace.exists_lt_norm, const_mul, exists_lt_norm, norm_eq_abs, norm_smul, not_differentiableAt_abs_zero, simp_rw, this.const_mul
-/
theorem not_differentiableAt_norm_zero [Nontrivial E] :
    ¬DifferentiableAt Real (‖·‖) (0 : E) := by
  obtain ⟨x, hx⟩ := NormedSpace.exists_lt_norm Real E 0
  intro h
  have : DifferentiableAt Real (fun t : Real => ‖t • x‖) 0 := DifferentiableAt.comp _ (by simpa) (by simp)
  have : DifferentiableAt Real (|·|) (0 : Real) := by
    simp_rw [norm_smul, norm_eq_abs] at this
    have aux : abs = fun t => (1 / ‖x‖) * (|t| * ‖x‖) := by field_simp
    rw [aux]
    exact this.const_mul _
  exact not_differentiableAt_abs_zero this

/--
theorem `ContDiffAt.contDiffAt_norm_smul` / 定理 `ContDiffAt.contDiffAt_norm_smul`

English:
theorem ContDiffAt.contDiffAt_norm_smul
  given: (ht : t != 0) (h : ContDiffAt Real n (‖·‖) x)
  proof: by
  have h1 : ContDiffAt Real n (fun y => t⁻¹ • y) (t • x) := (contDiff_const_smul t⁻¹).contDiffAt
  have h2 : ContDiffAt Real n (fun y => |t| * ‖y‖) x := h.const_smul |t|
  conv at h2 => enter [4]; rw [← one_smul Real x, ← inv_mul_cancel₀ ht, mul_smul]
  convert! h2.comp (t • x) h1 using 1
  ext y
  simp only [Function.comp_apply]
  rw [norm_smul]; rw [← mul_assoc]; rw [norm_eq_abs]; rw [← abs_mul]; rw [mul_inv_cancel₀ ht]; rw [abs_one]; rw [one_mul]

中文:
定理 ContDiffAt.contDiffAt_norm_smul
  条件: (ht : t != 0) (h : ContDiffAt 实数 n (‖·‖) x)
  证明: by
  have h1 : ContDiffAt Real n (fun y => t⁻¹ • y) (t • x) := (contDiff_const_smul t⁻¹).contDiffAt
  have h2 : ContDiffAt Real n (fun y => |t| * ‖y‖) x := h.const_smul |t|
  conv at h2 => enter [4]; rw [← one_smul Real x, ← inv_mul_cancel₀ ht, mul_smul]
  convert! h2.comp (t • x) h1 using 1
  ext y
  simp only [Function.comp_apply]
  rw [norm_smul]; rw [← mul_assoc]; rw [norm_eq_abs]; rw [← abs_mul]; rw [mul_inv_cancel₀ ht]; rw [abs_one]; rw [one_mul]

Depends on / 依赖: ContDiffAt, Function, Function.comp_apply, abs_mul, abs_one, comp_apply, const_smul, contDiffAt, contDiff_const_smul, convert, h.const_smul, h2.comp, mul_assoc, mul_smul, norm_eq_abs, norm_smul, one_mul, one_smul
-/
theorem ContDiffAt.contDiffAt_norm_smul (ht : t != 0) (h : ContDiffAt Real n (‖·‖) x) :
    ContDiffAt Real n (‖·‖) (t • x) := by
  have h1 : ContDiffAt Real n (fun y => t⁻¹ • y) (t • x) := (contDiff_const_smul t⁻¹).contDiffAt
  have h2 : ContDiffAt Real n (fun y => |t| * ‖y‖) x := h.const_smul |t|
  conv at h2 => enter [4]; rw [← one_smul Real x, ← inv_mul_cancel₀ ht, mul_smul]
  convert! h2.comp (t • x) h1 using 1
  ext y
  simp only [Function.comp_apply]
  rw [norm_smul]; rw [← mul_assoc]; rw [norm_eq_abs]; rw [← abs_mul]; rw [mul_inv_cancel₀ ht]; rw [abs_one]; rw [one_mul]

/--
theorem `contDiffAt_norm_smul_iff` / 定理 `contDiffAt_norm_smul_iff`

English:
theorem contDiffAt_norm_smul_iff
  given: (ht : t != 0)
  proof: h.contDiffAt_norm_smul ht
  mpr hd := by
    convert! hd.contDiffAt_norm_smul (inv_ne_zero ht)
    rw [smul_smul]; rw [inv_mul_cancel₀ ht]; rw [one_smul]

中文:
定理 contDiffAt_norm_smul_iff
  条件: (ht : t != 0)
  证明: h.contDiffAt_norm_smul ht
  mpr hd := by
    convert! hd.contDiffAt_norm_smul (inv_ne_zero ht)
    rw [smul_smul]; rw [inv_mul_cancel₀ ht]; rw [one_smul]

Depends on / 依赖: contDiffAt_norm_smul, h.contDiffAt_norm_smul
-/
theorem contDiffAt_norm_smul_iff (ht : t != 0) :
    ContDiffAt Real n (‖·‖) x ↔ ContDiffAt Real n (‖·‖) (t • x) where
  mp h := h.contDiffAt_norm_smul ht
  mpr hd := by
    convert! hd.contDiffAt_norm_smul (inv_ne_zero ht)
    rw [smul_smul]; rw [inv_mul_cancel₀ ht]; rw [one_smul]

/--
theorem `ContDiffAt.contDiffAt_norm_of_smul` / 定理 `ContDiffAt.contDiffAt_norm_of_smul`

English:
theorem ContDiffAt.contDiffAt_norm_of_smul
  given: (h : ContDiffAt Real n (‖·‖) (t • x))
  proof: by
  rcases eq_or_ne n 0 with rfl | hn
  · apply contDiffAt_zero.2
    exact ⟨univ, univ_mem, continuous_norm.continuousOn⟩
  obtain rfl | ht := eq_or_ne t 0
  · suffices Subsingleton E by
      rw [eq_const_of_subsingleton (‖·‖) 0]
      exact contDiffAt_const
    rw [zero_smul] at h
    by_contra!
exact not_differentiableAt_norm_zero E h.differentiableAt hn
.2 h · exact contDiffAt_norm_smul_iff ht

中文:
定理 ContDiffAt.contDiffAt_norm_of_smul
  条件: (h : ContDiffAt 实数 n (‖·‖) (t • x))
  证明: by
  rcases eq_or_ne n 0 with rfl | hn
  · apply contDiffAt_zero.2
    exact ⟨univ, univ_mem, continuous_norm.continuousOn⟩
  obtain rfl | ht := eq_or_ne t 0
  · suffices Subsingleton E by
      rw [eq_const_of_subsingleton (‖·‖) 0]
      exact contDiffAt_const
    rw [zero_smul] at h
    by_contra!
exact not_differentiableAt_norm_zero E h.differentiableAt hn
.2 h · exact contDiffAt_norm_smul_iff ht

Depends on / 依赖: Subsingleton, contDiffAt_const, contDiffAt_norm_smul_iff, contDiffAt_zero, continuousOn, continuous_norm, continuous_norm.continuousOn, differentiableAt, eq_const_of_subsingleton, eq_or_ne, h.differentiableAt, not_differentiableAt_norm_zero, univ_mem, zero_smul
-/
theorem ContDiffAt.contDiffAt_norm_of_smul (h : ContDiffAt Real n (‖·‖) (t • x)) :
    ContDiffAt Real n (‖·‖) x := by
  rcases eq_or_ne n 0 with rfl | hn
  · apply contDiffAt_zero.2
    exact ⟨univ, univ_mem, continuous_norm.continuousOn⟩
  obtain rfl | ht := eq_or_ne t 0
  · suffices Subsingleton E by
      rw [eq_const_of_subsingleton (‖·‖) 0]
      exact contDiffAt_const
    rw [zero_smul] at h
    by_contra!
exact not_differentiableAt_norm_zero E h.differentiableAt hn
.2 h · exact contDiffAt_norm_smul_iff ht

/--
theorem `HasStrictFDerivAt.hasStrictFDerivAt_norm_smul` / 定理 `HasStrictFDerivAt.hasStrictFDerivAt_norm_smul`

English:
theorem HasStrictFDerivAt.hasStrictFDerivAt_norm_smul
  proof: by
  have h1 : HasStrictFDerivAt (fun y => t⁻¹ • y) (t⁻¹ • ContinuousLinearMap.id Real E) (t • x) :=
.const_smul t⁻¹ hasStrictFDerivAt_id (t • x)
  have h2 : HasStrictFDerivAt (fun y => |t| * ‖y‖) (|t| • f) x := h.const_smul |t|
  conv at h2 => enter [3]; rw [← one_smul Real x, ← inv_mul_cancel₀ ht, mul_smul]
  convert! h2.comp (t • x) h1 with y
  · rw [norm_smul, ← mul_assoc, norm_eq_abs, ← abs_mul, mul_inv_cancel₀ ht, abs_one, one_mul]
  ext y
  simp only [smul_apply, smul_eq_mul, comp_smulₛₗ, map_inv₀, RingHom.id_apply, comp_id]
  rw [eq_inv_mul_iff_mul_eq₀ ht]; rw [← mul_assoc]; rw [self_mul_sign]

中文:
定理 HasStrictFDerivAt.hasStrictFDerivAt_norm_smul
  证明: by
  have h1 : HasStrictFDerivAt (fun y => t⁻¹ • y) (t⁻¹ • ContinuousLinearMap.id Real E) (t • x) :=
.const_smul t⁻¹ hasStrictFDerivAt_id (t • x)
  have h2 : HasStrictFDerivAt (fun y => |t| * ‖y‖) (|t| • f) x := h.const_smul |t|
  conv at h2 => enter [3]; rw [← one_smul Real x, ← inv_mul_cancel₀ ht, mul_smul]
  convert! h2.comp (t • x) h1 with y
  · rw [norm_smul, ← mul_assoc, norm_eq_abs, ← abs_mul, mul_inv_cancel₀ ht, abs_one, one_mul]
  ext y
  simp only [smul_apply, smul_eq_mul, comp_smulₛₗ, map_inv₀, RingHom.id_apply, comp_id]
  rw [eq_inv_mul_iff_mul_eq₀ ht]; rw [← mul_assoc]; rw [self_mul_sign]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id, HasStrictFDerivAt, abs_mul, abs_one, const_smul, convert, h.const_smul, h2.comp, hasStrictFDerivAt_id, mul_assoc, mul_smul, norm_eq_abs, norm_smul, one_mul, one_smul, smul_apply, smul_eq_mul
-/
theorem HasStrictFDerivAt.hasStrictFDerivAt_norm_smul
    (ht : t != 0) (h : HasStrictFDerivAt (‖·‖) f x) :
    HasStrictFDerivAt (‖·‖) ((SignType.sign t : Real) • f) (t • x) := by
  have h1 : HasStrictFDerivAt (fun y => t⁻¹ • y) (t⁻¹ • ContinuousLinearMap.id Real E) (t • x) :=
.const_smul t⁻¹ hasStrictFDerivAt_id (t • x)
  have h2 : HasStrictFDerivAt (fun y => |t| * ‖y‖) (|t| • f) x := h.const_smul |t|
  conv at h2 => enter [3]; rw [← one_smul Real x, ← inv_mul_cancel₀ ht, mul_smul]
  convert! h2.comp (t • x) h1 with y
  · rw [norm_smul, ← mul_assoc, norm_eq_abs, ← abs_mul, mul_inv_cancel₀ ht, abs_one, one_mul]
  ext y
  simp only [smul_apply, smul_eq_mul, comp_smulₛₗ, map_inv₀, RingHom.id_apply, comp_id]
  rw [eq_inv_mul_iff_mul_eq₀ ht]; rw [← mul_assoc]; rw [self_mul_sign]

/--
theorem `HasStrictFDerivAt.hasStrictDerivAt_norm_smul_neg` / 定理 `HasStrictFDerivAt.hasStrictDerivAt_norm_smul_neg`

English:
theorem HasStrictFDerivAt.hasStrictDerivAt_norm_smul_neg
  proof: by
  simpa [ht] using h.hasStrictFDerivAt_norm_smul ht.ne

中文:
定理 HasStrictFDerivAt.hasStrictDerivAt_norm_smul_neg
  证明: by
  simpa [ht] using h.hasStrictFDerivAt_norm_smul ht.ne

Depends on / 依赖: h.hasStrictFDerivAt_norm_smul, hasStrictFDerivAt_norm_smul, ht.ne
-/
theorem HasStrictFDerivAt.hasStrictDerivAt_norm_smul_neg
    (ht : t < 0) (h : HasStrictFDerivAt (‖·‖) f x) :
    HasStrictFDerivAt (‖·‖) (-f) (t • x) := by
  simpa [ht] using h.hasStrictFDerivAt_norm_smul ht.ne

/--
theorem `HasStrictFDerivAt.hasStrictDerivAt_norm_smul_pos` / 定理 `HasStrictFDerivAt.hasStrictDerivAt_norm_smul_pos`

English:
theorem HasStrictFDerivAt.hasStrictDerivAt_norm_smul_pos
  proof: by
  simpa [ht] using h.hasStrictFDerivAt_norm_smul ht.ne'

中文:
定理 HasStrictFDerivAt.hasStrictDerivAt_norm_smul_pos
  证明: by
  simpa [ht] using h.hasStrictFDerivAt_norm_smul ht.ne'

Depends on / 依赖: h.hasStrictFDerivAt_norm_smul, hasStrictFDerivAt_norm_smul, ht.ne
-/
theorem HasStrictFDerivAt.hasStrictDerivAt_norm_smul_pos
    (ht : 0 < t) (h : HasStrictFDerivAt (‖·‖) f x) :
    HasStrictFDerivAt (‖·‖) f (t • x) := by
  simpa [ht] using h.hasStrictFDerivAt_norm_smul ht.ne'

/--
theorem `HasFDerivAt.hasFDerivAt_norm_smul` / 定理 `HasFDerivAt.hasFDerivAt_norm_smul`

English:
theorem HasFDerivAt.hasFDerivAt_norm_smul
  proof: by
  have h1 : HasFDerivAt (fun y => t⁻¹ • y) (t⁻¹ • ContinuousLinearMap.id Real E) (t • x) :=
.const_smul t⁻¹ hasFDerivAt_id (t • x)
  have h2 : HasFDerivAt (fun y => |t| * ‖y‖) (|t| • f) x := h.const_smul |t|
  conv at h2 => enter [3]; rw [← one_smul Real x, ← inv_mul_cancel₀ ht, mul_smul]
  convert! h2.comp (t • x) h1 using 2 with y
  · simp only [Function.comp_apply]
    rw [norm_smul]; rw [← mul_assoc]; rw [norm_eq_abs]; rw [← abs_mul]; rw [mul_inv_cancel₀ ht]; rw [abs_one]; rw [one_mul]
  · ext y
    simp only [smul_apply, smul_eq_mul, comp_smulₛₗ, map_inv₀, RingHom.id_apply, comp_id]
    rw [eq_inv_mul_iff_mul_eq₀ ht]; rw [← mul_assoc]; rw [self_mul_sign]

中文:
定理 在点处Fréchet可导.hasFDerivAt_norm_smul
  证明: by
  have h1 : HasFDerivAt (fun y => t⁻¹ • y) (t⁻¹ • ContinuousLinearMap.id Real E) (t • x) :=
.const_smul t⁻¹ hasFDerivAt_id (t • x)
  have h2 : HasFDerivAt (fun y => |t| * ‖y‖) (|t| • f) x := h.const_smul |t|
  conv at h2 => enter [3]; rw [← one_smul Real x, ← inv_mul_cancel₀ ht, mul_smul]
  convert! h2.comp (t • x) h1 using 2 with y
  · simp only [Function.comp_apply]
    rw [norm_smul]; rw [← mul_assoc]; rw [norm_eq_abs]; rw [← abs_mul]; rw [mul_inv_cancel₀ ht]; rw [abs_one]; rw [one_mul]
  · ext y
    simp only [smul_apply, smul_eq_mul, comp_smulₛₗ, map_inv₀, RingHom.id_apply, comp_id]
    rw [eq_inv_mul_iff_mul_eq₀ ht]; rw [← mul_assoc]; rw [self_mul_sign]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id, Function, Function.comp_apply, HasFDerivAt, abs_mul, abs_one, comp_apply, const_smul, convert, h.const_smul, h2.comp, hasFDerivAt_id, mul_assoc, mul_smul, norm_eq_abs, norm_smul, one_mul, one_smul
-/
theorem HasFDerivAt.hasFDerivAt_norm_smul
    (ht : t != 0) (h : HasFDerivAt (‖·‖) f x) :
    HasFDerivAt (‖·‖) ((SignType.sign t : Real) • f) (t • x) := by
  have h1 : HasFDerivAt (fun y => t⁻¹ • y) (t⁻¹ • ContinuousLinearMap.id Real E) (t • x) :=
.const_smul t⁻¹ hasFDerivAt_id (t • x)
  have h2 : HasFDerivAt (fun y => |t| * ‖y‖) (|t| • f) x := h.const_smul |t|
  conv at h2 => enter [3]; rw [← one_smul Real x, ← inv_mul_cancel₀ ht, mul_smul]
  convert! h2.comp (t • x) h1 using 2 with y
  · simp only [Function.comp_apply]
    rw [norm_smul]; rw [← mul_assoc]; rw [norm_eq_abs]; rw [← abs_mul]; rw [mul_inv_cancel₀ ht]; rw [abs_one]; rw [one_mul]
  · ext y
    simp only [smul_apply, smul_eq_mul, comp_smulₛₗ, map_inv₀, RingHom.id_apply, comp_id]
    rw [eq_inv_mul_iff_mul_eq₀ ht]; rw [← mul_assoc]; rw [self_mul_sign]

/--
theorem `HasFDerivAt.hasFDerivAt_norm_smul_neg` / 定理 `HasFDerivAt.hasFDerivAt_norm_smul_neg`

English:
theorem HasFDerivAt.hasFDerivAt_norm_smul_neg
  proof: by
  simpa [ht] using h.hasFDerivAt_norm_smul ht.ne

中文:
定理 在点处Fréchet可导.hasFDerivAt_norm_smul_neg
  证明: by
  simpa [ht] using h.hasFDerivAt_norm_smul ht.ne

Depends on / 依赖: h.hasFDerivAt_norm_smul, hasFDerivAt_norm_smul, ht.ne
-/
theorem HasFDerivAt.hasFDerivAt_norm_smul_neg
    (ht : t < 0) (h : HasFDerivAt (‖·‖) f x) :
    HasFDerivAt (‖·‖) (-f) (t • x) := by
  simpa [ht] using h.hasFDerivAt_norm_smul ht.ne

/--
theorem `HasFDerivAt.hasFDerivAt_norm_smul_pos` / 定理 `HasFDerivAt.hasFDerivAt_norm_smul_pos`

English:
theorem HasFDerivAt.hasFDerivAt_norm_smul_pos
  proof: by
  simpa [ht] using h.hasFDerivAt_norm_smul ht.ne'

中文:
定理 在点处Fréchet可导.hasFDerivAt_norm_smul_pos
  证明: by
  simpa [ht] using h.hasFDerivAt_norm_smul ht.ne'

Depends on / 依赖: h.hasFDerivAt_norm_smul, hasFDerivAt_norm_smul, ht.ne
-/
theorem HasFDerivAt.hasFDerivAt_norm_smul_pos
    (ht : 0 < t) (h : HasFDerivAt (‖·‖) f x) :
    HasFDerivAt (‖·‖) f (t • x) := by
  simpa [ht] using h.hasFDerivAt_norm_smul ht.ne'

/--
theorem `differentiableAt_norm_smul` / 定理 `differentiableAt_norm_smul`

English:
theorem differentiableAt_norm_smul
  given: (ht : t != 0)
  proof: (hd.hasFDerivAt.hasFDerivAt_norm_smul ht).differentiableAt
  mpr hd := by
    convert! (hd.hasFDerivAt.hasFDerivAt_norm_smul (inv_ne_zero ht)).differentiableAt
    rw [smul_smul]; rw [inv_mul_cancel₀ ht]; rw [one_smul]

中文:
定理 differentiableAt_norm_smul
  条件: (ht : t != 0)
  证明: (hd.hasFDerivAt.hasFDerivAt_norm_smul ht).differentiableAt
  mpr hd := by
    convert! (hd.hasFDerivAt.hasFDerivAt_norm_smul (inv_ne_zero ht)).differentiableAt
    rw [smul_smul]; rw [inv_mul_cancel₀ ht]; rw [one_smul]

Depends on / 依赖: differentiableAt, hasFDerivAt, hasFDerivAt_norm_smul, hd.hasFDerivAt.hasFDerivAt_norm_smul
-/
theorem differentiableAt_norm_smul (ht : t != 0) :
    DifferentiableAt Real (‖·‖) x ↔ DifferentiableAt Real (‖·‖) (t • x) where
  mp hd := (hd.hasFDerivAt.hasFDerivAt_norm_smul ht).differentiableAt
  mpr hd := by
    convert! (hd.hasFDerivAt.hasFDerivAt_norm_smul (inv_ne_zero ht)).differentiableAt
    rw [smul_smul]; rw [inv_mul_cancel₀ ht]; rw [one_smul]

/--
theorem `DifferentiableAt.differentiableAt_norm_of_smul` / 定理 `DifferentiableAt.differentiableAt_norm_of_smul`

English:
theorem DifferentiableAt.differentiableAt_norm_of_smul
  given: (h : DifferentiableAt Real (‖·‖) (t • x))
  proof: by
  obtain rfl | ht := eq_or_ne t 0
  · suffices Subsingleton E from (hasFDerivAt_of_subsingleton _ _).differentiableAt
    rw [zero_smul] at h
    by_contra!
    exact not_differentiableAt_norm_zero E h
.2 h · exact differentiableAt_norm_smul ht

中文:
定理 DifferentiableAt.differentiableAt_norm_of_smul
  条件: (h : DifferentiableAt 实数 (‖·‖) (t • x))
  证明: by
  obtain rfl | ht := eq_or_ne t 0
  · suffices Subsingleton E from (hasFDerivAt_of_subsingleton _ _).differentiableAt
    rw [zero_smul] at h
    by_contra!
    exact not_differentiableAt_norm_zero E h
.2 h · exact differentiableAt_norm_smul ht

Depends on / 依赖: Subsingleton, differentiableAt, differentiableAt_norm_smul, eq_or_ne, hasFDerivAt_of_subsingleton, not_differentiableAt_norm_zero, zero_smul
-/
theorem DifferentiableAt.differentiableAt_norm_of_smul (h : DifferentiableAt Real (‖·‖) (t • x)) :
    DifferentiableAt Real (‖·‖) x := by
  obtain rfl | ht := eq_or_ne t 0
  · suffices Subsingleton E from (hasFDerivAt_of_subsingleton _ _).differentiableAt
    rw [zero_smul] at h
    by_contra!
    exact not_differentiableAt_norm_zero E h
.2 h · exact differentiableAt_norm_smul ht

/--
theorem `DifferentiableAt.fderiv_norm_self` / 定理 `DifferentiableAt.fderiv_norm_self`

English:
theorem DifferentiableAt.fderiv_norm_self
  given: {x : E} (h : DifferentiableAt Real (‖·‖) x)
  proof: by
  rw [← h.lineDeriv_eq_fderiv]; rw [lineDeriv]
  have (t : Real) : ‖x + t • x‖ = |1 + t| * ‖x‖ := by
    rw [← norm_eq_abs]; rw [← norm_smul]; rw [add_smul]; rw [one_smul]
  simp_rw [this]
  rw [deriv_mul_const]
  · conv_lhs => enter [1, 1]; change _root_.abs ∘ (fun t => 1 + t)
    rw [deriv_comp]; rw [deriv_abs]; rw [deriv_const_add_id]
    · simp
    · exact differentiableAt_abs (by simp)
    · exact differentiableAt_id.const_add _
  · exact (differentiableAt_abs (by simp)).comp _ (differentiableAt_id.const_add _)

中文:
定理 DifferentiableAt.fderiv_norm_self
  条件: {x : E} (h : DifferentiableAt 实数 (‖·‖) x)
  证明: by
  rw [← h.lineDeriv_eq_fderiv]; rw [lineDeriv]
  have (t : Real) : ‖x + t • x‖ = |1 + t| * ‖x‖ := by
    rw [← norm_eq_abs]; rw [← norm_smul]; rw [add_smul]; rw [one_smul]
  simp_rw [this]
  rw [deriv_mul_const]
  · conv_lhs => enter [1, 1]; change _root_.abs ∘ (fun t => 1 + t)
    rw [deriv_comp]; rw [deriv_abs]; rw [deriv_const_add_id]
    · simp
    · exact differentiableAt_abs (by simp)
    · exact differentiableAt_id.const_add _
  · exact (differentiableAt_abs (by simp)).comp _ (differentiableAt_id.const_add _)

Depends on / 依赖: _root_, _root_.abs, add_smul, const_add, conv_lhs, deriv_abs, deriv_comp, deriv_const_add_id, deriv_mul_const, differentiableAt_abs, differentiableAt_id, differentiableAt_id.const_add, h.lineDeriv_eq_fderiv, lineDeriv, lineDeriv_eq_fderiv, norm_eq_abs, norm_smul, one_smul, simp_rw
-/
theorem DifferentiableAt.fderiv_norm_self {x : E} (h : DifferentiableAt Real (‖·‖) x) :
    fderiv Real (‖·‖) x x = ‖x‖ := by
  rw [← h.lineDeriv_eq_fderiv]; rw [lineDeriv]
  have (t : Real) : ‖x + t • x‖ = |1 + t| * ‖x‖ := by
    rw [← norm_eq_abs]; rw [← norm_smul]; rw [add_smul]; rw [one_smul]
  simp_rw [this]
  rw [deriv_mul_const]
  · conv_lhs => enter [1, 1]; change _root_.abs ∘ (fun t => 1 + t)
    rw [deriv_comp]; rw [deriv_abs]; rw [deriv_const_add_id]
    · simp
    · exact differentiableAt_abs (by simp)
    · exact differentiableAt_id.const_add _
  · exact (differentiableAt_abs (by simp)).comp _ (differentiableAt_id.const_add _)

variable (x t) in
/--
theorem `fderiv_norm_smul` / 定理 `fderiv_norm_smul`

English:
theorem fderiv_norm_smul
  proof: by
  cases subsingleton_or_nontrivial E
  · simp_rw [(hasFDerivAt_of_subsingleton _ _).fderiv, smul_zero]
  · by_cases hd : DifferentiableAt Real (‖·‖) x
    · obtain rfl | ht := eq_or_ne t 0
      · simp only [zero_smul, _root_.sign_zero, SignType.coe_zero]
exact fderiv_zero_of_not_differentiableAt not_differentiableAt_norm_zero E
      · rw [(hd.hasFDerivAt.hasFDerivAt_norm_smul ht).fderiv]
    · rw [fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt]
      · simp
      · exact mt DifferentiableAt.differentiableAt_norm_of_smul hd

中文:
定理 fderiv_norm_smul
  证明: by
  cases subsingleton_or_nontrivial E
  · simp_rw [(hasFDerivAt_of_subsingleton _ _).fderiv, smul_zero]
  · by_cases hd : DifferentiableAt Real (‖·‖) x
    · obtain rfl | ht := eq_or_ne t 0
      · simp only [zero_smul, _root_.sign_zero, SignType.coe_zero]
exact fderiv_zero_of_not_differentiableAt not_differentiableAt_norm_zero E
      · rw [(hd.hasFDerivAt.hasFDerivAt_norm_smul ht).fderiv]
    · rw [fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt]
      · simp
      · exact mt DifferentiableAt.differentiableAt_norm_of_smul hd

Depends on / 依赖: DifferentiableAt, DifferentiableAt.differen, SignType, SignType.coe_zero, _root_, _root_.sign_zero, coe_zero, differen, eq_or_ne, fderiv, fderiv_zero_of_not_differentiableAt, hasFDerivAt, hasFDerivAt_norm_smul, hasFDerivAt_of_subsingleton, hd.hasFDerivAt.hasFDerivAt_norm_smul, not_differentiableAt_norm_zero, sign_zero, simp_rw, smul_zero, subsingleton_or_nontrivial
-/
theorem fderiv_norm_smul :
    fderiv Real (‖·‖) (t • x) = (SignType.sign t : Real) • (fderiv Real (‖·‖) x) := by
  cases subsingleton_or_nontrivial E
  · simp_rw [(hasFDerivAt_of_subsingleton _ _).fderiv, smul_zero]
  · by_cases hd : DifferentiableAt Real (‖·‖) x
    · obtain rfl | ht := eq_or_ne t 0
      · simp only [zero_smul, _root_.sign_zero, SignType.coe_zero]
exact fderiv_zero_of_not_differentiableAt not_differentiableAt_norm_zero E
      · rw [(hd.hasFDerivAt.hasFDerivAt_norm_smul ht).fderiv]
    · rw [fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt]
      · simp
      · exact mt DifferentiableAt.differentiableAt_norm_of_smul hd

/--
theorem `fderiv_norm_smul_pos` / 定理 `fderiv_norm_smul_pos`

English:
theorem fderiv_norm_smul_pos
  given: (ht : 0 < t)
  proof: by
  simp [fderiv_norm_smul, ht]

中文:
定理 fderiv_norm_smul_pos
  条件: (ht : 0 < t)
  证明: by
  simp [fderiv_norm_smul, ht]

Depends on / 依赖: fderiv_norm_smul
-/
theorem fderiv_norm_smul_pos (ht : 0 < t) :
    fderiv Real (‖·‖) (t • x) = fderiv Real (‖·‖) x := by
  simp [fderiv_norm_smul, ht]

/--
theorem `fderiv_norm_smul_neg` / 定理 `fderiv_norm_smul_neg`

English:
theorem fderiv_norm_smul_neg
  given: (ht : t < 0)
  proof: by
  simp [fderiv_norm_smul, ht]

中文:
定理 fderiv_norm_smul_neg
  条件: (ht : t < 0)
  证明: by
  simp [fderiv_norm_smul, ht]

Depends on / 依赖: fderiv_norm_smul
-/
theorem fderiv_norm_smul_neg (ht : t < 0) :
    fderiv Real (‖·‖) (t • x) = -fderiv Real (‖·‖) x := by
  simp [fderiv_norm_smul, ht]

/--
theorem `norm_fderiv_norm` / 定理 `norm_fderiv_norm`

English:
theorem norm_fderiv_norm
  given: [Nontrivial E] (h : DifferentiableAt Real (‖·‖) x)
  proof: by
  have : x != 0 := fun hx => not_differentiableAt_norm_zero E (hx ▸ h)
  refine le_antisymm (NNReal.coe_one ▸ norm_fderiv_le_of_lipschitz Real lipschitzWith_one_norm) ?_
  apply le_of_mul_le_mul_right _ (norm_pos_iff.2 this)
  calc
    1 * ‖x‖ = fderiv Real (‖·‖) x x := by rw [one_mul, h.fderiv_norm_self]
    _ <= ‖fderiv Real (‖·‖) x x‖ := le_norm_self _
    _ <= ‖fderiv Real (‖·‖) x‖ * ‖x‖ := le_opNorm _ _

中文:
定理 norm_fderiv_norm
  条件: [非平凡 E] (h : DifferentiableAt 实数 (‖·‖) x)
  证明: by
  have : x != 0 := fun hx => not_differentiableAt_norm_zero E (hx ▸ h)
  refine le_antisymm (NNReal.coe_one ▸ norm_fderiv_le_of_lipschitz Real lipschitzWith_one_norm) ?_
  apply le_of_mul_le_mul_right _ (norm_pos_iff.2 this)
  calc
    1 * ‖x‖ = fderiv Real (‖·‖) x x := by rw [one_mul, h.fderiv_norm_self]
    _ <= ‖fderiv Real (‖·‖) x x‖ := le_norm_self _
    _ <= ‖fderiv Real (‖·‖) x‖ * ‖x‖ := le_opNorm _ _

Depends on / 依赖: NNReal, NNReal.coe_one, coe_one, fderiv, fderiv_norm_self, h.fderiv_norm_self, le_antisymm, le_norm_self, le_of_mul_le_mul_right, le_opNorm, lipschitzWith_one_norm, norm_fderiv_le_of_lipschitz, norm_pos_iff, not_differentiableAt_norm_zero, one_mul
-/
theorem norm_fderiv_norm [Nontrivial E] (h : DifferentiableAt Real (‖·‖) x) :
    ‖fderiv Real (‖·‖) x‖ = 1 := by
  have : x != 0 := fun hx => not_differentiableAt_norm_zero E (hx ▸ h)
  refine le_antisymm (NNReal.coe_one ▸ norm_fderiv_le_of_lipschitz Real lipschitzWith_one_norm) ?_
  apply le_of_mul_le_mul_right _ (norm_pos_iff.2 this)
  calc
    1 * ‖x‖ = fderiv Real (‖·‖) x x := by rw [one_mul, h.fderiv_norm_self]
    _ <= ‖fderiv Real (‖·‖) x x‖ := le_norm_self _
    _ <= ‖fderiv Real (‖·‖) x‖ * ‖x‖ := le_opNorm _ _
