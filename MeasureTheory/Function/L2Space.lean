/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # `L^2` space

If `E` is an inner product space over `𝕜` (`ℝ` or `ℂ`), then `Lp E 2 μ`
(defined in `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`)
is also an inner product space, with inner product defined as `inner f g := ∫ a, ⟪f a, g a⟫ ∂μ`.

### Main results

* `mem_L1_inner` : for `f` and `g` in `Lp E 2 μ`, the pointwise inner product `fun x ↦ ⟪f x, g x⟫`
  belongs to `Lp 𝕜 1 μ`.
* `integrable_inner` : for `f` and `g` in `Lp E 2 μ`, the pointwise inner product
  `fun x ↦ ⟪f x, g x⟫` is integrable.
* `L2.innerProductSpace` : `Lp E 2 μ` is an inner product space.
-/

@[expose] public section

noncomputable section

open TopologicalSpace MeasureTheory MeasureTheory.Lp Filter

open scoped NNReal ENNReal MeasureTheory InnerProductSpace

namespace MeasureTheory

section

variable {α F : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup F]

/--
theorem `MemLp.integrable_sq` / 定理 `MemLp.integrable_sq`

English:
theorem MemLp.integrable_sq
  given: {f : α -> Real} (h : MemLp f 2 μ)
  statement: Integrable (fun x => f x ^ 2) μ
  proof: by
  simpa [← memLp_one_iff_integrable] using h.norm_rpow two_ne_zero ENNReal.ofNat_ne_top

中文:
定理 MemLp.integrable_sq
  条件: {f : α -> 实数} (h : MemLp f 2 μ)
  结论: 整数egrable (fun x => f x ^ 2) μ
  证明: by
  simpa [← memLp_one_iff_integrable] using h.norm_rpow two_ne_zero ENNReal.ofNat_ne_top

Depends on / 依赖: ENNReal, ENNReal.ofNat_ne_top, h.norm_rpow, memLp_one_iff_integrable, norm_rpow, ofNat_ne_top, two_ne_zero
-/
theorem MemLp.integrable_sq {f : α -> Real} (h : MemLp f 2 μ) : Integrable (fun x => f x ^ 2) μ := by
  simpa [← memLp_one_iff_integrable] using h.norm_rpow two_ne_zero ENNReal.ofNat_ne_top

/--
theorem `memLp_two_iff_integrable_sq_norm` / 定理 `memLp_two_iff_integrable_sq_norm`

English:
theorem memLp_two_iff_integrable_sq_norm
  given: {f : α -> F} (hf : AEStronglyMeasurable f μ)
  proof: by
  rw [← memLp_one_iff_integrable]
  convert! (memLp_norm_rpow_iff hf two_ne_zero ENNReal.ofNat_ne_top).symm
  · simp
  · rw [div_eq_mul_inv, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]

中文:
定理 memLp_two_iff_integrable_sq_norm
  条件: {f : α -> F} (hf : AEStronglyMeasurable f μ)
  证明: by
  rw [← memLp_one_iff_integrable]
  convert! (memLp_norm_rpow_iff hf two_ne_zero ENNReal.ofNat_ne_top).symm
  · simp
  · rw [div_eq_mul_inv, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]

Depends on / 依赖: ENNReal, ENNReal.mul_inv_cancel, ENNReal.ofNat_ne_top, convert, div_eq_mul_inv, memLp_norm_rpow_iff, memLp_one_iff_integrable, mul_inv_cancel, ofNat_ne_top, two_ne_zero
-/
theorem memLp_two_iff_integrable_sq_norm {f : α -> F} (hf : AEStronglyMeasurable f μ) :
    MemLp f 2 μ ↔ Integrable (fun x => ‖f x‖ ^ 2) μ := by
  rw [← memLp_one_iff_integrable]
  convert! (memLp_norm_rpow_iff hf two_ne_zero ENNReal.ofNat_ne_top).symm
  · simp
  · rw [div_eq_mul_inv, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]

/--
theorem `memLp_two_iff_integrable_sq` / 定理 `memLp_two_iff_integrable_sq`

English:
theorem memLp_two_iff_integrable_sq
  given: {f : α -> Real} (hf : AEStronglyMeasurable f μ)
  proof: by
  convert! memLp_two_iff_integrable_sq_norm hf using 3
  simp

中文:
定理 memLp_two_iff_integrable_sq
  条件: {f : α -> 实数} (hf : AEStronglyMeasurable f μ)
  证明: by
  convert! memLp_two_iff_integrable_sq_norm hf using 3
  simp

Depends on / 依赖: convert, memLp_two_iff_integrable_sq_norm
-/
theorem memLp_two_iff_integrable_sq {f : α -> Real} (hf : AEStronglyMeasurable f μ) :
    MemLp f 2 μ ↔ Integrable (fun x => f x ^ 2) μ := by
  convert! memLp_two_iff_integrable_sq_norm hf using 3
  simp

end

section InnerProductSpace

variable {α : Type*} {m : MeasurableSpace α} {p : Real>=0∞} {μ : Measure α}
variable {E 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/--
theorem `MemLp.const_inner` / 定理 `MemLp.const_inner`

English:
theorem MemLp.const_inner
  given: (c : E) {f : α -> E} (hf : MemLp f p μ)
  statement: MemLp (fun a => ⟪c, f a⟫) p μ
  proof: hf.of_le_mul (AEStronglyMeasurable.inner aestronglyMeasurable_const hf.1)
    (Eventually.of_forall fun _ => norm_inner_le_norm _ _)

中文:
定理 MemLp.const_inner
  条件: (c : E) {f : α -> E} (hf : MemLp f p μ)
  结论: MemLp (fun a => ⟪c, f a⟫) p μ
  证明: hf.of_le_mul (AEStronglyMeasurable.inner aestronglyMeasurable_const hf.1)
    (Eventually.of_forall fun _ => norm_inner_le_norm _ _)

Depends on / 依赖: AEStronglyMeasurable, AEStronglyMeasurable.inner, Eventually, Eventually.of_forall, aestronglyMeasurable_const, hf.of_le_mul, norm_inner_le_norm, of_forall, of_le_mul
-/
theorem MemLp.const_inner (c : E) {f : α -> E} (hf : MemLp f p μ) : MemLp (fun a => ⟪c, f a⟫) p μ :=
  hf.of_le_mul (AEStronglyMeasurable.inner aestronglyMeasurable_const hf.1)
    (Eventually.of_forall fun _ => norm_inner_le_norm _ _)

/--
theorem `MemLp.inner_const` / 定理 `MemLp.inner_const`

English:
theorem MemLp.inner_const
  given: {f : α -> E} (hf : MemLp f p μ) (c : E)
  statement: MemLp (fun a => ⟪f a, c⟫) p μ
  proof: hf.of_le_mul (c := ‖c‖) (AEStronglyMeasurable.inner hf.1 aestronglyMeasurable_const)
    (Eventually.of_forall fun x => by rw [mul_comm]; exact norm_inner_le_norm _ _)

中文:
定理 MemLp.inner_const
  条件: {f : α -> E} (hf : MemLp f p μ) (c : E)
  结论: MemLp (fun a => ⟪f a, c⟫) p μ
  证明: hf.of_le_mul (c := ‖c‖) (AEStronglyMeasurable.inner hf.1 aestronglyMeasurable_const)
    (Eventually.of_forall fun x => by rw [mul_comm]; exact norm_inner_le_norm _ _)

Depends on / 依赖: AEStronglyMeasurable, AEStronglyMeasurable.inner, Eventually, Eventually.of_forall, aestronglyMeasurable_const, hf.of_le_mul, mul_comm, norm_inner_le_norm, of_forall, of_le_mul
-/
theorem MemLp.inner_const {f : α -> E} (hf : MemLp f p μ) (c : E) : MemLp (fun a => ⟪f a, c⟫) p μ :=
  hf.of_le_mul (c := ‖c‖) (AEStronglyMeasurable.inner hf.1 aestronglyMeasurable_const)
    (Eventually.of_forall fun x => by rw [mul_comm]; exact norm_inner_le_norm _ _)

variable {f : α -> E}

@[fun_prop]
/--
theorem `Integrable.const_inner` / 定理 `Integrable.const_inner`

English:
theorem Integrable.const_inner
  given: (c : E) (hf : Integrable f μ)
  proof: by
  rw [← memLp_one_iff_integrable] at hf ⊢; exact hf.const_inner c

@[fun_prop]

中文:
定理 Integrable.const_inner
  条件: (c : E) (hf : 整数egrable f μ)
  证明: by
  rw [← memLp_one_iff_integrable] at hf ⊢; exact hf.const_inner c

@[fun_prop]

Depends on / 依赖: const_inner, hf.const_inner, memLp_one_iff_integrable
-/
theorem Integrable.const_inner (c : E) (hf : Integrable f μ) :
    Integrable (fun x => ⟪c, f x⟫) μ := by
  rw [← memLp_one_iff_integrable] at hf ⊢; exact hf.const_inner c

@[fun_prop]
/--
theorem `Integrable.inner_const` / 定理 `Integrable.inner_const`

English:
theorem Integrable.inner_const
  given: (hf : Integrable f μ) (c : E)
  proof: by
  rw [← memLp_one_iff_integrable] at hf ⊢; exact hf.inner_const c

中文:
定理 Integrable.inner_const
  条件: (hf : 整数egrable f μ) (c : E)
  证明: by
  rw [← memLp_one_iff_integrable] at hf ⊢; exact hf.inner_const c

Depends on / 依赖: hf.inner_const, inner_const, memLp_one_iff_integrable
-/
theorem Integrable.inner_const (hf : Integrable f μ) (c : E) :
    Integrable (fun x => ⟪f x, c⟫) μ := by
  rw [← memLp_one_iff_integrable] at hf ⊢; exact hf.inner_const c

variable [CompleteSpace E] [NormedSpace Real E]

/--
theorem `_root_.integral_inner` / 定理 `_root_.integral_inner`

English:
theorem _root_.integral_inner
  given: {f : α -> E} (hf : Integrable f μ) (c : E)
  proof: ((innerSL 𝕜 c).restrictScalars Real).integral_comp_comm hf

中文:
定理 _root_.integral_inner
  条件: {f : α -> E} (hf : 整数egrable f μ) (c : E)
  证明: ((innerSL 𝕜 c).restrictScalars Real).integral_comp_comm hf

Depends on / 依赖: innerSL, integral_comp_comm, restrictScalars
-/
theorem _root_.integral_inner {f : α -> E} (hf : Integrable f μ) (c : E) :
    ∫ x, ⟪c, f x⟫ ∂μ = ⟪c, ∫ x, f x ∂μ⟫ :=
  ((innerSL 𝕜 c).restrictScalars Real).integral_comp_comm hf

variable (𝕜)

/--
theorem `_root_.integral_eq_zero_of_forall_integral_inner_eq_zero` / 定理 `_root_.integral_eq_zero_of_forall_integral_inner_eq_zero`

English:
theorem _root_.integral_eq_zero_of_forall_integral_inner_eq_zero
  statement: (f : α -> E) (hf : Integrable f μ)
  proof: by
  specialize hf_int (∫ x, f x ∂μ); rwa [integral_inner hf, inner_self_eq_zero] at hf_int

中文:
定理 _root_.integral_eq_zero_of_forall_integral_inner_eq_zero
  结论: (f : α -> E) (hf : 整数egrable f μ)
  证明: by
  specialize hf_int (∫ x, f x ∂μ); rwa [integral_inner hf, inner_self_eq_zero] at hf_int

Depends on / 依赖: hf_int, inner_self_eq_zero, integral_inner, specialize
-/
theorem _root_.integral_eq_zero_of_forall_integral_inner_eq_zero (f : α -> E) (hf : Integrable f μ)
    (hf_int : forall c : E, ∫ x, ⟪c, f x⟫ ∂μ = 0) : ∫ x, f x ∂μ = 0 := by
  specialize hf_int (∫ x, f x ∂μ); rwa [integral_inner hf, inner_self_eq_zero] at hf_int

end InnerProductSpace

namespace L2

variable {α E F 𝕜 : Type*} [RCLike 𝕜] {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/--
theorem `eLpNorm_rpow_two_norm_lt_top` / 定理 `eLpNorm_rpow_two_norm_lt_top`

English:
theorem eLpNorm_rpow_two_norm_lt_top
  given: (f : Lp F 2 μ)
  proof: by
  have h_two : ENNReal.ofReal (2 : Real) = 2 := by simp
  rw [eLpNorm_norm_rpow f zero_lt_two]; rw [one_mul]; rw [h_two]
  exact ENNReal.rpow_lt_top_of_nonneg zero_le_two (Lp.eLpNorm_ne_top f)

中文:
定理 eLpNorm_rpow_two_norm_lt_top
  条件: (f : Lp F 2 μ)
  证明: by
  have h_two : ENNReal.ofReal (2 : Real) = 2 := by simp
  rw [eLpNorm_norm_rpow f zero_lt_two]; rw [one_mul]; rw [h_two]
  exact ENNReal.rpow_lt_top_of_nonneg zero_le_two (Lp.eLpNorm_ne_top f)

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.rpow_lt_top_of_nonneg, Lp.eLpNorm_ne_top, eLpNorm_ne_top, eLpNorm_norm_rpow, h_two, ofReal, one_mul, rpow_lt_top_of_nonneg, zero_le_two, zero_lt_two
-/
theorem eLpNorm_rpow_two_norm_lt_top (f : Lp F 2 μ) :
    eLpNorm (fun x => ‖f x‖ ^ (2 : Real)) 1 μ < ∞ := by
  have h_two : ENNReal.ofReal (2 : Real) = 2 := by simp
  rw [eLpNorm_norm_rpow f zero_lt_two]; rw [one_mul]; rw [h_two]
  exact ENNReal.rpow_lt_top_of_nonneg zero_le_two (Lp.eLpNorm_ne_top f)

/--
theorem `eLpNorm_inner_lt_top` / 定理 `eLpNorm_inner_lt_top`

English:
theorem eLpNorm_inner_lt_top
  given: (f g : α ->₂[μ] E)
  statement: eLpNorm (fun x : α => ⟪f x, g x⟫) 1 μ < ∞
  proof: by
  have h : forall x, ‖⟪f x, g x⟫‖ <= ‖‖f x‖ ^ (2 : Real) + ‖g x‖ ^ (2 : Real)‖ := by
    intro x
    rw [← @Nat.cast_two Real]; rw [Real.rpow_natCast]; rw [Real.rpow_natCast]
    calc
      ‖⟪f x, g x⟫‖ <= ‖f x‖ * ‖g x‖ := norm_inner_le_norm _ _
      _ <= 2 * ‖f x‖ * ‖g x‖ := by
        gcongr
 

中文:
定理 eLpNorm_inner_lt_top
  条件: (f g : α ->₂[μ] E)
  结论: eLpNorm (fun x : α => ⟪f x, g x⟫) 1 μ < ∞
  证明: by
  have h : forall x, ‖⟪f x, g x⟫‖ <= ‖‖f x‖ ^ (2 : Real) + ‖g x‖ ^ (2 : Real)‖ := by
    intro x
    rw [← @Nat.cast_two Real]; rw [Real.rpow_natCast]; rw [Real.rpow_natCast]
    calc
      ‖⟪f x, g x⟫‖ <= ‖f x‖ * ‖g x‖ := norm_inner_le_norm _ _
      _ <= 2 * ‖f x‖ * ‖g x‖ := by
        gcongr
 

Depends on / 依赖: Nat.cast_two, Real.rpow_natCast, cast_two, le_mul_of_one_le_left, norm_inner_le_norm, norm_nonneg, one_le_two, rpow_natCast
-/
theorem eLpNorm_inner_lt_top (f g : α ->₂[μ] E) : eLpNorm (fun x : α => ⟪f x, g x⟫) 1 μ < ∞ := by
  have h : forall x, ‖⟪f x, g x⟫‖ <= ‖‖f x‖ ^ (2 : Real) + ‖g x‖ ^ (2 : Real)‖ := by
    intro x
    rw [← @Nat.cast_two Real]; rw [Real.rpow_natCast]; rw [Real.rpow_natCast]
    calc
      ‖⟪f x, g x⟫‖ <= ‖f x‖ * ‖g x‖ := norm_inner_le_norm _ _
      _ <= 2 * ‖f x‖ * ‖g x‖ := by
        gcongr
        exact le_mul_of_one_le_left (norm_nonneg _) one_le_two
      -- TODO(kmill): the type ascription is getting around an elaboration error
      _ <= ‖(‖f x‖ ^ 2 + ‖g x‖ ^ 2 : Real)‖ := (two_mul_le_add_sq _ _).trans (le_abs_self _)
  refine (eLpNorm_mono_ae (ae_of_all _ h)).trans_lt ((eLpNorm_add_le ?_ ?_ le_rfl).trans_lt ?_)
  · exact ((Lp.aestronglyMeasurable f).norm.aemeasurable.pow_const _).aestronglyMeasurable
  · exact ((Lp.aestronglyMeasurable g).norm.aemeasurable.pow_const _).aestronglyMeasurable
  rw [ENNReal.add_lt_top]
  exact ⟨eLpNorm_rpow_two_norm_lt_top f, eLpNorm_rpow_two_norm_lt_top g⟩

section InnerProductSpace

open scoped ComplexConjugate

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inner 𝕜 (α ->₂[μ] E)
  body: ⟨fun f g => ∫ a, ⟪f a, g a⟫ ∂μ⟩

中文:
实例 :
  签名: Inner 𝕜 (α ->₂[μ] E)
  定义体: ⟨fun f g => ∫ a, ⟪f a, g a⟫ ∂μ⟩
-/
instance : Inner 𝕜 (α ->₂[μ] E) :=
  ⟨fun f g => ∫ a, ⟪f a, g a⟫ ∂μ⟩

/--
theorem `inner_def` / 定理 `inner_def`

English:
theorem inner_def
  given: (f g : α ->₂[μ] E)
  statement: ⟪f, g⟫ = ∫ a : α, ⟪f a, g a⟫ ∂μ
  proof: rfl

中文:
定理 inner_def
  条件: (f g : α ->₂[μ] E)
  结论: ⟪f, g⟫ = ∫ a : α, ⟪f a, g a⟫ ∂μ
  证明: rfl

Depends on / 依赖: Algebra, integralClosure
-/
theorem inner_def (f g : α ->₂[μ] E) : ⟪f, g⟫ = ∫ a : α, ⟪f a, g a⟫ ∂μ :=
  rfl

/--
theorem `integral_inner_eq_sq_eLpNorm` / 定理 `integral_inner_eq_sq_eLpNorm`

English:
theorem integral_inner_eq_sq_eLpNorm
  given: (f : α ->₂[μ] E)
  proof: by
  simp_rw [inner_self_eq_norm_sq_to_K]
  norm_cast
  rw [integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact Filter.Eventually.of_forall fun x => sq_nonneg _
  · exact ((Lp.aestronglyMeasurable f).norm.aemeasurable.pow_const _).aestronglyMeasurable
  congr
  ext1 x
  have h_two : (2 : Rea

中文:
定理 integral_inner_eq_sq_eLpNorm
  条件: (f : α ->₂[μ] E)
  证明: by
  simp_rw [inner_self_eq_norm_sq_to_K]
  norm_cast
  rw [integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact Filter.Eventually.of_forall fun x => sq_nonneg _
  · exact ((Lp.aestronglyMeasurable f).norm.aemeasurable.pow_const _).aestronglyMeasurable
  congr
  ext1 x
  have h_two : (2 : Rea

Depends on / 依赖: ENNReal, ENNReal.ofReal_rpow_of_nonneg, Eventually, Filter, Filter.Eventually.of_forall, Lp.aestronglyMeasurable, Real.rpow_natCast, aemeasurable, aestronglyMeasurable, h_two, inner_self_eq_norm_sq_to_K, integral_eq_lintegral_of_nonneg_ae, norm.aemeasurable.pow_const, norm_nonneg, ofReal_norm, ofReal_rpow_of_nonneg, of_forall, pow_const, rotate_left, rpow_natCast
-/
theorem integral_inner_eq_sq_eLpNorm (f : α ->₂[μ] E) :
    ∫ a, ⟪f a, f a⟫ ∂μ = ENNReal.toReal (∫⁻ a, (‖f a‖₊ : Real>=0∞) ^ (2 : Real) ∂μ) := by
  simp_rw [inner_self_eq_norm_sq_to_K]
  norm_cast
  rw [integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact Filter.Eventually.of_forall fun x => sq_nonneg _
  · exact ((Lp.aestronglyMeasurable f).norm.aemeasurable.pow_const _).aestronglyMeasurable
  congr
  ext1 x
  have h_two : (2 : Real) = ((2 : Nat) : Real) := by simp
  rw [← Real.rpow_natCast _ 2]; rw [← h_two]; rw [←
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two]; rw [ofReal_norm]
  norm_cast

/--
theorem `norm_sq_eq_re_inner` / 定理 `norm_sq_eq_re_inner`

English:
theorem norm_sq_eq_re_inner
  given: (f : α ->₂[μ] E)
  statement: ‖f‖ ^ 2 = RCLike.re ⟪f, f⟫
  proof: by
  have h_two : (2 : Real>=0∞).toReal = 2 := by simp
  rw [inner_def]; rw [integral_inner_eq_sq_eLpNorm]; rw [norm_def]; rw [← ENNReal.toReal_pow]; rw [RCLike.ofReal_re]; rw [ENNReal.toReal_eq_toReal_iff' (ENNReal.pow_ne_top (Lp.eLpNorm_ne_top f)) _]
  · rw [← ENNReal.rpow_natCast, eLpNorm_eq_eLpN

中文:
定理 norm_sq_eq_re_inner
  条件: (f : α ->₂[μ] E)
  结论: ‖f‖ ^ 2 = RCLike.re ⟪f, f⟫
  证明: by
  have h_two : (2 : Real>=0∞).toReal = 2 := by simp
  rw [inner_def]; rw [integral_inner_eq_sq_eLpNorm]; rw [norm_def]; rw [← ENNReal.toReal_pow]; rw [RCLike.ofReal_re]; rw [ENNReal.toReal_eq_toReal_iff' (ENNReal.pow_ne_top (Lp.eLpNorm_ne_top f)) _]
  · rw [← ENNReal.rpow_natCast, eLpNorm_eq_eLpN
-/
private theorem norm_sq_eq_re_inner (f : α ->₂[μ] E) : ‖f‖ ^ 2 = RCLike.re ⟪f, f⟫ := by
  have h_two : (2 : Real>=0∞).toReal = 2 := by simp
  rw [inner_def]; rw [integral_inner_eq_sq_eLpNorm]; rw [norm_def]; rw [← ENNReal.toReal_pow]; rw [RCLike.ofReal_re]; rw [ENNReal.toReal_eq_toReal_iff' (ENNReal.pow_ne_top (Lp.eLpNorm_ne_top f)) _]
  · rw [← ENNReal.rpow_natCast, eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top, eLpNorm', ←
      ENNReal.rpow_mul, one_div, h_two]
    simp [enorm_eq_nnnorm]
  · refine (lintegral_rpow_enorm_lt_top_of_eLpNorm'_lt_top zero_lt_two (ε := E) ?_).ne
    rw [← h_two]; rw [← eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top]
    finiteness

/--
theorem `mem_L1_inner` / 定理 `mem_L1_inner`

English:
theorem mem_L1_inner
  given: (f g : α ->₂[μ] E)
  proof: by
  simp_rw [mem_Lp_iff_eLpNorm_lt_top, eLpNorm_aeeqFun]; exact eLpNorm_inner_lt_top f g

中文:
定理 mem_L1_inner
  条件: (f g : α ->₂[μ] E)
  证明: by
  simp_rw [mem_Lp_iff_eLpNorm_lt_top, eLpNorm_aeeqFun]; exact eLpNorm_inner_lt_top f g

Depends on / 依赖: IsScalarTower, eLpNorm_aeeqFun, eLpNorm_inner_lt_top, integralClosure, mem_Lp_iff_eLpNorm_lt_top, simp_rw
-/
theorem mem_L1_inner (f g : α ->₂[μ] E) :
    AEEqFun.mk (fun x => ⟪f x, g x⟫)
        ((Lp.aestronglyMeasurable f).inner (Lp.aestronglyMeasurable g)) in
      Lp 𝕜 1 μ := by
  simp_rw [mem_Lp_iff_eLpNorm_lt_top, eLpNorm_aeeqFun]; exact eLpNorm_inner_lt_top f g

/--
theorem `integrable_inner` / 定理 `integrable_inner`

English:
theorem integrable_inner
  given: (f g : α ->₂[μ] E)
  statement: Integrable (fun x : α => ⟪f x, g x⟫) μ
  proof: (integrable_congr
        (AEEqFun.coeFn_mk (fun x => ⟪f x, g x⟫)
          ((Lp.aestronglyMeasurable f).inner (Lp.aestronglyMeasurable g)))).mp
    (AEEqFun.integrable_iff_mem_L1.mpr (mem_L1_inner f g))

中文:
定理 integrable_inner
  条件: (f g : α ->₂[μ] E)
  结论: 整数egrable (fun x : α => ⟪f x, g x⟫) μ
  证明: (integrable_congr
        (AEEqFun.coeFn_mk (fun x => ⟪f x, g x⟫)
          ((Lp.aestronglyMeasurable f).inner (Lp.aestronglyMeasurable g)))).mp
    (AEEqFun.integrable_iff_mem_L1.mpr (mem_L1_inner f g))

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_mk, AEEqFun.integrable_iff_mem_L1.mpr, Lp.aestronglyMeasurable, MulSemiringAction, aestronglyMeasurable, coeFn_mk, integrable_congr, integrable_iff_mem_L1, integralClosure, mem_L1_inner
-/
theorem integrable_inner (f g : α ->₂[μ] E) : Integrable (fun x : α => ⟪f x, g x⟫) μ :=
  (integrable_congr
        (AEEqFun.coeFn_mk (fun x => ⟪f x, g x⟫)
          ((Lp.aestronglyMeasurable f).inner (Lp.aestronglyMeasurable g)))).mp
    (AEEqFun.integrable_iff_mem_L1.mpr (mem_L1_inner f g))

/--
theorem `add_left'` / 定理 `add_left'`

English:
theorem add_left'
  given: (f f' g : α ->₂[μ] E)
  statement: ⟪f + f', g⟫ = ⟪f, g⟫ + ⟪f', g⟫
  proof: by
  simp_rw [inner_def, ← integral_add (integrable_inner (𝕜 := 𝕜) f g) (integrable_inner f' g),
    ← inner_add_left]
  refine integral_congr_ae ((coeFn_add f f').mono fun x hx => ?_)
  simp only [hx, Pi.add_apply]

中文:
定理 add_left'
  条件: (f f' g : α ->₂[μ] E)
  结论: ⟪f + f', g⟫ = ⟪f, g⟫ + ⟪f', g⟫
  证明: by
  simp_rw [inner_def, ← integral_add (integrable_inner (𝕜 := 𝕜) f g) (integrable_inner f' g),
    ← inner_add_left]
  refine integral_congr_ae ((coeFn_add f f').mono fun x hx => ?_)
  simp only [hx, Pi.add_apply]

Depends on / 依赖: SMulDistribClass, integralClosure
-/
private theorem add_left' (f f' g : α ->₂[μ] E) : ⟪f + f', g⟫ = ⟪f, g⟫ + ⟪f', g⟫ := by
  simp_rw [inner_def, ← integral_add (integrable_inner (𝕜 := 𝕜) f g) (integrable_inner f' g),
    ← inner_add_left]
  refine integral_congr_ae ((coeFn_add f f').mono fun x hx => ?_)
  simp only [hx, Pi.add_apply]

/--
theorem `smul_left'` / 定理 `smul_left'`

English:
theorem smul_left'
  given: (f g : α ->₂[μ] E) (r : 𝕜)
  statement: ⟪r • f, g⟫ = conj r * ⟪f, g⟫
  proof: by
  rw [inner_def]; rw [inner_def]; rw [← smul_eq_mul]; rw [← integral_smul]
  refine integral_congr_ae ((coeFn_smul r f).mono fun x hx => ?_)
  simp only
  rw [smul_eq_mul]; rw [← inner_smul_left]; rw [hx]; rw [Pi.smul_apply]

中文:
定理 smul_left'
  条件: (f g : α ->₂[μ] E) (r : 𝕜)
  结论: ⟪r • f, g⟫ = conj r * ⟪f, g⟫
  证明: by
  rw [inner_def]; rw [inner_def]; rw [← smul_eq_mul]; rw [← integral_smul]
  refine integral_congr_ae ((coeFn_smul r f).mono fun x hx => ?_)
  simp only
  rw [smul_eq_mul]; rw [← inner_smul_left]; rw [hx]; rw [Pi.smul_apply]
-/
private theorem smul_left' (f g : α ->₂[μ] E) (r : 𝕜) : ⟪r • f, g⟫ = conj r * ⟪f, g⟫ := by
  rw [inner_def]; rw [inner_def]; rw [← smul_eq_mul]; rw [← integral_smul]
  refine integral_congr_ae ((coeFn_smul r f).mono fun x hx => ?_)
  simp only
  rw [smul_eq_mul]; rw [← inner_smul_left]; rw [hx]; rw [Pi.smul_apply]

/--
Instance `innerProductSpace` / 实例 `innerProductSpace`

English:
instance innerProductSpace
  signature: : InnerProductSpace 𝕜 (α ->₂[μ] E) where
  body: private norm_sq_eq_re_inner
  conj_inner_symm _ _ := by simp_rw [inner_def, ← integral_conj, inner_conj_symm]
  add_left := private add_left'
  smul_left := private smul_left'

中文:
实例 innerProductSpace
  签名: : InnerProductSpace 𝕜 (α ->₂[μ] E) where
  定义体: private norm_sq_eq_re_inner
  conj_inner_symm _ _ := by simp_rw [inner_def, ← integral_conj, inner_conj_symm]
  add_left := private add_left'
  smul_left := private smul_left'

Depends on / 依赖: norm_sq_eq_re_inner, private
-/
instance innerProductSpace : InnerProductSpace 𝕜 (α ->₂[μ] E) where
  norm_sq_eq_re_inner := private norm_sq_eq_re_inner
  conj_inner_symm _ _ := by simp_rw [inner_def, ← integral_conj, inner_conj_symm]
  add_left := private add_left'
  smul_left := private smul_left'

end InnerProductSpace

section IndicatorConstLp

variable (𝕜) {s t : Set α}

/--
theorem `inner_indicatorConstLp_eq_setIntegral_inner` / 定理 `inner_indicatorConstLp_eq_setIntegral_inner`

English:
theorem inner_indicatorConstLp_eq_setIntegral_inner
  statement: (f : Lp E 2 μ) (hs : MeasurableSet s) (c : E)
  proof: by
  rw [inner_def]; rw [← integral_indicator hs]
  refine integral_congr_ae ((@indicatorConstLp_coeFn _ _ _ 2 μ _ s hs hμs c).mono fun x hx => ?_)
  have : ⟪indicatorConstLp 2 hs hμs c x, f x⟫ = s.indicator (fun x => ⟪c, f x⟫) x := by
    by_cases hxs : x in s <;> simp [hx, hxs]
  simpa

中文:
定理 inner_indicatorConstLp_eq_setIntegral_inner
  结论: (f : Lp E 2 μ) (hs : MeasurableSet s) (c : E)
  证明: by
  rw [inner_def]; rw [← integral_indicator hs]
  refine integral_congr_ae ((@indicatorConstLp_coeFn _ _ _ 2 μ _ s hs hμs c).mono fun x hx => ?_)
  have : ⟪indicatorConstLp 2 hs hμs c x, f x⟫ = s.indicator (fun x => ⟪c, f x⟫) x := by
    by_cases hxs : x in s <;> simp [hx, hxs]
  simpa

Depends on / 依赖: indicator, indicatorConstLp, indicatorConstLp_coeFn, inner_def, integral_congr_ae, integral_indicator, s.indicator
-/
theorem inner_indicatorConstLp_eq_setIntegral_inner (f : Lp E 2 μ) (hs : MeasurableSet s) (c : E)
    (hμs : μ s != ∞) : (⟪indicatorConstLp 2 hs hμs c, f⟫ : 𝕜) = ∫ x in s, ⟪c, f x⟫ ∂μ := by
  rw [inner_def]; rw [← integral_indicator hs]
  refine integral_congr_ae ((@indicatorConstLp_coeFn _ _ _ 2 μ _ s hs hμs c).mono fun x hx => ?_)
  have : ⟪indicatorConstLp 2 hs hμs c x, f x⟫ = s.indicator (fun x => ⟪c, f x⟫) x := by
    by_cases hxs : x in s <;> simp [hx, hxs]
  simpa

/--
theorem `inner_indicatorConstLp_eq_inner_setIntegral` / 定理 `inner_indicatorConstLp_eq_inner_setIntegral`

English:
theorem inner_indicatorConstLp_eq_inner_setIntegral
  statement: [CompleteSpace E] [NormedSpace Real E]
  proof: by
  rw [← integral_inner (integrableOn_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs)]; rw [L2.inner_indicatorConstLp_eq_setIntegral_inner]

中文:
定理 inner_indicatorConstLp_eq_inner_setIntegral
  结论: [CompleteSpace E] [NormedSpace 实数 E]
  证明: by
  rw [← integral_inner (integrableOn_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs)]; rw [L2.inner_indicatorConstLp_eq_setIntegral_inner]

Depends on / 依赖: L2.inner_indicatorConstLp_eq_setIntegral_inner, fact_one_le_two_ennreal, fact_one_le_two_ennreal.elim, inner_indicatorConstLp_eq_setIntegral_inner, integrableOn_Lp_of_measure_ne_top, integral_inner
-/
theorem inner_indicatorConstLp_eq_inner_setIntegral [CompleteSpace E] [NormedSpace Real E]
    (hs : MeasurableSet s) (hμs : μ s != ∞) (c : E) (f : Lp E 2 μ) :
    (⟪indicatorConstLp 2 hs hμs c, f⟫ : 𝕜) = ⟪c, ∫ x in s, f x ∂μ⟫ := by
  rw [← integral_inner (integrableOn_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs)]; rw [L2.inner_indicatorConstLp_eq_setIntegral_inner]

variable {𝕜}

/--
theorem `inner_indicatorConstLp_one` / 定理 `inner_indicatorConstLp_one`

English:
theorem inner_indicatorConstLp_one
  given: (hs : MeasurableSet s) (hμs : μ s != ∞) (f : Lp 𝕜 2 μ)
  proof: by
  rw [L2.inner_indicatorConstLp_eq_inner_setIntegral 𝕜 hs hμs (1 : 𝕜) f]; simp

中文:
定理 inner_indicatorConstLp_one
  条件: (hs : MeasurableSet s) (hμs : μ s != ∞) (f : Lp 𝕜 2 μ)
  证明: by
  rw [L2.inner_indicatorConstLp_eq_inner_setIntegral 𝕜 hs hμs (1 : 𝕜) f]; simp

Depends on / 依赖: L2.inner_indicatorConstLp_eq_inner_setIntegral, inner_indicatorConstLp_eq_inner_setIntegral
-/
theorem inner_indicatorConstLp_one (hs : MeasurableSet s) (hμs : μ s != ∞) (f : Lp 𝕜 2 μ) :
    ⟪indicatorConstLp 2 hs hμs (1 : 𝕜), f⟫ = ∫ x in s, f x ∂μ := by
  rw [L2.inner_indicatorConstLp_eq_inner_setIntegral 𝕜 hs hμs (1 : 𝕜) f]; simp

/--
lemma `inner_indicatorConstLp_indicatorConstLp` / 引理 `inner_indicatorConstLp_indicatorConstLp`

English:
lemma inner_indicatorConstLp_indicatorConstLp
  statement: [CompleteSpace E]
  proof: by
  let : InnerProductSpace Real E := InnerProductSpace.rclikeToReal 𝕜 E
  rw [inner_indicatorConstLp_eq_inner_setIntegral]; rw [setIntegral_indicatorConstLp hs]; rw [inner_smul_right_eq_smul]; rw [Set.inter_comm]

中文:
引理 inner_indicatorConstLp_indicatorConstLp
  结论: [CompleteSpace E]
  证明: by
  let : InnerProductSpace Real E := InnerProductSpace.rclikeToReal 𝕜 E
  rw [inner_indicatorConstLp_eq_inner_setIntegral]; rw [setIntegral_indicatorConstLp hs]; rw [inner_smul_right_eq_smul]; rw [Set.inter_comm]

Depends on / 依赖: InnerProductSpace, InnerProductSpace.rclikeToReal, Set.inter_comm, finiteness, indicatorConstLp, inner_indicatorConstLp_eq_inner_setIntegral, inner_smul_right_eq_smul, inter_comm, rclikeToReal, setIntegral_indicatorConstLp
-/
lemma inner_indicatorConstLp_indicatorConstLp [CompleteSpace E]
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s != ∞ := by finiteness)
    (hμt : μ t != ∞ := by finiteness) (a b : E) :
    ⟪indicatorConstLp 2 hs hμs a, indicatorConstLp 2 ht hμt b⟫ = μ.real (s inter t) • ⟪a, b⟫ := by
  let : InnerProductSpace Real E := InnerProductSpace.rclikeToReal 𝕜 E
  rw [inner_indicatorConstLp_eq_inner_setIntegral]; rw [setIntegral_indicatorConstLp hs]; rw [inner_smul_right_eq_smul]; rw [Set.inter_comm]

/--
lemma `inner_indicatorConstLp_one_indicatorConstLp_one` / 引理 `inner_indicatorConstLp_one_indicatorConstLp_one`

English:
lemma inner_indicatorConstLp_one_indicatorConstLp_one
  proof: by
  simp [inner_indicatorConstLp_indicatorConstLp, RCLike.ofReal_alg]

中文:
引理 inner_indicatorConstLp_one_indicatorConstLp_one
  证明: by
  simp [inner_indicatorConstLp_indicatorConstLp, RCLike.ofReal_alg]

Depends on / 依赖: RCLike, RCLike.ofReal_alg, finiteness, indicatorConstLp, inner_indicatorConstLp_indicatorConstLp, ofReal_alg
-/
lemma inner_indicatorConstLp_one_indicatorConstLp_one
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s != ∞ := by finiteness) (hμt : μ t != ∞ := by finiteness) :
    ⟪indicatorConstLp 2 hs hμs (1 : 𝕜), indicatorConstLp 2 ht hμt (1 : 𝕜)⟫ = μ.real (s inter t) := by
  simp [inner_indicatorConstLp_indicatorConstLp, RCLike.ofReal_alg]

/--
lemma `real_inner_indicatorConstLp_one_indicatorConstLp_one` / 引理 `real_inner_indicatorConstLp_one_indicatorConstLp_one`

English:
lemma real_inner_indicatorConstLp_one_indicatorConstLp_one
  proof: by
  simp [inner_indicatorConstLp_indicatorConstLp]

中文:
引理 real_inner_indicatorConstLp_one_indicatorConstLp_one
  证明: by
  simp [inner_indicatorConstLp_indicatorConstLp]

Depends on / 依赖: _Real, finiteness, indicatorConstLp, inner_indicatorConstLp_indicatorConstLp
-/
lemma real_inner_indicatorConstLp_one_indicatorConstLp_one
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s != ∞ := by finiteness) (hμt : μ t != ∞ := by finiteness) :
    ⟪indicatorConstLp 2 hs hμs (1 : Real), indicatorConstLp 2 ht hμt (1 : Real)⟫_Real = μ.real (s inter t) := by
  simp [inner_indicatorConstLp_indicatorConstLp]

/--
lemma `_root_.MeasureTheory.posSemidef_matrix_measure_inter` / 引理 `_root_.MeasureTheory.posSemidef_matrix_measure_inter`

English:
lemma _root_.MeasureTheory.posSemidef_matrix_measure_inter
  statement: {ι : Type*} [Finite ι] {s : ι -> (Set α)}
  proof: by
  simp only [mv, ne_eq, hv, not_false_eq_true,
    ← real_inner_indicatorConstLp_one_indicatorConstLp_one]
  exact Matrix.posSemidef_gram _ _

中文:
引理 _root_.MeasureTheory.posSemidef_matrix_measure_inter
  结论: {ι : 类型} [Finite ι] {s : ι -> (Set α)}
  证明: by
  simp only [mv, ne_eq, hv, not_false_eq_true,
    ← real_inner_indicatorConstLp_one_indicatorConstLp_one]
  exact Matrix.posSemidef_gram _ _

Depends on / 依赖: Matrix, Matrix.PosSemidef, Matrix.of, Matrix.posSemidef_gram, PosSemidef, finiteness, ne_eq, not_false_eq_true, posSemidef_gram, real_inner_indicatorConstLp_one_indicatorConstLp_one
-/
lemma _root_.MeasureTheory.posSemidef_matrix_measure_inter {ι : Type*} [Finite ι] {s : ι -> (Set α)}
    (mv : forall j, MeasurableSet (s j)) (hv : forall j, μ (s j) != ∞ := by finiteness) :
    Matrix.PosSemidef (Matrix.of fun i j : ι => μ.real (s i inter s j)) := by
  simp only [mv, ne_eq, hv, not_false_eq_true,
    ← real_inner_indicatorConstLp_one_indicatorConstLp_one]
  exact Matrix.posSemidef_gram _ _

end IndicatorConstLp

end L2

section InnerContinuous

variable {α 𝕜 : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [RCLike 𝕜]
variable (μ : Measure α) [IsFiniteMeasure μ]

open scoped BoundedContinuousFunction ComplexConjugate

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/--
theorem `BoundedContinuousFunction.inner_toLp` / 定理 `BoundedContinuousFunction.inner_toLp`

English:
theorem BoundedContinuousFunction.inner_toLp
  given: (f g : α ->ᵇ 𝕜)
  proof: by
  apply integral_congr_ae
  have hf_ae := f.coeFn_toLp 2 μ 𝕜
  have hg_ae := g.coeFn_toLp 2 μ 𝕜
  filter_upwards [hf_ae, hg_ae] with _ hf hg
  rw [hf]; rw [hg]
  simp

中文:
定理 BoundedContinuousFunction.inner_toLp
  条件: (f g : α ->ᵇ 𝕜)
  证明: by
  apply integral_congr_ae
  have hf_ae := f.coeFn_toLp 2 μ 𝕜
  have hg_ae := g.coeFn_toLp 2 μ 𝕜
  filter_upwards [hf_ae, hg_ae] with _ hf hg
  rw [hf]; rw [hg]
  simp

Depends on / 依赖: coeFn_toLp, f.coeFn_toLp, filter_upwards, g.coeFn_toLp, hf_ae, hg_ae, integral_congr_ae
-/
theorem BoundedContinuousFunction.inner_toLp (f g : α ->ᵇ 𝕜) :
    ⟪BoundedContinuousFunction.toLp 2 μ 𝕜 f, BoundedContinuousFunction.toLp 2 μ 𝕜 g⟫ =
      ∫ x, g x * conj (f x) ∂μ := by
  apply integral_congr_ae
  have hf_ae := f.coeFn_toLp 2 μ 𝕜
  have hg_ae := g.coeFn_toLp 2 μ 𝕜
  filter_upwards [hf_ae, hg_ae] with _ hf hg
  rw [hf]; rw [hg]
  simp

variable [CompactSpace α]

/--
theorem `ContinuousMap.inner_toLp` / 定理 `ContinuousMap.inner_toLp`

English:
theorem ContinuousMap.inner_toLp
  given: (f g : C(α, 𝕜))
  proof: by
  apply integral_congr_ae
  have hf_ae := f.coeFn_toLp (p := 2) (𝕜 := 𝕜) μ
  have hg_ae := g.coeFn_toLp (p := 2) (𝕜 := 𝕜) μ
  filter_upwards [hf_ae, hg_ae] with _ hf hg
  rw [hf]; rw [hg]
  simp

中文:
定理 ContinuousMap.inner_toLp
  条件: (f g : C(α, 𝕜))
  证明: by
  apply integral_congr_ae
  have hf_ae := f.coeFn_toLp (p := 2) (𝕜 := 𝕜) μ
  have hg_ae := g.coeFn_toLp (p := 2) (𝕜 := 𝕜) μ
  filter_upwards [hf_ae, hg_ae] with _ hf hg
  rw [hf]; rw [hg]
  simp

Depends on / 依赖: coeFn_toLp, f.coeFn_toLp, filter_upwards, g.coeFn_toLp, hf_ae, hg_ae, integral_congr_ae
-/
theorem ContinuousMap.inner_toLp (f g : C(α, 𝕜)) :
    ⟪ContinuousMap.toLp 2 μ 𝕜 f, ContinuousMap.toLp 2 μ 𝕜 g⟫ =
      ∫ x, g x * conj (f x) ∂μ := by
  apply integral_congr_ae
  have hf_ae := f.coeFn_toLp (p := 2) (𝕜 := 𝕜) μ
  have hg_ae := g.coeFn_toLp (p := 2) (𝕜 := 𝕜) μ
  filter_upwards [hf_ae, hg_ae] with _ hf hg
  rw [hf]; rw [hg]
  simp

end InnerContinuous

end MeasureTheory
