/-
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
module

public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Locally uniform limits of holomorphic functions

This file gathers some results about locally uniform limits of holomorphic functions on an open
subset of the complex plane.

## Main results

* `TendstoLocallyUniformlyOn.differentiableOn`: A locally uniform limit of holomorphic functions
  is holomorphic.
* `TendstoLocallyUniformlyOn.deriv`: Locally uniform convergence implies locally uniform
  convergence of the derivatives to the derivative of the limit.
-/

@[expose] public section


open Set Metric MeasureTheory Filter Complex intervalIntegral

open scoped Real Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace Complex E] {U K : Set Complex}
  {z : Complex} {M r δ : Real} {φ : Filter ι} {F : ι -> Complex -> E} {f g : Complex -> E}

namespace Complex

section Cderiv

/--
Definition of `cderiv` / `cderiv` 的定义

English:
definition cderiv
  signature: (r : Real) (f : Complex -> E) (z : Complex)
  body: (2 * π * I : Complex)⁻¹ • ∮ w in C(z, r), ((w - z) ^ 2)⁻¹ • f w

中文:
定义 cderiv
  签名: (r : 实数) (f : 复形 -> E) (z : 复形)
  定义体: (2 * π * I : Complex)⁻¹ • ∮ w in C(z, r), ((w - z) ^ 2)⁻¹ • f w
-/
noncomputable def cderiv (r : Real) (f : Complex -> E) (z : Complex) : E :=
  (2 * π * I : Complex)⁻¹ • ∮ w in C(z, r), ((w - z) ^ 2)⁻¹ • f w

/--
theorem `cderiv_eq_deriv` / 定理 `cderiv_eq_deriv`

English:
theorem cderiv_eq_deriv
  statement: [CompleteSpace E] (hU : IsOpen U) (hf : DifferentiableOn Complex f U) (hr : 0 < r)
  proof: two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable hU hzr hf (mem_ball_self hr)

中文:
定理 cderiv_eq_deriv
  结论: [完备空间 E] (hU : 是开集 U) (hf : DifferentiableOn 复形 f U) (hr : 0 < r)
  证明: two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable hU hzr hf (mem_ball_self hr)

Depends on / 依赖: mem_ball_self, two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
-/
theorem cderiv_eq_deriv [CompleteSpace E] (hU : IsOpen U) (hf : DifferentiableOn Complex f U) (hr : 0 < r)
    (hzr : closedBall z r subseteq U) : cderiv r f z = deriv f z :=
  two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable hU hzr hf (mem_ball_self hr)

/--
theorem `norm_cderiv_le` / 定理 `norm_cderiv_le`

English:
theorem norm_cderiv_le
  given: (hr : 0 < r) (hf : forall w in sphere z r, ‖f w‖ <= M)
  proof: by
  have hM : 0 <= M := by
    obtain ⟨w, hw⟩ : (sphere z r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
    exact (norm_nonneg _).trans (hf w hw)
  have h1 : forall w in sphere z r, ‖((w - z) ^ 2)⁻¹ • f w‖ <= M / r ^ 2 := by
    intro w hw
    simp only [mem_sphere_iff_norm] at hw hf
    sim

中文:
定理 norm_cderiv_le
  条件: (hr : 0 < r) (hf : 对任意 w in sphere z r, ‖f w‖ <= M)
  证明: by
  have hM : 0 <= M := by
    obtain ⟨w, hw⟩ : (sphere z r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
    exact (norm_nonneg _).trans (hf w hw)
  have h1 : forall w in sphere z r, ‖((w - z) ^ 2)⁻¹ • f w‖ <= M / r ^ 2 := by
    intro w hw
    simp only [mem_sphere_iff_norm] at hw hf
    sim

Depends on / 依赖: Nonempty, NormedSpace, NormedSpace.sphere_nonempty.mpr, cderiv, circleIntegral, circleIntegral.norm_integral_le_of_norm_le_const, hr.le, inv_mul_eq_div, le_rfl, mem_sphere_iff_norm, norm_integral_le_of_norm_le_const, norm_inv, norm_nonneg, norm_pow, norm_smul, sphere, sphere_nonempty, sq_pos_of_pos
-/
theorem norm_cderiv_le (hr : 0 < r) (hf : forall w in sphere z r, ‖f w‖ <= M) :
    ‖cderiv r f z‖ <= M / r := by
  have hM : 0 <= M := by
    obtain ⟨w, hw⟩ : (sphere z r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
    exact (norm_nonneg _).trans (hf w hw)
  have h1 : forall w in sphere z r, ‖((w - z) ^ 2)⁻¹ • f w‖ <= M / r ^ 2 := by
    intro w hw
    simp only [mem_sphere_iff_norm] at hw hf
    simp only [norm_smul, inv_mul_eq_div, hw, norm_inv, norm_pow]
    exact div_le_div₀ hM (hf w hw) (sq_pos_of_pos hr) le_rfl
  have h2 := circleIntegral.norm_integral_le_of_norm_le_const hr.le h1
  simp only [cderiv, norm_smul]
  refine (mul_le_mul le_rfl h2 (norm_nonneg _) (norm_nonneg _)).trans (le_of_eq ?_)
  simp [field, abs_of_nonneg Real.pi_pos.le]

/--
theorem `cderiv_sub` / 定理 `cderiv_sub`

English:
theorem cderiv_sub
  statement: (hr : 0 < r) (hf : ContinuousOn f (sphere z r))
  proof: by
  have h1 : ContinuousOn (fun w : Complex => ((w - z) ^ 2)⁻¹) (sphere z r) := by
    refine ((continuous_id'.fun_sub continuous_const).fun_pow 2).continuousOn.inv₀
      fun w hw h => hr.ne ?_
    rwa [mem_sphere_iff_norm, sq_eq_zero_iff.mp h, norm_zero] at hw
  simp_rw [cderiv, ← smul_sub]
  con

中文:
定理 cderiv_sub
  结论: (hr : 0 < r) (hf : ContinuousOn f (sphere z r))
  证明: by
  have h1 : ContinuousOn (fun w : Complex => ((w - z) ^ 2)⁻¹) (sphere z r) := by
    refine ((continuous_id'.fun_sub continuous_const).fun_pow 2).continuousOn.inv₀
      fun w hw h => hr.ne ?_
    rwa [mem_sphere_iff_norm, sq_eq_zero_iff.mp h, norm_zero] at hw
  simp_rw [cderiv, ← smul_sub]
  con

Depends on / 依赖: ContinuousOn, Pi.sub_apply, cderiv, circleIntegrable, circleIntegral, circleIntegral.integral_sub, continuousOn, continuousOn.inv, continuous_const, continuous_id, fun_pow, fun_smul, fun_sub, h1.fun_smul, hr.le, hr.ne, integral_sub, mem_sphere_iff_norm, norm_zero, simp_rw
-/
theorem cderiv_sub (hr : 0 < r) (hf : ContinuousOn f (sphere z r))
    (hg : ContinuousOn g (sphere z r)) : cderiv r (f - g) z = cderiv r f z - cderiv r g z := by
  have h1 : ContinuousOn (fun w : Complex => ((w - z) ^ 2)⁻¹) (sphere z r) := by
    refine ((continuous_id'.fun_sub continuous_const).fun_pow 2).continuousOn.inv₀
      fun w hw h => hr.ne ?_
    rwa [mem_sphere_iff_norm, sq_eq_zero_iff.mp h, norm_zero] at hw
  simp_rw [cderiv, ← smul_sub]
  congr 1
  simpa only [Pi.sub_apply, smul_sub] using
    circleIntegral.integral_sub ((h1.fun_smul hf).circleIntegrable hr.le)
      ((h1.fun_smul hg).circleIntegrable hr.le)

/--
theorem `norm_cderiv_lt` / 定理 `norm_cderiv_lt`

English:
theorem norm_cderiv_lt
  statement: (hr : 0 < r) (hfM : forall w in sphere z r, ‖f w‖ < M)
  proof: by
  obtain ⟨L, hL1, hL2⟩ : exists L < M, forall w in sphere z r, ‖f w‖ <= L := by
    have e1 : (sphere z r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
    have e2 : ContinuousOn (fun w => ‖f w‖) (sphere z r) := continuous_norm.comp_continuousOn hf
    obtain ⟨x, hx, hx'⟩ := (isCompact_spher

中文:
定理 norm_cderiv_lt
  结论: (hr : 0 < r) (hfM : 对任意 w in sphere z r, ‖f w‖ < M)
  证明: by
  obtain ⟨L, hL1, hL2⟩ : exists L < M, forall w in sphere z r, ‖f w‖ <= L := by
    have e1 : (sphere z r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
    have e2 : ContinuousOn (fun w => ‖f w‖) (sphere z r) := continuous_norm.comp_continuousOn hf
    obtain ⟨x, hx, hx'⟩ := (isCompact_spher

Depends on / 依赖: ContinuousOn, Nonempty, NormedSpace, NormedSpace.sphere_nonempty.mpr, comp_continuousOn, continuous_norm, continuous_norm.comp_continuousOn, div_lt_div_iff_of_pos_right, exists_isMaxOn, hr.le, isCompact_sphere, norm_cderiv_le, sphere, sphere_nonempty, trans_lt
-/
theorem norm_cderiv_lt (hr : 0 < r) (hfM : forall w in sphere z r, ‖f w‖ < M)
    (hf : ContinuousOn f (sphere z r)) : ‖cderiv r f z‖ < M / r := by
  obtain ⟨L, hL1, hL2⟩ : exists L < M, forall w in sphere z r, ‖f w‖ <= L := by
    have e1 : (sphere z r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
    have e2 : ContinuousOn (fun w => ‖f w‖) (sphere z r) := continuous_norm.comp_continuousOn hf
    obtain ⟨x, hx, hx'⟩ := (isCompact_sphere z r).exists_isMaxOn e1 e2
    exact ⟨‖f x‖, hfM x hx, hx'⟩
  exact (norm_cderiv_le hr hL2).trans_lt ((div_lt_div_iff_of_pos_right hr).mpr hL1)

/--
theorem `norm_cderiv_sub_lt` / 定理 `norm_cderiv_sub_lt`

English:
theorem norm_cderiv_sub_lt
  statement: (hr : 0 < r) (hfg : forall w in sphere z r, ‖f w - g w‖ < M)
  proof: cderiv_sub hr hf hg ▸ norm_cderiv_lt hr hfg (hf.sub hg)

中文:
定理 norm_cderiv_sub_lt
  结论: (hr : 0 < r) (hfg : 对任意 w in sphere z r, ‖f w - g w‖ < M)
  证明: cderiv_sub hr hf hg ▸ norm_cderiv_lt hr hfg (hf.sub hg)

Depends on / 依赖: cderiv_sub, hf.sub, norm_cderiv_lt
-/
theorem norm_cderiv_sub_lt (hr : 0 < r) (hfg : forall w in sphere z r, ‖f w - g w‖ < M)
    (hf : ContinuousOn f (sphere z r)) (hg : ContinuousOn g (sphere z r)) :
    ‖cderiv r f z - cderiv r g z‖ < M / r :=
  cderiv_sub hr hf hg ▸ norm_cderiv_lt hr hfg (hf.sub hg)

/--
theorem `_root_.TendstoUniformlyOn.cderiv` / 定理 `_root_.TendstoUniformlyOn.cderiv`

English:
theorem _root_.TendstoUniformlyOn.cderiv
  statement: (hF : TendstoUniformlyOn F f φ (cthickening δ K))
  proof: by
  rcases φ.eq_or_neBot with rfl | hne
  · simp only [TendstoUniformlyOn, eventually_bot, imp_true_iff]
  have e1 : ContinuousOn f (cthickening δ K) := TendstoUniformlyOn.continuousOn hF hFn.frequently
  rw [tendstoUniformlyOn_iff] at hF ⊢
  rintro ε hε
  filter_upwards [hF (ε * δ) (mul_pos hε hδ)

中文:
定理 _root_.TendstoUniformlyOn.cderiv
  结论: (hF : TendstoUniformlyOn F f φ (cthickening δ K))
  证明: by
  rcases φ.eq_or_neBot with rfl | hne
  · simp only [TendstoUniformlyOn, eventually_bot, imp_true_iff]
  have e1 : ContinuousOn f (cthickening δ K) := TendstoUniformlyOn.continuousOn hF hFn.frequently
  rw [tendstoUniformlyOn_iff] at hF ⊢
  rintro ε hε
  filter_upwards [hF (ε * δ) (mul_pos hε hδ)

Depends on / 依赖: ContinuousOn, TendstoUniformlyOn, TendstoUniformlyOn.continuousOn, closedBall_subset_cthickening, continuousOn, cthickening, dist_eq_norm, eq_or_neBot, eventually_bot, filter_upwards, frequently, hFn.frequently, imp_true_iff, mul_pos, simp_rw, sphere, sphere_subset_closedBall, tendstoUniformlyOn_iff
-/
theorem _root_.TendstoUniformlyOn.cderiv (hF : TendstoUniformlyOn F f φ (cthickening δ K))
    (hδ : 0 < δ) (hFn : forallᶠ n in φ, ContinuousOn (F n) (cthickening δ K)) :
    TendstoUniformlyOn (cderiv δ ∘ F) (cderiv δ f) φ K := by
  rcases φ.eq_or_neBot with rfl | hne
  · simp only [TendstoUniformlyOn, eventually_bot, imp_true_iff]
  have e1 : ContinuousOn f (cthickening δ K) := TendstoUniformlyOn.continuousOn hF hFn.frequently
  rw [tendstoUniformlyOn_iff] at hF ⊢
  rintro ε hε
  filter_upwards [hF (ε * δ) (mul_pos hε hδ), hFn] with n h h' z hz
  simp_rw [dist_eq_norm] at h ⊢
  have e2 : forall w in sphere z δ, ‖f w - F n w‖ < ε * δ := fun w hw1 =>
    h w (closedBall_subset_cthickening hz δ (sphere_subset_closedBall hw1))
  have e3 := sphere_subset_closedBall.trans (closedBall_subset_cthickening hz δ)
  have hf : ContinuousOn f (sphere z δ) :=
    e1.mono (sphere_subset_closedBall.trans (closedBall_subset_cthickening hz δ))
  simpa only [mul_div_cancel_right₀ _ hδ.ne.symm] using! norm_cderiv_sub_lt hδ e2 hf (h'.mono e3)

end Cderiv

variable [CompleteSpace E]

section Weierstrass

/--
theorem `tendstoUniformlyOn_deriv_of_cthickening_subset` / 定理 `tendstoUniformlyOn_deriv_of_cthickening_subset`

English:
theorem tendstoUniformlyOn_deriv_of_cthickening_subset
  statement: (hf : TendstoLocallyUniformlyOn F f φ U)
  proof: by
  have h1 : forallᶠ n in φ, ContinuousOn (F n) (cthickening δ K) := by
    filter_upwards [hF] with n h using h.continuousOn.mono hKU
  have h2 : IsCompact (cthickening δ K) := hK.cthickening
  have h3 : TendstoUniformlyOn F f φ (cthickening δ K) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCom

中文:
定理 tendstoUniformlyOn_deriv_of_cthickening_subset
  结论: (hf : TendstoLocallyUniformlyOn F f φ U)
  证明: by
  have h1 : forallᶠ n in φ, ContinuousOn (F n) (cthickening δ K) := by
    filter_upwards [hF] with n h using h.continuousOn.mono hKU
  have h2 : IsCompact (cthickening δ K) := hK.cthickening
  have h3 : TendstoUniformlyOn F f φ (cthickening δ K) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCom

Depends on / 依赖: ContinuousOn, IsCompact, TendstoUniformlyOn, cderiv, cderiv_eq_deriv, closedBall_subset_cthickening, continuousOn, cthickening, filter_upwards, h.continuousOn.mono, h3.cderiv, hK.cthickening, tendstoLocallyUniformlyOn_iff_forall_isCompact
-/
theorem tendstoUniformlyOn_deriv_of_cthickening_subset (hf : TendstoLocallyUniformlyOn F f φ U)
    (hF : forallᶠ n in φ, DifferentiableOn Complex (F n) U) {δ : Real} (hδ : 0 < δ) (hK : IsCompact K)
    (hU : IsOpen U) (hKU : cthickening δ K subseteq U) :
    TendstoUniformlyOn (deriv ∘ F) (cderiv δ f) φ K := by
  have h1 : forallᶠ n in φ, ContinuousOn (F n) (cthickening δ K) := by
    filter_upwards [hF] with n h using h.continuousOn.mono hKU
  have h2 : IsCompact (cthickening δ K) := hK.cthickening
  have h3 : TendstoUniformlyOn F f φ (cthickening δ K) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hf (cthickening δ K) hKU h2
  apply (h3.cderiv hδ h1).congr
  filter_upwards [hF] with n h z hz
  exact cderiv_eq_deriv hU h hδ ((closedBall_subset_cthickening hz δ).trans hKU)

/--
theorem `exists_cthickening_tendstoUniformlyOn` / 定理 `exists_cthickening_tendstoUniformlyOn`

English:
theorem exists_cthickening_tendstoUniformlyOn
  statement: (hf : TendstoLocallyUniformlyOn F f φ U)
  proof: by
  obtain ⟨δ, hδ, hKδ⟩ := hK.exists_cthickening_subset_open hU hKU
  exact ⟨δ, hδ, hKδ, tendstoUniformlyOn_deriv_of_cthickening_subset hf hF hδ hK hU hKδ⟩

中文:
定理 存在_cthickening_tendstoUniformlyOn
  结论: (hf : TendstoLocallyUniformlyOn F f φ U)
  证明: by
  obtain ⟨δ, hδ, hKδ⟩ := hK.exists_cthickening_subset_open hU hKU
  exact ⟨δ, hδ, hKδ, tendstoUniformlyOn_deriv_of_cthickening_subset hf hF hδ hK hU hKδ⟩

Depends on / 依赖: exists_cthickening_subset_open, hK.exists_cthickening_subset_open, tendstoUniformlyOn_deriv_of_cthickening_subset
-/
theorem exists_cthickening_tendstoUniformlyOn (hf : TendstoLocallyUniformlyOn F f φ U)
    (hF : forallᶠ n in φ, DifferentiableOn Complex (F n) U) (hK : IsCompact K) (hU : IsOpen U) (hKU : K subseteq U) :
    exists δ > 0, cthickening δ K subseteq U ∧ TendstoUniformlyOn (deriv ∘ F) (cderiv δ f) φ K := by
  obtain ⟨δ, hδ, hKδ⟩ := hK.exists_cthickening_subset_open hU hKU
  exact ⟨δ, hδ, hKδ, tendstoUniformlyOn_deriv_of_cthickening_subset hf hF hδ hK hU hKδ⟩

/--
theorem `_root_.TendstoLocallyUniformlyOn.differentiableOn` / 定理 `_root_.TendstoLocallyUniformlyOn.differentiableOn`

English:
theorem _root_.TendstoLocallyUniformlyOn.differentiableOn
  statement: [φ.NeBot]
  proof: by
  rintro x hx
  obtain ⟨K, ⟨hKx, hK⟩, hKU⟩ := (compact_basis_nhds x).mem_iff.mp (hU.mem_nhds hx)
  obtain ⟨δ, _, _, h1⟩ := exists_cthickening_tendstoUniformlyOn hf hF hK hU hKU
  have h2 : interior K subseteq U := interior_subset.trans hKU
  have h3 : forallᶠ n in φ, DifferentiableOn Complex (F n

中文:
定理 _root_.TendstoLocallyUniformlyOn.differentiableOn
  结论: [φ.NeBot]
  证明: by
  rintro x hx
  obtain ⟨K, ⟨hKx, hK⟩, hKU⟩ := (compact_basis_nhds x).mem_iff.mp (hU.mem_nhds hx)
  obtain ⟨δ, _, _, h1⟩ := exists_cthickening_tendstoUniformlyOn hf hF hK hU hKU
  have h2 : interior K subseteq U := interior_subset.trans hKU
  have h3 : forallᶠ n in φ, DifferentiableOn Complex (F n

Depends on / 依赖: DifferentiableOn, TendstoLocallyUniformlyOn, cderiv, compact_basis_nhds, exists_cthickening_tendstoUniformlyOn, filter_upwards, h.mono, hU.mem_nhds, hf.mono, interior, interior_subset, interior_subset.trans, mem_iff, mem_iff.mp, mem_nhds, subseteq
-/
theorem _root_.TendstoLocallyUniformlyOn.differentiableOn [φ.NeBot]
    (hf : TendstoLocallyUniformlyOn F f φ U) (hF : forallᶠ n in φ, DifferentiableOn Complex (F n) U)
    (hU : IsOpen U) : DifferentiableOn Complex f U := by
  rintro x hx
  obtain ⟨K, ⟨hKx, hK⟩, hKU⟩ := (compact_basis_nhds x).mem_iff.mp (hU.mem_nhds hx)
  obtain ⟨δ, _, _, h1⟩ := exists_cthickening_tendstoUniformlyOn hf hF hK hU hKU
  have h2 : interior K subseteq U := interior_subset.trans hKU
  have h3 : forallᶠ n in φ, DifferentiableOn Complex (F n) (interior K) := by
    filter_upwards [hF] with n h using h.mono h2
  have h4 : TendstoLocallyUniformlyOn F f φ (interior K) := hf.mono h2
  have h5 : TendstoLocallyUniformlyOn (deriv ∘ F) (cderiv δ f) φ (interior K) :=
    h1.tendstoLocallyUniformlyOn.mono interior_subset
  have h6 : forall x in interior K, HasDerivAt f (cderiv δ f x) x := fun x h =>
    hasDerivAt_of_tendsto_locally_uniformly_on' isOpen_interior h5 h3 (fun _ => h4.tendsto_at) h
  have h7 : DifferentiableOn Complex f (interior K) := fun x hx =>
    (h6 x hx).differentiableAt.differentiableWithinAt
  exact (h7.differentiableAt (interior_mem_nhds.mpr hKx)).differentiableWithinAt

/--
theorem `_root_.TendstoLocallyUniformlyOn.deriv` / 定理 `_root_.TendstoLocallyUniformlyOn.deriv`

English:
theorem _root_.TendstoLocallyUniformlyOn.deriv
  statement: (hf : TendstoLocallyUniformlyOn F f φ U)
  proof: by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  rcases φ.eq_or_neBot with rfl | hne
  · simp only [TendstoUniformlyOn, eventually_bot, imp_true_iff]
  rintro K hKU hK
  obtain ⟨δ, hδ, hK4, h⟩ := exists_cthickening_tendstoUniformlyOn hf hF hK hU hKU
  refine h.congr_right fun z hz => cd

中文:
定理 _root_.TendstoLocallyUniformlyOn.deriv
  结论: (hf : TendstoLocallyUniformlyOn F f φ U)
  证明: by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  rcases φ.eq_or_neBot with rfl | hne
  · simp only [TendstoUniformlyOn, eventually_bot, imp_true_iff]
  rintro K hKU hK
  obtain ⟨δ, hδ, hK4, h⟩ := exists_cthickening_tendstoUniformlyOn hf hF hK hU hKU
  refine h.congr_right fun z hz => cd

Depends on / 依赖: TendstoUniformlyOn, cderiv_eq_deriv, closedBall_subset_cthickening, congr_right, differentiableOn, eq_or_neBot, eventually_bot, exists_cthickening_tendstoUniformlyOn, h.congr_right, hf.differentiableOn, imp_true_iff, tendstoLocallyUniformlyOn_iff_forall_isCompact
-/
theorem _root_.TendstoLocallyUniformlyOn.deriv (hf : TendstoLocallyUniformlyOn F f φ U)
    (hF : forallᶠ n in φ, DifferentiableOn Complex (F n) U) (hU : IsOpen U) :
    TendstoLocallyUniformlyOn (deriv ∘ F) (deriv f) φ U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  rcases φ.eq_or_neBot with rfl | hne
  · simp only [TendstoUniformlyOn, eventually_bot, imp_true_iff]
  rintro K hKU hK
  obtain ⟨δ, hδ, hK4, h⟩ := exists_cthickening_tendstoUniformlyOn hf hF hK hU hKU
  refine h.congr_right fun z hz => cderiv_eq_deriv hU (hf.differentiableOn hF hU) hδ ?_
  exact (closedBall_subset_cthickening hz δ).trans hK4

end Weierstrass

section Tsums

/--
theorem `differentiableOn_tsum_of_summable_norm` / 定理 `differentiableOn_tsum_of_summable_norm`

English:
theorem differentiableOn_tsum_of_summable_norm
  statement: {u : ι -> Real} (hu : Summable u)
  proof: by
  have hc := (tendstoUniformlyOn_tsum hu hF_le).tendstoLocallyUniformlyOn
  refine hc.differentiableOn (Eventually.of_forall fun s => ?_) hU
  exact DifferentiableOn.fun_sum fun i _ => hf i

中文:
定理 differentiableOn_tsum_of_summable_norm
  结论: {u : ι -> 实数} (hu : Summable u)
  证明: by
  have hc := (tendstoUniformlyOn_tsum hu hF_le).tendstoLocallyUniformlyOn
  refine hc.differentiableOn (Eventually.of_forall fun s => ?_) hU
  exact DifferentiableOn.fun_sum fun i _ => hf i

Depends on / 依赖: DifferentiableOn, DifferentiableOn.fun_sum, Eventually, Eventually.of_forall, differentiableOn, fun_sum, hF_le, hc.differentiableOn, of_forall, tendstoLocallyUniformlyOn, tendstoUniformlyOn_tsum
-/
theorem differentiableOn_tsum_of_summable_norm {u : ι -> Real} (hu : Summable u)
    (hf : forall i : ι, DifferentiableOn Complex (F i) U) (hU : IsOpen U)
    (hF_le : forall (i : ι) (w : Complex), w in U -> ‖F i w‖ <= u i) :
    DifferentiableOn Complex (fun w : Complex => ∑' i : ι, F i w) U := by
  have hc := (tendstoUniformlyOn_tsum hu hF_le).tendstoLocallyUniformlyOn
  refine hc.differentiableOn (Eventually.of_forall fun s => ?_) hU
  exact DifferentiableOn.fun_sum fun i _ => hf i

/--
theorem `hasSum_deriv_of_summable_norm` / 定理 `hasSum_deriv_of_summable_norm`

English:
theorem hasSum_deriv_of_summable_norm
  statement: {u : ι -> Real} (hu : Summable u)
  proof: by
  rw [HasSum]
  have hc := (tendstoUniformlyOn_tsum hu hF_le).tendstoLocallyUniformlyOn
  convert!
    (hc.deriv (Eventually.of_forall fun s => DifferentiableOn.fun_sum fun i _ => hf i)
          hU).tendsto_at
      hz using 1
  ext1 s
  exact (deriv_fun_sum fun i _ => (hf i).differentiableAt (h

中文:
定理 hasSum_deriv_of_summable_norm
  结论: {u : ι -> 实数} (hu : Summable u)
  证明: by
  rw [HasSum]
  have hc := (tendstoUniformlyOn_tsum hu hF_le).tendstoLocallyUniformlyOn
  convert!
    (hc.deriv (Eventually.of_forall fun s => DifferentiableOn.fun_sum fun i _ => hf i)
          hU).tendsto_at
      hz using 1
  ext1 s
  exact (deriv_fun_sum fun i _ => (hf i).differentiableAt (h

Depends on / 依赖: DifferentiableOn, DifferentiableOn.fun_sum, Eventually, Eventually.of_forall, HasSum, convert, deriv_fun_sum, differentiableAt, fun_sum, hF_le, hU.mem_nhds, hc.deriv, mem_nhds, of_forall, tendstoLocallyUniformlyOn, tendstoUniformlyOn_tsum, tendsto_at
-/
theorem hasSum_deriv_of_summable_norm {u : ι -> Real} (hu : Summable u)
    (hf : forall i : ι, DifferentiableOn Complex (F i) U) (hU : IsOpen U)
    (hF_le : forall (i : ι) (w : Complex), w in U -> ‖F i w‖ <= u i) (hz : z in U) :
    HasSum (fun i : ι => deriv (F i) z) (deriv (fun w : Complex => ∑' i : ι, F i w) z) := by
  rw [HasSum]
  have hc := (tendstoUniformlyOn_tsum hu hF_le).tendstoLocallyUniformlyOn
  convert!
    (hc.deriv (Eventually.of_forall fun s => DifferentiableOn.fun_sum fun i _ => hf i)
          hU).tendsto_at
      hz using 1
  ext1 s
  exact (deriv_fun_sum fun i _ => (hf i).differentiableAt (hU.mem_nhds hz)).symm

end Tsums

section LogDeriv

/--
theorem `logDeriv_tendsto` / 定理 `logDeriv_tendsto`

English:
theorem logDeriv_tendsto
  statement: {ι : Type*} {p : Filter ι} {f : ι -> Complex -> Complex} {g : Complex -> Complex}
  proof: ((hF.deriv hf hs).tendsto_at hx).div (hF.tendsto_at hx) hg

中文:
定理 logDeriv_tendsto
  结论: {ι : 类型} {p : 滤子 ι} {f : ι -> 复形 -> 复形} {g : 复形 -> 复形}
  证明: ((hF.deriv hf hs).tendsto_at hx).div (hF.tendsto_at hx) hg

Depends on / 依赖: hF.deriv, hF.tendsto_at, tendsto_at
-/
theorem logDeriv_tendsto {ι : Type*} {p : Filter ι} {f : ι -> Complex -> Complex} {g : Complex -> Complex}
    {s : Set Complex} (hs : IsOpen s) {x : Complex} (hx : x in s) (hF : TendstoLocallyUniformlyOn f g p s)
    (hf : forallᶠ n in p, DifferentiableOn Complex (f n) s) (hg : g x != 0) :
    Tendsto (fun n => logDeriv (f n) x) p (𝓝 (logDeriv g x)) :=
  ((hF.deriv hf hs).tendsto_at hx).div (hF.tendsto_at hx) hg

end LogDeriv

end Complex
