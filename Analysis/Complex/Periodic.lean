/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Order.Filter.ZeroAndBoundedAtFilter

/-!
# Periodic holomorphic functions

We show that if `f : ℂ → ℂ` satisfies `f (z + h) = f z`, for some nonzero real `h`, then there is a
function `F` such that `f z = F (exp (2 * π * I * z / h))` for all `z`; and if `f` is holomorphic
at some `z`, then `F` is holomorphic at `exp (2 * π * I * z / h)`.

We also show (using Riemann's removable singularity theorem) that if `f` is holomorphic and bounded
for all sufficiently large `im z`, then `F` extends to a holomorphic function on a neighbourhood of
`0`. As a consequence, if `f` tends to zero as `im z → ∞`, then in fact it decays *exponentially*
to zero. These results are important in the theory of modular forms.
-/

@[expose] public section

open Complex Filter Asymptotics

open scoped Real Topology

noncomputable section

local notation "I∞" => comap im atTop

variable (h : Real)

namespace Function.Periodic

/--
Definition of `qParam` / `qParam` 的定义

English:
definition qParam
  signature: (z : Complex)
  body: exp (2 * π * I * z / h)

中文:
定义 qParam
  签名: (z : 复形)
  定义体: exp (2 * π * I * z / h)
-/
def qParam (z : Complex) : Complex := exp (2 * π * I * z / h)

/--
Definition of `invQParam` / `invQParam` 的定义

English:
definition invQParam
  signature: (q : Complex)
  body: h / (2 * π * I) * log q

local notation "𝕢" => qParam

中文:
定义 invQParam
  签名: (q : 复形)
  定义体: h / (2 * π * I) * log q

local notation "𝕢" => qParam
-/
def invQParam (q : Complex) : Complex := h / (2 * π * I) * log q

local notation "𝕢" => qParam

section qParam

/--
theorem `norm_qParam` / 定理 `norm_qParam`

English:
theorem norm_qParam
  given: (z : Complex)
  statement: ‖𝕢 h z‖ = Real.exp (-2 * π * im z / h)
  proof: by
  simp only [qParam, norm_exp, div_ofReal_re, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im,
    mul_zero, sub_zero, I_re, mul_im, zero_mul, add_zero, I_im, mul_one, sub_self, zero_sub,
    neg_mul]

中文:
定理 norm_qParam
  条件: (z : 复形)
  结论: ‖𝕢 h z‖ = 实数.exp (-2 * π * im z / h)
  证明: by
  simp only [qParam, norm_exp, div_ofReal_re, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im,
    mul_zero, sub_zero, I_re, mul_im, zero_mul, add_zero, I_im, mul_one, sub_self, zero_sub,
    neg_mul]

Depends on / 依赖: I_im, I_re, add_zero, div_ofReal_re, im_ofNat, mul_im, mul_one, mul_re, mul_zero, neg_mul, norm_exp, ofReal_im, ofReal_re, qParam, re_ofNat, sub_self, sub_zero, zero_mul, zero_sub
-/
theorem norm_qParam (z : Complex) : ‖𝕢 h z‖ = Real.exp (-2 * π * im z / h) := by
  simp only [qParam, norm_exp, div_ofReal_re, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im,
    mul_zero, sub_zero, I_re, mul_im, zero_mul, add_zero, I_im, mul_one, sub_self, zero_sub,
    neg_mul]

/--
theorem `im_invQParam` / 定理 `im_invQParam`

English:
theorem im_invQParam
  given: (q : Complex)
  statement: im (invQParam h q) = -h / (2 * π) * Real.log ‖q‖
  proof: by
  simp only [invQParam, ← div_div, div_I, neg_mul, neg_im, mul_im, mul_re, div_ofReal_re,
    div_ofNat_re, ofReal_re, I_re, mul_zero, div_ofReal_im, div_ofNat_im, ofReal_im, zero_div, I_im,
    mul_one, sub_self, zero_mul, add_zero, log_re, zero_add, neg_div]

中文:
定理 im_invQParam
  条件: (q : 复形)
  结论: im (invQParam h q) = -h / (2 * π) * 实数.log ‖q‖
  证明: by
  simp only [invQParam, ← div_div, div_I, neg_mul, neg_im, mul_im, mul_re, div_ofReal_re,
    div_ofNat_re, ofReal_re, I_re, mul_zero, div_ofReal_im, div_ofNat_im, ofReal_im, zero_div, I_im,
    mul_one, sub_self, zero_mul, add_zero, log_re, zero_add, neg_div]

Depends on / 依赖: I_im, I_re, add_zero, div_I, div_div, div_ofNat_im, div_ofNat_re, div_ofReal_im, div_ofReal_re, invQParam, log_re, mul_im, mul_one, mul_re, mul_zero, neg_div, neg_im, neg_mul, ofReal_im, ofReal_re
-/
theorem im_invQParam (q : Complex) : im (invQParam h q) = -h / (2 * π) * Real.log ‖q‖ := by
  simp only [invQParam, ← div_div, div_I, neg_mul, neg_im, mul_im, mul_re, div_ofReal_re,
    div_ofNat_re, ofReal_re, I_re, mul_zero, div_ofReal_im, div_ofNat_im, ofReal_im, zero_div, I_im,
    mul_one, sub_self, zero_mul, add_zero, log_re, zero_add, neg_div]

variable {h} -- next few theorems all assume h ≠ 0 or 0 < h

/--
theorem `qParam_right_inv` / 定理 `qParam_right_inv`

English:
theorem qParam_right_inv
  given: (hh : h != 0) {q : Complex} (hq : q != 0)
  statement: 𝕢 h (invQParam h q) = q
  proof: by
  simp only [qParam, invQParam, ← mul_assoc, mul_div_cancel₀ _ two_pi_I_ne_zero,
    mul_div_cancel_left₀ _ (ofReal_ne_zero.mpr hh), exp_log hq]

中文:
定理 qParam_right_inv
  条件: (hh : h != 0) {q : 复形} (hq : q != 0)
  结论: 𝕢 h (invQParam h q) = q
  证明: by
  simp only [qParam, invQParam, ← mul_assoc, mul_div_cancel₀ _ two_pi_I_ne_zero,
    mul_div_cancel_left₀ _ (ofReal_ne_zero.mpr hh), exp_log hq]

Depends on / 依赖: exp_log, invQParam, mul_assoc, ofReal_ne_zero, ofReal_ne_zero.mpr, qParam, two_pi_I_ne_zero
-/
theorem qParam_right_inv (hh : h != 0) {q : Complex} (hq : q != 0) : 𝕢 h (invQParam h q) = q := by
  simp only [qParam, invQParam, ← mul_assoc, mul_div_cancel₀ _ two_pi_I_ne_zero,
    mul_div_cancel_left₀ _ (ofReal_ne_zero.mpr hh), exp_log hq]

/--
theorem `qParam_left_inv_mod_period` / 定理 `qParam_left_inv_mod_period`

English:
theorem qParam_left_inv_mod_period
  given: (hh : h != 0) (z : Complex)
  proof: by
  dsimp only [qParam, invQParam]
  obtain ⟨m, hm⟩ := log_exp_exists (2 * ↑π * I * z / ↑h)
  refine ⟨m, by rw [hm, mul_div_assoc, mul_comm (m : Complex), ← mul_add, ← mul_assoc,
    div_mul_cancel₀ _ two_pi_I_ne_zero, mul_add, mul_div_cancel₀ _ (mod_cast hh), mul_comm]⟩

中文:
定理 qParam_left_inv_mod_period
  条件: (hh : h != 0) (z : 复形)
  证明: by
  dsimp only [qParam, invQParam]
  obtain ⟨m, hm⟩ := log_exp_exists (2 * ↑π * I * z / ↑h)
  refine ⟨m, by rw [hm, mul_div_assoc, mul_comm (m : Complex), ← mul_add, ← mul_assoc,
    div_mul_cancel₀ _ two_pi_I_ne_zero, mul_add, mul_div_cancel₀ _ (mod_cast hh), mul_comm]⟩

Depends on / 依赖: invQParam, log_exp_exists, mod_cast, mul_add, mul_assoc, mul_comm, mul_div_assoc, qParam, two_pi_I_ne_zero
-/
theorem qParam_left_inv_mod_period (hh : h != 0) (z : Complex) :
    exists m : Int, invQParam h (𝕢 h z) = z + m * h := by
  dsimp only [qParam, invQParam]
  obtain ⟨m, hm⟩ := log_exp_exists (2 * ↑π * I * z / ↑h)
  refine ⟨m, by rw [hm, mul_div_assoc, mul_comm (m : Complex), ← mul_add, ← mul_assoc,
    div_mul_cancel₀ _ two_pi_I_ne_zero, mul_add, mul_div_cancel₀ _ (mod_cast hh), mul_comm]⟩

/--
theorem `norm_qParam_lt_iff` / 定理 `norm_qParam_lt_iff`

English:
theorem norm_qParam_lt_iff
  given: (hh : 0 < h) (A : Real) (z : Complex)
  proof: by
  rw [norm_qParam]; rw [Real.exp_lt_exp]; rw [div_lt_div_iff_of_pos_right hh]; rw [mul_lt_mul_left_of_neg]
  simpa using Real.pi_pos

中文:
定理 norm_qParam_lt_iff
  条件: (hh : 0 < h) (A : 实数) (z : 复形)
  证明: by
  rw [norm_qParam]; rw [Real.exp_lt_exp]; rw [div_lt_div_iff_of_pos_right hh]; rw [mul_lt_mul_left_of_neg]
  simpa using Real.pi_pos

Depends on / 依赖: Real.exp_lt_exp, Real.pi_pos, div_lt_div_iff_of_pos_right, exp_lt_exp, mul_lt_mul_left_of_neg, norm_qParam, pi_pos
-/
theorem norm_qParam_lt_iff (hh : 0 < h) (A : Real) (z : Complex) :
    ‖qParam h z‖ < Real.exp (-2 * π * A / h) ↔ A < im z := by
  rw [norm_qParam]; rw [Real.exp_lt_exp]; rw [div_lt_div_iff_of_pos_right hh]; rw [mul_lt_mul_left_of_neg]
  simpa using Real.pi_pos

/--
theorem `norm_qParam_lt_one` / 定理 `norm_qParam_lt_one`

English:
theorem norm_qParam_lt_one
  given: (hh : 0 < h) {z : Complex} (hz : 0 < im z)
  statement: ‖𝕢 h z‖ < 1
  proof: by
  simpa using (norm_qParam_lt_iff hh 0 z).mpr hz

中文:
定理 norm_qParam_lt_one
  条件: (hh : 0 < h) {z : 复形} (hz : 0 < im z)
  结论: ‖𝕢 h z‖ < 1
  证明: by
  simpa using (norm_qParam_lt_iff hh 0 z).mpr hz

Depends on / 依赖: norm_qParam_lt_iff
-/
theorem norm_qParam_lt_one (hh : 0 < h) {z : Complex} (hz : 0 < im z) : ‖𝕢 h z‖ < 1 := by
  simpa using (norm_qParam_lt_iff hh 0 z).mpr hz

/--
lemma `qParam_ne_zero` / 引理 `qParam_ne_zero`

English:
lemma qParam_ne_zero
  given: (z : Complex)
  statement: 𝕢 h z != 0
  proof: by
  simp [qParam, exp_ne_zero]

@[fun_prop]

中文:
引理 qParam_ne_zero
  条件: (z : 复形)
  结论: 𝕢 h z != 0
  证明: by
  simp [qParam, exp_ne_zero]

@[fun_prop]

Depends on / 依赖: exp_ne_zero, qParam
-/
lemma qParam_ne_zero (z : Complex) : 𝕢 h z != 0 := by
  simp [qParam, exp_ne_zero]

@[fun_prop]
/--
lemma `continuous_qParam` / 引理 `continuous_qParam`

English:
lemma continuous_qParam
  statement: Continuous (𝕢 h)
  proof: by
  unfold qParam
  fun_prop

@[fun_prop]

中文:
引理 continuous_qParam
  结论: 连续 (𝕢 h)
  证明: by
  unfold qParam
  fun_prop

@[fun_prop]

Depends on / 依赖: fun_prop, qParam
-/
lemma continuous_qParam : Continuous (𝕢 h) := by
  unfold qParam
  fun_prop

@[fun_prop]
/--
lemma `differentiable_qParam` / 引理 `differentiable_qParam`

English:
lemma differentiable_qParam
  statement: Differentiable Complex (𝕢 h)
  proof: by
  unfold qParam
  fun_prop

@[fun_prop]

中文:
引理 differentiable_qParam
  结论: 可微 复形 (𝕢 h)
  证明: by
  unfold qParam
  fun_prop

@[fun_prop]

Depends on / 依赖: fun_prop, qParam
-/
lemma differentiable_qParam : Differentiable Complex (𝕢 h) := by
  unfold qParam
  fun_prop

@[fun_prop]
/--
lemma `contDiff_qParam` / 引理 `contDiff_qParam`

English:
lemma contDiff_qParam
  given: (m : WithTop Nat∞)
  statement: ContDiff Complex m (𝕢 h)
  proof: by
  unfold qParam
  fun_prop

中文:
引理 contDiff_qParam
  条件: (m : WithTop 自然数∞)
  结论: 连续可微 复形 m (𝕢 h)
  证明: by
  unfold qParam
  fun_prop

Depends on / 依赖: fun_prop, qParam
-/
lemma contDiff_qParam (m : WithTop Nat∞) : ContDiff Complex m (𝕢 h) := by
  unfold qParam
  fun_prop

/--
theorem `qParam_tendsto` / 定理 `qParam_tendsto`

English:
theorem qParam_tendsto
  given: (hh : 0 < h)
  statement: Tendsto (qParam h) I∞ (𝓝[!=] 0)
  proof: by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
    (.of_forall fun q => exp_ne_zero _)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_qParam]
  apply (tendsto_comap'_iff (m := fun y => Real.exp (-2 * π * y / h)) (range_im ▸ univ_mem)).mpr
  refine Real.tendsto_exp_atBot.comp (.atBot_div_const hh (tendsto_id.const_mul_atTop_of_neg ?_))
  simpa using Real.pi_pos

中文:
定理 qParam_tendsto
  条件: (hh : 0 < h)
  结论: 收敛 (qParam h) I∞ (𝓝[!=] 0)
  证明: by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
    (.of_forall fun q => exp_ne_zero _)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_qParam]
  apply (tendsto_comap'_iff (m := fun y => Real.exp (-2 * π * y / h)) (range_im ▸ univ_mem)).mpr
  refine Real.tendsto_exp_atBot.comp (.atBot_div_const hh (tendsto_id.const_mul_atTop_of_neg ?_))
  simpa using Real.pi_pos

Depends on / 依赖: Real.exp, Real.pi_pos, Real.tendsto_exp_atBot.comp, _iff, atBot_div_const, const_mul_atTop_of_neg, exp_ne_zero, norm_qParam, of_forall, pi_pos, range_im, tendsto_comap, tendsto_exp_atBot, tendsto_id, tendsto_id.const_mul_atTop_of_neg, tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within, tendsto_zero_iff_norm_tendsto_zero, univ_mem
-/
theorem qParam_tendsto (hh : 0 < h) : Tendsto (qParam h) I∞ (𝓝[!=] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
    (.of_forall fun q => exp_ne_zero _)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_qParam]
  apply (tendsto_comap'_iff (m := fun y => Real.exp (-2 * π * y / h)) (range_im ▸ univ_mem)).mpr
  refine Real.tendsto_exp_atBot.comp (.atBot_div_const hh (tendsto_id.const_mul_atTop_of_neg ?_))
  simpa using Real.pi_pos

/--
theorem `invQParam_tendsto` / 定理 `invQParam_tendsto`

English:
theorem invQParam_tendsto
  given: (hh : 0 < h)
  statement: Tendsto (invQParam h) (𝓝[!=] 0) I∞
  proof: by
  simp only [tendsto_comap_iff, comp_def, im_invQParam]
  apply Tendsto.const_mul_atBot_of_neg (div_neg_of_neg_of_pos (neg_lt_zero.mpr hh) (by positivity))
  exact Real.tendsto_log_nhdsGT_zero.comp tendsto_norm_nhdsNE_zero

中文:
定理 invQParam_tendsto
  条件: (hh : 0 < h)
  结论: 收敛 (invQParam h) (𝓝[!=] 0) I∞
  证明: by
  simp only [tendsto_comap_iff, comp_def, im_invQParam]
  apply Tendsto.const_mul_atBot_of_neg (div_neg_of_neg_of_pos (neg_lt_zero.mpr hh) (by positivity))
  exact Real.tendsto_log_nhdsGT_zero.comp tendsto_norm_nhdsNE_zero

Depends on / 依赖: Real.tendsto_log_nhdsGT_zero.comp, Tendsto, Tendsto.const_mul_atBot_of_neg, comp_def, const_mul_atBot_of_neg, div_neg_of_neg_of_pos, im_invQParam, neg_lt_zero, neg_lt_zero.mpr, tendsto_comap_iff, tendsto_log_nhdsGT_zero, tendsto_norm_nhdsNE_zero
-/
theorem invQParam_tendsto (hh : 0 < h) : Tendsto (invQParam h) (𝓝[!=] 0) I∞ := by
  simp only [tendsto_comap_iff, comp_def, im_invQParam]
  apply Tendsto.const_mul_atBot_of_neg (div_neg_of_neg_of_pos (neg_lt_zero.mpr hh) (by positivity))
  exact Real.tendsto_log_nhdsGT_zero.comp tendsto_norm_nhdsNE_zero

end qParam

section PeriodicOnComplex

variable (h : Real) (f : Complex -> Complex)

/--
Definition of `cuspFunction` / `cuspFunction` 的定义

English:
definition cuspFunction
  signature: : Complex -> Complex
  body: update (f ∘ invQParam h) 0 (limUnder (𝓝[!=] 0) (f ∘ invQParam h))

中文:
定义 cuspFunction
  签名: : 复形 -> 复形
  定义体: update (f ∘ invQParam h) 0 (limUnder (𝓝[!=] 0) (f ∘ invQParam h))

Depends on / 依赖: invQParam, limUnder, update
-/
def cuspFunction : Complex -> Complex :=
  update (f ∘ invQParam h) 0 (limUnder (𝓝[!=] 0) (f ∘ invQParam h))

/--
theorem `cuspFunction_eq_of_nonzero` / 定理 `cuspFunction_eq_of_nonzero`

English:
theorem cuspFunction_eq_of_nonzero
  given: {q : Complex} (hq : q != 0)
  proof: update_of_ne hq ..

中文:
定理 cuspFunction_eq_of_nonzero
  条件: {q : 复形} (hq : q != 0)
  证明: update_of_ne hq ..

Depends on / 依赖: update_of_ne
-/
theorem cuspFunction_eq_of_nonzero {q : Complex} (hq : q != 0) :
    cuspFunction h f q = f (invQParam h q) :=
  update_of_ne hq ..

/--
theorem `cuspFunction_zero_eq_limUnder_nhds_ne` / 定理 `cuspFunction_zero_eq_limUnder_nhds_ne`

English:
theorem cuspFunction_zero_eq_limUnder_nhds_ne
  proof: by
  conv_lhs => simp only [cuspFunction, update_self]
  refine congr_arg lim (Filter.map_congr <| eventuallyEq_nhdsWithin_of_eqOn fun r hr => ?_)
  rw [cuspFunction]; rw [update_of_ne hr]

中文:
定理 cuspFunction_zero_eq_limUnder_nhds_ne
  证明: by
  conv_lhs => simp only [cuspFunction, update_self]
  refine congr_arg lim (Filter.map_congr <| eventuallyEq_nhdsWithin_of_eqOn fun r hr => ?_)
  rw [cuspFunction]; rw [update_of_ne hr]

Depends on / 依赖: Filter, Filter.map_congr, congr_arg, conv_lhs, cuspFunction, eventuallyEq_nhdsWithin_of_eqOn, map_congr, update_of_ne, update_self
-/
theorem cuspFunction_zero_eq_limUnder_nhds_ne :
    cuspFunction h f 0 = limUnder (𝓝[!=] 0) (cuspFunction h f) := by
  conv_lhs => simp only [cuspFunction, update_self]
  refine congr_arg lim (Filter.map_congr <| eventuallyEq_nhdsWithin_of_eqOn fun r hr => ?_)
  rw [cuspFunction]; rw [update_of_ne hr]

variable {f h}

/--
theorem `eq_cuspFunction` / 定理 `eq_cuspFunction`

English:
theorem eq_cuspFunction
  given: (hh : h != 0) (hf : Periodic f h) (z : Complex)
  proof: by
  have : (cuspFunction h f) (𝕢 h z) = f (invQParam h (𝕢 h z)) := by
    rw [cuspFunction]; rw [update_of_ne]; rw [comp_apply]
    exact exp_ne_zero _
  obtain ⟨m, hm⟩ := qParam_left_inv_mod_period hh z
  simpa only [this, hm] using hf.int_mul m z

中文:
定理 eq_cuspFunction
  条件: (hh : h != 0) (hf : 周期 f h) (z : 复形)
  证明: by
  have : (cuspFunction h f) (𝕢 h z) = f (invQParam h (𝕢 h z)) := by
    rw [cuspFunction]; rw [update_of_ne]; rw [comp_apply]
    exact exp_ne_zero _
  obtain ⟨m, hm⟩ := qParam_left_inv_mod_period hh z
  simpa only [this, hm] using hf.int_mul m z

Depends on / 依赖: comp_apply, cuspFunction, exp_ne_zero, hf.int_mul, int_mul, invQParam, qParam_left_inv_mod_period, update_of_ne
-/
theorem eq_cuspFunction (hh : h != 0) (hf : Periodic f h) (z : Complex) :
    (cuspFunction h f) (𝕢 h z) = f z := by
  have : (cuspFunction h f) (𝕢 h z) = f (invQParam h (𝕢 h z)) := by
    rw [cuspFunction]; rw [update_of_ne]; rw [comp_apply]
    exact exp_ne_zero _
  obtain ⟨m, hm⟩ := qParam_left_inv_mod_period hh z
  simpa only [this, hm] using hf.int_mul m z

/--
lemma `tendsto_nhds_zero` / 引理 `tendsto_nhds_zero`

English:
lemma tendsto_nhds_zero
  given: {f : Complex -> Complex} (hcts : ContinuousAt (cuspFunction h f) 0)
  proof: by
  apply (tendsto_nhdsWithin_of_tendsto_nhds hcts.tendsto).congr'
  filter_upwards [self_mem_nhdsWithin] with a using cuspFunction_eq_of_nonzero h f

中文:
引理 tendsto_nhds_zero
  条件: {f : 复形 -> 复形} (hcts : ContinuousAt (cuspFunction h f) 0)
  证明: by
  apply (tendsto_nhdsWithin_of_tendsto_nhds hcts.tendsto).congr'
  filter_upwards [self_mem_nhdsWithin] with a using cuspFunction_eq_of_nonzero h f

Depends on / 依赖: cuspFunction_eq_of_nonzero, filter_upwards, hcts.tendsto, self_mem_nhdsWithin, tendsto, tendsto_nhdsWithin_of_tendsto_nhds
-/
lemma tendsto_nhds_zero {f : Complex -> Complex} (hcts : ContinuousAt (cuspFunction h f) 0) :
    Tendsto (fun x => f (invQParam h x)) (𝓝[!=] 0) (𝓝 (cuspFunction h f 0)) := by
  apply (tendsto_nhdsWithin_of_tendsto_nhds hcts.tendsto).congr'
  filter_upwards [self_mem_nhdsWithin] with a using cuspFunction_eq_of_nonzero h f

end PeriodicOnComplex

section HoloOnC

variable {h : Real} {f : Complex -> Complex}

/--
theorem `differentiableAt_cuspFunction` / 定理 `differentiableAt_cuspFunction`

English:
theorem differentiableAt_cuspFunction
  statement: (hh : h != 0) (hf : Periodic f h)
  proof: by
  let q := 𝕢 h z
  have qdiff : HasStrictDerivAt (𝕢 h) (q * (2 * π * I / h)) z := by
    simpa only [id_eq, mul_one] using! (((hasStrictDerivAt_id z).const_mul _).div_const _).cexp
  -- Now show that the q-map has a differentiable local inverse at z, say L : ℂ → ℂ with L q = z.
  have diff_ne : q * (2 * π * I / h) != 0 :=
    mul_ne_zero (exp_ne_zero _) (div_ne_zero two_pi_I_ne_zero <| mod_cast hh)
  let L := (qdiff.localInverse (𝕢 h) _ z) diff_ne
  have diff_L : DifferentiableAt Complex L q :=
    (qdiff.to_localInverse diff_ne).hasStrictFDerivAt.differentiableAt
  have hL : 𝕢 h ∘ L =ᶠ[𝓝 q] (id : Complex -> Complex) :=
    (qdiff.hasStrictFDerivAt_equiv diff_ne).eventually_right_inverse
  -- Thus, if F = cuspFunction h f, we have F q' = f (L q') for q' near q.
  -- Since L is differentiable at q, and f is differentiable at L q [ = z], we conclude
  -- that F is differentiable at q.
  have hF := hL.fun_comp (cuspFunction h f)
  have : cuspFunction h f ∘ 𝕢 h ∘ L = f ∘ L := funext fun z => eq_cuspFunction hh hf (L z)
  rw [this] at hF
  rw [← EventuallyEq.eq_of_nhds (qdiff.hasStrictFDerivAt_equiv diff_ne).eventually_left_inverse]
    at hol_z
  exact (hol_z.comp q diff_L).congr_of_eventuallyEq hF.symm

中文:
定理 differentiableAt_cuspFunction
  结论: (hh : h != 0) (hf : 周期 f h)
  证明: by
  let q := 𝕢 h z
  have qdiff : HasStrictDerivAt (𝕢 h) (q * (2 * π * I / h)) z := by
    simpa only [id_eq, mul_one] using! (((hasStrictDerivAt_id z).const_mul _).div_const _).cexp
  -- Now show that the q-map has a differentiable local inverse at z, say L : ℂ → ℂ with L q = z.
  have diff_ne : q * (2 * π * I / h) != 0 :=
    mul_ne_zero (exp_ne_zero _) (div_ne_zero two_pi_I_ne_zero <| mod_cast hh)
  let L := (qdiff.localInverse (𝕢 h) _ z) diff_ne
  have diff_L : DifferentiableAt Complex L q :=
    (qdiff.to_localInverse diff_ne).hasStrictFDerivAt.differentiableAt
  have hL : 𝕢 h ∘ L =ᶠ[𝓝 q] (id : Complex -> Complex) :=
    (qdiff.hasStrictFDerivAt_equiv diff_ne).eventually_right_inverse
  -- Thus, if F = cuspFunction h f, we have F q' = f (L q') for q' near q.
  -- Since L is differentiable at q, and f is differentiable at L q [ = z], we conclude
  -- that F is differentiable at q.
  have hF := hL.fun_comp (cuspFunction h f)
  have : cuspFunction h f ∘ 𝕢 h ∘ L = f ∘ L := funext fun z => eq_cuspFunction hh hf (L z)
  rw [this] at hF
  rw [← EventuallyEq.eq_of_nhds (qdiff.hasStrictFDerivAt_equiv diff_ne).eventually_left_inverse]
    at hol_z
  exact (hol_z.comp q diff_L).congr_of_eventuallyEq hF.symm

Depends on / 依赖: HasStrictDerivAt, const_mul, div_const, hasStrictDerivAt_id, id_eq, mul_one
-/
theorem differentiableAt_cuspFunction (hh : h != 0) (hf : Periodic f h)
    {z : Complex} (hol_z : DifferentiableAt Complex f z) :
    DifferentiableAt Complex (cuspFunction h f) (𝕢 h z) := by
  let q := 𝕢 h z
  have qdiff : HasStrictDerivAt (𝕢 h) (q * (2 * π * I / h)) z := by
    simpa only [id_eq, mul_one] using! (((hasStrictDerivAt_id z).const_mul _).div_const _).cexp
  -- Now show that the q-map has a differentiable local inverse at z, say L : ℂ → ℂ with L q = z.
  have diff_ne : q * (2 * π * I / h) != 0 :=
    mul_ne_zero (exp_ne_zero _) (div_ne_zero two_pi_I_ne_zero <| mod_cast hh)
  let L := (qdiff.localInverse (𝕢 h) _ z) diff_ne
  have diff_L : DifferentiableAt Complex L q :=
    (qdiff.to_localInverse diff_ne).hasStrictFDerivAt.differentiableAt
  have hL : 𝕢 h ∘ L =ᶠ[𝓝 q] (id : Complex -> Complex) :=
    (qdiff.hasStrictFDerivAt_equiv diff_ne).eventually_right_inverse
  -- Thus, if F = cuspFunction h f, we have F q' = f (L q') for q' near q.
  -- Since L is differentiable at q, and f is differentiable at L q [ = z], we conclude
  -- that F is differentiable at q.
  have hF := hL.fun_comp (cuspFunction h f)
  have : cuspFunction h f ∘ 𝕢 h ∘ L = f ∘ L := funext fun z => eq_cuspFunction hh hf (L z)
  rw [this] at hF
  rw [← EventuallyEq.eq_of_nhds (qdiff.hasStrictFDerivAt_equiv diff_ne).eventually_left_inverse]
    at hol_z
  exact (hol_z.comp q diff_L).congr_of_eventuallyEq hF.symm

/--
theorem `eventually_differentiableAt_cuspFunction_nhds_ne_zero` / 定理 `eventually_differentiableAt_cuspFunction_nhds_ne_zero`

English:
theorem eventually_differentiableAt_cuspFunction_nhds_ne_zero
  statement: (hh : 0 < h) (hf : Periodic f h)
  proof: by
  refine ((invQParam_tendsto hh).eventually h_hol).mp ?_
  refine eventually_nhdsWithin_of_forall (fun q hq h_diff => ?_)
  rw [← qParam_right_inv hh.ne' hq]
  exact differentiableAt_cuspFunction hh.ne' hf h_diff

中文:
定理 eventually_differentiableAt_cuspFunction_nhds_ne_zero
  结论: (hh : 0 < h) (hf : 周期 f h)
  证明: by
  refine ((invQParam_tendsto hh).eventually h_hol).mp ?_
  refine eventually_nhdsWithin_of_forall (fun q hq h_diff => ?_)
  rw [← qParam_right_inv hh.ne' hq]
  exact differentiableAt_cuspFunction hh.ne' hf h_diff

Depends on / 依赖: differentiableAt_cuspFunction, eventually, eventually_nhdsWithin_of_forall, h_diff, h_hol, hh.ne, invQParam_tendsto, qParam_right_inv
-/
theorem eventually_differentiableAt_cuspFunction_nhds_ne_zero (hh : 0 < h) (hf : Periodic f h)
    (h_hol : forallᶠ z in I∞, DifferentiableAt Complex f z) :
    forallᶠ q in 𝓝[!=] 0, DifferentiableAt Complex (cuspFunction h f) q := by
  refine ((invQParam_tendsto hh).eventually h_hol).mp ?_
  refine eventually_nhdsWithin_of_forall (fun q hq h_diff => ?_)
  rw [← qParam_right_inv hh.ne' hq]
  exact differentiableAt_cuspFunction hh.ne' hf h_diff

end HoloOnC

section HoloAtInfC

variable {h : Real} {f : Complex -> Complex}

/--
theorem `boundedAtFilter_cuspFunction` / 定理 `boundedAtFilter_cuspFunction`

English:
theorem boundedAtFilter_cuspFunction
  given: (hh : 0 < h) (h_bd : BoundedAtFilter I∞ f)
  proof: by
  refine (h_bd.comp_tendsto <| invQParam_tendsto hh).congr' ?_ (by simp)
  refine eventually_nhdsWithin_of_forall fun q hq => ?_
  rw [cuspFunction_eq_of_nonzero _ _ hq]; rw [comp_def]

中文:
定理 boundedAtFilter_cuspFunction
  条件: (hh : 0 < h) (h_bd : BoundedAtFilter I∞ f)
  证明: by
  refine (h_bd.comp_tendsto <| invQParam_tendsto hh).congr' ?_ (by simp)
  refine eventually_nhdsWithin_of_forall fun q hq => ?_
  rw [cuspFunction_eq_of_nonzero _ _ hq]; rw [comp_def]

Depends on / 依赖: comp_def, comp_tendsto, cuspFunction_eq_of_nonzero, eventually_nhdsWithin_of_forall, h_bd, h_bd.comp_tendsto, invQParam_tendsto
-/
theorem boundedAtFilter_cuspFunction (hh : 0 < h) (h_bd : BoundedAtFilter I∞ f) :
    BoundedAtFilter (𝓝[!=] 0) (cuspFunction h f) := by
  refine (h_bd.comp_tendsto <| invQParam_tendsto hh).congr' ?_ (by simp)
  refine eventually_nhdsWithin_of_forall fun q hq => ?_
  rw [cuspFunction_eq_of_nonzero _ _ hq]; rw [comp_def]

/--
theorem `cuspFunction_zero_of_zero_at_inf` / 定理 `cuspFunction_zero_of_zero_at_inf`

English:
theorem cuspFunction_zero_of_zero_at_inf
  given: (hh : 0 < h) (h_zer : ZeroAtFilter I∞ f)
  proof: by
  simpa only [cuspFunction, update_self] using (h_zer.comp (invQParam_tendsto hh)).limUnder_eq

中文:
定理 cuspFunction_zero_of_zero_at_inf
  条件: (hh : 0 < h) (h_zer : ZeroAtFilter I∞ f)
  证明: by
  simpa only [cuspFunction, update_self] using (h_zer.comp (invQParam_tendsto hh)).limUnder_eq

Depends on / 依赖: cuspFunction, h_zer, h_zer.comp, invQParam_tendsto, limUnder_eq, update_self
-/
theorem cuspFunction_zero_of_zero_at_inf (hh : 0 < h) (h_zer : ZeroAtFilter I∞ f) :
    cuspFunction h f 0 = 0 := by
  simpa only [cuspFunction, update_self] using (h_zer.comp (invQParam_tendsto hh)).limUnder_eq

/--
theorem `differentiableAt_cuspFunction_zero` / 定理 `differentiableAt_cuspFunction_zero`

English:
theorem differentiableAt_cuspFunction_zero
  statement: (hh : 0 < h) (hf : Periodic f h)
  proof: by
  obtain ⟨c, t⟩ := (boundedAtFilter_cuspFunction hh h_bd).bound
  replace t := (eventually_differentiableAt_cuspFunction_nhds_ne_zero hh hf h_hol).and t
  simp only [norm_one, Pi.one_apply, mul_one] at t
  obtain ⟨S, hS1, hS2, hS3⟩ := eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp t)
  have h_diff : DifferentiableOn Complex (cuspFunction h f) (S \ {0}) :=
    fun x hx => (hS1 x hx.1 hx.2).1.differentiableWithinAt
  have hF_bd : BddAbove (norm ∘ cuspFunction h f '' (S \ {0})) := by
    use c
    simp only [mem_upperBounds, Set.mem_image, Set.mem_sdiff, forall_exists_index, and_imp]
    intro y q hq hq2 hy
    simpa only [← hy, norm_one, mul_one] using! (hS1 q hq hq2).2
  have := differentiableOn_update_limUnder_of_bddAbove (IsOpen.mem_nhds hS2 hS3) h_diff hF_bd
  rw [← cuspFunction_zero_eq_limUnder_nhds_ne]; rw [update_eq_self] at this
  exact this.differentiableAt (IsOpen.mem_nhds hS2 hS3)

中文:
定理 differentiableAt_cuspFunction_zero
  结论: (hh : 0 < h) (hf : 周期 f h)
  证明: by
  obtain ⟨c, t⟩ := (boundedAtFilter_cuspFunction hh h_bd).bound
  replace t := (eventually_differentiableAt_cuspFunction_nhds_ne_zero hh hf h_hol).and t
  simp only [norm_one, Pi.one_apply, mul_one] at t
  obtain ⟨S, hS1, hS2, hS3⟩ := eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp t)
  have h_diff : DifferentiableOn Complex (cuspFunction h f) (S \ {0}) :=
    fun x hx => (hS1 x hx.1 hx.2).1.differentiableWithinAt
  have hF_bd : BddAbove (norm ∘ cuspFunction h f '' (S \ {0})) := by
    use c
    simp only [mem_upperBounds, Set.mem_image, Set.mem_sdiff, forall_exists_index, and_imp]
    intro y q hq hq2 hy
    simpa only [← hy, norm_one, mul_one] using! (hS1 q hq hq2).2
  have := differentiableOn_update_limUnder_of_bddAbove (IsOpen.mem_nhds hS2 hS3) h_diff hF_bd
  rw [← cuspFunction_zero_eq_limUnder_nhds_ne]; rw [update_eq_self] at this
  exact this.differentiableAt (IsOpen.mem_nhds hS2 hS3)

Depends on / 依赖: BddAbove, DifferentiableOn, Pi.one_apply, boundedAtFilter_cuspFunction, cuspFunction, differentiableWithinAt, eventually_differentiableAt_cuspFunction_nhds_ne_zero, eventually_nhdsWithin_iff, eventually_nhdsWithin_iff.mp, eventually_nhds_iff, eventually_nhds_iff.mp, hF_bd, h_bd, h_diff, h_hol, mem_, mul_one, norm_one, one_apply, replace
-/
theorem differentiableAt_cuspFunction_zero (hh : 0 < h) (hf : Periodic f h)
    (h_hol : forallᶠ z in I∞, DifferentiableAt Complex f z) (h_bd : BoundedAtFilter I∞ f) :
    DifferentiableAt Complex (cuspFunction h f) 0 := by
  obtain ⟨c, t⟩ := (boundedAtFilter_cuspFunction hh h_bd).bound
  replace t := (eventually_differentiableAt_cuspFunction_nhds_ne_zero hh hf h_hol).and t
  simp only [norm_one, Pi.one_apply, mul_one] at t
  obtain ⟨S, hS1, hS2, hS3⟩ := eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp t)
  have h_diff : DifferentiableOn Complex (cuspFunction h f) (S \ {0}) :=
    fun x hx => (hS1 x hx.1 hx.2).1.differentiableWithinAt
  have hF_bd : BddAbove (norm ∘ cuspFunction h f '' (S \ {0})) := by
    use c
    simp only [mem_upperBounds, Set.mem_image, Set.mem_sdiff, forall_exists_index, and_imp]
    intro y q hq hq2 hy
    simpa only [← hy, norm_one, mul_one] using! (hS1 q hq hq2).2
  have := differentiableOn_update_limUnder_of_bddAbove (IsOpen.mem_nhds hS2 hS3) h_diff hF_bd
  rw [← cuspFunction_zero_eq_limUnder_nhds_ne]; rw [update_eq_self] at this
  exact this.differentiableAt (IsOpen.mem_nhds hS2 hS3)

/--
theorem `tendsto_at_I_inf` / 定理 `tendsto_at_I_inf`

English:
theorem tendsto_at_I_inf
  statement: (hh : 0 < h) (hf : Periodic f h)
  proof: by
  suffices Tendsto (cuspFunction h f) (𝓝[!=] 0) (𝓝 <| cuspFunction h f 0) by
    simpa only [Function.comp_def, eq_cuspFunction hh.ne' hf] using this.comp (qParam_tendsto hh)
  exact tendsto_nhdsWithin_of_tendsto_nhds
    (differentiableAt_cuspFunction_zero hh hf h_hol h_bd).continuousAt.tendsto

中文:
定理 tendsto_at_I_inf
  结论: (hh : 0 < h) (hf : 周期 f h)
  证明: by
  suffices Tendsto (cuspFunction h f) (𝓝[!=] 0) (𝓝 <| cuspFunction h f 0) by
    simpa only [Function.comp_def, eq_cuspFunction hh.ne' hf] using this.comp (qParam_tendsto hh)
  exact tendsto_nhdsWithin_of_tendsto_nhds
    (differentiableAt_cuspFunction_zero hh hf h_hol h_bd).continuousAt.tendsto

Depends on / 依赖: Function, Function.comp_def, Tendsto, comp_def, continuousAt, continuousAt.tendsto, cuspFunction, differentiableAt_cuspFunction_zero, eq_cuspFunction, h_bd, h_hol, hh.ne, qParam_tendsto, tendsto, tendsto_nhdsWithin_of_tendsto_nhds, this.comp
-/
theorem tendsto_at_I_inf (hh : 0 < h) (hf : Periodic f h)
    (h_hol : forallᶠ z in I∞, DifferentiableAt Complex f z) (h_bd : BoundedAtFilter I∞ f) :
    Tendsto f I∞ (𝓝 <| cuspFunction h f 0) := by
  suffices Tendsto (cuspFunction h f) (𝓝[!=] 0) (𝓝 <| cuspFunction h f 0) by
    simpa only [Function.comp_def, eq_cuspFunction hh.ne' hf] using this.comp (qParam_tendsto hh)
  exact tendsto_nhdsWithin_of_tendsto_nhds
    (differentiableAt_cuspFunction_zero hh hf h_hol h_bd).continuousAt.tendsto

/--
theorem `exp_decay_sub_of_bounded_at_inf` / 定理 `exp_decay_sub_of_bounded_at_inf`

English:
theorem exp_decay_sub_of_bounded_at_inf
  statement: (hh : 0 < h) (hf : Periodic f h)
  proof: by
  simpa [comp_def, eq_cuspFunction hh.ne' hf, norm_qParam] using
.isBigO_sub.mono differentiableAt_cuspFunction_zero hh hf h_hol h_bd
.norm_right .comp_tendsto (qParam_tendsto hh) nhdsWithin_le_nhds

中文:
定理 exp_decay_sub_of_bounded_at_inf
  结论: (hh : 0 < h) (hf : 周期 f h)
  证明: by
  simpa [comp_def, eq_cuspFunction hh.ne' hf, norm_qParam] using
.isBigO_sub.mono differentiableAt_cuspFunction_zero hh hf h_hol h_bd
.norm_right .comp_tendsto (qParam_tendsto hh) nhdsWithin_le_nhds

Depends on / 依赖: comp_def, comp_tendsto, differentiableAt_cuspFunction_zero, eq_cuspFunction, h_bd, h_hol, hh.ne, isBigO_sub, isBigO_sub.mono, nhdsWithin_le_nhds, norm_qParam, norm_right, qParam_tendsto
-/
theorem exp_decay_sub_of_bounded_at_inf (hh : 0 < h) (hf : Periodic f h)
    (h_hol : forallᶠ z in I∞, DifferentiableAt Complex f z) (h_bd : BoundedAtFilter I∞ f) :
    (fun z => f z - cuspFunction h f 0) =O[I∞] (fun z => Real.exp (-2 * π * im z / h)) := by
  simpa [comp_def, eq_cuspFunction hh.ne' hf, norm_qParam] using
.isBigO_sub.mono differentiableAt_cuspFunction_zero hh hf h_hol h_bd
.norm_right .comp_tendsto (qParam_tendsto hh) nhdsWithin_le_nhds

/--
theorem `exp_decay_of_zero_at_inf` / 定理 `exp_decay_of_zero_at_inf`

English:
theorem exp_decay_of_zero_at_inf
  statement: (hh : 0 < h) (hf : Periodic f h)
  proof: by
  simpa [cuspFunction_zero_of_zero_at_inf hh h_zer, sub_zero] using
    exp_decay_sub_of_bounded_at_inf hh hf h_hol h_zer.boundedAtFilter

中文:
定理 exp_decay_of_zero_at_inf
  结论: (hh : 0 < h) (hf : 周期 f h)
  证明: by
  simpa [cuspFunction_zero_of_zero_at_inf hh h_zer, sub_zero] using
    exp_decay_sub_of_bounded_at_inf hh hf h_hol h_zer.boundedAtFilter

Depends on / 依赖: boundedAtFilter, cuspFunction_zero_of_zero_at_inf, exp_decay_sub_of_bounded_at_inf, h_hol, h_zer, h_zer.boundedAtFilter, sub_zero
-/
theorem exp_decay_of_zero_at_inf (hh : 0 < h) (hf : Periodic f h)
    (h_hol : forallᶠ z in I∞, DifferentiableAt Complex f z) (h_zer : ZeroAtFilter I∞ f) :
    f =O[I∞] fun z => Real.exp (-2 * π * im z / h) := by
  simpa [cuspFunction_zero_of_zero_at_inf hh h_zer, sub_zero] using
    exp_decay_sub_of_bounded_at_inf hh hf h_hol h_zer.boundedAtFilter

end HoloAtInfC

section arithmetic

/--
lemma `cuspFunction_smul` / 引理 `cuspFunction_smul`

English:
lemma cuspFunction_smul
  given: {h} {f : Complex -> Complex} (hfcts : ContinuousAt (cuspFunction h f) 0) (a : Complex)
  proof: by
  simp only [cuspFunction] at *
  ext y
  obtain rfl | hy := eq_or_ne y 0
  · simpa using! (Tendsto.const_mul _ (by simpa using! hfcts)).limUnder_eq
  · simp [hy]

中文:
引理 cuspFunction_smul
  条件: {h} {f : 复形 -> 复形} (hfcts : ContinuousAt (cuspFunction h f) 0) (a : 复形)
  证明: by
  simp only [cuspFunction] at *
  ext y
  obtain rfl | hy := eq_or_ne y 0
  · simpa using! (Tendsto.const_mul _ (by simpa using! hfcts)).limUnder_eq
  · simp [hy]

Depends on / 依赖: Tendsto, Tendsto.const_mul, const_mul, cuspFunction, eq_or_ne, limUnder_eq
-/
lemma cuspFunction_smul {h} {f : Complex -> Complex} (hfcts : ContinuousAt (cuspFunction h f) 0) (a : Complex) :
    cuspFunction h (a • f) = a • cuspFunction h f := by
  simp only [cuspFunction] at *
  ext y
  obtain rfl | hy := eq_or_ne y 0
  · simpa using! (Tendsto.const_mul _ (by simpa using! hfcts)).limUnder_eq
  · simp [hy]

/--
lemma `cuspFunction_neg` / 引理 `cuspFunction_neg`

English:
lemma cuspFunction_neg
  given: {h} {f : Complex -> Complex} (hfcts : ContinuousAt (cuspFunction h f) 0)
  proof: by
  simpa using cuspFunction_smul hfcts (-1)

中文:
引理 cuspFunction_neg
  条件: {h} {f : 复形 -> 复形} (hfcts : ContinuousAt (cuspFunction h f) 0)
  证明: by
  simpa using cuspFunction_smul hfcts (-1)

Depends on / 依赖: cuspFunction_smul
-/
lemma cuspFunction_neg {h} {f : Complex -> Complex} (hfcts : ContinuousAt (cuspFunction h f) 0) :
    cuspFunction h (-f) = -cuspFunction h f := by
  simpa using cuspFunction_smul hfcts (-1)

/--
lemma `cuspFunction_add` / 引理 `cuspFunction_add`

English:
lemma cuspFunction_add
  statement: {h} {f g : Complex -> Complex} (hfcts : ContinuousAt (cuspFunction h f) 0)
  proof: by
  simp only [cuspFunction]
  ext y
  obtain hy | rfl := ne_or_eq y 0
  · simp [hy]
  · simpa using! (tendsto_nhds_limUnder ⟨_, tendsto_nhds_zero hfcts⟩).add
.limUnder_eq (tendsto_nhds_limUnder ⟨_, tendsto_nhds_zero hgcts⟩)

中文:
引理 cuspFunction_add
  结论: {h} {f g : 复形 -> 复形} (hfcts : ContinuousAt (cuspFunction h f) 0)
  证明: by
  simp only [cuspFunction]
  ext y
  obtain hy | rfl := ne_or_eq y 0
  · simp [hy]
  · simpa using! (tendsto_nhds_limUnder ⟨_, tendsto_nhds_zero hfcts⟩).add
.limUnder_eq (tendsto_nhds_limUnder ⟨_, tendsto_nhds_zero hgcts⟩)

Depends on / 依赖: cuspFunction, limUnder_eq, ne_or_eq, tendsto_nhds_limUnder, tendsto_nhds_zero
-/
lemma cuspFunction_add {h} {f g : Complex -> Complex} (hfcts : ContinuousAt (cuspFunction h f) 0)
    (hgcts : ContinuousAt (cuspFunction h g) 0) :
    cuspFunction h (f + g) = cuspFunction h f + cuspFunction h g := by
  simp only [cuspFunction]
  ext y
  obtain hy | rfl := ne_or_eq y 0
  · simp [hy]
  · simpa using! (tendsto_nhds_limUnder ⟨_, tendsto_nhds_zero hfcts⟩).add
.limUnder_eq (tendsto_nhds_limUnder ⟨_, tendsto_nhds_zero hgcts⟩)

/--
lemma `cuspFunction_sub` / 引理 `cuspFunction_sub`

English:
lemma cuspFunction_sub
  statement: {h} {f g : Complex -> Complex} (hfcts : ContinuousAt (cuspFunction h f) 0)
  proof: by
  simpa [sub_eq_add_neg, ← cuspFunction_neg hgcts]
    using cuspFunction_add hfcts (by simp [cuspFunction_neg, hgcts])

中文:
引理 cuspFunction_sub
  结论: {h} {f g : 复形 -> 复形} (hfcts : ContinuousAt (cuspFunction h f) 0)
  证明: by
  simpa [sub_eq_add_neg, ← cuspFunction_neg hgcts]
    using cuspFunction_add hfcts (by simp [cuspFunction_neg, hgcts])

Depends on / 依赖: cuspFunction_add, cuspFunction_neg, sub_eq_add_neg
-/
lemma cuspFunction_sub {h} {f g : Complex -> Complex} (hfcts : ContinuousAt (cuspFunction h f) 0)
    (hgcts : ContinuousAt (cuspFunction h g) 0) :
    cuspFunction h (f - g) = cuspFunction h f - cuspFunction h g := by
  simpa [sub_eq_add_neg, ← cuspFunction_neg hgcts]
    using cuspFunction_add hfcts (by simp [cuspFunction_neg, hgcts])

end arithmetic

end Function.Periodic
