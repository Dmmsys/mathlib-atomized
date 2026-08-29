/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Limits and asymptotics of power functions at `+∞`

This file contains results about the limiting behaviour of power functions at `+∞`. For convenience
some results on asymptotics as `x → 0` (those which are not just continuity statements) are also
located here.
-/

public section


noncomputable section

open Real Topology NNReal ENNReal Filter ComplexConjugate Finset Set

/-!
## Limits at `+∞`
-/


section Limits

open Real Filter

/--
theorem `tendsto_rpow_atTop` / 定理 `tendsto_rpow_atTop`

English:
theorem tendsto_rpow_atTop
  given: {y : Real} (hy : 0 < y)
  statement: Tendsto (fun x : Real => x ^ y) atTop atTop
  proof: by
  rw [(atTop_basis' 0).tendsto_right_iff]
  intro b hb
  filter_upwards [eventually_ge_atTop 0, eventually_ge_atTop (b ^ (1 / y))] with x hx₀ hx
  simpa (disch := positivity) [Real.rpow_inv_le_iff_of_pos] using hx

中文:
定理 tendsto_rpow_atTop
  条件: {y : 实数} (hy : 0 < y)
  结论: 收敛 (fun x : 实数 => x ^ y) atTop atTop
  证明: by
  rw [(atTop_basis' 0).tendsto_right_iff]
  intro b hb
  filter_upwards [eventually_ge_atTop 0, eventually_ge_atTop (b ^ (1 / y))] with x hx₀ hx
  simpa (disch := positivity) [Real.rpow_inv_le_iff_of_pos] using hx

Depends on / 依赖: Real.rpow_inv_le_iff_of_pos, atTop_basis, eventually_ge_atTop, filter_upwards, rpow_inv_le_iff_of_pos, tendsto_right_iff
-/
theorem tendsto_rpow_atTop {y : Real} (hy : 0 < y) : Tendsto (fun x : Real => x ^ y) atTop atTop := by
  rw [(atTop_basis' 0).tendsto_right_iff]
  intro b hb
  filter_upwards [eventually_ge_atTop 0, eventually_ge_atTop (b ^ (1 / y))] with x hx₀ hx
  simpa (disch := positivity) [Real.rpow_inv_le_iff_of_pos] using hx

/--
theorem `tendsto_rpow_neg_nhdsGT_zero` / 定理 `tendsto_rpow_neg_nhdsGT_zero`

English:
theorem tendsto_rpow_neg_nhdsGT_zero
  given: {y : Real} (hr : y < 0)
  proof: by
  simp_rw +singlePass [← neg_neg y, Real.rpow_neg_eq_inv_rpow]
  exact (tendsto_rpow_atTop <| neg_pos.mpr hr).comp tendsto_inv_nhdsGT_zero

中文:
定理 tendsto_rpow_neg_nhdsGT_zero
  条件: {y : 实数} (hr : y < 0)
  证明: by
  simp_rw +singlePass [← neg_neg y, Real.rpow_neg_eq_inv_rpow]
  exact (tendsto_rpow_atTop <| neg_pos.mpr hr).comp tendsto_inv_nhdsGT_zero

Depends on / 依赖: Real.rpow_neg_eq_inv_rpow, neg_neg, neg_pos, neg_pos.mpr, rpow_neg_eq_inv_rpow, simp_rw, singlePass, tendsto_inv_nhdsGT_zero, tendsto_rpow_atTop
-/
theorem tendsto_rpow_neg_nhdsGT_zero {y : Real} (hr : y < 0) :
    Tendsto (fun (x : Real) => x ^ y) (𝓝[>] 0) atTop := by
  simp_rw +singlePass [← neg_neg y, Real.rpow_neg_eq_inv_rpow]
  exact (tendsto_rpow_atTop <| neg_pos.mpr hr).comp tendsto_inv_nhdsGT_zero

/--
theorem `tendsto_rpow_neg_atTop` / 定理 `tendsto_rpow_neg_atTop`

English:
theorem tendsto_rpow_neg_atTop
  given: {y : Real} (hy : 0 < y)
  statement: Tendsto (fun x : Real => x ^ (-y)) atTop (𝓝 0)
  proof: Tendsto.congr' (eventuallyEq_of_mem (Ioi_mem_atTop 0) fun _ hx => (rpow_neg (le_of_lt hx) y).symm)
    (tendsto_rpow_atTop hy).inv_tendsto_atTop

中文:
定理 tendsto_rpow_neg_atTop
  条件: {y : 实数} (hy : 0 < y)
  结论: 收敛 (fun x : 实数 => x ^ (-y)) atTop (𝓝 0)
  证明: Tendsto.congr' (eventuallyEq_of_mem (Ioi_mem_atTop 0) fun _ hx => (rpow_neg (le_of_lt hx) y).symm)
    (tendsto_rpow_atTop hy).inv_tendsto_atTop

Depends on / 依赖: Ioi_mem_atTop, Tendsto, Tendsto.congr, eventuallyEq_of_mem, inv_tendsto_atTop, le_of_lt, rpow_neg, tendsto_rpow_atTop
-/
theorem tendsto_rpow_neg_atTop {y : Real} (hy : 0 < y) : Tendsto (fun x : Real => x ^ (-y)) atTop (𝓝 0) :=
  Tendsto.congr' (eventuallyEq_of_mem (Ioi_mem_atTop 0) fun _ hx => (rpow_neg (le_of_lt hx) y).symm)
    (tendsto_rpow_atTop hy).inv_tendsto_atTop

open Asymptotics in
/--
lemma `tendsto_rpow_atTop_of_base_lt_one` / 引理 `tendsto_rpow_atTop_of_base_lt_one`

English:
lemma tendsto_rpow_atTop_of_base_lt_one
  given: (b : Real) (hb₀ : -1 < b) (hb₁ : b < 1)
  proof: by
  rcases lt_trichotomy b 0 with hb | rfl | hb
  case inl => -- b < 0
    simp_rw [Real.rpow_def_of_nonpos hb.le, hb.ne, ite_false]
    rw [← isLittleO_const_iff (c := (1 : Real)) one_ne_zero]; rw [(one_mul (1 : Real)).symm]
    refine IsLittleO.mul_isBigO ?exp ?cos
    case exp =>
      rw [isLit

中文:
引理 tendsto_rpow_atTop_of_base_lt_one
  条件: (b : 实数) (hb₀ : -1 < b) (hb₁ : b < 1)
  证明: by
  rcases lt_trichotomy b 0 with hb | rfl | hb
  case inl => -- b < 0
    simp_rw [Real.rpow_def_of_nonpos hb.le, hb.ne, ite_false]
    rw [← isLittleO_const_iff (c := (1 : Real)) one_ne_zero]; rw [(one_mul (1 : Real)).symm]
    refine IsLittleO.mul_isBigO ?exp ?cos
    case exp =>
      rw [isLit

Depends on / 依赖: Eventually, Eventually.of_fo, IsLittleO, IsLittleO.mul_isBigO, Real.rpow_def_of_nonpos, hb.le, hb.ne, isBigO_iff, isLittleO_const_iff, ite_false, log_neg_eq_log, log_neg_iff, lt_trichotomy, mul_isBigO, of_fo, one_mul, one_ne_zero, rpow_def_of_nonpos, simp_rw, tendsto_const_mul_atBot_of_neg
-/
lemma tendsto_rpow_atTop_of_base_lt_one (b : Real) (hb₀ : -1 < b) (hb₁ : b < 1) :
    Tendsto (b ^ · : Real -> Real) atTop (𝓝 (0 : Real)) := by
  rcases lt_trichotomy b 0 with hb | rfl | hb
  case inl => -- b < 0
    simp_rw [Real.rpow_def_of_nonpos hb.le, hb.ne, ite_false]
    rw [← isLittleO_const_iff (c := (1 : Real)) one_ne_zero]; rw [(one_mul (1 : Real)).symm]
    refine IsLittleO.mul_isBigO ?exp ?cos
    case exp =>
      rw [isLittleO_const_iff one_ne_zero]
refine tendsto_exp_atBot.comp (tendsto_const_mul_atBot_of_neg ?_).mpr tendsto_id
      rw [← log_neg_eq_log]; rw [log_neg_iff (by linarith)]
      linarith
    case cos =>
      rw [isBigO_iff]
      exact ⟨1, Eventually.of_forall fun x => by simp [Real.abs_cos_le_one]⟩
  case inr.inl => -- b = 0
    refine Tendsto.mono_right ?_ (Iff.mpr pure_le_nhds_iff rfl)
    rw [tendsto_pure]
    filter_upwards [eventually_ne_atTop 0] with _ hx
    simp [hx]
  case inr.inr => -- b > 0
    simp_rw [Real.rpow_def_of_pos hb]
refine tendsto_exp_atBot.comp (tendsto_const_mul_atBot_of_neg ?_).mpr tendsto_id
    exact (log_neg_iff hb).mpr hb₁

/--
lemma `tendsto_rpow_atBot_of_base_lt_one` / 引理 `tendsto_rpow_atBot_of_base_lt_one`

English:
lemma tendsto_rpow_atBot_of_base_lt_one
  given: (b : Real) (hb₀ : 0 < b) (hb₁ : b < 1)
  proof: by
  simp_rw [Real.rpow_def_of_pos (by positivity : 0 < b)]
refine tendsto_exp_atTop.comp (tendsto_const_mul_atTop_iff_neg <| tendsto_id (α := Real)).mpr ?_
  exact (log_neg_iff hb₀).mpr hb₁

中文:
引理 tendsto_rpow_atBot_of_base_lt_one
  条件: (b : 实数) (hb₀ : 0 < b) (hb₁ : b < 1)
  证明: by
  simp_rw [Real.rpow_def_of_pos (by positivity : 0 < b)]
refine tendsto_exp_atTop.comp (tendsto_const_mul_atTop_iff_neg <| tendsto_id (α := Real)).mpr ?_
  exact (log_neg_iff hb₀).mpr hb₁

Depends on / 依赖: Real.rpow_def_of_pos, log_neg_iff, rpow_def_of_pos, simp_rw, tendsto_const_mul_atTop_iff_neg, tendsto_exp_atTop, tendsto_exp_atTop.comp, tendsto_id
-/
lemma tendsto_rpow_atBot_of_base_lt_one (b : Real) (hb₀ : 0 < b) (hb₁ : b < 1) :
    Tendsto (b ^ · : Real -> Real) atBot atTop := by
  simp_rw [Real.rpow_def_of_pos (by positivity : 0 < b)]
refine tendsto_exp_atTop.comp (tendsto_const_mul_atTop_iff_neg <| tendsto_id (α := Real)).mpr ?_
  exact (log_neg_iff hb₀).mpr hb₁

/--
lemma `tendsto_rpow_atTop_of_base_gt_one` / 引理 `tendsto_rpow_atTop_of_base_gt_one`

English:
lemma tendsto_rpow_atTop_of_base_gt_one
  given: (b : Real) (hb : 1 < b)
  proof: by
  simp_rw [Real.rpow_def_of_pos (by positivity : 0 < b)]
refine tendsto_exp_atTop.comp (tendsto_const_mul_atTop_iff_pos <| tendsto_id (α := Real)).mpr ?_
  exact log_pos hb

中文:
引理 tendsto_rpow_atTop_of_base_gt_one
  条件: (b : 实数) (hb : 1 < b)
  证明: by
  simp_rw [Real.rpow_def_of_pos (by positivity : 0 < b)]
refine tendsto_exp_atTop.comp (tendsto_const_mul_atTop_iff_pos <| tendsto_id (α := Real)).mpr ?_
  exact log_pos hb

Depends on / 依赖: Real.rpow_def_of_pos, log_pos, rpow_def_of_pos, simp_rw, tendsto_const_mul_atTop_iff_pos, tendsto_exp_atTop, tendsto_exp_atTop.comp, tendsto_id
-/
lemma tendsto_rpow_atTop_of_base_gt_one (b : Real) (hb : 1 < b) :
    Tendsto (b ^ · : Real -> Real) atTop atTop := by
  simp_rw [Real.rpow_def_of_pos (by positivity : 0 < b)]
refine tendsto_exp_atTop.comp (tendsto_const_mul_atTop_iff_pos <| tendsto_id (α := Real)).mpr ?_
  exact log_pos hb

/--
lemma `tendsto_rpow_atBot_of_base_gt_one` / 引理 `tendsto_rpow_atBot_of_base_gt_one`

English:
lemma tendsto_rpow_atBot_of_base_gt_one
  given: (b : Real) (hb : 1 < b)
  proof: by
  simp_rw [Real.rpow_def_of_pos (by positivity : 0 < b)]
refine tendsto_exp_atBot.comp (tendsto_const_mul_atBot_of_pos ?_).mpr tendsto_id
exact (log_pos_iff (by positivity)).mpr by aesop

中文:
引理 tendsto_rpow_atBot_of_base_gt_one
  条件: (b : 实数) (hb : 1 < b)
  证明: by
  simp_rw [Real.rpow_def_of_pos (by positivity : 0 < b)]
refine tendsto_exp_atBot.comp (tendsto_const_mul_atBot_of_pos ?_).mpr tendsto_id
exact (log_pos_iff (by positivity)).mpr by aesop

Depends on / 依赖: Real.rpow_def_of_pos, log_pos_iff, rpow_def_of_pos, simp_rw, tendsto_const_mul_atBot_of_pos, tendsto_exp_atBot, tendsto_exp_atBot.comp, tendsto_id
-/
lemma tendsto_rpow_atBot_of_base_gt_one (b : Real) (hb : 1 < b) :
    Tendsto (b ^ · : Real -> Real) atBot (𝓝 0) := by
  simp_rw [Real.rpow_def_of_pos (by positivity : 0 < b)]
refine tendsto_exp_atBot.comp (tendsto_const_mul_atBot_of_pos ?_).mpr tendsto_id
exact (log_pos_iff (by positivity)).mpr by aesop

/--
theorem `tendsto_rpow_div_mul_add` / 定理 `tendsto_rpow_div_mul_add`

English:
theorem tendsto_rpow_div_mul_add
  given: (a b c : Real) (hb : 0 != b)
  proof: by
  refine
    Tendsto.congr' ?_
      ((tendsto_exp_nhds_zero_nhds_one.comp
            (by
              simpa only [mul_zero, pow_one] using
                (tendsto_const_nhds (x := a)).mul
                  (tendsto_div_pow_mul_exp_add_atTop b c 1 hb))).comp
        tendsto_log_atTop)
  apply 

中文:
定理 tendsto_rpow_div_mul_add
  条件: (a b c : 实数) (hb : 0 != b)
  证明: by
  refine
    Tendsto.congr' ?_
      ((tendsto_exp_nhds_zero_nhds_one.comp
            (by
              simpa only [mul_zero, pow_one] using
                (tendsto_const_nhds (x := a)).mul
                  (tendsto_div_pow_mul_exp_add_atTop b c 1 hb))).comp
        tendsto_log_atTop)
  apply 

Depends on / 依赖: Function, Function.comp_apply, Ioi_mem_atTop, Set.mem_Ioi, Tendsto, Tendsto.congr, comp_apply, eventuallyEq_of_mem, exp_log, log_rpow, mem_Ioi, mul_zero, pow_one, rpow_pos_of_pos, tendsto_const_nhds, tendsto_div_pow_mul_exp_add_atTop, tendsto_exp_nhds_zero_nhds_one, tendsto_exp_nhds_zero_nhds_one.comp, tendsto_log_atTop
-/
theorem tendsto_rpow_div_mul_add (a b c : Real) (hb : 0 != b) :
    Tendsto (fun x => x ^ (a / (b * x + c))) atTop (𝓝 1) := by
  refine
    Tendsto.congr' ?_
      ((tendsto_exp_nhds_zero_nhds_one.comp
            (by
              simpa only [mul_zero, pow_one] using
                (tendsto_const_nhds (x := a)).mul
                  (tendsto_div_pow_mul_exp_add_atTop b c 1 hb))).comp
        tendsto_log_atTop)
  apply eventuallyEq_of_mem (Ioi_mem_atTop (0 : Real))
  intro x hx
  simp only [Set.mem_Ioi, Function.comp_apply] at hx ⊢
  rw [exp_log hx]; rw [← exp_log (rpow_pos_of_pos hx (a / (b * x + c)))]; rw [log_rpow hx (a / (b * x + c))]
  field_simp

/--
theorem `tendsto_rpow_div` / 定理 `tendsto_rpow_div`

English:
theorem tendsto_rpow_div
  statement: Tendsto (fun x => x ^ ((1 : Real) / x)) atTop (𝓝 1)
  proof: by
  convert! tendsto_rpow_div_mul_add (1 : Real) _ (0 : Real) zero_ne_one
  ring

中文:
定理 tendsto_rpow_div
  结论: 收敛 (fun x => x ^ ((1 : 实数) / x)) atTop (𝓝 1)
  证明: by
  convert! tendsto_rpow_div_mul_add (1 : Real) _ (0 : Real) zero_ne_one
  ring

Depends on / 依赖: convert, tendsto_rpow_div_mul_add, zero_ne_one
-/
theorem tendsto_rpow_div : Tendsto (fun x => x ^ ((1 : Real) / x)) atTop (𝓝 1) := by
  convert! tendsto_rpow_div_mul_add (1 : Real) _ (0 : Real) zero_ne_one
  ring

/--
theorem `tendsto_rpow_neg_div` / 定理 `tendsto_rpow_neg_div`

English:
theorem tendsto_rpow_neg_div
  statement: Tendsto (fun x => x ^ (-(1 : Real) / x)) atTop (𝓝 1)
  proof: by
  convert! tendsto_rpow_div_mul_add (-(1 : Real)) _ (0 : Real) zero_ne_one
  ring

中文:
定理 tendsto_rpow_neg_div
  结论: 收敛 (fun x => x ^ (-(1 : 实数) / x)) atTop (𝓝 1)
  证明: by
  convert! tendsto_rpow_div_mul_add (-(1 : Real)) _ (0 : Real) zero_ne_one
  ring

Depends on / 依赖: convert, tendsto_rpow_div_mul_add, zero_ne_one
-/
theorem tendsto_rpow_neg_div : Tendsto (fun x => x ^ (-(1 : Real) / x)) atTop (𝓝 1) := by
  convert! tendsto_rpow_div_mul_add (-(1 : Real)) _ (0 : Real) zero_ne_one
  ring

/--
theorem `tendsto_exp_div_rpow_atTop` / 定理 `tendsto_exp_div_rpow_atTop`

English:
theorem tendsto_exp_div_rpow_atTop
  given: (s : Real)
  statement: Tendsto (fun x : Real => exp x / x ^ s) atTop atTop
  proof: by
  obtain ⟨n, hn⟩ := archimedean_iff_nat_lt.1 Real.instArchimedean s
  refine tendsto_atTop_mono' _ ?_ (tendsto_exp_div_pow_atTop n)
  filter_upwards [eventually_gt_atTop (0 : Real), eventually_ge_atTop (1 : Real)] with x hx₀ hx₁
  gcongr
  simpa using rpow_le_rpow_of_exponent_le hx₁ hn.le

中文:
定理 tendsto_exp_div_rpow_atTop
  条件: (s : 实数)
  结论: 收敛 (fun x : 实数 => exp x / x ^ s) atTop atTop
  证明: by
  obtain ⟨n, hn⟩ := archimedean_iff_nat_lt.1 Real.instArchimedean s
  refine tendsto_atTop_mono' _ ?_ (tendsto_exp_div_pow_atTop n)
  filter_upwards [eventually_gt_atTop (0 : Real), eventually_ge_atTop (1 : Real)] with x hx₀ hx₁
  gcongr
  simpa using rpow_le_rpow_of_exponent_le hx₁ hn.le

Depends on / 依赖: Real.instArchimedean, archimedean_iff_nat_lt, eventually_ge_atTop, eventually_gt_atTop, filter_upwards, hn.le, instArchimedean, rpow_le_rpow_of_exponent_le, tendsto_atTop_mono, tendsto_exp_div_pow_atTop
-/
theorem tendsto_exp_div_rpow_atTop (s : Real) : Tendsto (fun x : Real => exp x / x ^ s) atTop atTop := by
  obtain ⟨n, hn⟩ := archimedean_iff_nat_lt.1 Real.instArchimedean s
  refine tendsto_atTop_mono' _ ?_ (tendsto_exp_div_pow_atTop n)
  filter_upwards [eventually_gt_atTop (0 : Real), eventually_ge_atTop (1 : Real)] with x hx₀ hx₁
  gcongr
  simpa using rpow_le_rpow_of_exponent_le hx₁ hn.le

/--
theorem `tendsto_exp_mul_div_rpow_atTop` / 定理 `tendsto_exp_mul_div_rpow_atTop`

English:
theorem tendsto_exp_mul_div_rpow_atTop
  given: (s : Real) (b : Real) (hb : 0 < b)
  proof: by
  refine ((tendsto_rpow_atTop hb).comp (tendsto_exp_div_rpow_atTop (s / b))).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : Real)] with x hx₀
  simp [Real.div_rpow, (exp_pos x).le, rpow_nonneg, ← Real.rpow_mul, ← exp_mul,
    mul_comm x, hb.ne', *]

中文:
定理 tendsto_exp_mul_div_rpow_atTop
  条件: (s : 实数) (b : 实数) (hb : 0 < b)
  证明: by
  refine ((tendsto_rpow_atTop hb).comp (tendsto_exp_div_rpow_atTop (s / b))).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : Real)] with x hx₀
  simp [Real.div_rpow, (exp_pos x).le, rpow_nonneg, ← Real.rpow_mul, ← exp_mul,
    mul_comm x, hb.ne', *]

Depends on / 依赖: Real.div_rpow, Real.rpow_mul, div_rpow, eventually_ge_atTop, exp_mul, exp_pos, filter_upwards, hb.ne, mul_comm, rpow_mul, rpow_nonneg, tendsto_exp_div_rpow_atTop, tendsto_rpow_atTop
-/
theorem tendsto_exp_mul_div_rpow_atTop (s : Real) (b : Real) (hb : 0 < b) :
    Tendsto (fun x : Real => exp (b * x) / x ^ s) atTop atTop := by
  refine ((tendsto_rpow_atTop hb).comp (tendsto_exp_div_rpow_atTop (s / b))).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : Real)] with x hx₀
  simp [Real.div_rpow, (exp_pos x).le, rpow_nonneg, ← Real.rpow_mul, ← exp_mul,
    mul_comm x, hb.ne', *]

/--
theorem `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero` / 定理 `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`

English:
theorem tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
  given: (s : Real) (b : Real) (hb : 0 < b)
  proof: by
  refine (tendsto_exp_mul_div_rpow_atTop s b hb).inv_tendsto_atTop.congr' ?_
  filter_upwards with x using by simp [exp_neg, inv_div, div_eq_mul_inv _ (exp _)]

nonrec theorem NNReal.tendsto_rpow_atTop {y : Real} (hy : 0 < y) :
    Tendsto (fun x : Real>=0 => x ^ y) atTop atTop := by
  rw [Filter

中文:
定理 tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
  条件: (s : 实数) (b : 实数) (hb : 0 < b)
  证明: by
  refine (tendsto_exp_mul_div_rpow_atTop s b hb).inv_tendsto_atTop.congr' ?_
  filter_upwards with x using by simp [exp_neg, inv_div, div_eq_mul_inv _ (exp _)]

nonrec theorem NNReal.tendsto_rpow_atTop {y : Real} (hy : 0 < y) :
    Tendsto (fun x : Real>=0 => x ^ y) atTop atTop := by
  rw [Filter

Depends on / 依赖: div_eq_mul_inv, exp_neg, filter_upwards, inv_div, inv_tendsto_atTop, inv_tendsto_atTop.congr, tendsto_exp_mul_div_rpow_atTop
-/
theorem tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s : Real) (b : Real) (hb : 0 < b) :
    Tendsto (fun x : Real => x ^ s * exp (-b * x)) atTop (𝓝 0) := by
  refine (tendsto_exp_mul_div_rpow_atTop s b hb).inv_tendsto_atTop.congr' ?_
  filter_upwards with x using by simp [exp_neg, inv_div, div_eq_mul_inv _ (exp _)]

nonrec theorem NNReal.tendsto_rpow_atTop {y : Real} (hy : 0 < y) :
    Tendsto (fun x : Real>=0 => x ^ y) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨c, hc⟩ := tendsto_atTop_atTop.mp (tendsto_rpow_atTop hy) b
  use c.toNNReal
  intro a ha
  exact mod_cast hc a (Real.toNNReal_le_iff_le_coe.mp ha)

/--
theorem `ENNReal.tendsto_rpow_at_top` / 定理 `ENNReal.tendsto_rpow_at_top`

English:
theorem ENNReal.tendsto_rpow_at_top
  given: {y : Real} (hy : 0 < y)
  proof: by
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  intro x
  obtain ⟨c, _, hc⟩ :=
    (atTop_basis_Ioi.tendsto_iff atTop_basis_Ioi).mp (NNReal.tendsto_rpow_atTop hy) x trivial
  have hc' : Set.Ioi ↑c in 𝓝 (⊤ : Real>=0∞) := Ioi_mem_nhds ENNReal.coe_lt_top
  filter_upwards [hc'] with a ha
  by_cases ha' 

中文:
定理 广义非负实数.tendsto_rpow_at_top
  条件: {y : 实数} (hy : 0 < y)
  证明: by
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  intro x
  obtain ⟨c, _, hc⟩ :=
    (atTop_basis_Ioi.tendsto_iff atTop_basis_Ioi).mp (NNReal.tendsto_rpow_atTop hy) x trivial
  have hc' : Set.Ioi ↑c in 𝓝 (⊤ : Real>=0∞) := Ioi_mem_nhds ENNReal.coe_lt_top
  filter_upwards [hc'] with a ha
  by_cases ha' 

Depends on / 依赖: ENNReal, ENNReal.coe_lt_top, ENNReal.coe_rpow_of_nonneg, ENNReal.tendsto_nhds_top_iff_nnreal, Ioi_mem_nhds, NNReal, NNReal.tendsto_rpow_atTop, Set.Ioi, Set.mem_Ioi, atTop_basis_Ioi, atTop_basis_Ioi.tendsto_iff, coe_lt_coe, coe_lt_top, coe_rpow_of_nonneg, filter_upwards, hy.le, mem_Ioi, mod_cast, tendsto_iff, tendsto_nhds_top_iff_nnreal
-/
theorem ENNReal.tendsto_rpow_at_top {y : Real} (hy : 0 < y) :
    Tendsto (fun x : Real>=0∞ => x ^ y) (𝓝 ⊤) (𝓝 ⊤) := by
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  intro x
  obtain ⟨c, _, hc⟩ :=
    (atTop_basis_Ioi.tendsto_iff atTop_basis_Ioi).mp (NNReal.tendsto_rpow_atTop hy) x trivial
  have hc' : Set.Ioi ↑c in 𝓝 (⊤ : Real>=0∞) := Ioi_mem_nhds ENNReal.coe_lt_top
  filter_upwards [hc'] with a ha
  by_cases ha' : a = ⊤
  · simp [ha', hy]
  lift a to Real>=0 using ha'
  simp only [Set.mem_Ioi, coe_lt_coe] at ha hc
  rw [← ENNReal.coe_rpow_of_nonneg _ hy.le]
  exact mod_cast hc a ha

end Limits

/-!
## Asymptotic results: `IsBigO`, `IsLittleO` and `IsTheta`
-/


namespace Complex

section

variable {α : Type*} {l : Filter α} {f g : α -> Complex}

open Asymptotics

/--
theorem `isTheta_exp_arg_mul_im` / 定理 `isTheta_exp_arg_mul_im`

English:
theorem isTheta_exp_arg_mul_im
  given: (hl : IsBoundedUnder (· <= ·) l fun x => |(g x).im|)
  proof: by
  rcases hl with ⟨b, hb⟩
  refine Real.isTheta_exp_comp_one.2 ⟨π * b, ?_⟩
  rw [eventually_map] at hb ⊢
  refine hb.mono fun x hx => ?_
  rw [abs_mul]
  exact mul_le_mul (abs_arg_le_pi _) hx (abs_nonneg _) Real.pi_pos.le

中文:
定理 isTheta_exp_arg_mul_im
  条件: (hl : IsBoundedUnder (· <= ·) l fun x => |(g x).im|)
  证明: by
  rcases hl with ⟨b, hb⟩
  refine Real.isTheta_exp_comp_one.2 ⟨π * b, ?_⟩
  rw [eventually_map] at hb ⊢
  refine hb.mono fun x hx => ?_
  rw [abs_mul]
  exact mul_le_mul (abs_arg_le_pi _) hx (abs_nonneg _) Real.pi_pos.le

Depends on / 依赖: Real.isTheta_exp_comp_one, Real.pi_pos.le, abs_arg_le_pi, abs_mul, abs_nonneg, eventually_map, hb.mono, isTheta_exp_comp_one, mul_le_mul, pi_pos
-/
theorem isTheta_exp_arg_mul_im (hl : IsBoundedUnder (· <= ·) l fun x => |(g x).im|) :
    (fun x => Real.exp (arg (f x) * im (g x))) =Θ[l] fun _ => (1 : Real) := by
  rcases hl with ⟨b, hb⟩
  refine Real.isTheta_exp_comp_one.2 ⟨π * b, ?_⟩
  rw [eventually_map] at hb ⊢
  refine hb.mono fun x hx => ?_
  rw [abs_mul]
  exact mul_le_mul (abs_arg_le_pi _) hx (abs_nonneg _) Real.pi_pos.le

/--
theorem `isBigO_cpow_rpow` / 定理 `isBigO_cpow_rpow`

English:
theorem isBigO_cpow_rpow
  given: (hl : IsBoundedUnder (· <= ·) l fun x => |(g x).im|)
  proof: calc
    (fun x => f x ^ g x) =O[l]
        (show α -> Real from fun x => ‖f x‖ ^ (g x).re / Real.exp (arg (f x) * im (g x))) :=
      isBigO_of_le _ fun _ => (norm_cpow_le _ _).trans (le_abs_self _)
    _ =Θ[l] (show α -> Real from fun x => ‖f x‖ ^ (g x).re / (1 : Real)) :=
      ((isTheta_refl _ _

中文:
定理 isBigO_cpow_rpow
  条件: (hl : IsBoundedUnder (· <= ·) l fun x => |(g x).im|)
  证明: calc
    (fun x => f x ^ g x) =O[l]
        (show α -> Real from fun x => ‖f x‖ ^ (g x).re / Real.exp (arg (f x) * im (g x))) :=
      isBigO_of_le _ fun _ => (norm_cpow_le _ _).trans (le_abs_self _)
    _ =Θ[l] (show α -> Real from fun x => ‖f x‖ ^ (g x).re / (1 : Real)) :=
      ((isTheta_refl _ _

Depends on / 依赖: EventuallyEq, EventuallyEq.rfl, Real.exp, div_one, isBigO_of_le, isTheta_exp_arg_mul_im, isTheta_refl, le_abs_self, mapComp, norm_cpow_le
-/
theorem isBigO_cpow_rpow (hl : IsBoundedUnder (· <= ·) l fun x => |(g x).im|) :
    (fun x => f x ^ g x) =O[l] fun x => ‖f x‖ ^ (g x).re :=
  calc
    (fun x => f x ^ g x) =O[l]
        (show α -> Real from fun x => ‖f x‖ ^ (g x).re / Real.exp (arg (f x) * im (g x))) :=
      isBigO_of_le _ fun _ => (norm_cpow_le _ _).trans (le_abs_self _)
    _ =Θ[l] (show α -> Real from fun x => ‖f x‖ ^ (g x).re / (1 : Real)) :=
      ((isTheta_refl _ _).div (isTheta_exp_arg_mul_im hl))
    _ =ᶠ[l] (show α -> Real from fun x => ‖f x‖ ^ (g x).re) := by
      simp only [div_one, EventuallyEq.rfl]

/--
theorem `isTheta_cpow_rpow` / 定理 `isTheta_cpow_rpow`

English:
theorem isTheta_cpow_rpow
  statement: (hl_im : IsBoundedUnder (· <= ·) l fun x => |(g x).im|)
  proof: calc
    (fun x => f x ^ g x) =Θ[l]
        (fun x => ‖f x‖ ^ (g x).re / Real.exp (arg (f x) * im (g x))) :=
.of_norm_eventuallyEq hl.mono fun _ => norm_cpow_of_imp
    _ =Θ[l] fun x => ‖f x‖ ^ (g x).re / (1 : Real) :=
      (isTheta_refl _ _).div (isTheta_exp_arg_mul_im hl_im)
    _ =ᶠ[l] (fun x =>

中文:
定理 isTheta_cpow_rpow
  结论: (hl_im : IsBoundedUnder (· <= ·) l fun x => |(g x).im|)
  证明: calc
    (fun x => f x ^ g x) =Θ[l]
        (fun x => ‖f x‖ ^ (g x).re / Real.exp (arg (f x) * im (g x))) :=
.of_norm_eventuallyEq hl.mono fun _ => norm_cpow_of_imp
    _ =Θ[l] fun x => ‖f x‖ ^ (g x).re / (1 : Real) :=
      (isTheta_refl _ _).div (isTheta_exp_arg_mul_im hl_im)
    _ =ᶠ[l] (fun x =>

Depends on / 依赖: EventuallyEq, EventuallyEq.rfl, Real.exp, div_one, hl.mono, hl_im, isTheta_exp_arg_mul_im, isTheta_refl, norm_cpow_of_imp, of_norm_eventuallyEq
-/
theorem isTheta_cpow_rpow (hl_im : IsBoundedUnder (· <= ·) l fun x => |(g x).im|)
    (hl : forallᶠ x in l, f x = 0 -> re (g x) = 0 -> g x = 0) :
    (fun x => f x ^ g x) =Θ[l] fun x => ‖f x‖ ^ (g x).re :=
  calc
    (fun x => f x ^ g x) =Θ[l]
        (fun x => ‖f x‖ ^ (g x).re / Real.exp (arg (f x) * im (g x))) :=
.of_norm_eventuallyEq hl.mono fun _ => norm_cpow_of_imp
    _ =Θ[l] fun x => ‖f x‖ ^ (g x).re / (1 : Real) :=
      (isTheta_refl _ _).div (isTheta_exp_arg_mul_im hl_im)
    _ =ᶠ[l] (fun x => ‖f x‖ ^ (g x).re) := by
      simp only [div_one, EventuallyEq.rfl]

/--
theorem `isTheta_cpow_const_rpow` / 定理 `isTheta_cpow_const_rpow`

English:
theorem isTheta_cpow_const_rpow
  given: {b : Complex} (hl : b.re = 0 -> b != 0 -> forallᶠ x in l, f x != 0)
  proof: isTheta_cpow_rpow isBoundedUnder_const by
    simpa only [eventually_imp_distrib_right, not_imp_not, Imp.swap (a := b.re = 0)] using hl

中文:
定理 isTheta_cpow_const_rpow
  条件: {b : 复形} (hl : b.re = 0 -> b != 0 -> 对任意ᶠ x in l, f x != 0)
  证明: isTheta_cpow_rpow isBoundedUnder_const by
    simpa only [eventually_imp_distrib_right, not_imp_not, Imp.swap (a := b.re = 0)] using hl

Depends on / 依赖: Imp.swap, b.re, eventually_imp_distrib_right, isBoundedUnder_const, isTheta_cpow_rpow, not_imp_not
-/
theorem isTheta_cpow_const_rpow {b : Complex} (hl : b.re = 0 -> b != 0 -> forallᶠ x in l, f x != 0) :
    (fun x => f x ^ b) =Θ[l] fun x => ‖f x‖ ^ b.re :=
isTheta_cpow_rpow isBoundedUnder_const by
    simpa only [eventually_imp_distrib_right, not_imp_not, Imp.swap (a := b.re = 0)] using hl

end

end Complex

open Real

namespace Asymptotics

variable {α : Type*} {r c : Real} {l : Filter α} {f g : α -> Real}

/--
theorem `IsBigOWith.rpow` / 定理 `IsBigOWith.rpow`

English:
theorem IsBigOWith.rpow
  given: (h : IsBigOWith c l f g) (hc : 0 <= c) (hr : 0 <= r) (hg : 0 <=ᶠ[l] g)
  proof: by
  apply IsBigOWith.of_bound
  filter_upwards [hg, h.bound] with x hgx hx
  calc
    |f x ^ r| <= |f x| ^ r := abs_rpow_le_abs_rpow _ _
    _ <= (c * |g x|) ^ r := by gcongr; assumption
    _ = c ^ r * |g x ^ r| := by rw [mul_rpow hc (abs_nonneg _), abs_rpow_of_nonneg hgx]

中文:
定理 IsBigOWith.rpow
  条件: (h : IsBigOWith c l f g) (hc : 0 <= c) (hr : 0 <= r) (hg : 0 <=ᶠ[l] g)
  证明: by
  apply IsBigOWith.of_bound
  filter_upwards [hg, h.bound] with x hgx hx
  calc
    |f x ^ r| <= |f x| ^ r := abs_rpow_le_abs_rpow _ _
    _ <= (c * |g x|) ^ r := by gcongr; assumption
    _ = c ^ r * |g x ^ r| := by rw [mul_rpow hc (abs_nonneg _), abs_rpow_of_nonneg hgx]

Depends on / 依赖: IsBigOWith, IsBigOWith.of_bound, abs_nonneg, abs_rpow_le_abs_rpow, abs_rpow_of_nonneg, filter_upwards, h.bound, mul_rpow, of_bound
-/
theorem IsBigOWith.rpow (h : IsBigOWith c l f g) (hc : 0 <= c) (hr : 0 <= r) (hg : 0 <=ᶠ[l] g) :
    IsBigOWith (c ^ r) l (fun x => f x ^ r) fun x => g x ^ r := by
  apply IsBigOWith.of_bound
  filter_upwards [hg, h.bound] with x hgx hx
  calc
    |f x ^ r| <= |f x| ^ r := abs_rpow_le_abs_rpow _ _
    _ <= (c * |g x|) ^ r := by gcongr; assumption
    _ = c ^ r * |g x ^ r| := by rw [mul_rpow hc (abs_nonneg _), abs_rpow_of_nonneg hgx]

/--
theorem `IsBigO.rpow` / 定理 `IsBigO.rpow`

English:
theorem IsBigO.rpow
  given: (hr : 0 <= r) (hg : 0 <=ᶠ[l] g) (h : f =O[l] g)
  proof: let ⟨_, hc, h'⟩ := h.exists_nonneg
  (h'.rpow hc hr hg).isBigO

中文:
定理 IsBigO.rpow
  条件: (hr : 0 <= r) (hg : 0 <=ᶠ[l] g) (h : f =O[l] g)
  证明: let ⟨_, hc, h'⟩ := h.exists_nonneg
  (h'.rpow hc hr hg).isBigO

Depends on / 依赖: exists_nonneg, h.exists_nonneg, isBigO
-/
theorem IsBigO.rpow (hr : 0 <= r) (hg : 0 <=ᶠ[l] g) (h : f =O[l] g) :
    (fun x => f x ^ r) =O[l] fun x => g x ^ r :=
  let ⟨_, hc, h'⟩ := h.exists_nonneg
  (h'.rpow hc hr hg).isBigO

/--
theorem `IsTheta.rpow` / 定理 `IsTheta.rpow`

English:
theorem IsTheta.rpow
  given: (hf : 0 <=ᶠ[l] f) (hg : 0 <=ᶠ[l] g) (h : f =Θ[l] g)
  proof: by
  wlog hr : r >= 0 with rpow_pos
  · rw [← isTheta_inv]
    grw [← EventuallyEq.isTheta <| hf.mono fun x hfx => Real.rpow_neg hfx r]
    grw [← EventuallyEq.isTheta <| hg.mono fun x hgx => Real.rpow_neg hgx r]
exact rpow_pos hf hg h by linarith
  exact ⟨h.1.rpow hr hg, h.2.rpow hr hf⟩

中文:
定理 IsTheta.rpow
  条件: (hf : 0 <=ᶠ[l] f) (hg : 0 <=ᶠ[l] g) (h : f =Θ[l] g)
  证明: by
  wlog hr : r >= 0 with rpow_pos
  · rw [← isTheta_inv]
    grw [← EventuallyEq.isTheta <| hf.mono fun x hfx => Real.rpow_neg hfx r]
    grw [← EventuallyEq.isTheta <| hg.mono fun x hgx => Real.rpow_neg hgx r]
exact rpow_pos hf hg h by linarith
  exact ⟨h.1.rpow hr hg, h.2.rpow hr hf⟩

Depends on / 依赖: EventuallyEq, EventuallyEq.isTheta, Real.rpow_neg, hf.mono, hg.mono, isTheta, isTheta_inv, rpow_neg, rpow_pos
-/
theorem IsTheta.rpow (hf : 0 <=ᶠ[l] f) (hg : 0 <=ᶠ[l] g) (h : f =Θ[l] g) :
    (fun x => f x ^ r) =Θ[l] fun x => g x ^ r := by
  wlog hr : r >= 0 with rpow_pos
  · rw [← isTheta_inv]
    grw [← EventuallyEq.isTheta <| hf.mono fun x hfx => Real.rpow_neg hfx r]
    grw [← EventuallyEq.isTheta <| hg.mono fun x hgx => Real.rpow_neg hgx r]
exact rpow_pos hf hg h by linarith
  exact ⟨h.1.rpow hr hg, h.2.rpow hr hf⟩

/--
theorem `IsLittleO.rpow` / 定理 `IsLittleO.rpow`

English:
theorem IsLittleO.rpow
  given: (hr : 0 < r) (hg : 0 <=ᶠ[l] g) (h : f =o[l] g)
  proof: by
  refine .of_isBigOWith fun c hc => ?_
  rw [← rpow_inv_rpow hc.le hr.ne']
  refine (h.forall_isBigOWith ?_).rpow ?_ ?_ hg <;> positivity

中文:
定理 IsLittleO.rpow
  条件: (hr : 0 < r) (hg : 0 <=ᶠ[l] g) (h : f =o[l] g)
  证明: by
  refine .of_isBigOWith fun c hc => ?_
  rw [← rpow_inv_rpow hc.le hr.ne']
  refine (h.forall_isBigOWith ?_).rpow ?_ ?_ hg <;> positivity

Depends on / 依赖: forall_isBigOWith, h.forall_isBigOWith, hc.le, hr.ne, of_isBigOWith, rpow_inv_rpow
-/
theorem IsLittleO.rpow (hr : 0 < r) (hg : 0 <=ᶠ[l] g) (h : f =o[l] g) :
    (fun x => f x ^ r) =o[l] fun x => g x ^ r := by
  refine .of_isBigOWith fun c hc => ?_
  rw [← rpow_inv_rpow hc.le hr.ne']
  refine (h.forall_isBigOWith ?_).rpow ?_ ?_ hg <;> positivity

/--
lemma `IsBigO.sqrt` / 引理 `IsBigO.sqrt`

English:
lemma IsBigO.sqrt
  given: (hfg : f =O[l] g) (hg : 0 <=ᶠ[l] g)
  proof: by
  simpa [Real.sqrt_eq_rpow] using hfg.rpow one_half_pos.le hg

中文:
引理 IsBigO.sqrt
  条件: (hfg : f =O[l] g) (hg : 0 <=ᶠ[l] g)
  证明: by
  simpa [Real.sqrt_eq_rpow] using hfg.rpow one_half_pos.le hg
-/
protected lemma IsBigO.sqrt (hfg : f =O[l] g) (hg : 0 <=ᶠ[l] g) :
    (fun x => √(f x)) =O[l] (fun x => √(g x)) := by
  simpa [Real.sqrt_eq_rpow] using hfg.rpow one_half_pos.le hg

/--
lemma `IsLittleO.sqrt` / 引理 `IsLittleO.sqrt`

English:
lemma IsLittleO.sqrt
  given: (hfg : f =o[l] g) (hg : 0 <=ᶠ[l] g)
  proof: by
  simpa [Real.sqrt_eq_rpow] using hfg.rpow one_half_pos hg

中文:
引理 IsLittleO.sqrt
  条件: (hfg : f =o[l] g) (hg : 0 <=ᶠ[l] g)
  证明: by
  simpa [Real.sqrt_eq_rpow] using hfg.rpow one_half_pos hg
-/
protected lemma IsLittleO.sqrt (hfg : f =o[l] g) (hg : 0 <=ᶠ[l] g) :
    (fun x => √(f x)) =o[l] (fun x => √(g x)) := by
  simpa [Real.sqrt_eq_rpow] using hfg.rpow one_half_pos hg

/--
lemma `IsTheta.sqrt` / 引理 `IsTheta.sqrt`

English:
lemma IsTheta.sqrt
  given: (hfg : f =Θ[l] g) (hf : 0 <=ᶠ[l] f) (hg : 0 <=ᶠ[l] g)
  proof: ⟨hfg.1.sqrt hg, hfg.2.sqrt hf⟩

中文:
引理 IsTheta.sqrt
  条件: (hfg : f =Θ[l] g) (hf : 0 <=ᶠ[l] f) (hg : 0 <=ᶠ[l] g)
  证明: ⟨hfg.1.sqrt hg, hfg.2.sqrt hf⟩
-/
protected lemma IsTheta.sqrt (hfg : f =Θ[l] g) (hf : 0 <=ᶠ[l] f) (hg : 0 <=ᶠ[l] g) :
    (Real.sqrt <| f ·) =Θ[l] (Real.sqrt <| g ·) :=
  ⟨hfg.1.sqrt hg, hfg.2.sqrt hf⟩

/--
theorem `isBigO_atTop_natCast_rpow_of_tendsto_div_rpow` / 定理 `isBigO_atTop_natCast_rpow_of_tendsto_div_rpow`

English:
theorem isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
  statement: {𝕜 : Type*} [RCLike 𝕜] {g : Nat -> 𝕜}
  proof: by
  refine (isBigO_of_div_tendsto_nhds ?_ ‖a‖ ?_).of_norm_left
  · filter_upwards [eventually_ne_atTop 0] with _ h
    simp [Real.rpow_eq_zero_iff_of_nonneg, h]
  · exact hlim.norm.congr fun n => by simp [abs_of_nonneg, show 0 <= (n : Real) ^ r by positivity]

中文:
定理 isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
  结论: {𝕜 : 类型} [RCLike 𝕜] {g : 自然数 -> 𝕜}
  证明: by
  refine (isBigO_of_div_tendsto_nhds ?_ ‖a‖ ?_).of_norm_left
  · filter_upwards [eventually_ne_atTop 0] with _ h
    simp [Real.rpow_eq_zero_iff_of_nonneg, h]
  · exact hlim.norm.congr fun n => by simp [abs_of_nonneg, show 0 <= (n : Real) ^ r by positivity]

Depends on / 依赖: Real.rpow_eq_zero_iff_of_nonneg, abs_of_nonneg, eventually_ne_atTop, filter_upwards, hlim.norm.congr, isBigO_of_div_tendsto_nhds, of_norm_left, rpow_eq_zero_iff_of_nonneg
-/
theorem isBigO_atTop_natCast_rpow_of_tendsto_div_rpow {𝕜 : Type*} [RCLike 𝕜] {g : Nat -> 𝕜}
    {a : 𝕜} {r : Real} (hlim : Tendsto (fun n => g n / (n ^ r : Real)) atTop (𝓝 a)) :
    g =O[atTop] fun n => (n : Real) ^ r := by
  refine (isBigO_of_div_tendsto_nhds ?_ ‖a‖ ?_).of_norm_left
  · filter_upwards [eventually_ne_atTop 0] with _ h
    simp [Real.rpow_eq_zero_iff_of_nonneg, h]
  · exact hlim.norm.congr fun n => by simp [abs_of_nonneg, show 0 <= (n : Real) ^ r by positivity]

variable {E : Type*} [SeminormedRing E] (a b c : Real)

/--
theorem `IsBigO.mul_atTop_rpow_of_isBigO_rpow` / 定理 `IsBigO.mul_atTop_rpow_of_isBigO_rpow`

English:
theorem IsBigO.mul_atTop_rpow_of_isBigO_rpow
  statement: {f g : Real -> E}
  proof: by
  refine (hf.mul hg).trans (Eventually.isBigO ?_)
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [← Real.rpow_add (zero_lt_one.trans_le ht)]; rw [Real.norm_of_nonneg (Real.rpow_nonneg
    (zero_le_one.trans ht) (a + b))]
  exact Real.rpow_le_rpow_of_exponent_le ht h

中文:
定理 IsBigO.mul_atTop_rpow_of_isBigO_rpow
  结论: {f g : 实数 -> E}
  证明: by
  refine (hf.mul hg).trans (Eventually.isBigO ?_)
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [← Real.rpow_add (zero_lt_one.trans_le ht)]; rw [Real.norm_of_nonneg (Real.rpow_nonneg
    (zero_le_one.trans ht) (a + b))]
  exact Real.rpow_le_rpow_of_exponent_le ht h

Depends on / 依赖: Eventually, Eventually.isBigO, Real.norm_of_nonneg, Real.rpow_add, Real.rpow_le_rpow_of_exponent_le, Real.rpow_nonneg, eventually_ge_atTop, filter_upwards, hf.mul, isBigO, norm_of_nonneg, rpow_add, rpow_le_rpow_of_exponent_le, rpow_nonneg, trans_le, zero_le_one, zero_le_one.trans, zero_lt_one, zero_lt_one.trans_le
-/
theorem IsBigO.mul_atTop_rpow_of_isBigO_rpow {f g : Real -> E}
    (hf : f =O[atTop] fun t => (t : Real) ^ a) (hg : g =O[atTop] fun t => (t : Real) ^ b)
    (h : a + b <= c) :
    (f * g) =O[atTop] fun t => (t : Real) ^ c := by
  refine (hf.mul hg).trans (Eventually.isBigO ?_)
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [← Real.rpow_add (zero_lt_one.trans_le ht)]; rw [Real.norm_of_nonneg (Real.rpow_nonneg
    (zero_le_one.trans ht) (a + b))]
  exact Real.rpow_le_rpow_of_exponent_le ht h

/--
theorem `IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow` / 定理 `IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow`

English:
theorem IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
  statement: {f g : Nat -> E}
  proof: by
  refine (hf.mul hg).trans (Eventually.isBigO ?_)
  filter_upwards [eventually_ge_atTop 1] with t ht
  replace ht : 1 <= (t : Real) := Nat.one_le_cast.mpr ht
  rw [← Real.rpow_add (zero_lt_one.trans_le ht)]; rw [Real.norm_of_nonneg (Real.rpow_nonneg
    (zero_le_one.trans ht) (a + b))]
  exact Re

中文:
定理 IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
  结论: {f g : 自然数 -> E}
  证明: by
  refine (hf.mul hg).trans (Eventually.isBigO ?_)
  filter_upwards [eventually_ge_atTop 1] with t ht
  replace ht : 1 <= (t : Real) := Nat.one_le_cast.mpr ht
  rw [← Real.rpow_add (zero_lt_one.trans_le ht)]; rw [Real.norm_of_nonneg (Real.rpow_nonneg
    (zero_le_one.trans ht) (a + b))]
  exact Re

Depends on / 依赖: Eventually, Eventually.isBigO, Nat.one_le_cast.mpr, Real.norm_of_nonneg, Real.rpow_add, Real.rpow_le_rpow_of_exponent_le, Real.rpow_nonneg, eventually_ge_atTop, filter_upwards, hf.mul, isBigO, norm_of_nonneg, one_le_cast, replace, rpow_add, rpow_le_rpow_of_exponent_le, rpow_nonneg, trans_le, zero_le_one, zero_le_one.trans
-/
theorem IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow {f g : Nat -> E}
    (hf : f =O[atTop] fun n => (n : Real) ^ a) (hg : g =O[atTop] fun n => (n : Real) ^ b)
    (h : a + b <= c) :
    (f * g) =O[atTop] fun n => (n : Real) ^ c := by
  refine (hf.mul hg).trans (Eventually.isBigO ?_)
  filter_upwards [eventually_ge_atTop 1] with t ht
  replace ht : 1 <= (t : Real) := Nat.one_le_cast.mpr ht
  rw [← Real.rpow_add (zero_lt_one.trans_le ht)]; rw [Real.norm_of_nonneg (Real.rpow_nonneg
    (zero_le_one.trans ht) (a + b))]
  exact Real.rpow_le_rpow_of_exponent_le ht h

/--
theorem `IsBigO.rpow_rpow_nhdsGE_zero_of_le_of_imp` / 定理 `IsBigO.rpow_rpow_nhdsGE_zero_of_le_of_imp`

English:
theorem IsBigO.rpow_rpow_nhdsGE_zero_of_le_of_imp
  given: {a b : Real} (h : a <= b) (himp : b = 0 -> a = 0)
  proof: .of_bound' mem_of_superset (Icc_mem_nhdsGE one_pos) fun x hx => by
    simpa [Real.abs_rpow_of_nonneg hx.1, abs_of_nonneg hx.1]
     using Real.rpow_le_rpow_of_exponent_ge_of_imp hx.1 hx.2 h fun _ => himp

中文:
定理 IsBigO.rpow_rpow_nhdsGE_zero_of_le_of_imp
  条件: {a b : 实数} (h : a <= b) (himp : b = 0 -> a = 0)
  证明: .of_bound' mem_of_superset (Icc_mem_nhdsGE one_pos) fun x hx => by
    simpa [Real.abs_rpow_of_nonneg hx.1, abs_of_nonneg hx.1]
     using Real.rpow_le_rpow_of_exponent_ge_of_imp hx.1 hx.2 h fun _ => himp

Depends on / 依赖: Icc_mem_nhdsGE, Real.abs_rpow_of_nonneg, Real.rpow_le_rpow_of_exponent_ge_of_imp, abs_of_nonneg, abs_rpow_of_nonneg, mem_of_superset, of_bound, one_pos, rpow_le_rpow_of_exponent_ge_of_imp
-/
theorem IsBigO.rpow_rpow_nhdsGE_zero_of_le_of_imp {a b : Real} (h : a <= b) (himp : b = 0 -> a = 0) :
    (· ^ b : Real -> Real) =O[𝓝[>=] 0] (· ^ a) :=
.of_bound' mem_of_superset (Icc_mem_nhdsGE one_pos) fun x hx => by
    simpa [Real.abs_rpow_of_nonneg hx.1, abs_of_nonneg hx.1]
     using Real.rpow_le_rpow_of_exponent_ge_of_imp hx.1 hx.2 h fun _ => himp

/--
theorem `IsBigO.rpow_rpow_nhdsGE_zero_of_le` / 定理 `IsBigO.rpow_rpow_nhdsGE_zero_of_le`

English:
theorem IsBigO.rpow_rpow_nhdsGE_zero_of_le
  given: {a b : Real} (h : a <= b) (hb : b != 0)
  proof: .rpow_rpow_nhdsGE_zero_of_le_of_imp h (absurd · hb)

中文:
定理 IsBigO.rpow_rpow_nhdsGE_zero_of_le
  条件: {a b : 实数} (h : a <= b) (hb : b != 0)
  证明: .rpow_rpow_nhdsGE_zero_of_le_of_imp h (absurd · hb)

Depends on / 依赖: absurd, rpow_rpow_nhdsGE_zero_of_le_of_imp
-/
theorem IsBigO.rpow_rpow_nhdsGE_zero_of_le {a b : Real} (h : a <= b) (hb : b != 0) :
    (· ^ b : Real -> Real) =O[𝓝[>=] 0] (· ^ a) :=
  .rpow_rpow_nhdsGE_zero_of_le_of_imp h (absurd · hb)

/--
theorem `IsBigO.id_rpow_of_le_one` / 定理 `IsBigO.id_rpow_of_le_one`

English:
theorem IsBigO.id_rpow_of_le_one
  given: {a : Real} (ha : a <= 1)
  proof: by
  simpa using! rpow_rpow_nhdsGE_zero_of_le ha (by simp)

中文:
定理 IsBigO.id_rpow_of_le_one
  条件: {a : 实数} (ha : a <= 1)
  证明: by
  simpa using! rpow_rpow_nhdsGE_zero_of_le ha (by simp)

Depends on / 依赖: rpow_rpow_nhdsGE_zero_of_le
-/
theorem IsBigO.id_rpow_of_le_one {a : Real} (ha : a <= 1) :
    (id : Real -> Real) =O[𝓝[>=] 0] (· ^ a) := by
  simpa using! rpow_rpow_nhdsGE_zero_of_le ha (by simp)

end Asymptotics

open Asymptotics

/--
theorem `isLittleO_rpow_exp_pos_mul_atTop` / 定理 `isLittleO_rpow_exp_pos_mul_atTop`

English:
theorem isLittleO_rpow_exp_pos_mul_atTop
  given: (s : Real) {b : Real} (hb : 0 < b)
  proof: isLittleO_of_tendsto (fun _ h => absurd h (exp_pos _).ne') by
    simpa only [div_eq_mul_inv, exp_neg, neg_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s b hb

中文:
定理 isLittleO_rpow_exp_pos_mul_atTop
  条件: (s : 实数) {b : 实数} (hb : 0 < b)
  证明: isLittleO_of_tendsto (fun _ h => absurd h (exp_pos _).ne') by
    simpa only [div_eq_mul_inv, exp_neg, neg_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s b hb

Depends on / 依赖: absurd, div_eq_mul_inv, exp_neg, exp_pos, isLittleO_of_tendsto, neg_mul, tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
-/
theorem isLittleO_rpow_exp_pos_mul_atTop (s : Real) {b : Real} (hb : 0 < b) :
    (fun x : Real => x ^ s) =o[atTop] fun x => exp (b * x) :=
isLittleO_of_tendsto (fun _ h => absurd h (exp_pos _).ne') by
    simpa only [div_eq_mul_inv, exp_neg, neg_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s b hb

/--
theorem `isLittleO_zpow_exp_pos_mul_atTop` / 定理 `isLittleO_zpow_exp_pos_mul_atTop`

English:
theorem isLittleO_zpow_exp_pos_mul_atTop
  given: (k : Int) {b : Real} (hb : 0 < b)
  proof: by
  simpa only [Real.rpow_intCast] using isLittleO_rpow_exp_pos_mul_atTop k hb

中文:
定理 isLittleO_zpow_exp_pos_mul_atTop
  条件: (k : 整数) {b : 实数} (hb : 0 < b)
  证明: by
  simpa only [Real.rpow_intCast] using isLittleO_rpow_exp_pos_mul_atTop k hb

Depends on / 依赖: Real.rpow_intCast, isLittleO_rpow_exp_pos_mul_atTop, rpow_intCast
-/
theorem isLittleO_zpow_exp_pos_mul_atTop (k : Int) {b : Real} (hb : 0 < b) :
    (fun x : Real => x ^ k) =o[atTop] fun x => exp (b * x) := by
  simpa only [Real.rpow_intCast] using isLittleO_rpow_exp_pos_mul_atTop k hb

/--
theorem `isLittleO_pow_exp_pos_mul_atTop` / 定理 `isLittleO_pow_exp_pos_mul_atTop`

English:
theorem isLittleO_pow_exp_pos_mul_atTop
  given: (k : Nat) {b : Real} (hb : 0 < b)
  proof: by
  simpa using isLittleO_zpow_exp_pos_mul_atTop k hb

中文:
定理 isLittleO_pow_exp_pos_mul_atTop
  条件: (k : 自然数) {b : 实数} (hb : 0 < b)
  证明: by
  simpa using isLittleO_zpow_exp_pos_mul_atTop k hb

Depends on / 依赖: isLittleO_zpow_exp_pos_mul_atTop
-/
theorem isLittleO_pow_exp_pos_mul_atTop (k : Nat) {b : Real} (hb : 0 < b) :
    (fun x : Real => x ^ k) =o[atTop] fun x => exp (b * x) := by
  simpa using isLittleO_zpow_exp_pos_mul_atTop k hb

/--
theorem `isLittleO_rpow_exp_atTop` / 定理 `isLittleO_rpow_exp_atTop`

English:
theorem isLittleO_rpow_exp_atTop
  given: (s : Real)
  statement: (fun x : Real => x ^ s) =o[atTop] exp
  proof: by
  simpa only [one_mul] using isLittleO_rpow_exp_pos_mul_atTop s one_pos

中文:
定理 isLittleO_rpow_exp_atTop
  条件: (s : 实数)
  结论: (fun x : 实数 => x ^ s) =o[atTop] exp
  证明: by
  simpa only [one_mul] using isLittleO_rpow_exp_pos_mul_atTop s one_pos

Depends on / 依赖: isLittleO_rpow_exp_pos_mul_atTop, one_mul, one_pos
-/
theorem isLittleO_rpow_exp_atTop (s : Real) : (fun x : Real => x ^ s) =o[atTop] exp := by
  simpa only [one_mul] using isLittleO_rpow_exp_pos_mul_atTop s one_pos

/--
theorem `isLittleO_exp_neg_mul_rpow_atTop` / 定理 `isLittleO_exp_neg_mul_rpow_atTop`

English:
theorem isLittleO_exp_neg_mul_rpow_atTop
  given: {a : Real} (ha : 0 < a) (b : Real)
  proof: by
  apply isLittleO_of_tendsto'
  · refine (eventually_gt_atTop 0).mono fun t ht h => ?_
    rw [rpow_eq_zero_iff_of_nonneg ht.le] at h
    exact (ht.ne' h.1).elim
  · refine (tendsto_exp_mul_div_rpow_atTop (-b) a ha).inv_tendsto_atTop.congr' ?_
    refine (eventually_ge_atTop 0).mono fun t ht => ?

中文:
定理 isLittleO_exp_neg_mul_rpow_atTop
  条件: {a : 实数} (ha : 0 < a) (b : 实数)
  证明: by
  apply isLittleO_of_tendsto'
  · refine (eventually_gt_atTop 0).mono fun t ht h => ?_
    rw [rpow_eq_zero_iff_of_nonneg ht.le] at h
    exact (ht.ne' h.1).elim
  · refine (tendsto_exp_mul_div_rpow_atTop (-b) a ha).inv_tendsto_atTop.congr' ?_
    refine (eventually_ge_atTop 0).mono fun t ht => ?

Depends on / 依赖: Real.exp_neg, eventually_ge_atTop, eventually_gt_atTop, exp_neg, ht.le, ht.ne, inv_tendsto_atTop, inv_tendsto_atTop.congr, isLittleO_of_tendsto, rpow_eq_zero_iff_of_nonneg, rpow_neg, tendsto_exp_mul_div_rpow_atTop
-/
theorem isLittleO_exp_neg_mul_rpow_atTop {a : Real} (ha : 0 < a) (b : Real) :
    IsLittleO atTop (fun x : Real => exp (-a * x)) fun x : Real => x ^ b := by
  apply isLittleO_of_tendsto'
  · refine (eventually_gt_atTop 0).mono fun t ht h => ?_
    rw [rpow_eq_zero_iff_of_nonneg ht.le] at h
    exact (ht.ne' h.1).elim
  · refine (tendsto_exp_mul_div_rpow_atTop (-b) a ha).inv_tendsto_atTop.congr' ?_
    refine (eventually_ge_atTop 0).mono fun t ht => ?_
    simp [field, Real.exp_neg, rpow_neg ht]

/--
theorem `isLittleO_exp_mul_rpow_of_lt` / 定理 `isLittleO_exp_mul_rpow_of_lt`

English:
theorem isLittleO_exp_mul_rpow_of_lt
  given: (k : Real) {a b : Real} (ha' : a < b)
  proof: by
  refine (isLittleO_of_tendsto (fun _ h => (Real.exp_ne_zero _ h).elim) ?_)
  simp_rw [← div_mul_eq_mul_div₀, ← Real.exp_sub, ← sub_mul, ← neg_sub b a,
    mul_comm _ (_ ^ k)]
  exact tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ (sub_pos.mpr ha')

中文:
定理 isLittleO_exp_mul_rpow_of_lt
  条件: (k : 实数) {a b : 实数} (ha' : a < b)
  证明: by
  refine (isLittleO_of_tendsto (fun _ h => (Real.exp_ne_zero _ h).elim) ?_)
  simp_rw [← div_mul_eq_mul_div₀, ← Real.exp_sub, ← sub_mul, ← neg_sub b a,
    mul_comm _ (_ ^ k)]
  exact tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ (sub_pos.mpr ha')

Depends on / 依赖: Real.exp_ne_zero, Real.exp_sub, exp_ne_zero, exp_sub, isLittleO_of_tendsto, mul_comm, neg_sub, simp_rw, sub_mul, sub_pos, sub_pos.mpr, tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
-/
theorem isLittleO_exp_mul_rpow_of_lt (k : Real) {a b : Real} (ha' : a < b) :
    (fun t => Real.exp (a * t) * t ^ k) =o[atTop] fun t => Real.exp (b * t) := by
  refine (isLittleO_of_tendsto (fun _ h => (Real.exp_ne_zero _ h).elim) ?_)
  simp_rw [← div_mul_eq_mul_div₀, ← Real.exp_sub, ← sub_mul, ← neg_sub b a,
    mul_comm _ (_ ^ k)]
  exact tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ (sub_pos.mpr ha')

/--
theorem `isLittleO_log_rpow_atTop` / 定理 `isLittleO_log_rpow_atTop`

English:
theorem isLittleO_log_rpow_atTop
  given: {r : Real} (hr : 0 < r)
  statement: log =o[atTop] fun x => x ^ r
  proof: calc
    log =O[atTop] fun x => r * log x := isBigO_self_const_mul hr.ne' _ _
    _ =ᶠ[atTop] fun x => log (x ^ r) :=
      ((eventually_gt_atTop 0).mono fun _ hx => (log_rpow hx _).symm)
    _ =o[atTop] fun x => x ^ r := isLittleO_log_id_atTop.comp_tendsto (tendsto_rpow_atTop hr)

中文:
定理 isLittleO_log_rpow_atTop
  条件: {r : 实数} (hr : 0 < r)
  结论: log =o[atTop] fun x => x ^ r
  证明: calc
    log =O[atTop] fun x => r * log x := isBigO_self_const_mul hr.ne' _ _
    _ =ᶠ[atTop] fun x => log (x ^ r) :=
      ((eventually_gt_atTop 0).mono fun _ hx => (log_rpow hx _).symm)
    _ =o[atTop] fun x => x ^ r := isLittleO_log_id_atTop.comp_tendsto (tendsto_rpow_atTop hr)

Depends on / 依赖: comp_tendsto, eventually_gt_atTop, hr.ne, isBigO_self_const_mul, isLittleO_log_id_atTop, isLittleO_log_id_atTop.comp_tendsto, log_rpow, tendsto_rpow_atTop
-/
theorem isLittleO_log_rpow_atTop {r : Real} (hr : 0 < r) : log =o[atTop] fun x => x ^ r :=
  calc
    log =O[atTop] fun x => r * log x := isBigO_self_const_mul hr.ne' _ _
    _ =ᶠ[atTop] fun x => log (x ^ r) :=
      ((eventually_gt_atTop 0).mono fun _ hx => (log_rpow hx _).symm)
    _ =o[atTop] fun x => x ^ r := isLittleO_log_id_atTop.comp_tendsto (tendsto_rpow_atTop hr)

/--
theorem `isLittleO_log_rpow_rpow_atTop` / 定理 `isLittleO_log_rpow_rpow_atTop`

English:
theorem isLittleO_log_rpow_rpow_atTop
  given: {s : Real} (r : Real) (hs : 0 < s)
  proof: let r' := max r 1
have hr : 0 < r' := lt_max_iff.2 Or.inr one_pos
  have H : 0 < s / r' := div_pos hs hr
  calc
    (fun x => log x ^ r) =O[atTop] fun x => log x ^ r' :=
.of_norm_eventuallyLE by
        filter_upwards [tendsto_log_atTop.eventually_ge_atTop 1] with x hx
        rw [Real.norm_of_nonne

中文:
定理 isLittleO_log_rpow_rpow_atTop
  条件: {s : 实数} (r : 实数) (hs : 0 < s)
  证明: let r' := max r 1
have hr : 0 < r' := lt_max_iff.2 Or.inr one_pos
  have H : 0 < s / r' := div_pos hs hr
  calc
    (fun x => log x ^ r) =O[atTop] fun x => log x ^ r' :=
.of_norm_eventuallyLE by
        filter_upwards [tendsto_log_atTop.eventually_ge_atTop 1] with x hx
        rw [Real.norm_of_nonne

Depends on / 依赖: Or.inr, Real.norm_of_nonneg, _root_, _root_.tendsto_rpow_atTop, div_pos, eventually, eventually_ge_atTop, filter_upwards, isLittleO_log_rpow_atTop, le_max_left, lt_max_iff, norm_of_nonneg, of_norm_eventuallyLE, one_pos, tendsto_log_atTop, tendsto_log_atTop.eventually_ge_atTop, tendsto_rpow_atTop
-/
theorem isLittleO_log_rpow_rpow_atTop {s : Real} (r : Real) (hs : 0 < s) :
    (fun x => log x ^ r) =o[atTop] fun x => x ^ s :=
  let r' := max r 1
have hr : 0 < r' := lt_max_iff.2 Or.inr one_pos
  have H : 0 < s / r' := div_pos hs hr
  calc
    (fun x => log x ^ r) =O[atTop] fun x => log x ^ r' :=
.of_norm_eventuallyLE by
        filter_upwards [tendsto_log_atTop.eventually_ge_atTop 1] with x hx
        rw [Real.norm_of_nonneg (by positivity)]
        gcongr
        exact le_max_left _ _
    _ =o[atTop] fun x => (x ^ (s / r')) ^ r' :=
      ((isLittleO_log_rpow_atTop H).rpow hr <|
(_root_.tendsto_rpow_atTop H).eventually eventually_ge_atTop 0)
    _ =ᶠ[atTop] fun x => x ^ s :=
      (eventually_ge_atTop 0).mono fun x hx => by simp only [← rpow_mul hx, div_mul_cancel₀ _ hr.ne']

/--
theorem `isLittleO_abs_log_rpow_rpow_nhdsGT_zero` / 定理 `isLittleO_abs_log_rpow_rpow_nhdsGT_zero`

English:
theorem isLittleO_abs_log_rpow_rpow_nhdsGT_zero
  given: {s : Real} (r : Real) (hs : s < 0)
  proof: ((isLittleO_log_rpow_rpow_atTop r (neg_pos.2 hs)).comp_tendsto tendsto_inv_nhdsGT_zero).congr'
    (mem_of_superset (Icc_mem_nhdsGT one_pos) fun x hx => by
      simp [abs_of_nonpos, log_nonpos hx.1 hx.2])
    (eventually_mem_nhdsWithin.mono fun x hx => by
      rw [Function.comp_apply]; rw [inv_rpo

中文:
定理 isLittleO_abs_log_rpow_rpow_nhdsGT_zero
  条件: {s : 实数} (r : 实数) (hs : s < 0)
  证明: ((isLittleO_log_rpow_rpow_atTop r (neg_pos.2 hs)).comp_tendsto tendsto_inv_nhdsGT_zero).congr'
    (mem_of_superset (Icc_mem_nhdsGT one_pos) fun x hx => by
      simp [abs_of_nonpos, log_nonpos hx.1 hx.2])
    (eventually_mem_nhdsWithin.mono fun x hx => by
      rw [Function.comp_apply]; rw [inv_rpo

Depends on / 依赖: Function, Function.comp_apply, Icc_mem_nhdsGT, abs_of_nonpos, comp_apply, comp_tendsto, eventually_mem_nhdsWithin, eventually_mem_nhdsWithin.mono, hx.out.le, inv_inv, inv_rpow, isLittleO_log_rpow_rpow_atTop, log_nonpos, mem_of_superset, neg_pos, one_pos, rpow_neg, tendsto_inv_nhdsGT_zero
-/
theorem isLittleO_abs_log_rpow_rpow_nhdsGT_zero {s : Real} (r : Real) (hs : s < 0) :
    (fun x => |log x| ^ r) =o[𝓝[>] 0] fun x => x ^ s :=
  ((isLittleO_log_rpow_rpow_atTop r (neg_pos.2 hs)).comp_tendsto tendsto_inv_nhdsGT_zero).congr'
    (mem_of_superset (Icc_mem_nhdsGT one_pos) fun x hx => by
      simp [abs_of_nonpos, log_nonpos hx.1 hx.2])
    (eventually_mem_nhdsWithin.mono fun x hx => by
      rw [Function.comp_apply]; rw [inv_rpow hx.out.le]; rw [rpow_neg hx.out.le]; rw [inv_inv])

/--
theorem `isLittleO_log_rpow_nhdsGT_zero` / 定理 `isLittleO_log_rpow_nhdsGT_zero`

English:
theorem isLittleO_log_rpow_nhdsGT_zero
  given: {r : Real} (hr : r < 0)
  statement: log =o[𝓝[>] 0] fun x => x ^ r
  proof: (isLittleO_abs_log_rpow_rpow_nhdsGT_zero 1 hr).neg_left.congr'
    (mem_of_superset (Icc_mem_nhdsGT one_pos) fun x hx => by
      simp [abs_of_nonpos (log_nonpos hx.1 hx.2)])
    .rfl

中文:
定理 isLittleO_log_rpow_nhdsGT_zero
  条件: {r : 实数} (hr : r < 0)
  结论: log =o[𝓝[>] 0] fun x => x ^ r
  证明: (isLittleO_abs_log_rpow_rpow_nhdsGT_zero 1 hr).neg_left.congr'
    (mem_of_superset (Icc_mem_nhdsGT one_pos) fun x hx => by
      simp [abs_of_nonpos (log_nonpos hx.1 hx.2)])
    .rfl

Depends on / 依赖: Icc_mem_nhdsGT, abs_of_nonpos, isLittleO_abs_log_rpow_rpow_nhdsGT_zero, log_nonpos, mem_of_superset, neg_left, neg_left.congr, one_pos
-/
theorem isLittleO_log_rpow_nhdsGT_zero {r : Real} (hr : r < 0) : log =o[𝓝[>] 0] fun x => x ^ r :=
  (isLittleO_abs_log_rpow_rpow_nhdsGT_zero 1 hr).neg_left.congr'
    (mem_of_superset (Icc_mem_nhdsGT one_pos) fun x hx => by
      simp [abs_of_nonpos (log_nonpos hx.1 hx.2)])
    .rfl

/--
theorem `tendsto_log_div_rpow_nhdsGT_zero` / 定理 `tendsto_log_div_rpow_nhdsGT_zero`

English:
theorem tendsto_log_div_rpow_nhdsGT_zero
  given: {r : Real} (hr : r < 0)
  proof: (isLittleO_log_rpow_nhdsGT_zero hr).tendsto_div_nhds_zero

中文:
定理 tendsto_log_div_rpow_nhdsGT_zero
  条件: {r : 实数} (hr : r < 0)
  证明: (isLittleO_log_rpow_nhdsGT_zero hr).tendsto_div_nhds_zero

Depends on / 依赖: isLittleO_log_rpow_nhdsGT_zero, tendsto_div_nhds_zero
-/
theorem tendsto_log_div_rpow_nhdsGT_zero {r : Real} (hr : r < 0) :
    Tendsto (fun x => log x / x ^ r) (𝓝[>] 0) (𝓝 0) :=
  (isLittleO_log_rpow_nhdsGT_zero hr).tendsto_div_nhds_zero

/--
theorem `tendsto_log_mul_rpow_nhdsGT_zero` / 定理 `tendsto_log_mul_rpow_nhdsGT_zero`

English:
theorem tendsto_log_mul_rpow_nhdsGT_zero
  given: {r : Real} (hr : 0 < r)
  proof: (tendsto_log_div_rpow_nhdsGT_zero <| neg_lt_zero.2 hr).congr'
    eventually_mem_nhdsWithin.mono fun x hx => by rw [rpow_neg hx.out.le, div_inv_eq_mul]

中文:
定理 tendsto_log_mul_rpow_nhdsGT_zero
  条件: {r : 实数} (hr : 0 < r)
  证明: (tendsto_log_div_rpow_nhdsGT_zero <| neg_lt_zero.2 hr).congr'
    eventually_mem_nhdsWithin.mono fun x hx => by rw [rpow_neg hx.out.le, div_inv_eq_mul]

Depends on / 依赖: div_inv_eq_mul, eventually_mem_nhdsWithin, eventually_mem_nhdsWithin.mono, hx.out.le, neg_lt_zero, rpow_neg, tendsto_log_div_rpow_nhdsGT_zero
-/
theorem tendsto_log_mul_rpow_nhdsGT_zero {r : Real} (hr : 0 < r) :
    Tendsto (fun x => log x * x ^ r) (𝓝[>] 0) (𝓝 0) :=
(tendsto_log_div_rpow_nhdsGT_zero <| neg_lt_zero.2 hr).congr'
    eventually_mem_nhdsWithin.mono fun x hx => by rw [rpow_neg hx.out.le, div_inv_eq_mul]

/--
lemma `tendsto_log_mul_self_nhdsLT_zero` / 引理 `tendsto_log_mul_self_nhdsLT_zero`

English:
lemma tendsto_log_mul_self_nhdsLT_zero
  statement: Filter.Tendsto (fun x => log x * x) (𝓝[<] 0) (𝓝 0)
  proof: by
  have h := tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  simp only [Real.rpow_one] at h
  have h_eq : forall x in Set.Iio 0, (-(fun x => log x * x) ∘ (fun x => |x|)) x = log x * x := by
    simp only [Set.mem_Iio, Pi.neg_apply, Function.comp_apply, log_abs]
    intro x hx
    simp only [abs_of_

中文:
引理 tendsto_log_mul_self_nhdsLT_zero
  结论: 滤子.收敛 (fun x => log x * x) (𝓝[<] 0) (𝓝 0)
  证明: by
  have h := tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  simp only [Real.rpow_one] at h
  have h_eq : forall x in Set.Iio 0, (-(fun x => log x * x) ∘ (fun x => |x|)) x = log x * x := by
    simp only [Set.mem_Iio, Pi.neg_apply, Function.comp_apply, log_abs]
    intro x hx
    simp only [abs_of_

Depends on / 依赖: Function, Function.comp_apply, Pi.neg_apply, Real.rpow_one, Set.Iio, Set.mem_Iio, abs_of_nonpos, comp_apply, h.comp, h_eq, hx.le, log_abs, mem_Iio, mono_left, mul_neg, neg_apply, neg_neg, neg_zero, nhdsWithin_mono, nth_rewrite
-/
lemma tendsto_log_mul_self_nhdsLT_zero : Filter.Tendsto (fun x => log x * x) (𝓝[<] 0) (𝓝 0) := by
  have h := tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  simp only [Real.rpow_one] at h
  have h_eq : forall x in Set.Iio 0, (-(fun x => log x * x) ∘ (fun x => |x|)) x = log x * x := by
    simp only [Set.mem_Iio, Pi.neg_apply, Function.comp_apply, log_abs]
    intro x hx
    simp only [abs_of_nonpos hx.le, mul_neg, neg_neg]
  refine tendsto_nhdsWithin_congr h_eq ?_
  nth_rewrite 3 [← neg_zero]
  refine (h.comp (tendsto_abs_nhdsNE_zero.mono_left ?_)).neg
  refine nhdsWithin_mono 0 (fun x hx => ?_)
  push _ in _ at hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hx.ne, not_false_eq_true]
