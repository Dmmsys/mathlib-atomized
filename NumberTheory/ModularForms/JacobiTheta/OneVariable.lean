/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-! # Jacobi's theta function

This file defines the one-variable Jacobi theta function

$$\theta(\tau) = \sum_{n \in \mathbb{Z}} \exp (i \pi n ^ 2 \tau),$$

and proves the modular transformation properties `θ (τ + 2) = θ τ` and
`θ (-1 / τ) = (-I * τ) ^ (1 / 2) * θ τ`, using Poisson's summation formula for the latter. We also
show that `θ` is differentiable on `ℍ`, and `θ(τ) - 1` has exponential decay as `im τ → ∞`.
-/

@[expose] public section

open Complex Real Asymptotics Filter Topology

open scoped Real UpperHalfPlane

/--
Definition of `jacobiTheta` / `jacobiTheta` 的定义

English:
definition jacobiTheta
  signature: (τ : Complex)
  body: ∑' n : Int, cexp (π * I * (n : Complex) ^ 2 * τ)

中文:
定义 jacobiTheta
  签名: (τ : Complex)
  定义体: ∑' n : Int, cexp (π * I * (n : Complex) ^ 2 * τ)
-/
noncomputable def jacobiTheta (τ : Complex) : Complex := ∑' n : Int, cexp (π * I * (n : Complex) ^ 2 * τ)

/--
lemma `jacobiTheta_eq_jacobiTheta₂` / 引理 `jacobiTheta_eq_jacobiTheta₂`

English:
lemma jacobiTheta_eq_jacobiTheta₂
  given: (τ : Complex)
  statement: jacobiTheta τ = jacobiTheta₂ 0 τ
  proof: tsum_congr (by simp [jacobiTheta₂_term])

中文:
引理 jacobiTheta_eq_jacobiTheta₂
  条件: (τ : Complex)
  结论: jacobiTheta τ = jacobiTheta₂ 0 τ
  证明: tsum_congr (by simp [jacobiTheta₂_term])

Depends on / 依赖: tsum_congr
-/
lemma jacobiTheta_eq_jacobiTheta₂ (τ : Complex) : jacobiTheta τ = jacobiTheta₂ 0 τ :=
  tsum_congr (by simp [jacobiTheta₂_term])

/--
theorem `jacobiTheta_two_add` / 定理 `jacobiTheta_two_add`

English:
theorem jacobiTheta_two_add
  given: (τ : Complex)
  statement: jacobiTheta (2 + τ) = jacobiTheta τ
  proof: by
  simp_rw [jacobiTheta_eq_jacobiTheta₂, add_comm, jacobiTheta₂_add_right]

中文:
定理 jacobiTheta_two_add
  条件: (τ : Complex)
  结论: jacobiTheta (2 + τ) = jacobiTheta τ
  证明: by
  simp_rw [jacobiTheta_eq_jacobiTheta₂, add_comm, jacobiTheta₂_add_right]

Depends on / 依赖: add_comm, simp_rw
-/
theorem jacobiTheta_two_add (τ : Complex) : jacobiTheta (2 + τ) = jacobiTheta τ := by
  simp_rw [jacobiTheta_eq_jacobiTheta₂, add_comm, jacobiTheta₂_add_right]

/--
theorem `jacobiTheta_T_sq_smul` / 定理 `jacobiTheta_T_sq_smul`

English:
theorem jacobiTheta_T_sq_smul
  given: (τ : ℍ)
  statement: jacobiTheta (ModularGroup.T ^ 2 • τ :) = jacobiTheta τ
  proof: by
  suffices (ModularGroup.T ^ 2 • τ :) = (2 : Complex) + ↑τ by simp_rw [this, jacobiTheta_two_add]
  have : ModularGroup.T ^ (2 : Nat) = ModularGroup.T ^ (2 : Int) := rfl
  simp_rw [this, UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]
  norm_cast

中文:
定理 jacobiTheta_T_sq_smul
  条件: (τ : ℍ)
  结论: jacobiTheta (ModularGroup.T ^ 2 • τ :) = jacobiTheta τ
  证明: by
  suffices (ModularGroup.T ^ 2 • τ :) = (2 : Complex) + ↑τ by simp_rw [this, jacobiTheta_two_add]
  have : ModularGroup.T ^ (2 : Nat) = ModularGroup.T ^ (2 : Int) := rfl
  simp_rw [this, UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]
  norm_cast

Depends on / 依赖: ModularGroup, ModularGroup.T, UpperHalfPlane, UpperHalfPlane.coe_vadd, UpperHalfPlane.modular_T_zpow_smul, coe_vadd, jacobiTheta_two_add, modular_T_zpow_smul, simp_rw
-/
theorem jacobiTheta_T_sq_smul (τ : ℍ) : jacobiTheta (ModularGroup.T ^ 2 • τ :) = jacobiTheta τ := by
  suffices (ModularGroup.T ^ 2 • τ :) = (2 : Complex) + ↑τ by simp_rw [this, jacobiTheta_two_add]
  have : ModularGroup.T ^ (2 : Nat) = ModularGroup.T ^ (2 : Int) := rfl
  simp_rw [this, UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]
  norm_cast

/--
theorem `jacobiTheta_S_smul` / 定理 `jacobiTheta_S_smul`

English:
theorem jacobiTheta_S_smul
  given: (τ : ℍ)
  proof: by
  have h0 : (τ : Complex) != 0 := ne_of_apply_ne im (zero_im.symm ▸ ne_of_gt τ.2)
  have h1 : (-I * τ) ^ (1 / 2 : Complex) != 0 := by
    rw [Ne]; rw [cpow_eq_zero_iff]; rw [not_and_or]
exact Or.inl mul_ne_zero (neg_ne_zero.mpr I_ne_zero) h0
  simp_rw [UpperHalfPlane.modular_S_smul, jacobiTheta_e

中文:
定理 jacobiTheta_S_smul
  条件: (τ : ℍ)
  证明: by
  have h0 : (τ : Complex) != 0 := ne_of_apply_ne im (zero_im.symm ▸ ne_of_gt τ.2)
  have h1 : (-I * τ) ^ (1 / 2 : Complex) != 0 := by
    rw [Ne]; rw [cpow_eq_zero_iff]; rw [not_and_or]
exact Or.inl mul_ne_zero (neg_ne_zero.mpr I_ne_zero) h0
  simp_rw [UpperHalfPlane.modular_S_smul, jacobiTheta_e

Depends on / 依赖: Complex.exp_zero, I_ne_zero, Or.inl, UpperHalfPlane, UpperHalfPlane.modular_S_smul, cpow_eq_zero_iff, div_self, exp_zero, inv_n, modular_S_smul, mul_assoc, mul_ne_zero, mul_one, mul_one_div, mul_zero, ne_of_apply_ne, ne_of_gt, neg_ne_zero, neg_ne_zero.mpr, not_and_or
-/
theorem jacobiTheta_S_smul (τ : ℍ) :
    jacobiTheta ↑(ModularGroup.S • τ) = (-I * τ) ^ (1 / 2 : Complex) * jacobiTheta τ := by
  have h0 : (τ : Complex) != 0 := ne_of_apply_ne im (zero_im.symm ▸ ne_of_gt τ.2)
  have h1 : (-I * τ) ^ (1 / 2 : Complex) != 0 := by
    rw [Ne]; rw [cpow_eq_zero_iff]; rw [not_and_or]
exact Or.inl mul_ne_zero (neg_ne_zero.mpr I_ne_zero) h0
  simp_rw [UpperHalfPlane.modular_S_smul, jacobiTheta_eq_jacobiTheta₂, ← ofReal_zero]
  norm_cast
  simp_rw [jacobiTheta₂_functional_equation 0 τ, zero_pow two_ne_zero, mul_zero, zero_div,
    Complex.exp_zero, mul_one, ← mul_assoc, mul_one_div, div_self h1, one_mul,
    inv_neg, neg_div, one_div]

/--
theorem `norm_exp_mul_sq_le` / 定理 `norm_exp_mul_sq_le`

English:
theorem norm_exp_mul_sq_le
  given: {τ : Complex} (hτ : 0 < τ.im) (n : Int)
  proof: by
  let y := rexp (-π * τ.im)
  have h : y < 1 := exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) hτ)
  refine (le_of_eq ?_).trans (?_ : y ^ n ^ 2 <= _)
  · rw [norm_exp]
    have : (π * I * n ^ 2 * τ : Complex).re = -π * τ.im * (n : Real) ^ 2 := by
      rw [(by push_cast; ring 

中文:
定理 norm_exp_mul_sq_le
  条件: {τ : Complex} (hτ : 0 < τ.im) (n : 整数)
  证明: by
  let y := rexp (-π * τ.im)
  have h : y < 1 := exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) hτ)
  refine (le_of_eq ?_).trans (?_ : y ^ n ^ 2 <= _)
  · rw [norm_exp]
    have : (π * I * n ^ 2 * τ : Complex).re = -π * τ.im * (n : Real) ^ 2 := by
      rw [(by push_cast; ring 

Depends on / 依赖: Int.cast_pow, Int.eq_ofNat_of_zero_le, cast_pow, eq_ofNat_of_zero_le, exp_lt_one_iff, exp_lt_one_iff.mpr, exp_mul, le_of_eq, mul_I_re, mul_neg_of_neg_of_pos, neg_lt_zero, neg_lt_zero.mpr, norm_exp, pi_pos, re_ofReal_mul, rpow_in, sq_nonneg
-/
theorem norm_exp_mul_sq_le {τ : Complex} (hτ : 0 < τ.im) (n : Int) :
    ‖cexp (π * I * (n : Complex) ^ 2 * τ)‖ <= rexp (-π * τ.im) ^ n.natAbs := by
  let y := rexp (-π * τ.im)
  have h : y < 1 := exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) hτ)
  refine (le_of_eq ?_).trans (?_ : y ^ n ^ 2 <= _)
  · rw [norm_exp]
    have : (π * I * n ^ 2 * τ : Complex).re = -π * τ.im * (n : Real) ^ 2 := by
      rw [(by push_cast; ring : (π * I * n ^ 2 * τ : Complex) = (π * n ^ 2 : Real) * (τ * I))]; rw [re_ofReal_mul]; rw [mul_I_re]
      ring
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (sq_nonneg n)
    rw [this]; rw [exp_mul]; rw [← Int.cast_pow]; rw [rpow_intCast]; rw [hm]; rw [zpow_natCast]
  · have : n ^ 2 = (n.natAbs ^ 2 :) := by rw [Nat.cast_pow, Int.natAbs_sq]
    rw [this]; rw [zpow_natCast]
    exact pow_le_pow_of_le_one (exp_pos _).le h.le ((sq n.natAbs).symm ▸ n.natAbs.le_mul_self)

/--
theorem `hasSum_nat_jacobiTheta` / 定理 `hasSum_nat_jacobiTheta`

English:
theorem hasSum_nat_jacobiTheta
  given: {τ : Complex} (hτ : 0 < im τ)
  proof: by
  have := hasSum_jacobiTheta₂_term 0 hτ
  simp_rw [jacobiTheta₂_term, mul_zero, zero_add, ← jacobiTheta_eq_jacobiTheta₂] at this
  have := this.nat_add_neg
  rw [← hasSum_nat_add_iff' 1] at this
  simp_rw [Finset.sum_range_one, Int.cast_neg, Int.cast_natCast, Nat.cast_zero, neg_zero,
    Int.cast

中文:
定理 hasSum_nat_jacobiTheta
  条件: {τ : Complex} (hτ : 0 < im τ)
  证明: by
  have := hasSum_jacobiTheta₂_term 0 hτ
  simp_rw [jacobiTheta₂_term, mul_zero, zero_add, ← jacobiTheta_eq_jacobiTheta₂] at this
  have := this.nat_add_neg
  rw [← hasSum_nat_add_iff' 1] at this
  simp_rw [Finset.sum_range_one, Int.cast_neg, Int.cast_natCast, Nat.cast_zero, neg_zero,
    Int.cast

Depends on / 依赖: Complex.exp_zero, Finset, Finset.sum_range_one, Int.cast_natCast, Int.cast_neg, Int.cast_zero, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_sub_assoc, cast_add, cast_natCast, cast_neg, cast_one, cast_zero, convert, div_c, exp_zero, hasSum_nat_add_iff, mul_two
-/
theorem hasSum_nat_jacobiTheta {τ : Complex} (hτ : 0 < im τ) :
    HasSum (fun n : Nat => cexp (π * I * ((n : Complex) + 1) ^ 2 * τ)) ((jacobiTheta τ - 1) / 2) := by
  have := hasSum_jacobiTheta₂_term 0 hτ
  simp_rw [jacobiTheta₂_term, mul_zero, zero_add, ← jacobiTheta_eq_jacobiTheta₂] at this
  have := this.nat_add_neg
  rw [← hasSum_nat_add_iff' 1] at this
  simp_rw [Finset.sum_range_one, Int.cast_neg, Int.cast_natCast, Nat.cast_zero, neg_zero,
    Int.cast_zero, sq (0 : Complex), mul_zero, zero_mul, neg_sq, ← mul_two,
    Complex.exp_zero, add_sub_assoc, (by norm_num : (1 : Complex) - 1 * 2 = -1), ← sub_eq_add_neg,
    Nat.cast_add, Nat.cast_one] at this
  convert! this.div_const 2 using 1
  simp_rw [mul_div_cancel_right₀ _ (two_ne_zero' Complex)]

/--
theorem `jacobiTheta_eq_tsum_nat` / 定理 `jacobiTheta_eq_tsum_nat`

English:
theorem jacobiTheta_eq_tsum_nat
  given: {τ : Complex} (hτ : 0 < im τ)
  proof: by
  rw [(hasSum_nat_jacobiTheta hτ).tsum_eq]; rw [mul_div_cancel₀ _ (two_ne_zero' Complex)]; rw [← add_sub_assoc]; rw [add_sub_cancel_left]

中文:
定理 jacobiTheta_eq_tsum_nat
  条件: {τ : Complex} (hτ : 0 < im τ)
  证明: by
  rw [(hasSum_nat_jacobiTheta hτ).tsum_eq]; rw [mul_div_cancel₀ _ (two_ne_zero' Complex)]; rw [← add_sub_assoc]; rw [add_sub_cancel_left]

Depends on / 依赖: add_sub_assoc, add_sub_cancel_left, hasSum_nat_jacobiTheta, tsum_eq, two_ne_zero
-/
theorem jacobiTheta_eq_tsum_nat {τ : Complex} (hτ : 0 < im τ) :
    jacobiTheta τ = ↑1 + ↑2 * ∑' n : Nat, cexp (π * I * ((n : Complex) + 1) ^ 2 * τ) := by
  rw [(hasSum_nat_jacobiTheta hτ).tsum_eq]; rw [mul_div_cancel₀ _ (two_ne_zero' Complex)]; rw [← add_sub_assoc]; rw [add_sub_cancel_left]

/--
theorem `norm_jacobiTheta_sub_one_le` / 定理 `norm_jacobiTheta_sub_one_le`

English:
theorem norm_jacobiTheta_sub_one_le
  given: {τ : Complex} (hτ : 0 < im τ)
  proof: by
  suffices ‖∑' n : Nat, cexp (π * I * ((n : Complex) + 1) ^ 2 * τ)‖ <=
      rexp (-π * τ.im) / (1 - rexp (-π * τ.im)) by
    calc
      ‖jacobiTheta τ - 1‖ = ↑2 * ‖∑' n : Nat, cexp (π * I * ((n : Complex) + 1) ^ 2 * τ)‖ := by
        rw [sub_eq_iff_eq_add'.mpr (jacobiTheta_eq_tsum_nat hτ)]; rw [

中文:
定理 norm_jacobiTheta_sub_one_le
  条件: {τ : Complex} (hτ : 0 < im τ)
  证明: by
  suffices ‖∑' n : Nat, cexp (π * I * ((n : Complex) + 1) ^ 2 * τ)‖ <=
      rexp (-π * τ.im) / (1 - rexp (-π * τ.im)) by
    calc
      ‖jacobiTheta τ - 1‖ = ↑2 * ‖∑' n : Nat, cexp (π * I * ((n : Complex) + 1) ^ 2 * τ)‖ := by
        rw [sub_eq_iff_eq_add'.mpr (jacobiTheta_eq_tsum_nat hτ)]; rw [

Depends on / 依赖: Complex.norm_two, div_mul_comm, jacobiTheta, jacobiTheta_eq_tsum_nat, mul_comm, norm_mul, norm_two, sub_eq_iff_eq_add
-/
theorem norm_jacobiTheta_sub_one_le {τ : Complex} (hτ : 0 < im τ) :
    ‖jacobiTheta τ - 1‖ <= 2 / (1 - rexp (-π * τ.im)) * rexp (-π * τ.im) := by
  suffices ‖∑' n : Nat, cexp (π * I * ((n : Complex) + 1) ^ 2 * τ)‖ <=
      rexp (-π * τ.im) / (1 - rexp (-π * τ.im)) by
    calc
      ‖jacobiTheta τ - 1‖ = ↑2 * ‖∑' n : Nat, cexp (π * I * ((n : Complex) + 1) ^ 2 * τ)‖ := by
        rw [sub_eq_iff_eq_add'.mpr (jacobiTheta_eq_tsum_nat hτ)]; rw [norm_mul]; rw [Complex.norm_two]
      _ <= 2 * (rexp (-π * τ.im) / (1 - rexp (-π * τ.im))) := by gcongr
      _ = 2 / (1 - rexp (-π * τ.im)) * rexp (-π * τ.im) := by rw [div_mul_comm, mul_comm]
  have : forall n : Nat, ‖cexp (π * I * ((n : Complex) + 1) ^ 2 * τ)‖ <= rexp (-π * τ.im) ^ (n + 1) := by
    intro n
    simpa only [Int.cast_add, Int.cast_one] using! norm_exp_mul_sq_le hτ (n + 1)
  have s : HasSum (fun n : Nat =>
      rexp (-π * τ.im) ^ (n + 1)) (rexp (-π * τ.im) / (1 - rexp (-π * τ.im))) := by
    simp_rw [pow_succ', div_eq_mul_inv, hasSum_mul_left_iff (Real.exp_ne_zero _)]
    exact hasSum_geometric_of_lt_one (exp_pos (-π * τ.im)).le
      (exp_lt_one_iff.mpr <| mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) hτ)
  have aux : Summable fun n : Nat => ‖cexp (π * I * ((n : Complex) + 1) ^ 2 * τ)‖ :=
    .of_nonneg_of_le (fun n => norm_nonneg _) this s.summable
  exact (norm_tsum_le_tsum_norm aux).trans ((aux.tsum_mono s.summable this).trans_eq s.tsum_eq)

/--
theorem `isBigO_at_im_infty_jacobiTheta_sub_one` / 定理 `isBigO_at_im_infty_jacobiTheta_sub_one`

English:
theorem isBigO_at_im_infty_jacobiTheta_sub_one
  proof: by
  simp_rw [IsBigO, IsBigOWith, Filter.eventually_comap, Filter.eventually_atTop]
  refine ⟨2 / (1 - rexp (-(π * 1))), 1, fun y hy τ hτ =>
    (norm_jacobiTheta_sub_one_le (hτ.symm ▸ zero_lt_one.trans_le hy : 0 < im τ)).trans ?_⟩
  rw [Real.norm_eq_abs]; rw [Real.abs_exp]; rw [hτ]; rw [neg_mul]
  

中文:
定理 isBigO_at_im_infty_jacobiTheta_sub_one
  证明: by
  simp_rw [IsBigO, IsBigOWith, Filter.eventually_comap, Filter.eventually_atTop]
  refine ⟨2 / (1 - rexp (-(π * 1))), 1, fun y hy τ hτ =>
    (norm_jacobiTheta_sub_one_le (hτ.symm ▸ zero_lt_one.trans_le hy : 0 < im τ)).trans ?_⟩
  rw [Real.norm_eq_abs]; rw [Real.abs_exp]; rw [hτ]; rw [neg_mul]
  

Depends on / 依赖: Filter, Filter.eventually_atTop, Filter.eventually_comap, IsBigO, IsBigOWith, Real.abs_exp, Real.norm_eq_abs, abs_exp, eventually_atTop, eventually_comap, neg_mul, norm_eq_abs, norm_jacobiTheta_sub_one_le, pi_pos, simp_rw, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem isBigO_at_im_infty_jacobiTheta_sub_one :
    (fun τ => jacobiTheta τ - 1) =O[comap im atTop] fun τ => rexp (-π * τ.im) := by
  simp_rw [IsBigO, IsBigOWith, Filter.eventually_comap, Filter.eventually_atTop]
  refine ⟨2 / (1 - rexp (-(π * 1))), 1, fun y hy τ hτ =>
    (norm_jacobiTheta_sub_one_le (hτ.symm ▸ zero_lt_one.trans_le hy : 0 < im τ)).trans ?_⟩
  rw [Real.norm_eq_abs]; rw [Real.abs_exp]; rw [hτ]; rw [neg_mul]
  gcongr
  simp [pi_pos]

/--
theorem `differentiableAt_jacobiTheta` / 定理 `differentiableAt_jacobiTheta`

English:
theorem differentiableAt_jacobiTheta
  given: {τ : Complex} (hτ : 0 < im τ)
  proof: by
  simp_rw [funext jacobiTheta_eq_jacobiTheta₂]
  exact differentiableAt_jacobiTheta₂_snd 0 hτ

中文:
定理 differentiableAt_jacobiTheta
  条件: {τ : Complex} (hτ : 0 < im τ)
  证明: by
  simp_rw [funext jacobiTheta_eq_jacobiTheta₂]
  exact differentiableAt_jacobiTheta₂_snd 0 hτ

Depends on / 依赖: simp_rw
-/
theorem differentiableAt_jacobiTheta {τ : Complex} (hτ : 0 < im τ) :
    DifferentiableAt Complex jacobiTheta τ := by
  simp_rw [funext jacobiTheta_eq_jacobiTheta₂]
  exact differentiableAt_jacobiTheta₂_snd 0 hτ

/--
theorem `continuousAt_jacobiTheta` / 定理 `continuousAt_jacobiTheta`

English:
theorem continuousAt_jacobiTheta
  given: {τ : Complex} (hτ : 0 < im τ)
  statement: ContinuousAt jacobiTheta τ
  proof: (differentiableAt_jacobiTheta hτ).continuousAt

中文:
定理 continuousAt_jacobiTheta
  条件: {τ : Complex} (hτ : 0 < im τ)
  结论: ContinuousAt jacobiTheta τ
  证明: (differentiableAt_jacobiTheta hτ).continuousAt

Depends on / 依赖: continuousAt, differentiableAt_jacobiTheta
-/
theorem continuousAt_jacobiTheta {τ : Complex} (hτ : 0 < im τ) : ContinuousAt jacobiTheta τ :=
  (differentiableAt_jacobiTheta hτ).continuousAt
