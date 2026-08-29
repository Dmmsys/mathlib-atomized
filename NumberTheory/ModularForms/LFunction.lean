/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.ModularForms.Bounds
public import Mathlib.NumberTheory.LSeries.AbstractFuncEq
public import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
public import Mathlib.Analysis.PSeries

/-!
# The `L`-function of a modular form
-/

@[expose] public section

open UpperHalfPlane hiding I
open scoped Real
open Filter Complex MatrixGroups Asymptotics

variable {Γ : Subgroup (GL (Fin 2) Real)} [Γ.IsArithmetic]
  {k : Int} (hk : 0 < k) {F : Type*} [FunLike F ℍ Complex] (f : F) {s : Complex}

local notation "h" => Subgroup.strictWidthInfty

open ConjAct Pointwise in
private local instance :
    Subgroup.IsArithmetic (toConjAct (ModularGroup.S : GL (Fin 2) Real)⁻¹ • Γ) := by
  convert Subgroup.IsArithmetic.conj Γ ↑(ModularGroup.S⁻¹)
  simp only [ModularGroup.S_inv, ← map_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.S]

namespace ModularForm

variable [ModularFormClass F Γ k]

section asymptotics -- private lemmas about aymptotics along `I * ℝ`

/--
lemma `tendsto_ofComplex_I_mul_atTop_atImInfty` / 引理 `tendsto_ofComplex_I_mul_atTop_atImInfty`

English:
lemma tendsto_ofComplex_I_mul_atTop_atImInfty
  proof: by
  rw [atImInfty]; rw [tendsto_comap_iff]
  refine tendsto_id.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [ofComplex_apply_of_im_pos, ht, ← coe_im]

include F k Γ in -- conclusion doesn't explicitly refer these

中文:
引理 tendsto_ofComplex_I_mul_atTop_atImInfty
  证明: by
  rw [atImInfty]; rw [tendsto_comap_iff]
  refine tendsto_id.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [ofComplex_apply_of_im_pos, ht, ← coe_im]

include F k Γ in -- conclusion doesn't explicitly refer these
-/
private lemma tendsto_ofComplex_I_mul_atTop_atImInfty :
    Tendsto (fun t : Real => ofComplex (I * t)) atTop atImInfty := by
  rw [atImInfty]; rw [tendsto_comap_iff]
  refine tendsto_id.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [ofComplex_apply_of_im_pos, ht, ← coe_im]

include F k Γ in -- conclusion doesn't explicitly refer these
/--
lemma `isBigO_comp_ofComplex_I_mul_sub_valueAtInfty` / 引理 `isBigO_comp_ofComplex_I_mul_sub_valueAtInfty`

English:
lemma isBigO_comp_ofComplex_I_mul_sub_valueAtInfty
  given: (r : Real)
  proof: by
  obtain ⟨C, hCpos, hCO⟩ := ModularFormClass.exp_decay_sub_atImInfty' f
  refine (hCO.comp_tendsto tendsto_ofComplex_I_mul_atTop_atImInfty).trans ?_
  refine (EventuallyEq.isBigO ?_).trans (isLittleO_exp_neg_mul_rpow_atTop hCpos r).isBigO
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [ht, ofComplex_apply_of_im_pos, ← coe_im]

中文:
引理 isBigO_comp_ofComplex_I_mul_sub_valueAtInfty
  条件: (r : 实数)
  证明: by
  obtain ⟨C, hCpos, hCO⟩ := ModularFormClass.exp_decay_sub_atImInfty' f
  refine (hCO.comp_tendsto tendsto_ofComplex_I_mul_atTop_atImInfty).trans ?_
  refine (EventuallyEq.isBigO ?_).trans (isLittleO_exp_neg_mul_rpow_atTop hCpos r).isBigO
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [ht, ofComplex_apply_of_im_pos, ← coe_im]
-/
private lemma isBigO_comp_ofComplex_I_mul_sub_valueAtInfty (r : Real) :
    (fun t : Real => f (ofComplex (I * t)) - valueAtInfty f) =O[atTop] (fun t => t ^ r) := by
  obtain ⟨C, hCpos, hCO⟩ := ModularFormClass.exp_decay_sub_atImInfty' f
  refine (hCO.comp_tendsto tendsto_ofComplex_I_mul_atTop_atImInfty).trans ?_
  refine (EventuallyEq.isBigO ?_).trans (isLittleO_exp_neg_mul_rpow_atTop hCpos r).isBigO
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [ht, ofComplex_apply_of_im_pos, ← coe_im]

end asymptotics

/--
Definition of `weakFEPair` / `weakFEPair` 的定义

English:
definition weakFEPair
  signature: : WeakFEPair Complex where
  body: f (ofComplex (I * t))
  g t := translate f ModularGroup.S (ofComplex (I * t))
  k := k
  hk := mod_cast hk
  ε := I ^ k
  hε := zpow_ne_zero _ I_ne_zero
  f₀ := valueAtInfty f
  g₀ := valueAtInfty (translate f ModularGroup.S)
  hf_int := ContinuousOn.locallyIntegrableOn (by fun_prop) measurableSet_Ioi
  hg_int := ContinuousOn.locallyIntegrableOn (by fun_prop) measurableSet_Ioi
  h_feq t (ht : 0 < t) := by
    rw [coe_translate]; rw [slash_def]
    suffices f (ofComplex (I * t⁻¹)) = I ^ k * t ^ k *
        (f ((ModularGroup.S : GL (Fin 2) Real) • ofComplex (I * t)) * ofComplex (I * t) ^ (-k)) by
      simpa [σ, denom]
    rw [ofComplex_apply_of_im_pos (by simpa)]; rw [ofComplex_apply_of_im_pos (by simpa)]; rw [mul_comm (f _)]; rw [← mul_assoc]; rw [← mul_zpow]; rw [zpow_neg]; rw [mul_inv_cancel₀ (zpow_ne_zero _ (by aesop))]
    simp only [one_mul]
    congr 1
    ext
    rw [coe_smul_of_det_pos (by simp)]
    simp [num, denom, div_eq_mul_inv, mul_comm]
  hf_top r := by -- `by exact` to hide use of private lemma in @[expose]'d declaration
    exact isBigO_comp_ofComplex_I_mul_sub_valueAtInfty f r
  hg_top r := by -- `by exact` to hide use of private lemma in @[expose]'d declaration
    exact isBigO_comp_ofComplex_I_mul_sub_valueAtInfty (translate f ModularGroup.S) r

中文:
定义 weakFEPair
  签名: : WeakFEPair 复形 where
  定义体: f (ofComplex (I * t))
  g t := translate f ModularGroup.S (ofComplex (I * t))
  k := k
  hk := mod_cast hk
  ε := I ^ k
  hε := zpow_ne_zero _ I_ne_zero
  f₀ := valueAtInfty f
  g₀ := valueAtInfty (translate f ModularGroup.S)
  hf_int := ContinuousOn.locallyIntegrableOn (by fun_prop) measurableSet_Ioi
  hg_int := ContinuousOn.locallyIntegrableOn (by fun_prop) measurableSet_Ioi
  h_feq t (ht : 0 < t) := by
    rw [coe_translate]; rw [slash_def]
    suffices f (ofComplex (I * t⁻¹)) = I ^ k * t ^ k *
        (f ((ModularGroup.S : GL (Fin 2) Real) • ofComplex (I * t)) * ofComplex (I * t) ^ (-k)) by
      simpa [σ, denom]
    rw [ofComplex_apply_of_im_pos (by simpa)]; rw [ofComplex_apply_of_im_pos (by simpa)]; rw [mul_comm (f _)]; rw [← mul_assoc]; rw [← mul_zpow]; rw [zpow_neg]; rw [mul_inv_cancel₀ (zpow_ne_zero _ (by aesop))]
    simp only [one_mul]
    congr 1
    ext
    rw [coe_smul_of_det_pos (by simp)]
    simp [num, denom, div_eq_mul_inv, mul_comm]
  hf_top r := by -- `by exact` to hide use of private lemma in @[expose]'d declaration
    exact isBigO_comp_ofComplex_I_mul_sub_valueAtInfty f r
  hg_top r := by -- `by exact` to hide use of private lemma in @[expose]'d declaration
    exact isBigO_comp_ofComplex_I_mul_sub_valueAtInfty (translate f ModularGroup.S) r
-/
@[simps] noncomputable def weakFEPair : WeakFEPair Complex where
  f t := f (ofComplex (I * t))
  g t := translate f ModularGroup.S (ofComplex (I * t))
  k := k
  hk := mod_cast hk
  ε := I ^ k
  hε := zpow_ne_zero _ I_ne_zero
  f₀ := valueAtInfty f
  g₀ := valueAtInfty (translate f ModularGroup.S)
  hf_int := ContinuousOn.locallyIntegrableOn (by fun_prop) measurableSet_Ioi
  hg_int := ContinuousOn.locallyIntegrableOn (by fun_prop) measurableSet_Ioi
  h_feq t (ht : 0 < t) := by
    rw [coe_translate]; rw [slash_def]
    suffices f (ofComplex (I * t⁻¹)) = I ^ k * t ^ k *
        (f ((ModularGroup.S : GL (Fin 2) Real) • ofComplex (I * t)) * ofComplex (I * t) ^ (-k)) by
      simpa [σ, denom]
    rw [ofComplex_apply_of_im_pos (by simpa)]; rw [ofComplex_apply_of_im_pos (by simpa)]; rw [mul_comm (f _)]; rw [← mul_assoc]; rw [← mul_zpow]; rw [zpow_neg]; rw [mul_inv_cancel₀ (zpow_ne_zero _ (by aesop))]
    simp only [one_mul]
    congr 1
    ext
    rw [coe_smul_of_det_pos (by simp)]
    simp [num, denom, div_eq_mul_inv, mul_comm]
  hf_top r := by -- `by exact` to hide use of private lemma in @[expose]'d declaration
    exact isBigO_comp_ofComplex_I_mul_sub_valueAtInfty f r
  hg_top r := by -- `by exact` to hide use of private lemma in @[expose]'d declaration
    exact isBigO_comp_ofComplex_I_mul_sub_valueAtInfty (translate f ModularGroup.S) r

/--
Definition of `Λ` / `Λ` 的定义

English:
definition Λ
  signature: : Complex -> Complex
  body: (weakFEPair hk f).Λ

中文:
定义 Λ
  签名: : 复形 -> 复形
  定义体: (weakFEPair hk f).Λ

Depends on / 依赖: weakFEPair
-/
noncomputable def Λ : Complex -> Complex := (weakFEPair hk f).Λ

/--
lemma `hasSum_Λ_of_qExpansion_isBigO` / 引理 `hasSum_Λ_of_qExpansion_isBigO`

English:
lemma hasSum_Λ_of_qExpansion_isBigO
  statement: {r : Real}
  proof: by
  rw [hΛ]
  have hh := Γ.strictWidthInfty_pos
  have hΓ := Γ.strictWidthInfty_mem_strictPeriods
  refine hasSum_mellin_pi_mul₀ (fun _ => by positivity) hpos ?_ ?_
  · -- show `q`-expansion converges to `f` on positive imaginary axis
    intro t (ht : 0 < t)
    have := hasSum_qExpansion f hh hΓ (ofComplex (I * t))
    convert! hasSum_ite_sub_hasSum this 0 using 2 with n
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · simp [hn.ne', Function.Periodic.qParam, ofComplex_apply_eq_ite, ht, ← exp_nat_mul]
        grind [I_sq]
    · simp only [weakFEPair]
      rw [qExpansion_coeff_zero hh]; rw [pow_zero]; rw [mul_one]
      · exact ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ
      · exact SlashInvariantFormClass.periodic_comp_ofComplex f hΓ
  · -- show summability of Dirichlet series
    simp_rw [mul_comm (2 : Real), mul_div_assoc,
      Real.mul_rpow (Nat.cast_nonneg _) (show 0 <= 2 / h Γ by positivity), ← div_div]
    apply Summable.div_const
    apply summable_of_isBigO_nat (Real.summable_nat_rpow.mpr <| show r - s.re < -1 by linarith)
    simp only [Real.rpow_sub' (Nat.cast_nonneg _) (show r - s.re != 0 by linarith)]
    apply IsBigO.mul _ (isBigO_refl _ _)
    simpa using hcoeff.norm_left

中文:
引理 hasSum_Λ_of_qExpansion_isBigO
  结论: {r : 实数}
  证明: by
  rw [hΛ]
  have hh := Γ.strictWidthInfty_pos
  have hΓ := Γ.strictWidthInfty_mem_strictPeriods
  refine hasSum_mellin_pi_mul₀ (fun _ => by positivity) hpos ?_ ?_
  · -- show `q`-expansion converges to `f` on positive imaginary axis
    intro t (ht : 0 < t)
    have := hasSum_qExpansion f hh hΓ (ofComplex (I * t))
    convert! hasSum_ite_sub_hasSum this 0 using 2 with n
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · simp [hn.ne', Function.Periodic.qParam, ofComplex_apply_eq_ite, ht, ← exp_nat_mul]
        grind [I_sq]
    · simp only [weakFEPair]
      rw [qExpansion_coeff_zero hh]; rw [pow_zero]; rw [mul_one]
      · exact ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ
      · exact SlashInvariantFormClass.periodic_comp_ofComplex f hΓ
  · -- show summability of Dirichlet series
    simp_rw [mul_comm (2 : Real), mul_div_assoc,
      Real.mul_rpow (Nat.cast_nonneg _) (show 0 <= 2 / h Γ by positivity), ← div_div]
    apply Summable.div_const
    apply summable_of_isBigO_nat (Real.summable_nat_rpow.mpr <| show r - s.re < -1 by linarith)
    simp only [Real.rpow_sub' (Nat.cast_nonneg _) (show r - s.re != 0 by linarith)]
    apply IsBigO.mul _ (isBigO_refl _ _)
    simpa using hcoeff.norm_left
-/
private lemma hasSum_Λ_of_qExpansion_isBigO {r : Real}
    (hpos : 0 < s.re) (hs : r + 1 < s.re)
    (hΛ : Λ hk f s = mellin (fun t => (weakFEPair hk f).f t - (weakFEPair hk f).f₀) s)
    (hcoeff : (fun n => (qExpansion (h Γ) f).coeff n) =O[atTop] fun n => (n : Real) ^ r) :
    HasSum (fun n => π ^ (-s) * Gamma s * (qExpansion (h Γ) f).coeff n /
      ↑(2 * n / h Γ : Real) ^ s) (Λ hk f s) := by
  rw [hΛ]
  have hh := Γ.strictWidthInfty_pos
  have hΓ := Γ.strictWidthInfty_mem_strictPeriods
  refine hasSum_mellin_pi_mul₀ (fun _ => by positivity) hpos ?_ ?_
  · -- show `q`-expansion converges to `f` on positive imaginary axis
    intro t (ht : 0 < t)
    have := hasSum_qExpansion f hh hΓ (ofComplex (I * t))
    convert! hasSum_ite_sub_hasSum this 0 using 2 with n
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · simp [hn.ne', Function.Periodic.qParam, ofComplex_apply_eq_ite, ht, ← exp_nat_mul]
        grind [I_sq]
    · simp only [weakFEPair]
      rw [qExpansion_coeff_zero hh]; rw [pow_zero]; rw [mul_one]
      · exact ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ
      · exact SlashInvariantFormClass.periodic_comp_ofComplex f hΓ
  · -- show summability of Dirichlet series
    simp_rw [mul_comm (2 : Real), mul_div_assoc,
      Real.mul_rpow (Nat.cast_nonneg _) (show 0 <= 2 / h Γ by positivity), ← div_div]
    apply Summable.div_const
    apply summable_of_isBigO_nat (Real.summable_nat_rpow.mpr <| show r - s.re < -1 by linarith)
    simp only [Real.rpow_sub' (Nat.cast_nonneg _) (show r - s.re != 0 by linarith)]
    apply IsBigO.mul _ (isBigO_refl _ _)
    simpa using hcoeff.norm_left

/--
lemma `hasSum_Λ` / 引理 `hasSum_Λ`

English:
lemma hasSum_Λ
  given: (hs : k + 1 < s.re)
  proof: by
  refine hasSum_Λ_of_qExpansion_isBigO hk f (r := k)
    (by linarith [show (0 : Real) < k from mod_cast hk]) (by exact_mod_cast hs) ?_ ?_
  · rw [Λ, ← ((weakFEPair hk f).hasMellin <| by grind [weakFEPair]).2]
  · simpa using ModularFormClass.qExpansion_isBigO hk.le f

中文:
引理 hasSum_Λ
  条件: (hs : k + 1 < s.re)
  证明: by
  refine hasSum_Λ_of_qExpansion_isBigO hk f (r := k)
    (by linarith [show (0 : Real) < k from mod_cast hk]) (by exact_mod_cast hs) ?_ ?_
  · rw [Λ, ← ((weakFEPair hk f).hasMellin <| by grind [weakFEPair]).2]
  · simpa using ModularFormClass.qExpansion_isBigO hk.le f

Depends on / 依赖: ModularFormClass, ModularFormClass.qExpansion_isBigO, hasMellin, hk.le, mod_cast, qExpansion_isBigO, weakFEPair
-/
lemma hasSum_Λ (hs : k + 1 < s.re) :
    HasSum (fun n => π ^ (-s) * Gamma s * (qExpansion (h Γ) f).coeff n /
      ↑(2 * n / h Γ : Real) ^ s) (Λ hk f s) := by
  refine hasSum_Λ_of_qExpansion_isBigO hk f (r := k)
    (by linarith [show (0 : Real) < k from mod_cast hk]) (by exact_mod_cast hs) ?_ ?_
  · rw [Λ, ← ((weakFEPair hk f).hasMellin <| by grind [weakFEPair]).2]
  · simpa using ModularFormClass.qExpansion_isBigO hk.le f

/--
Definition of `L` / `L` 的定义

English:
definition L
  signature: (s : Complex)
  body: Λ hk f s * (2 / GammaComplex s)

中文:
定义 L
  签名: (s : 复形)
  定义体: Λ hk f s * (2 / GammaComplex s)

Depends on / 依赖: GammaComplex
-/
noncomputable def L (s : Complex) : Complex := Λ hk f s * (2 / GammaComplex s)

/--
lemma `hasSum_L_of_hasSum_Λ` / 引理 `hasSum_L_of_hasSum_Λ`

English:
lemma hasSum_L_of_hasSum_Λ
  statement: (hs : 0 < s.re)
  proof: by
  convert! hΛ.mul_right (2 / GammaComplex s * h Γ ^ (-s)) using 1
  · ext n
    generalize (PowerSeries.coeff n) (qExpansion (h Γ) f) = p
    rw [GammaComplex]; rw [← div_div]; rw [← div_div]; rw [div_self two_ne_zero]; rw [one_div]; rw [cpow_neg (2 * _)]; rw [inv_inv]; rw [← ofReal_ofNat]; rw [mul_cpow_ofReal_nonneg two_pos.le Real.pi_pos.le]
    simp only [ofReal_div, ofReal_mul, ofReal_ofNat, ofReal_natCast]
    have : (2 * n / h Γ : Complex) ^ s = 2 ^ s * n ^ s / h Γ ^ s := by
      rw [← ofReal_ofNat]; rw [← ofReal_natCast]; rw [← ofReal_mul]; rw [div_cpow_ofReal_nonneg (by grind) Γ.strictWidthInfty_nonneg]; rw [ofReal_mul]; rw [mul_cpow_ofReal_nonneg zero_le_two n.cast_nonneg]
    rw [this]; rw [cpow_neg]; rw [cpow_neg]
    have := Gamma_ne_zero_of_re_pos hs
    have := cpow_ne_zero_iff (y := s).mpr (.inl <| ofReal_ne_zero.mpr Γ.strictWidthInfty_pos.ne')
    field_simp
  · grind [L]

中文:
引理 hasSum_L_of_hasSum_Λ
  结论: (hs : 0 < s.re)
  证明: by
  convert! hΛ.mul_right (2 / GammaComplex s * h Γ ^ (-s)) using 1
  · ext n
    generalize (PowerSeries.coeff n) (qExpansion (h Γ) f) = p
    rw [GammaComplex]; rw [← div_div]; rw [← div_div]; rw [div_self two_ne_zero]; rw [one_div]; rw [cpow_neg (2 * _)]; rw [inv_inv]; rw [← ofReal_ofNat]; rw [mul_cpow_ofReal_nonneg two_pos.le Real.pi_pos.le]
    simp only [ofReal_div, ofReal_mul, ofReal_ofNat, ofReal_natCast]
    have : (2 * n / h Γ : Complex) ^ s = 2 ^ s * n ^ s / h Γ ^ s := by
      rw [← ofReal_ofNat]; rw [← ofReal_natCast]; rw [← ofReal_mul]; rw [div_cpow_ofReal_nonneg (by grind) Γ.strictWidthInfty_nonneg]; rw [ofReal_mul]; rw [mul_cpow_ofReal_nonneg zero_le_two n.cast_nonneg]
    rw [this]; rw [cpow_neg]; rw [cpow_neg]
    have := Gamma_ne_zero_of_re_pos hs
    have := cpow_ne_zero_iff (y := s).mpr (.inl <| ofReal_ne_zero.mpr Γ.strictWidthInfty_pos.ne')
    field_simp
  · grind [L]
-/
private lemma hasSum_L_of_hasSum_Λ (hs : 0 < s.re)
    (hΛ : HasSum (fun n => π ^ (-s) * Gamma s *
      (qExpansion (h Γ) f).coeff n / ↑(2 * n / h Γ : Real) ^ s) (Λ hk f s)) :
    HasSum (fun i => (qExpansion (h Γ) f).coeff i / ↑i ^ s) (h Γ ^ (-s) * L hk f s) := by
  convert! hΛ.mul_right (2 / GammaComplex s * h Γ ^ (-s)) using 1
  · ext n
    generalize (PowerSeries.coeff n) (qExpansion (h Γ) f) = p
    rw [GammaComplex]; rw [← div_div]; rw [← div_div]; rw [div_self two_ne_zero]; rw [one_div]; rw [cpow_neg (2 * _)]; rw [inv_inv]; rw [← ofReal_ofNat]; rw [mul_cpow_ofReal_nonneg two_pos.le Real.pi_pos.le]
    simp only [ofReal_div, ofReal_mul, ofReal_ofNat, ofReal_natCast]
    have : (2 * n / h Γ : Complex) ^ s = 2 ^ s * n ^ s / h Γ ^ s := by
      rw [← ofReal_ofNat]; rw [← ofReal_natCast]; rw [← ofReal_mul]; rw [div_cpow_ofReal_nonneg (by grind) Γ.strictWidthInfty_nonneg]; rw [ofReal_mul]; rw [mul_cpow_ofReal_nonneg zero_le_two n.cast_nonneg]
    rw [this]; rw [cpow_neg]; rw [cpow_neg]
    have := Gamma_ne_zero_of_re_pos hs
    have := cpow_ne_zero_iff (y := s).mpr (.inl <| ofReal_ne_zero.mpr Γ.strictWidthInfty_pos.ne')
    field_simp
  · grind [L]

/--
theorem `hasSum_L` / 定理 `hasSum_L`

English:
theorem hasSum_L
  given: (hs : k + 1 < s.re)
  proof: hasSum_L_of_hasSum_Λ hk f (by linarith [show (0 : Real) < k from mod_cast hk]) (hasSum_Λ hk f hs)

中文:
定理 hasSum_L
  条件: (hs : k + 1 < s.re)
  证明: hasSum_L_of_hasSum_Λ hk f (by linarith [show (0 : Real) < k from mod_cast hk]) (hasSum_Λ hk f hs)

Depends on / 依赖: mod_cast
-/
theorem hasSum_L (hs : k + 1 < s.re) :
    HasSum (fun n => (qExpansion (h Γ) f).coeff n / n ^ s) (h Γ ^ (-s) * L hk f s) :=
  hasSum_L_of_hasSum_Λ hk f (by linarith [show (0 : Real) < k from mod_cast hk]) (hasSum_Λ hk f hs)

end ModularForm

open ModularForm

namespace CuspForm

variable [CuspFormClass F Γ k]

/--
lemma `isStrongFEPair` / 引理 `isStrongFEPair`

English:
lemma isStrongFEPair
  statement: IsStrongFEPair (weakFEPair hk f) where
  proof: (CuspFormClass.zero_at_infty f).valueAtInfty_eq_zero
  hg₀ := (CuspFormClass.zero_at_infty <| translate f ModularGroup.S).valueAtInfty_eq_zero

@[fun_prop]

中文:
引理 isStrongFEPair
  结论: 是StrongFEPair (weakFEPair hk f) where
  证明: (CuspFormClass.zero_at_infty f).valueAtInfty_eq_zero
  hg₀ := (CuspFormClass.zero_at_infty <| translate f ModularGroup.S).valueAtInfty_eq_zero

@[fun_prop]

Depends on / 依赖: CuspFormClass, CuspFormClass.zero_at_infty, valueAtInfty_eq_zero, zero_at_infty
-/
lemma isStrongFEPair : IsStrongFEPair (weakFEPair hk f) where
  hf₀ := (CuspFormClass.zero_at_infty f).valueAtInfty_eq_zero
  hg₀ := (CuspFormClass.zero_at_infty <| translate f ModularGroup.S).valueAtInfty_eq_zero

@[fun_prop]
/--
lemma `differentiable_Λ` / 引理 `differentiable_Λ`

English:
lemma differentiable_Λ
  statement: Differentiable Complex (Λ hk f)
  proof: (isStrongFEPair hk f).differentiable_Λ

中文:
引理 differentiable_Λ
  结论: 可微 复形 (Λ hk f)
  证明: (isStrongFEPair hk f).differentiable_Λ

Depends on / 依赖: isStrongFEPair
-/
lemma differentiable_Λ : Differentiable Complex (Λ hk f) :=
  (isStrongFEPair hk f).differentiable_Λ

/--
lemma `Λ_eq_mellin` / 引理 `Λ_eq_mellin`

English:
lemma Λ_eq_mellin
  statement: Λ hk f = mellin (fun t => f (ofComplex (I * t)))
  proof: (isStrongFEPair hk f).Λ_eq

中文:
引理 Λ_eq_mellin
  结论: Λ hk f = mellin (fun t => f (ofComplex (I * t)))
  证明: (isStrongFEPair hk f).Λ_eq

Depends on / 依赖: isStrongFEPair
-/
lemma Λ_eq_mellin : Λ hk f = mellin (fun t => f (ofComplex (I * t))) :=
  (isStrongFEPair hk f).Λ_eq

/--
lemma `hasSum_Λ` / 引理 `hasSum_Λ`

English:
lemma hasSum_Λ
  given: (hk : 0 < k) (hs : k / 2 + 1 < s.re)
  proof: by
  refine hasSum_Λ_of_qExpansion_isBigO hk f (r := k / 2)
    (by linarith [show (0 : Real) < k from mod_cast hk]) hs ?_ ?_
  · simp [Λ_eq_mellin, (CuspFormClass.zero_at_infty f).valueAtInfty_eq_zero]
  · simpa using CuspFormClass.qExpansion_isBigO f

@[fun_prop]

中文:
引理 hasSum_Λ
  条件: (hk : 0 < k) (hs : k / 2 + 1 < s.re)
  证明: by
  refine hasSum_Λ_of_qExpansion_isBigO hk f (r := k / 2)
    (by linarith [show (0 : Real) < k from mod_cast hk]) hs ?_ ?_
  · simp [Λ_eq_mellin, (CuspFormClass.zero_at_infty f).valueAtInfty_eq_zero]
  · simpa using CuspFormClass.qExpansion_isBigO f

@[fun_prop]

Depends on / 依赖: CuspFormClass, CuspFormClass.qExpansion_isBigO, CuspFormClass.zero_at_infty, mod_cast, qExpansion_isBigO, valueAtInfty_eq_zero, zero_at_infty
-/
lemma hasSum_Λ (hk : 0 < k) (hs : k / 2 + 1 < s.re) :
    HasSum (fun n => π ^ (-s) * Gamma s * (qExpansion (h Γ) f).coeff n / ↑(2 * n / h Γ : Real) ^ s)
      (Λ hk f s) := by
  refine hasSum_Λ_of_qExpansion_isBigO hk f (r := k / 2)
    (by linarith [show (0 : Real) < k from mod_cast hk]) hs ?_ ?_
  · simp [Λ_eq_mellin, (CuspFormClass.zero_at_infty f).valueAtInfty_eq_zero]
  · simpa using CuspFormClass.qExpansion_isBigO f

@[fun_prop]
/--
lemma `differentiable_L` / 引理 `differentiable_L`

English:
lemma differentiable_L
  statement: Differentiable Complex (L hk f)
  proof: by
  unfold L
  simp only [div_eq_mul_inv]
  fun_prop

中文:
引理 differentiable_L
  结论: 可微 复形 (L hk f)
  证明: by
  unfold L
  simp only [div_eq_mul_inv]
  fun_prop

Depends on / 依赖: div_eq_mul_inv, fun_prop
-/
lemma differentiable_L : Differentiable Complex (L hk f) := by
  unfold L
  simp only [div_eq_mul_inv]
  fun_prop

/--
theorem `hasSum_L` / 定理 `hasSum_L`

English:
theorem hasSum_L
  given: (hs : k / 2 + 1 < s.re)
  proof: hasSum_L_of_hasSum_Λ hk f (by linarith [show (0 : Real) < k from mod_cast hk]) (hasSum_Λ f hk hs)

中文:
定理 hasSum_L
  条件: (hs : k / 2 + 1 < s.re)
  证明: hasSum_L_of_hasSum_Λ hk f (by linarith [show (0 : Real) < k from mod_cast hk]) (hasSum_Λ f hk hs)

Depends on / 依赖: mod_cast
-/
theorem hasSum_L (hs : k / 2 + 1 < s.re) :
    HasSum (fun n => (qExpansion (h Γ) f).coeff n / n ^ s) (h Γ ^ (-s) * L hk f s) :=
  hasSum_L_of_hasSum_Λ hk f (by linarith [show (0 : Real) < k from mod_cast hk]) (hasSum_Λ f hk hs)

end CuspForm
