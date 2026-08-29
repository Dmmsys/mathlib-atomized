/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# The Petersson scalar product

For `f, f'` functions `ℍ → ℂ`, we define `petersson k f f'` to be the function
`τ ↦ conj (f τ) * f' τ * τ.im ^ k`.

We show this function is (weight 0) invariant under `Γ` if `f, f'` are (weight `k`) invariant under
`Γ`.
-/

@[expose] public section


open UpperHalfPlane Asymptotics Filter

open scoped MatrixGroups ComplexConjugate ModularForm

namespace UpperHalfPlane

/--
Definition of `petersson` / `petersson` 的定义

English:
definition petersson
  signature: (k : Int) (f f' : ℍ -> Complex) (τ : ℍ)
  body: conj (f τ) * f' τ * τ.im ^ k

@[fun_prop]

中文:
定义 petersson
  签名: (k : 整数) (f f' : ℍ -> 复形) (τ : ℍ)
  定义体: conj (f τ) * f' τ * τ.im ^ k

@[fun_prop]
-/
noncomputable def petersson (k : Int) (f f' : ℍ -> Complex) (τ : ℍ) :=
  conj (f τ) * f' τ * τ.im ^ k

@[fun_prop]
/--
lemma `petersson_continuous` / 引理 `petersson_continuous`

English:
lemma petersson_continuous
  given: (k : Int) {f f' : ℍ -> Complex} (hf : Continuous f) (hf' : Continuous f')
  proof: by
  unfold petersson
  fun_prop (disch := simp [im_ne_zero _])

中文:
引理 petersson_continuous
  条件: (k : 整数) {f f' : ℍ -> 复形} (hf : 连续 f) (hf' : 连续 f')
  证明: by
  unfold petersson
  fun_prop (disch := simp [im_ne_zero _])

Depends on / 依赖: fun_prop, im_ne_zero, petersson
-/
lemma petersson_continuous (k : Int) {f f' : ℍ -> Complex} (hf : Continuous f) (hf' : Continuous f') :
    Continuous (petersson k f f') := by
  unfold petersson
  fun_prop (disch := simp [im_ne_zero _])

/--
lemma `petersson_slash` / 引理 `petersson_slash`

English:
lemma petersson_slash
  given: (k : Int) (f f' : ℍ -> Complex) (g : GL (Fin 2) Real) (τ : ℍ)
  proof: by
  set D := |g.det.val|
  have hD : (D : Complex) != 0 := mod_cast abs_ne_zero.mpr g.det_ne_zero
  set j := denom g τ
  calc petersson k (f ∣[k] g) (f' ∣[k] g) τ
  _ = D ^ (k - 2 + k) * conj (σ g (f (g • τ))) * σ g (f' (g • τ))
      * (τ.im ^ k * j.normSq ^ (-k)) := by
    simp [Complex.normSq_eq_conj_mul_self, (by abel : k - 2 + k = (k - 1) + (k - 1)), petersson,
      zpow_add₀ hD, mul_zpow, ModularForm.slash_def, -Matrix.GeneralLinearGroup.val_det_apply]
    ring
  _ = D ^ (k - 2) * (conj (σ g (f (g • τ))) * σ g (f' (g • τ)) * (D * τ.im / j.normSq) ^ k) := by
    rw [div_zpow]; rw [mul_zpow]; rw [zpow_neg]; rw [div_eq_mul_inv]; rw [zpow_add₀ hD]
    ring
  _ = D ^ (k - 2) * (conj (σ g (f (g • τ))) * σ g (f' (g • τ)) * (im (g • τ)) ^ k) := by
    rw [im_smul_eq_div_normSq]; rw [Complex.ofReal_div]; rw [Complex.ofReal_mul]
  _ = D ^ (k - 2) * σ g (petersson k f f' (g • τ)) := by simp [petersson, σ_conj]

中文:
引理 petersson_slash
  条件: (k : 整数) (f f' : ℍ -> 复形) (g : GL (有限集 2) 实数) (τ : ℍ)
  证明: by
  set D := |g.det.val|
  have hD : (D : Complex) != 0 := mod_cast abs_ne_zero.mpr g.det_ne_zero
  set j := denom g τ
  calc petersson k (f ∣[k] g) (f' ∣[k] g) τ
  _ = D ^ (k - 2 + k) * conj (σ g (f (g • τ))) * σ g (f' (g • τ))
      * (τ.im ^ k * j.normSq ^ (-k)) := by
    simp [Complex.normSq_eq_conj_mul_self, (by abel : k - 2 + k = (k - 1) + (k - 1)), petersson,
      zpow_add₀ hD, mul_zpow, ModularForm.slash_def, -Matrix.GeneralLinearGroup.val_det_apply]
    ring
  _ = D ^ (k - 2) * (conj (σ g (f (g • τ))) * σ g (f' (g • τ)) * (D * τ.im / j.normSq) ^ k) := by
    rw [div_zpow]; rw [mul_zpow]; rw [zpow_neg]; rw [div_eq_mul_inv]; rw [zpow_add₀ hD]
    ring
  _ = D ^ (k - 2) * (conj (σ g (f (g • τ))) * σ g (f' (g • τ)) * (im (g • τ)) ^ k) := by
    rw [im_smul_eq_div_normSq]; rw [Complex.ofReal_div]; rw [Complex.ofReal_mul]
  _ = D ^ (k - 2) * σ g (petersson k f f' (g • τ)) := by simp [petersson, σ_conj]

Depends on / 依赖: Complex.normSq_eq_conj_mul_self, GeneralLinearGroup, Matrix, Matrix.GeneralLinearGroup.val_det_apply, ModularForm, ModularForm.slash_def, abs_ne_zero, abs_ne_zero.mpr, det_ne_zero, g.det.val, g.det_ne_zero, j.normSq, mod_cast, mul_zpow, normSq, normSq_eq_conj_mul_self, petersson, slash_def, val_det_apply
-/
lemma petersson_slash (k : Int) (f f' : ℍ -> Complex) (g : GL (Fin 2) Real) (τ : ℍ) :
    petersson k (f ∣[k] g) (f' ∣[k] g) τ =
      |g.det.val| ^ (k - 2) * σ g (petersson k f f' (g • τ)) := by
  set D := |g.det.val|
  have hD : (D : Complex) != 0 := mod_cast abs_ne_zero.mpr g.det_ne_zero
  set j := denom g τ
  calc petersson k (f ∣[k] g) (f' ∣[k] g) τ
  _ = D ^ (k - 2 + k) * conj (σ g (f (g • τ))) * σ g (f' (g • τ))
      * (τ.im ^ k * j.normSq ^ (-k)) := by
    simp [Complex.normSq_eq_conj_mul_self, (by abel : k - 2 + k = (k - 1) + (k - 1)), petersson,
      zpow_add₀ hD, mul_zpow, ModularForm.slash_def, -Matrix.GeneralLinearGroup.val_det_apply]
    ring
  _ = D ^ (k - 2) * (conj (σ g (f (g • τ))) * σ g (f' (g • τ)) * (D * τ.im / j.normSq) ^ k) := by
    rw [div_zpow]; rw [mul_zpow]; rw [zpow_neg]; rw [div_eq_mul_inv]; rw [zpow_add₀ hD]
    ring
  _ = D ^ (k - 2) * (conj (σ g (f (g • τ))) * σ g (f' (g • τ)) * (im (g • τ)) ^ k) := by
    rw [im_smul_eq_div_normSq]; rw [Complex.ofReal_div]; rw [Complex.ofReal_mul]
  _ = D ^ (k - 2) * σ g (petersson k f f' (g • τ)) := by simp [petersson, σ_conj]

/--
lemma `petersson_slash_SL` / 引理 `petersson_slash_SL`

English:
lemma petersson_slash_SL
  given: (k : Int) (f f' : ℍ -> Complex) (g : SL(2, Int)) (τ : ℍ)
  proof: by
  -- need to disable a simp lemma as it works against `Matrix.SpecialLinearGroup.det_coe`
  simp [σ, ModularForm.SL_slash, petersson_slash,
    -Matrix.SpecialLinearGroup.map_apply_coe]

中文:
引理 petersson_slash_SL
  条件: (k : 整数) (f f' : ℍ -> 复形) (g : SL(2, 整数)) (τ : ℍ)
  证明: by
  -- need to disable a simp lemma as it works against `Matrix.SpecialLinearGroup.det_coe`
  simp [σ, ModularForm.SL_slash, petersson_slash,
    -Matrix.SpecialLinearGroup.map_apply_coe]
-/
lemma petersson_slash_SL (k : Int) (f f' : ℍ -> Complex) (g : SL(2, Int)) (τ : ℍ) :
    petersson k (f ∣[k] g) (f' ∣[k] g) τ = petersson k f f' (g • τ) := by
  -- need to disable a simp lemma as it works against `Matrix.SpecialLinearGroup.det_coe`
  simp [σ, ModularForm.SL_slash, petersson_slash,
    -Matrix.SpecialLinearGroup.map_apply_coe]

/--
lemma `petersson_symm` / 引理 `petersson_symm`

English:
lemma petersson_symm
  given: (k : Int) (f f' : ℍ -> Complex) (τ : ℍ)
  proof: by
  simp [petersson, mul_comm]

中文:
引理 petersson_symm
  条件: (k : 整数) (f f' : ℍ -> 复形) (τ : ℍ)
  证明: by
  simp [petersson, mul_comm]

Depends on / 依赖: mul_comm, petersson
-/
lemma petersson_symm (k : Int) (f f' : ℍ -> Complex) (τ : ℍ) :
    petersson k f' f τ = conj (petersson k f f' τ) := by
  simp [petersson, mul_comm]

/--
lemma `petersson_norm_symm` / 引理 `petersson_norm_symm`

English:
lemma petersson_norm_symm
  given: (k : Int) (f f' : ℍ -> Complex) (τ : ℍ)
  proof: by
  simp [petersson_symm k f]

中文:
引理 petersson_norm_symm
  条件: (k : 整数) (f f' : ℍ -> 复形) (τ : ℍ)
  证明: by
  simp [petersson_symm k f]

Depends on / 依赖: petersson_symm
-/
lemma petersson_norm_symm (k : Int) (f f' : ℍ -> Complex) (τ : ℍ) :
    ‖petersson k f' f τ‖ = ‖petersson k f f' τ‖ := by
  simp [petersson_symm k f]

end UpperHalfPlane

section

variable {F F' : Type*} [FunLike F ℍ Complex] [FunLike F' ℍ Complex]

/--
lemma `SlashInvariantFormClass.norm_petersson_smul` / 引理 `SlashInvariantFormClass.norm_petersson_smul`

English:
lemma SlashInvariantFormClass.norm_petersson_smul
  statement: {k g τ} {Γ : Subgroup (GL (Fin 2) Real)}
  proof: by
  conv_rhs => rw [← slash_action_eq f _ hg, ← slash_action_eq f' _ hg, petersson_slash,
    Subgroup.HasDetPlusMinusOne.abs_det hg, Complex.ofReal_one, one_zpow, one_mul, norm_σ]

中文:
引理 斜不变形式类.norm_petersson_smul
  结论: {k g τ} {Γ : 子群 (GL (有限集 2) 实数)}
  证明: by
  conv_rhs => rw [← slash_action_eq f _ hg, ← slash_action_eq f' _ hg, petersson_slash,
    Subgroup.HasDetPlusMinusOne.abs_det hg, Complex.ofReal_one, one_zpow, one_mul, norm_σ]

Depends on / 依赖: Complex.ofReal_one, HasDetPlusMinusOne, Subgroup, Subgroup.HasDetPlusMinusOne.abs_det, abs_det, conv_rhs, ofReal_one, one_mul, one_zpow, petersson_slash, slash_action_eq
-/
lemma SlashInvariantFormClass.norm_petersson_smul {k g τ} {Γ : Subgroup (GL (Fin 2) Real)}
    [Γ.HasDetPlusMinusOne] [SlashInvariantFormClass F Γ k] {f : F}
    [SlashInvariantFormClass F' Γ k] {f' : F'} (hg : g in Γ) :
    ‖petersson k f f' (g • τ)‖ = ‖petersson k f f' τ‖ := by
  conv_rhs => rw [← slash_action_eq f _ hg, ← slash_action_eq f' _ hg, petersson_slash,
    Subgroup.HasDetPlusMinusOne.abs_det hg, Complex.ofReal_one, one_zpow, one_mul, norm_σ]

/--
lemma `SlashInvariantFormClass.petersson_smul` / 引理 `SlashInvariantFormClass.petersson_smul`

English:
lemma SlashInvariantFormClass.petersson_smul
  statement: {k g τ} {Γ : Subgroup (GL (Fin 2) Real)} [Γ.HasDetOne]
  proof: by
  simpa [SlashInvariantFormClass.slash_action_eq _ _ hg, Subgroup.HasDetOne.det_eq hg, σ]
    using (petersson_slash k f f' g τ).symm

中文:
引理 斜不变形式类.petersson_smul
  结论: {k g τ} {Γ : 子群 (GL (有限集 2) 实数)} [Γ.有DetOne]
  证明: by
  simpa [SlashInvariantFormClass.slash_action_eq _ _ hg, Subgroup.HasDetOne.det_eq hg, σ]
    using (petersson_slash k f f' g τ).symm

Depends on / 依赖: HasDetOne, SlashInvariantFormClass, SlashInvariantFormClass.slash_action_eq, Subgroup, Subgroup.HasDetOne.det_eq, det_eq, petersson_slash, slash_action_eq
-/
lemma SlashInvariantFormClass.petersson_smul {k g τ} {Γ : Subgroup (GL (Fin 2) Real)} [Γ.HasDetOne]
    [SlashInvariantFormClass F Γ k] {f : F} [SlashInvariantFormClass F' Γ k] {f' : F'}
    (hg : g in Γ) : petersson k f f' (g • τ) = petersson k f f' τ := by
  simpa [SlashInvariantFormClass.slash_action_eq _ _ hg, Subgroup.HasDetOne.det_eq hg, σ]
    using (petersson_slash k f f' g τ).symm

namespace UpperHalfPlane.IsZeroAtImInfty

variable (k : Int) (Γ : Subgroup (GL (Fin 2) Real))
    [Fact (IsCusp OnePoint.infty Γ)] [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    [ModularFormClass F Γ k] [ModularFormClass F' Γ k]

include Γ -- can't be inferred from statements

/--
lemma `petersson_exp_decay_left` / 引理 `petersson_exp_decay_left`

English:
lemma petersson_exp_decay_left
  given: {f : F} (h_bd : IsZeroAtImInfty f) (f' : F')
  proof: by
  obtain ⟨b, hb, hbf⟩ := ModularFormClass.exp_decay_atImInfty' f h_bd
  obtain ⟨a, ha, ha'⟩ := exists_between hb
  use a, ha
  apply IsBigO.of_norm_left
  simp_rw [petersson, norm_mul, Complex.norm_conj, mul_comm ‖f _‖ ‖f' _‖, norm_zpow, mul_assoc,
      Complex.norm_real, Real.norm_of_nonneg (fun {τ : ℍ} => τ.im_pos).le]
  conv_rhs => enter [τ]; rw [← one_mul (Real.exp _)]
  have hf' : IsBoundedAtImInfty f' := ModularFormClass.bdd_at_infty f'
  refine hf'.norm_left.mul ((hbf.norm_left.mul <| isBigO_refl _ _).trans ?_)
  refine IsBigO.comp_tendsto (f := fun t : Real => Real.exp (-b * t) * t ^ k)
     (g := fun t : Real => Real.exp (-a * t)) ?_ tendsto_comap
  simpa using (isLittleO_exp_mul_rpow_of_lt k (neg_lt_neg ha')).isBigO

中文:
引理 petersson_exp_decay_left
  条件: {f : F} (h_bd : IsZeroAtImInfty f) (f' : F')
  证明: by
  obtain ⟨b, hb, hbf⟩ := ModularFormClass.exp_decay_atImInfty' f h_bd
  obtain ⟨a, ha, ha'⟩ := exists_between hb
  use a, ha
  apply IsBigO.of_norm_left
  simp_rw [petersson, norm_mul, Complex.norm_conj, mul_comm ‖f _‖ ‖f' _‖, norm_zpow, mul_assoc,
      Complex.norm_real, Real.norm_of_nonneg (fun {τ : ℍ} => τ.im_pos).le]
  conv_rhs => enter [τ]; rw [← one_mul (Real.exp _)]
  have hf' : IsBoundedAtImInfty f' := ModularFormClass.bdd_at_infty f'
  refine hf'.norm_left.mul ((hbf.norm_left.mul <| isBigO_refl _ _).trans ?_)
  refine IsBigO.comp_tendsto (f := fun t : Real => Real.exp (-b * t) * t ^ k)
     (g := fun t : Real => Real.exp (-a * t)) ?_ tendsto_comap
  simpa using (isLittleO_exp_mul_rpow_of_lt k (neg_lt_neg ha')).isBigO

Depends on / 依赖: Complex.norm_conj, Complex.norm_real, IsBigO, IsBigO.of_norm_left, IsBoundedAtImInfty, ModularFormClass, ModularFormClass.bdd_at_infty, ModularFormClass.exp_decay_atImInfty, Real.exp, Real.norm_of_nonneg, bdd_at_infty, conv_rhs, exists_between, exp_decay_atImInfty, h_bd, hbf.norm_left.mul, im_pos, isBigO_refl, mul_assoc, mul_comm
-/
lemma petersson_exp_decay_left {f : F} (h_bd : IsZeroAtImInfty f) (f' : F') :
    exists a > 0, petersson k f f' =O[atImInfty] fun τ => Real.exp (-a * im τ) := by
  obtain ⟨b, hb, hbf⟩ := ModularFormClass.exp_decay_atImInfty' f h_bd
  obtain ⟨a, ha, ha'⟩ := exists_between hb
  use a, ha
  apply IsBigO.of_norm_left
  simp_rw [petersson, norm_mul, Complex.norm_conj, mul_comm ‖f _‖ ‖f' _‖, norm_zpow, mul_assoc,
      Complex.norm_real, Real.norm_of_nonneg (fun {τ : ℍ} => τ.im_pos).le]
  conv_rhs => enter [τ]; rw [← one_mul (Real.exp _)]
  have hf' : IsBoundedAtImInfty f' := ModularFormClass.bdd_at_infty f'
  refine hf'.norm_left.mul ((hbf.norm_left.mul <| isBigO_refl _ _).trans ?_)
  refine IsBigO.comp_tendsto (f := fun t : Real => Real.exp (-b * t) * t ^ k)
     (g := fun t : Real => Real.exp (-a * t)) ?_ tendsto_comap
  simpa using (isLittleO_exp_mul_rpow_of_lt k (neg_lt_neg ha')).isBigO

/--
lemma `petersson_exp_decay_right` / 引理 `petersson_exp_decay_right`

English:
lemma petersson_exp_decay_right
  given: (f : F) {f' : F'} (h_bd : IsZeroAtImInfty f')
  proof: by
  obtain ⟨a, ha, ha'⟩ := h_bd.petersson_exp_decay_left k Γ f
exact ⟨a, ha, .of_norm_left ha'.norm_left.congr_left petersson_norm_symm k f f'⟩

omit Γ in

中文:
引理 petersson_exp_decay_right
  条件: (f : F) {f' : F'} (h_bd : IsZeroAtImInfty f')
  证明: by
  obtain ⟨a, ha, ha'⟩ := h_bd.petersson_exp_decay_left k Γ f
exact ⟨a, ha, .of_norm_left ha'.norm_left.congr_left petersson_norm_symm k f f'⟩

omit Γ in

Depends on / 依赖: congr_left, h_bd, h_bd.petersson_exp_decay_left, norm_left, norm_left.congr_left, of_norm_left, petersson_exp_decay_left, petersson_norm_symm
-/
lemma petersson_exp_decay_right (f : F) {f' : F'} (h_bd : IsZeroAtImInfty f') :
    exists a > 0, petersson k f f' =O[atImInfty] fun τ => Real.exp (-a * im τ) := by
  obtain ⟨a, ha, ha'⟩ := h_bd.petersson_exp_decay_left k Γ f
exact ⟨a, ha, .of_norm_left ha'.norm_left.congr_left petersson_norm_symm k f f'⟩

omit Γ in
-- this lemma can't go in `UpperHalfPlane.FunctionsBoundedAtInfty` because it needs `Real.exp`
/--
lemma `of_exp_decay` / 引理 `of_exp_decay`

English:
lemma of_exp_decay
  statement: {E : Type*} [NormedAddCommGroup E] {f : ℍ -> E}
  proof: by
  obtain ⟨a, ha, ha'⟩ := hf
refine ha'.trans_tendsto (Real.tendsto_exp_atBot.comp ?_).comp tendsto_comap
  exact tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr ha)

中文:
引理 of_exp_decay
  结论: {E : 类型} [赋范交换加群 E] {f : ℍ -> E}
  证明: by
  obtain ⟨a, ha, ha'⟩ := hf
refine ha'.trans_tendsto (Real.tendsto_exp_atBot.comp ?_).comp tendsto_comap
  exact tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr ha)

Depends on / 依赖: Real.tendsto_exp_atBot.comp, const_mul_atTop_of_neg, neg_lt_zero, neg_lt_zero.mpr, tendsto_comap, tendsto_exp_atBot, tendsto_id, tendsto_id.const_mul_atTop_of_neg, trans_tendsto
-/
lemma of_exp_decay {E : Type*} [NormedAddCommGroup E] {f : ℍ -> E}
    (hf : exists c > 0, f =O[atImInfty] fun τ => Real.exp (-c * τ.im)) :
    IsZeroAtImInfty f := by
  obtain ⟨a, ha, ha'⟩ := hf
refine ha'.trans_tendsto (Real.tendsto_exp_atBot.comp ?_).comp tendsto_comap
  exact tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr ha)

/--
lemma `petersson_isZeroAtImInfty_left` / 引理 `petersson_isZeroAtImInfty_left`

English:
lemma petersson_isZeroAtImInfty_left
  given: {f : F} (h_bd : IsZeroAtImInfty f) (f' : F')
  proof: of_exp_decay (h_bd.petersson_exp_decay_left k Γ f')

中文:
引理 petersson_isZeroAtImInfty_left
  条件: {f : F} (h_bd : IsZeroAtImInfty f) (f' : F')
  证明: of_exp_decay (h_bd.petersson_exp_decay_left k Γ f')

Depends on / 依赖: h_bd, h_bd.petersson_exp_decay_left, of_exp_decay, petersson_exp_decay_left
-/
lemma petersson_isZeroAtImInfty_left {f : F} (h_bd : IsZeroAtImInfty f) (f' : F') :
    IsZeroAtImInfty (petersson k f f') :=
  of_exp_decay (h_bd.petersson_exp_decay_left k Γ f')

/--
lemma `petersson_isZeroAtImInfty_right` / 引理 `petersson_isZeroAtImInfty_right`

English:
lemma petersson_isZeroAtImInfty_right
  given: (f : F) {f' : F'} (h_bd : IsZeroAtImInfty f')
  proof: of_exp_decay (h_bd.petersson_exp_decay_right k Γ f)

中文:
引理 petersson_isZeroAtImInfty_right
  条件: (f : F) {f' : F'} (h_bd : IsZeroAtImInfty f')
  证明: of_exp_decay (h_bd.petersson_exp_decay_right k Γ f)

Depends on / 依赖: h_bd, h_bd.petersson_exp_decay_right, of_exp_decay, petersson_exp_decay_right
-/
lemma petersson_isZeroAtImInfty_right (f : F) {f' : F'} (h_bd : IsZeroAtImInfty f') :
    IsZeroAtImInfty (petersson k f f') :=
  of_exp_decay (h_bd.petersson_exp_decay_right k Γ f)

end UpperHalfPlane.IsZeroAtImInfty

end
