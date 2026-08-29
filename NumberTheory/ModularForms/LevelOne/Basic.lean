/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
public import Mathlib.NumberTheory.Modular
public import Mathlib.NumberTheory.ModularForms.QExpansion
/-!
# Level one modular forms

This file contains results specific to modular forms of level one, i.e. modular forms for
`SL(2, ℤ)`.

Finite-dimensionality of these spaces is proved in a later file
(`Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean`).
-/

public section

open UpperHalfPlane ModularGroup SlashInvariantForm ModularForm Complex
  CongruenceSubgroup Real Function SlashInvariantFormClass ModularFormClass Periodic MatrixGroups

local notation "𝕢" => qParam

variable {F : Type*} [FunLike F ℍ Complex] {k : Int}

namespace SlashInvariantForm

variable [SlashInvariantFormClass F 𝒮ℒ k]

/--
lemma `exists_one_half_le_im_and_norm_le` / 引理 `exists_one_half_le_im_and_norm_le`

English:
lemma exists_one_half_le_im_and_norm_le
  given: (hk : k <= 0) (f : F) (τ : ℍ)
  proof: let ⟨γ, hγ, hdenom⟩ := exists_one_half_le_im_smul_and_norm_denom_le τ
  ⟨γ • τ, hγ, by
    have : SlashInvariantFormClass F Γ(1) k := Gamma_one_coe_eq_SL ▸ ‹_›
    simpa only [slash_action_eqn_SL'' _ (mem_Gamma_one γ), norm_mul, norm_zpow]
using le_mul_of_one_le_left (norm_nonneg _)
        one_le_zpow_of_nonpos₀ (norm_pos_iff.2 (denom_ne_zero _ _)) hdenom hk⟩

中文:
引理 存在_one_half_le_im_and_norm_le
  条件: (hk : k <= 0) (f : F) (τ : ℍ)
  证明: let ⟨γ, hγ, hdenom⟩ := exists_one_half_le_im_smul_and_norm_denom_le τ
  ⟨γ • τ, hγ, by
    have : SlashInvariantFormClass F Γ(1) k := Gamma_one_coe_eq_SL ▸ ‹_›
    simpa only [slash_action_eqn_SL'' _ (mem_Gamma_one γ), norm_mul, norm_zpow]
using le_mul_of_one_le_left (norm_nonneg _)
        one_le_zpow_of_nonpos₀ (norm_pos_iff.2 (denom_ne_zero _ _)) hdenom hk⟩

Depends on / 依赖: Gamma_one_coe_eq_SL, SlashInvariantFormClass, denom_ne_zero, exists_one_half_le_im_smul_and_norm_denom_le, hdenom, le_mul_of_one_le_left, mem_Gamma_one, norm_mul, norm_nonneg, norm_pos_iff, norm_zpow, slash_action_eqn_SL
-/
lemma exists_one_half_le_im_and_norm_le (hk : k <= 0) (f : F) (τ : ℍ) :
    exists ξ : ℍ, 1 / 2 <= ξ.im ∧ ‖f τ‖ <= ‖f ξ‖ :=
  let ⟨γ, hγ, hdenom⟩ := exists_one_half_le_im_smul_and_norm_denom_le τ
  ⟨γ • τ, hγ, by
    have : SlashInvariantFormClass F Γ(1) k := Gamma_one_coe_eq_SL ▸ ‹_›
    simpa only [slash_action_eqn_SL'' _ (mem_Gamma_one γ), norm_mul, norm_zpow]
using le_mul_of_one_le_left (norm_nonneg _)
        one_le_zpow_of_nonpos₀ (norm_pos_iff.2 (denom_ne_zero _ _)) hdenom hk⟩

variable (k) in
/--
lemma `wt_eq_zero_of_eq_const` / 引理 `wt_eq_zero_of_eq_const`

English:
lemma wt_eq_zero_of_eq_const
  given: {f : F} {c : Complex} (hf : ⇑f = Function.const _ c)
  proof: by
  have : SlashInvariantFormClass F Γ(1) k := Gamma_one_coe_eq_SL ▸ ‹_›
  have hI := slash_action_eqn_SL'' f (mem_Gamma_one S) I
  have h2I2 := slash_action_eqn_SL'' f (mem_Gamma_one S) ((⟨2, two_pos⟩ : {x : Real // 0 < x}) • .I)
  simp_rw [sl_moeb, hf, Function.const, denom_S] at hI h2I2
  suffices (2 : Complex) ^ k = 1 ↔ k = 0 by
    simpa [mul_zpow, zpow_ne_zero, this] using h2I2.symm.trans hI
simpa using ofReal_inj.trans zpow_eq_one_iff_right₀ (two_pos.le : (0 : Real) <= 2) (by norm_num1)

中文:
引理 wt_eq_zero_of_eq_const
  条件: {f : F} {c : 复形} (hf : ⇑f = 函数.const _ c)
  证明: by
  have : SlashInvariantFormClass F Γ(1) k := Gamma_one_coe_eq_SL ▸ ‹_›
  have hI := slash_action_eqn_SL'' f (mem_Gamma_one S) I
  have h2I2 := slash_action_eqn_SL'' f (mem_Gamma_one S) ((⟨2, two_pos⟩ : {x : Real // 0 < x}) • .I)
  simp_rw [sl_moeb, hf, Function.const, denom_S] at hI h2I2
  suffices (2 : Complex) ^ k = 1 ↔ k = 0 by
    simpa [mul_zpow, zpow_ne_zero, this] using h2I2.symm.trans hI
simpa using ofReal_inj.trans zpow_eq_one_iff_right₀ (two_pos.le : (0 : Real) <= 2) (by norm_num1)

Depends on / 依赖: Function, Function.const, Gamma_one_coe_eq_SL, SlashInvariantFormClass, denom_S, h2I2.symm.trans, mem_Gamma_one, mul_zpow, norm_num1, ofReal_inj, ofReal_inj.trans, simp_rw, sl_moeb, slash_action_eqn_SL, two_pos, two_pos.le, zpow_ne_zero
-/
lemma wt_eq_zero_of_eq_const {f : F} {c : Complex} (hf : ⇑f = Function.const _ c) :
    k = 0 ∨ c = 0 := by
  have : SlashInvariantFormClass F Γ(1) k := Gamma_one_coe_eq_SL ▸ ‹_›
  have hI := slash_action_eqn_SL'' f (mem_Gamma_one S) I
  have h2I2 := slash_action_eqn_SL'' f (mem_Gamma_one S) ((⟨2, two_pos⟩ : {x : Real // 0 < x}) • .I)
  simp_rw [sl_moeb, hf, Function.const, denom_S] at hI h2I2
  suffices (2 : Complex) ^ k = 1 ↔ k = 0 by
    simpa [mul_zpow, zpow_ne_zero, this] using h2I2.symm.trans hI
simpa using ofReal_inj.trans zpow_eq_one_iff_right₀ (two_pos.le : (0 : Real) <= 2) (by norm_num1)

/--
theorem `slash_action_generators_SL2Z` / 定理 `slash_action_generators_SL2Z`

English:
theorem slash_action_generators_SL2Z
  statement: {f : ℍ -> Complex} {k : Int}
  proof: by
  intro γ
  have h𝒮ℒ : 𝒮ℒ = Subgroup.closure ({↑S, ↑T} : Set (GL (Fin 2) Real)) := by
    rw [MonoidHom.range_eq_map]; rw [← SpecialLinearGroup.SL2Z_generators]; rw [MonoidHom.map_closure]; rw [Set.image_pair]
    rfl
  exact (slash_action_generators h𝒮ℒ).mpr (fun g hg => by rcases hg with rfl | rfl <;> assumption)
    _ (MonoidHom.mem_range.mpr ⟨γ, rfl⟩)

中文:
定理 slash_action_generators_SL2Z
  结论: {f : ℍ -> 复形} {k : 整数}
  证明: by
  intro γ
  have h𝒮ℒ : 𝒮ℒ = Subgroup.closure ({↑S, ↑T} : Set (GL (Fin 2) Real)) := by
    rw [MonoidHom.range_eq_map]; rw [← SpecialLinearGroup.SL2Z_generators]; rw [MonoidHom.map_closure]; rw [Set.image_pair]
    rfl
  exact (slash_action_generators h𝒮ℒ).mpr (fun g hg => by rcases hg with rfl | rfl <;> assumption)
    _ (MonoidHom.mem_range.mpr ⟨γ, rfl⟩)

Depends on / 依赖: MonoidHom, MonoidHom.map_closure, MonoidHom.mem_range.mpr, MonoidHom.range_eq_map, SL2Z_generators, Set.image_pair, SpecialLinearGroup, SpecialLinearGroup.SL2Z_generators, Subgroup, Subgroup.closure, closure, image_pair, map_closure, mem_range, range_eq_map, slash_action_generators
-/
theorem slash_action_generators_SL2Z {f : ℍ -> Complex} {k : Int}
    (hS : f ∣[k] S = f) (hT : f ∣[k] T = f) : forall γ : SL(2, Int), f ∣[k] γ = f := by
  intro γ
  have h𝒮ℒ : 𝒮ℒ = Subgroup.closure ({↑S, ↑T} : Set (GL (Fin 2) Real)) := by
    rw [MonoidHom.range_eq_map]; rw [← SpecialLinearGroup.SL2Z_generators]; rw [MonoidHom.map_closure]; rw [Set.image_pair]
    rfl
  exact (slash_action_generators h𝒮ℒ).mpr (fun g hg => by rcases hg with rfl | rfl <;> assumption)
    _ (MonoidHom.mem_range.mpr ⟨γ, rfl⟩)

end SlashInvariantForm

/--
lemma `one_mem_strictPeriods_SL` / 引理 `one_mem_strictPeriods_SL`

English:
lemma one_mem_strictPeriods_SL
  statement: (1 : Real) in (𝒮ℒ).strictPeriods
  proof: by simp

中文:
引理 one_mem_strictPeriods_SL
  结论: (1 : 实数) in (𝒮ℒ).strictPeriods
  证明: by simp
-/
lemma one_mem_strictPeriods_SL : (1 : Real) in (𝒮ℒ).strictPeriods := by simp

namespace ModularFormClass

variable [ModularFormClass F 𝒮ℒ k]

/--
theorem `cuspFunction_eqOn_const_of_nonpos_wt` / 定理 `cuspFunction_eqOn_const_of_nonpos_wt`

English:
theorem cuspFunction_eqOn_const_of_nonpos_wt
  given: (hk : k <= 0) (f : F)
  proof: by
  refine eq_const_of_exists_le (fun q hq => ?_) (exp_nonneg (-π)) ?_ (fun q hq => ?_)
  · exact (ModularFormClass.differentiableAt_cuspFunction f one_pos one_mem_strictPeriods_SL
      (mem_ball_zero_iff.mp hq)).differentiableWithinAt
  · simp [pi_pos]
  · simp only [Metric.mem_closedBall, dist_zero_right]
    rcases eq_or_ne q 0 with rfl | hq'
    · refine ⟨0, by simpa only [norm_zero] using exp_nonneg _, le_rfl⟩
    · obtain ⟨ξ, hξ, hξ₂⟩ := exists_one_half_le_im_and_norm_le hk f
        ⟨_, im_invQParam_pos_of_norm_lt_one Real.zero_lt_one (mem_ball_zero_iff.mp hq) hq'⟩
      exact ⟨_, norm_qParam_le_of_one_half_le_im hξ,
        by simpa [← SlashInvariantFormClass.eq_cuspFunction f _ one_mem_strictPeriods_SL
            one_ne_zero, qParam_right_inv one_ne_zero hq'] using hξ₂⟩

中文:
定理 cuspFunction_eqOn_const_of_nonpos_wt
  条件: (hk : k <= 0) (f : F)
  证明: by
  refine eq_const_of_exists_le (fun q hq => ?_) (exp_nonneg (-π)) ?_ (fun q hq => ?_)
  · exact (ModularFormClass.differentiableAt_cuspFunction f one_pos one_mem_strictPeriods_SL
      (mem_ball_zero_iff.mp hq)).differentiableWithinAt
  · simp [pi_pos]
  · simp only [Metric.mem_closedBall, dist_zero_right]
    rcases eq_or_ne q 0 with rfl | hq'
    · refine ⟨0, by simpa only [norm_zero] using exp_nonneg _, le_rfl⟩
    · obtain ⟨ξ, hξ, hξ₂⟩ := exists_one_half_le_im_and_norm_le hk f
        ⟨_, im_invQParam_pos_of_norm_lt_one Real.zero_lt_one (mem_ball_zero_iff.mp hq) hq'⟩
      exact ⟨_, norm_qParam_le_of_one_half_le_im hξ,
        by simpa [← SlashInvariantFormClass.eq_cuspFunction f _ one_mem_strictPeriods_SL
            one_ne_zero, qParam_right_inv one_ne_zero hq'] using hξ₂⟩
-/
private theorem cuspFunction_eqOn_const_of_nonpos_wt (hk : k <= 0) (f : F) :
    Set.EqOn (cuspFunction 1 f) (const Complex (cuspFunction 1 f 0)) (Metric.ball 0 1) := by
  refine eq_const_of_exists_le (fun q hq => ?_) (exp_nonneg (-π)) ?_ (fun q hq => ?_)
  · exact (ModularFormClass.differentiableAt_cuspFunction f one_pos one_mem_strictPeriods_SL
      (mem_ball_zero_iff.mp hq)).differentiableWithinAt
  · simp [pi_pos]
  · simp only [Metric.mem_closedBall, dist_zero_right]
    rcases eq_or_ne q 0 with rfl | hq'
    · refine ⟨0, by simpa only [norm_zero] using exp_nonneg _, le_rfl⟩
    · obtain ⟨ξ, hξ, hξ₂⟩ := exists_one_half_le_im_and_norm_le hk f
        ⟨_, im_invQParam_pos_of_norm_lt_one Real.zero_lt_one (mem_ball_zero_iff.mp hq) hq'⟩
      exact ⟨_, norm_qParam_le_of_one_half_le_im hξ,
        by simpa [← SlashInvariantFormClass.eq_cuspFunction f _ one_mem_strictPeriods_SL
            one_ne_zero, qParam_right_inv one_ne_zero hq'] using hξ₂⟩

/--
theorem `levelOne_nonpos_wt_const` / 定理 `levelOne_nonpos_wt_const`

English:
theorem levelOne_nonpos_wt_const
  given: (hk : k <= 0) (f : F)
  proof: by
  ext z
  have hQ : 𝕢 1 z in (Metric.ball 0 1) := by
    simpa using (norm_qParam_lt_iff zero_lt_one 0 z.1).mpr z.2
  simpa [← SlashInvariantFormClass.eq_cuspFunction f _ one_mem_strictPeriods_SL one_ne_zero]
    using cuspFunction_eqOn_const_of_nonpos_wt hk f hQ

中文:
定理 levelOne_nonpos_wt_const
  条件: (hk : k <= 0) (f : F)
  证明: by
  ext z
  have hQ : 𝕢 1 z in (Metric.ball 0 1) := by
    simpa using (norm_qParam_lt_iff zero_lt_one 0 z.1).mpr z.2
  simpa [← SlashInvariantFormClass.eq_cuspFunction f _ one_mem_strictPeriods_SL one_ne_zero]
    using cuspFunction_eqOn_const_of_nonpos_wt hk f hQ
-/
private theorem levelOne_nonpos_wt_const (hk : k <= 0) (f : F) :
    f = Function.const ℍ (cuspFunction 1 f 0) := by
  ext z
  have hQ : 𝕢 1 z in (Metric.ball 0 1) := by
    simpa using (norm_qParam_lt_iff zero_lt_one 0 z.1).mpr z.2
  simpa [← SlashInvariantFormClass.eq_cuspFunction f _ one_mem_strictPeriods_SL one_ne_zero]
    using cuspFunction_eqOn_const_of_nonpos_wt hk f hQ

/--
lemma `levelOne_neg_weight_eq_zero` / 引理 `levelOne_neg_weight_eq_zero`

English:
lemma levelOne_neg_weight_eq_zero
  given: (hk : k < 0) (f : F)
  statement: ⇑f = 0
  proof: by
  have hf := levelOne_nonpos_wt_const hk.le f
  rcases wt_eq_zero_of_eq_const k hf with rfl | hf₀
  · exact (lt_irrefl _ hk).elim
  · rw [hf, hf₀, const_zero]

中文:
引理 levelOne_neg_weight_eq_zero
  条件: (hk : k < 0) (f : F)
  结论: ⇑f = 0
  证明: by
  have hf := levelOne_nonpos_wt_const hk.le f
  rcases wt_eq_zero_of_eq_const k hf with rfl | hf₀
  · exact (lt_irrefl _ hk).elim
  · rw [hf, hf₀, const_zero]

Depends on / 依赖: const_zero, hk.le, levelOne_nonpos_wt_const, lt_irrefl, wt_eq_zero_of_eq_const
-/
lemma levelOne_neg_weight_eq_zero (hk : k < 0) (f : F) : ⇑f = 0 := by
  have hf := levelOne_nonpos_wt_const hk.le f
  rcases wt_eq_zero_of_eq_const k hf with rfl | hf₀
  · exact (lt_irrefl _ hk).elim
  · rw [hf, hf₀, const_zero]

/--
lemma `levelOne_weight_zero_const` / 引理 `levelOne_weight_zero_const`

English:
lemma levelOne_weight_zero_const
  given: [ModularFormClass F 𝒮ℒ 0] (f : F)
  proof: ⟨_, levelOne_nonpos_wt_const le_rfl f⟩

中文:
引理 levelOne_weight_zero_const
  条件: [模形式类 F 𝒮ℒ 0] (f : F)
  证明: ⟨_, levelOne_nonpos_wt_const le_rfl f⟩

Depends on / 依赖: le_rfl, levelOne_nonpos_wt_const
-/
lemma levelOne_weight_zero_const [ModularFormClass F 𝒮ℒ 0] (f : F) :
    exists c, ⇑f = Function.const _ c :=
  ⟨_, levelOne_nonpos_wt_const le_rfl f⟩

end ModularFormClass

/--
lemma `ModularForm.levelOne_weight_zero_rank_one` / 引理 `ModularForm.levelOne_weight_zero_rank_one`

English:
lemma ModularForm.levelOne_weight_zero_rank_one
  statement: Module.rank Complex (ModularForm 𝒮ℒ 0) = 1
  proof: by
  refine rank_eq_one (const 1) (by simp [DFunLike.ne_iff]) fun g => ?_
  obtain ⟨c', hc'⟩ := levelOne_weight_zero_const g
  aesop

中文:
引理 模形式.levelOne_weight_zero_rank_one
  结论: 模.rank 复形 (模形式 𝒮ℒ 0) = 1
  证明: by
  refine rank_eq_one (const 1) (by simp [DFunLike.ne_iff]) fun g => ?_
  obtain ⟨c', hc'⟩ := levelOne_weight_zero_const g
  aesop

Depends on / 依赖: DFunLike, DFunLike.ne_iff, levelOne_weight_zero_const, ne_iff, rank_eq_one
-/
lemma ModularForm.levelOne_weight_zero_rank_one : Module.rank Complex (ModularForm 𝒮ℒ 0) = 1 := by
  refine rank_eq_one (const 1) (by simp [DFunLike.ne_iff]) fun g => ?_
  obtain ⟨c', hc'⟩ := levelOne_weight_zero_const g
  aesop

/--
lemma `ModularForm.levelOne_neg_weight_rank_zero` / 引理 `ModularForm.levelOne_neg_weight_rank_zero`

English:
lemma ModularForm.levelOne_neg_weight_rank_zero
  given: (hk : k < 0)
  proof: by
  refine rank_eq_zero_iff.mpr fun f => ⟨_, one_ne_zero, ?_⟩
  simpa [← FunLike.coe_zero_iff] using levelOne_neg_weight_eq_zero hk f

中文:
引理 模形式.levelOne_neg_weight_rank_zero
  条件: (hk : k < 0)
  证明: by
  refine rank_eq_zero_iff.mpr fun f => ⟨_, one_ne_zero, ?_⟩
  simpa [← FunLike.coe_zero_iff] using levelOne_neg_weight_eq_zero hk f

Depends on / 依赖: FunLike, FunLike.coe_zero_iff, coe_zero_iff, levelOne_neg_weight_eq_zero, one_ne_zero, rank_eq_zero_iff, rank_eq_zero_iff.mpr
-/
lemma ModularForm.levelOne_neg_weight_rank_zero (hk : k < 0) :
    Module.rank Complex (ModularForm 𝒮ℒ k) = 0 := by
  refine rank_eq_zero_iff.mpr fun f => ⟨_, one_ne_zero, ?_⟩
  simpa [← FunLike.coe_zero_iff] using levelOne_neg_weight_eq_zero hk f
