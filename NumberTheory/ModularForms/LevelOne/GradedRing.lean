/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# The graded ring of level-1 modular forms

This file collects structural results about the graded ring `⨁ k, ModularForm 𝒮ℒ k` of
level-1 modular forms, beyond those that fall out of the dimension formula directly.

## Main results

* `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`: the pointwise identity
  `Δ = (E₄³ - E₆²) / 1728`.
* `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq_graded`: the same identity in the graded
  ring `⨁ k, ModularForm 𝒮ℒ k`.
-/

public noncomputable section

open UpperHalfPlane ModularForm ModularFormClass MatrixGroups EisensteinSeries

namespace ModularForm

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def E₄CubeSubE₆SqForm
  body: ModularForm.mcast (by decide) (E₄.pow 3) - ModularForm.mcast (by decide) (E₆.pow 2)

中文:
定义 noncomputable
  签名: def E₄CubeSubE₆SqForm
  定义体: ModularForm.mcast (by decide) (E₄.pow 3) - ModularForm.mcast (by decide) (E₆.pow 2)
-/
private noncomputable def E₄CubeSubE₆SqForm : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by decide) (E₄.pow 3) - ModularForm.mcast (by decide) (E₆.pow 2)

/--
lemma `E₄CubeSubE₆SqForm_apply` / 引理 `E₄CubeSubE₆SqForm_apply`

English:
lemma E₄CubeSubE₆SqForm_apply
  given: (z : ℍ)
  proof: by
  simp only [E₄CubeSubE₆SqForm, coe_mcast, coe_pow, sub_apply, Pi.pow_apply]

中文:
引理 E₄CubeSubE₆SqForm_apply
  条件: (z : ℍ)
  证明: by
  simp only [E₄CubeSubE₆SqForm, coe_mcast, coe_pow, sub_apply, Pi.pow_apply]
-/
private lemma E₄CubeSubE₆SqForm_apply (z : ℍ) :
    E₄CubeSubE₆SqForm z = E₄ z ^ 3 - E₆ z ^ 2 := by
  simp only [E₄CubeSubE₆SqForm, coe_mcast, coe_pow, sub_apply, Pi.pow_apply]

/--
lemma `E₄CubeSubE₆SqForm_qExpansion_eq` / 引理 `E₄CubeSubE₆SqForm_qExpansion_eq`

English:
lemma E₄CubeSubE₆SqForm_qExpansion_eq
  proof: by
  simp only [E₄CubeSubE₆SqForm, FunLike.coe_sub, coe_mcast,
    ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  ring

中文:
引理 E₄CubeSubE₆SqForm_qExpansion_eq
  证明: by
  simp only [E₄CubeSubE₆SqForm, FunLike.coe_sub, coe_mcast,
    ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  ring
-/
private lemma E₄CubeSubE₆SqForm_qExpansion_eq :
    qExpansion 1 E₄CubeSubE₆SqForm = qExpansion 1 E₄ * qExpansion 1 E₄ * qExpansion 1 E₄ -
      qExpansion 1 E₆ * qExpansion 1 E₆ := by
  simp only [E₄CubeSubE₆SqForm, FunLike.coe_sub, coe_mcast,
    ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  ring

/--
lemma `E₄CubeSubE₆SqForm_isCuspForm` / 引理 `E₄CubeSubE₆SqForm_isCuspForm`

English:
lemma E₄CubeSubE₆SqForm_isCuspForm
  statement: IsCuspForm E₄CubeSubE₆SqForm
  proof: by
  simp [isCuspForm_iff_coeffZero_eq_zero, E₄CubeSubE₆SqForm_qExpansion_eq,
    PowerSeries.coeff_mul, -PowerSeries.coeff_zero_eq_constantCoeff,
    E_qExpansion_coeff_zero _ ⟨2, rfl⟩, E_qExpansion_coeff_zero _ ⟨3, rfl⟩]

中文:
引理 E₄CubeSubE₆SqForm_isCuspForm
  结论: IsCuspForm E₄CubeSubE₆SqForm
  证明: by
  simp [isCuspForm_iff_coeffZero_eq_zero, E₄CubeSubE₆SqForm_qExpansion_eq,
    PowerSeries.coeff_mul, -PowerSeries.coeff_zero_eq_constantCoeff,
    E_qExpansion_coeff_zero _ ⟨2, rfl⟩, E_qExpansion_coeff_zero _ ⟨3, rfl⟩]
-/
private lemma E₄CubeSubE₆SqForm_isCuspForm : IsCuspForm E₄CubeSubE₆SqForm := by
  simp [isCuspForm_iff_coeffZero_eq_zero, E₄CubeSubE₆SqForm_qExpansion_eq,
    PowerSeries.coeff_mul, -PowerSeries.coeff_zero_eq_constantCoeff,
    E_qExpansion_coeff_zero _ ⟨2, rfl⟩, E_qExpansion_coeff_zero _ ⟨3, rfl⟩]

/--
lemma `E₄CubeSubE₆SqForm_qExpansion_coeff_one` / 引理 `E₄CubeSubE₆SqForm_qExpansion_coeff_one`

English:
lemma E₄CubeSubE₆SqForm_qExpansion_coeff_one
  proof: by
  rw [E₄CubeSubE₆SqForm_qExpansion_eq]
  norm_num [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₄_qExpansion_coeff_one,
    E₆_qExpansion_coeff_one, E_qExpansion_coeff_zero _ ⟨2, rfl⟩,
    E_qExpansion_coeff_zero _ ⟨3, rfl⟩]

中文:
引理 E₄CubeSubE₆SqForm_qExpansion_coeff_one
  证明: by
  rw [E₄CubeSubE₆SqForm_qExpansion_eq]
  norm_num [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₄_qExpansion_coeff_one,
    E₆_qExpansion_coeff_one, E_qExpansion_coeff_zero _ ⟨2, rfl⟩,
    E_qExpansion_coeff_zero _ ⟨3, rfl⟩]
-/
private lemma E₄CubeSubE₆SqForm_qExpansion_coeff_one :
    (qExpansion 1 E₄CubeSubE₆SqForm).coeff 1 = 1728 := by
  rw [E₄CubeSubE₆SqForm_qExpansion_eq]
  norm_num [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₄_qExpansion_coeff_one,
    E₆_qExpansion_coeff_one, E_qExpansion_coeff_zero _ ⟨2, rfl⟩,
    E_qExpansion_coeff_zero _ ⟨3, rfl⟩]

/--
theorem `discriminant_eq_E₄_cube_sub_E₆_sq` / 定理 `discriminant_eq_E₄_cube_sub_E₆_sq`

English:
theorem discriminant_eq_E₄_cube_sub_E₆_sq
  given: (z : ℍ)
  proof: by
  obtain ⟨g, hg⟩ := E₄CubeSubE₆SqForm_isCuspForm
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve g
  have hgE : (g : ℍ -> Complex) = E₄CubeSubE₆SqForm := congrArg DFunLike.coe hg
  have hc_eq : c = 1728 := by
    have hcΔ : (c • CuspForm.discriminant : ℍ -> Complex) = g := congrArg DFunLike.coe hc
    have hgΔ := ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c
      CuspForm.discriminant
    rw [hcΔ]; rw [hgE] at hgΔ
    simpa [PowerSeries.coeff_smul, discriminant_qExpansion_coeff_one,
      E₄CubeSubE₆SqForm_qExpansion_coeff_one] using (congr_arg (·.coeff 1) hgΔ).symm
  have h1728 : (1728 : Complex) * discriminant z = E₄ z ^ 3 - E₆ z ^ 2 := by
    rw [← hc_eq]; rw [show c * discriminant z = (c • CuspForm.discriminant) z from rfl]; rw [hc]; rw [congr_fun hgE z]; rw [E₄CubeSubE₆SqForm_apply]
  linear_combination h1728 / 1728

中文:
定理 discriminant_eq_E₄_cube_sub_E₆_sq
  条件: (z : ℍ)
  证明: by
  obtain ⟨g, hg⟩ := E₄CubeSubE₆SqForm_isCuspForm
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve g
  have hgE : (g : ℍ -> Complex) = E₄CubeSubE₆SqForm := congrArg DFunLike.coe hg
  have hc_eq : c = 1728 := by
    have hcΔ : (c • CuspForm.discriminant : ℍ -> Complex) = g := congrArg DFunLike.coe hc
    have hgΔ := ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c
      CuspForm.discriminant
    rw [hcΔ]; rw [hgE] at hgΔ
    simpa [PowerSeries.coeff_smul, discriminant_qExpansion_coeff_one,
      E₄CubeSubE₆SqForm_qExpansion_coeff_one] using (congr_arg (·.coeff 1) hgΔ).symm
  have h1728 : (1728 : Complex) * discriminant z = E₄ z ^ 3 - E₆ z ^ 2 := by
    rw [← hc_eq]; rw [show c * discriminant z = (c • CuspForm.discriminant) z from rfl]; rw [hc]; rw [congr_fun hgE z]; rw [E₄CubeSubE₆SqForm_apply]
  linear_combination h1728 / 1728

Depends on / 依赖: CuspForm, CuspForm.discriminant, CuspForm.exists_smul_discriminant_of_weight_eq_twelve, DFunLike, DFunLike.coe, ModularForm, ModularForm.qExpansion_smul, PowerSeries, PowerSeries.coeff_smul, coeff_smul, discriminant, discriminant_qExpansion_coeff_, exists_smul_discriminant_of_weight_eq_twelve, hc_eq, one_mem_strictPeriods_SL, one_pos, qExpansion_smul
-/
theorem discriminant_eq_E₄_cube_sub_E₆_sq (z : ℍ) :
    discriminant z = (E₄ z ^ 3 - E₆ z ^ 2) / 1728 := by
  obtain ⟨g, hg⟩ := E₄CubeSubE₆SqForm_isCuspForm
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve g
  have hgE : (g : ℍ -> Complex) = E₄CubeSubE₆SqForm := congrArg DFunLike.coe hg
  have hc_eq : c = 1728 := by
    have hcΔ : (c • CuspForm.discriminant : ℍ -> Complex) = g := congrArg DFunLike.coe hc
    have hgΔ := ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c
      CuspForm.discriminant
    rw [hcΔ]; rw [hgE] at hgΔ
    simpa [PowerSeries.coeff_smul, discriminant_qExpansion_coeff_one,
      E₄CubeSubE₆SqForm_qExpansion_coeff_one] using (congr_arg (·.coeff 1) hgΔ).symm
  have h1728 : (1728 : Complex) * discriminant z = E₄ z ^ 3 - E₆ z ^ 2 := by
    rw [← hc_eq]; rw [show c * discriminant z = (c • CuspForm.discriminant) z from rfl]; rw [hc]; rw [congr_fun hgE z]; rw [E₄CubeSubE₆SqForm_apply]
  linear_combination h1728 / 1728

/--
theorem `discriminant_eq_E₄_cube_sub_E₆_sq_graded` / 定理 `discriminant_eq_E₄_cube_sub_E₆_sq_graded`

English:
theorem discriminant_eq_E₄_cube_sub_E₆_sq_graded
  proof: by
  simp only [ModularForm.directSum_of_pow]
  change DirectSum.of (ModularForm 𝒮ℒ) 12 CuspForm.discriminant = (1 / 1728 : Complex) •
    (DirectSum.of (ModularForm 𝒮ℒ) 12 (E₄.pow 3) - DirectSum.of (ModularForm 𝒮ℒ) 12 (E₆.pow 2))
  rw [← map_sub (DirectSum.of (ModularForm 𝒮ℒ) 12)]; rw [← DirectSum.of_smul]
  congr 1
  ext z
  change ModularForm.discriminant z = (1 / 1728 : Complex) * (E₄ z ^ 3 - E₆ z ^ 2)
  grind [discriminant_eq_E₄_cube_sub_E₆_sq z]

中文:
定理 discriminant_eq_E₄_cube_sub_E₆_sq_graded
  证明: by
  simp only [ModularForm.directSum_of_pow]
  change DirectSum.of (ModularForm 𝒮ℒ) 12 CuspForm.discriminant = (1 / 1728 : Complex) •
    (DirectSum.of (ModularForm 𝒮ℒ) 12 (E₄.pow 3) - DirectSum.of (ModularForm 𝒮ℒ) 12 (E₆.pow 2))
  rw [← map_sub (DirectSum.of (ModularForm 𝒮ℒ) 12)]; rw [← DirectSum.of_smul]
  congr 1
  ext z
  change ModularForm.discriminant z = (1 / 1728 : Complex) * (E₄ z ^ 3 - E₆ z ^ 2)
  grind [discriminant_eq_E₄_cube_sub_E₆_sq z]

Depends on / 依赖: CuspForm, CuspForm.discriminant, DirectSum, DirectSum.of, DirectSum.of_smul, ModularForm, ModularForm.directSum_of_pow, ModularForm.discriminant, directSum_of_pow, discriminant, map_sub, of_smul
-/
theorem discriminant_eq_E₄_cube_sub_E₆_sq_graded :
    DirectSum.of (ModularForm 𝒮ℒ) 12 CuspForm.discriminant =
      (1 / 1728 : Complex) • (.of (ModularForm 𝒮ℒ) 4 E₄ ^ 3 - .of (ModularForm 𝒮ℒ) 6 E₆ ^ 2) := by
  simp only [ModularForm.directSum_of_pow]
  change DirectSum.of (ModularForm 𝒮ℒ) 12 CuspForm.discriminant = (1 / 1728 : Complex) •
    (DirectSum.of (ModularForm 𝒮ℒ) 12 (E₄.pow 3) - DirectSum.of (ModularForm 𝒮ℒ) 12 (E₆.pow 2))
  rw [← map_sub (DirectSum.of (ModularForm 𝒮ℒ) 12)]; rw [← DirectSum.of_smul]
  congr 1
  ext z
  change ModularForm.discriminant z = (1 / 1728 : Complex) * (E₄ z ^ 3 - E₆ z ^ 2)
  grind [discriminant_eq_E₄_cube_sub_E₆_sq z]

end ModularForm

end
