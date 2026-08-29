/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
public import Mathlib.Analysis.Normed.Module.Normalize

/-! # Unitary elements span C⋆-algebras

## Main results

+ `CStarAlgebra.exists_sum_four_unitary`: every element `x` in a unital C⋆-algebra is a linear
  combination of four unitary elements, and the norm of each coefficient does not exceed `‖x‖ / 2`.
+ `CStarAlgebra.span_unitary`: a unital C⋆-algebra is spanned by its unitary elements.
-/

@[expose] public section

variable {A : Type*} [CStarAlgebra A]

open scoped ComplexStarModule
open Complex

section Ordered

variable [PartialOrder A] [StarOrderedRing A]

/--
lemma `IsSelfAdjoint.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary` / 引理 `IsSelfAdjoint.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary`

English:
lemma IsSelfAdjoint.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary
  statement: (a : A) (ha : IsSelfAdjoint a)
  proof: by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · simp [Subsingleton.elim (a + I • CFC.sqrt (1 - a ^ 2)) 1, one_mem (unitary A)]
  have key : a + I • CFC.sqrt (1 - a ^ 2) = cfc (fun x : Complex => x.re + I * √(1 - x.re ^ 2)) a := by
    rw [CFC.sqrt_eq_real_sqrt (1 - a ^ 2) ?nonneg]
    case nonneg =>
      rwa [sub_nonneg, ← CStarAlgebra.norm_le_one_iff_of_nonneg (a ^ 2), sq, ha.norm_mul_self,
        sq_le_one_iff₀ (by positivity)]
    rw [cfc_add ..]; rw [cfc_const_mul ..]; rw [← cfc_real_eq_complex (fun x => x) ha]; rw [cfc_id' Real a]; rw [← cfc_real_eq_complex (fun x => √(1 - x ^ 2)) ha]; rw [cfcₙ_eq_cfc]; rw [cfc_comp' (√·) (1 - · ^ 2) a]; rw [cfc_sub ..]; rw [cfc_pow ..]; rw [cfc_const_one ..]; rw [cfc_id' ..]
  rw [key]; rw [cfc_unitary_iff ..]
  intro x hx
  rw [← starRingEnd_apply]; rw [← Complex.normSq_eq_conj_mul_self]; rw [Complex.normSq_ofReal_add_I_mul_sqrt_one_sub]; rw [Complex.ofReal_one]
.trans ha_norm exact spectrum.norm_le_norm_of_mem (ha.spectrumRestricts.apply_mem hx)

中文:
引理 IsSelfAdjoint.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary
  结论: (a : A) (ha : IsSelfAdjoint a)
  证明: by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · simp [Subsingleton.elim (a + I • CFC.sqrt (1 - a ^ 2)) 1, one_mem (unitary A)]
  have key : a + I • CFC.sqrt (1 - a ^ 2) = cfc (fun x : Complex => x.re + I * √(1 - x.re ^ 2)) a := by
    rw [CFC.sqrt_eq_real_sqrt (1 - a ^ 2) ?nonneg]
    case nonneg =>
      rwa [sub_nonneg, ← CStarAlgebra.norm_le_one_iff_of_nonneg (a ^ 2), sq, ha.norm_mul_self,
        sq_le_one_iff₀ (by positivity)]
    rw [cfc_add ..]; rw [cfc_const_mul ..]; rw [← cfc_real_eq_complex (fun x => x) ha]; rw [cfc_id' Real a]; rw [← cfc_real_eq_complex (fun x => √(1 - x ^ 2)) ha]; rw [cfcₙ_eq_cfc]; rw [cfc_comp' (√·) (1 - · ^ 2) a]; rw [cfc_sub ..]; rw [cfc_pow ..]; rw [cfc_const_one ..]; rw [cfc_id' ..]
  rw [key]; rw [cfc_unitary_iff ..]
  intro x hx
  rw [← starRingEnd_apply]; rw [← Complex.normSq_eq_conj_mul_self]; rw [Complex.normSq_ofReal_add_I_mul_sqrt_one_sub]; rw [Complex.ofReal_one]
.trans ha_norm exact spectrum.norm_le_norm_of_mem (ha.spectrumRestricts.apply_mem hx)

Depends on / 依赖: CFC.sqrt, CFC.sqrt_eq_real_sqrt, CStarAlgebra, CStarAlgebra.norm_le_one_iff_of_nonneg, Subsingleton, Subsingleton.elim, cfc_add, cfc_const_mul, cfc_real_eq_complex, ha.norm_mul_self, nonneg, norm_le_one_iff_of_nonneg, norm_mul_self, one_mem, sqrt_eq_real_sqrt, sub_nonneg, subsingleton_or_nontrivial, unitary, x.re
-/
lemma IsSelfAdjoint.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary (a : A) (ha : IsSelfAdjoint a)
    (ha_norm : ‖a‖ <= 1) : a + I • CFC.sqrt (1 - a ^ 2) in unitary A := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · simp [Subsingleton.elim (a + I • CFC.sqrt (1 - a ^ 2)) 1, one_mem (unitary A)]
  have key : a + I • CFC.sqrt (1 - a ^ 2) = cfc (fun x : Complex => x.re + I * √(1 - x.re ^ 2)) a := by
    rw [CFC.sqrt_eq_real_sqrt (1 - a ^ 2) ?nonneg]
    case nonneg =>
      rwa [sub_nonneg, ← CStarAlgebra.norm_le_one_iff_of_nonneg (a ^ 2), sq, ha.norm_mul_self,
        sq_le_one_iff₀ (by positivity)]
    rw [cfc_add ..]; rw [cfc_const_mul ..]; rw [← cfc_real_eq_complex (fun x => x) ha]; rw [cfc_id' Real a]; rw [← cfc_real_eq_complex (fun x => √(1 - x ^ 2)) ha]; rw [cfcₙ_eq_cfc]; rw [cfc_comp' (√·) (1 - · ^ 2) a]; rw [cfc_sub ..]; rw [cfc_pow ..]; rw [cfc_const_one ..]; rw [cfc_id' ..]
  rw [key]; rw [cfc_unitary_iff ..]
  intro x hx
  rw [← starRingEnd_apply]; rw [← Complex.normSq_eq_conj_mul_self]; rw [Complex.normSq_ofReal_add_I_mul_sqrt_one_sub]; rw [Complex.ofReal_one]
.trans ha_norm exact spectrum.norm_le_norm_of_mem (ha.spectrumRestricts.apply_mem hx)

/-- For `a` selfadjoint with `‖a‖ ≤ 1`, this is the unitary `a + I • √(1 - a ^ 2)`. -/
@[simps]
/--
Definition of `selfAdjoint.unitarySelfAddISMul` / `selfAdjoint.unitarySelfAddISMul` 的定义

English:
definition selfAdjoint.unitarySelfAddISMul
  signature: (a : selfAdjoint A) (ha_norm : ‖a‖ <= 1)
  body: ⟨(a : A) + I • CFC.sqrt (1 - a ^ 2 : A), a.2.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary _ ha_norm⟩

中文:
定义 selfAdjoint.unitarySelfAddISMul
  签名: (a : selfAdjoint A) (ha_norm : ‖a‖ <= 1)
  定义体: ⟨(a : A) + I • CFC.sqrt (1 - a ^ 2 : A), a.2.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary _ ha_norm⟩

Depends on / 依赖: CFC.sqrt, ha_norm, self_add_I_smul_cfcSqrt_sub_sq_mem_unitary
-/
noncomputable def selfAdjoint.unitarySelfAddISMul (a : selfAdjoint A) (ha_norm : ‖a‖ <= 1) :
    unitary A :=
  ⟨(a : A) + I • CFC.sqrt (1 - a ^ 2 : A), a.2.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary _ ha_norm⟩

/--
lemma `selfAdjoint.star_coe_unitarySelfAddISMul` / 引理 `selfAdjoint.star_coe_unitarySelfAddISMul`

English:
lemma selfAdjoint.star_coe_unitarySelfAddISMul
  given: (a : selfAdjoint A) (ha_norm : ‖a‖ <= 1)
  proof: by
  simp [IsSelfAdjoint.star_eq, ← sub_eq_add_neg, (CFC.sqrt_nonneg (1 - a ^ 2 : A)).isSelfAdjoint]

中文:
引理 selfAdjoint.star_coe_unitarySelfAddISMul
  条件: (a : selfAdjoint A) (ha_norm : ‖a‖ <= 1)
  证明: by
  simp [IsSelfAdjoint.star_eq, ← sub_eq_add_neg, (CFC.sqrt_nonneg (1 - a ^ 2 : A)).isSelfAdjoint]

Depends on / 依赖: CFC.sqrt_nonneg, IsSelfAdjoint, IsSelfAdjoint.star_eq, isSelfAdjoint, sqrt_nonneg, star_eq, sub_eq_add_neg
-/
lemma selfAdjoint.star_coe_unitarySelfAddISMul (a : selfAdjoint A) (ha_norm : ‖a‖ <= 1) :
    (star (unitarySelfAddISMul a ha_norm) : A) = a - I • CFC.sqrt (1 - a ^ 2 : A) := by
  simp [IsSelfAdjoint.star_eq, ← sub_eq_add_neg, (CFC.sqrt_nonneg (1 - a ^ 2 : A)).isSelfAdjoint]

/--
lemma `selfAdjoint.realPart_unitarySelfAddISMul` / 引理 `selfAdjoint.realPart_unitarySelfAddISMul`

English:
lemma selfAdjoint.realPart_unitarySelfAddISMul
  given: (a : selfAdjoint A) (ha_norm : ‖a‖ <= 1)
  proof: by
  simp [IsSelfAdjoint.imaginaryPart (x := CFC.sqrt (1 - a ^ 2 : A)) (by cfc_tac)]

中文:
引理 selfAdjoint.realPart_unitarySelfAddISMul
  条件: (a : selfAdjoint A) (ha_norm : ‖a‖ <= 1)
  证明: by
  simp [IsSelfAdjoint.imaginaryPart (x := CFC.sqrt (1 - a ^ 2 : A)) (by cfc_tac)]

Depends on / 依赖: CFC.sqrt, IsSelfAdjoint, IsSelfAdjoint.imaginaryPart, cfc_tac, imaginaryPart
-/
lemma selfAdjoint.realPart_unitarySelfAddISMul (a : selfAdjoint A) (ha_norm : ‖a‖ <= 1) :
    ℜ (unitarySelfAddISMul a ha_norm : A) = a := by
  simp [IsSelfAdjoint.imaginaryPart (x := CFC.sqrt (1 - a ^ 2 : A)) (by cfc_tac)]

/--
lemma `CStarAlgebra.norm_smul_two_inv_smul_add_four_unitary` / 引理 `CStarAlgebra.norm_smul_two_inv_smul_add_four_unitary`

English:
lemma CStarAlgebra.norm_smul_two_inv_smul_add_four_unitary
  given: (x : A) (hx : x != 0)
  proof: selfAdjoint.unitarySelfAddISMul (ℜ (‖x‖⁻¹ • x))
      (by simpa [norm_smul, inv_mul_le_one₀ (norm_pos_iff.2 hx)] using! realPart.norm_le x)
    let u₂ : unitary A := selfAdjoint.unitarySelfAddISMul (ℑ (‖x‖⁻¹ • x))
      (by simpa [norm_smul, inv_mul_le_one₀ (norm_pos_iff.2 hx)] using! imaginaryPart.norm_le x)
    x = ‖x‖ • (2⁻¹ : Real) • (u₁ + star u₁ + I • (u₂ + star u₂) : A) := by
  intro u₁ u₂
  rw [smul_add]; rw [smul_comm _ I]; rw [Unitary.coe_star]; rw [Unitary.coe_star]; rw [← realPart_apply_coe (u₁ : A)]; rw [← realPart_apply_coe (u₂ : A)]
  simpa only [u₁, u₂, selfAdjoint.realPart_unitarySelfAddISMul, realPart_add_I_smul_imaginaryPart]
using! Eq.symm NormedSpace.norm_smul_normalize x

中文:
引理 CStar代数.norm_smul_two_inv_smul_add_four_unitary
  条件: (x : A) (hx : x != 0)
  证明: selfAdjoint.unitarySelfAddISMul (ℜ (‖x‖⁻¹ • x))
      (by simpa [norm_smul, inv_mul_le_one₀ (norm_pos_iff.2 hx)] using! realPart.norm_le x)
    let u₂ : unitary A := selfAdjoint.unitarySelfAddISMul (ℑ (‖x‖⁻¹ • x))
      (by simpa [norm_smul, inv_mul_le_one₀ (norm_pos_iff.2 hx)] using! imaginaryPart.norm_le x)
    x = ‖x‖ • (2⁻¹ : Real) • (u₁ + star u₁ + I • (u₂ + star u₂) : A) := by
  intro u₁ u₂
  rw [smul_add]; rw [smul_comm _ I]; rw [Unitary.coe_star]; rw [Unitary.coe_star]; rw [← realPart_apply_coe (u₁ : A)]; rw [← realPart_apply_coe (u₂ : A)]
  simpa only [u₁, u₂, selfAdjoint.realPart_unitarySelfAddISMul, realPart_add_I_smul_imaginaryPart]
using! Eq.symm NormedSpace.norm_smul_normalize x

Depends on / 依赖: selfAdjoint, selfAdjoint.unitarySelfAddISMul, unitarySelfAddISMul
-/
lemma CStarAlgebra.norm_smul_two_inv_smul_add_four_unitary (x : A) (hx : x != 0) :
    let u₁ : unitary A := selfAdjoint.unitarySelfAddISMul (ℜ (‖x‖⁻¹ • x))
      (by simpa [norm_smul, inv_mul_le_one₀ (norm_pos_iff.2 hx)] using! realPart.norm_le x)
    let u₂ : unitary A := selfAdjoint.unitarySelfAddISMul (ℑ (‖x‖⁻¹ • x))
      (by simpa [norm_smul, inv_mul_le_one₀ (norm_pos_iff.2 hx)] using! imaginaryPart.norm_le x)
    x = ‖x‖ • (2⁻¹ : Real) • (u₁ + star u₁ + I • (u₂ + star u₂) : A) := by
  intro u₁ u₂
  rw [smul_add]; rw [smul_comm _ I]; rw [Unitary.coe_star]; rw [Unitary.coe_star]; rw [← realPart_apply_coe (u₁ : A)]; rw [← realPart_apply_coe (u₂ : A)]
  simpa only [u₁, u₂, selfAdjoint.realPart_unitarySelfAddISMul, realPart_add_I_smul_imaginaryPart]
using! Eq.symm NormedSpace.norm_smul_normalize x

end Ordered

/--
lemma `CStarAlgebra.exists_sum_four_unitary` / 引理 `CStarAlgebra.exists_sum_four_unitary`

English:
lemma CStarAlgebra.exists_sum_four_unitary
  given: (x : A)
  proof: by
  let _ := CStarAlgebra.spectralOrder
  let _ := CStarAlgebra.spectralOrderedRing
  obtain (rfl | hx) := eq_or_ne x 0
  · exact ⟨![1, -1, 1, -1], 0, by simp⟩
  · have := norm_smul_two_inv_smul_add_four_unitary x hx
    extract_lets u₁ u₂ at this
    use ![u₁, star u₁, u₂, star u₂], ![‖x‖ * 2⁻¹, ‖x‖ * 2⁻¹, ‖x‖ * 2⁻¹ * I, ‖x‖ * 2⁻¹ * I]
    constructor
    · conv_lhs => rw [this]
      simp [Fin.sum_univ_four, ← Complex.coe_smul]
      module
    · intro i
      fin_cases i
      all_goals simp [div_eq_mul_inv]

中文:
引理 CStar代数.存在_sum_four_unitary
  条件: (x : A)
  证明: by
  let _ := CStarAlgebra.spectralOrder
  let _ := CStarAlgebra.spectralOrderedRing
  obtain (rfl | hx) := eq_or_ne x 0
  · exact ⟨![1, -1, 1, -1], 0, by simp⟩
  · have := norm_smul_two_inv_smul_add_four_unitary x hx
    extract_lets u₁ u₂ at this
    use ![u₁, star u₁, u₂, star u₂], ![‖x‖ * 2⁻¹, ‖x‖ * 2⁻¹, ‖x‖ * 2⁻¹ * I, ‖x‖ * 2⁻¹ * I]
    constructor
    · conv_lhs => rw [this]
      simp [Fin.sum_univ_four, ← Complex.coe_smul]
      module
    · intro i
      fin_cases i
      all_goals simp [div_eq_mul_inv]

Depends on / 依赖: CStarAlgebra, CStarAlgebra.spectralOrder, CStarAlgebra.spectralOrderedRing, Complex.coe_smul, Fin.sum_univ_four, all_goals, coe_smul, conv_lhs, div_eq_mul_inv, eq_or_ne, extract_lets, fin_cases, module, norm_smul_two_inv_smul_add_four_unitary, spectralOrder, spectralOrderedRing, sum_univ_four
-/
lemma CStarAlgebra.exists_sum_four_unitary (x : A) :
    exists u : Fin 4 -> unitary A, exists c : Fin 4 -> Complex, x = ∑ i, c i • (u i : A) ∧ forall i, ‖c i‖ <= ‖x‖ / 2 := by
  let _ := CStarAlgebra.spectralOrder
  let _ := CStarAlgebra.spectralOrderedRing
  obtain (rfl | hx) := eq_or_ne x 0
  · exact ⟨![1, -1, 1, -1], 0, by simp⟩
  · have := norm_smul_two_inv_smul_add_four_unitary x hx
    extract_lets u₁ u₂ at this
    use ![u₁, star u₁, u₂, star u₂], ![‖x‖ * 2⁻¹, ‖x‖ * 2⁻¹, ‖x‖ * 2⁻¹ * I, ‖x‖ * 2⁻¹ * I]
    constructor
    · conv_lhs => rw [this]
      simp [Fin.sum_univ_four, ← Complex.coe_smul]
      module
    · intro i
      fin_cases i
      all_goals simp [div_eq_mul_inv]

variable (A) in
open Submodule in
/--
lemma `CStarAlgebra.span_unitary` / 引理 `CStarAlgebra.span_unitary`

English:
lemma CStarAlgebra.span_unitary
  statement: span Complex (unitary A : Set A) = ⊤
  proof: by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨u, c, rfl, h⟩ := CStarAlgebra.exists_sum_four_unitary x
  exact sum_mem fun i _ => smul_mem _ _ (subset_span (u i).2)

中文:
引理 CStar代数.span_unitary
  结论: span 复形 (unitary A : 集合 A) = ⊤
  证明: by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨u, c, rfl, h⟩ := CStarAlgebra.exists_sum_four_unitary x
  exact sum_mem fun i _ => smul_mem _ _ (subset_span (u i).2)

Depends on / 依赖: CStarAlgebra, CStarAlgebra.exists_sum_four_unitary, eq_top_iff, exists_sum_four_unitary, smul_mem, subset_span, sum_mem
-/
lemma CStarAlgebra.span_unitary : span Complex (unitary A : Set A) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨u, c, rfl, h⟩ := CStarAlgebra.exists_sum_four_unitary x
  exact sum_mem fun i _ => smul_mem _ _ (subset_span (u i).2)
