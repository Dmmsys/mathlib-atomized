/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Deligne's archimedean Gamma-factors

In the theory of L-series one frequently encounters the following functions (of a complex variable
`s`) introduced in Deligne's landmark paper *Valeurs de fonctions L et périodes d'intégrales*:

$$ \Gamma_{\mathbb{R}}(s) = \pi ^ {-s / 2} \Gamma (s / 2) $$

and

$$ \Gamma_{\mathbb{C}}(s) = 2 (2 \pi) ^ {-s} \Gamma (s). $$

These are the factors that need to be included in the Dedekind zeta function of a number field
for each real, resp. complex, infinite place.

(Note that these are *not* the same as Mathlib's `Real.Gamma` vs. `Complex.Gamma`; Deligne's
functions both take a complex variable as input.)

This file defines these functions, and proves some elementary properties, including a reflection
formula which is an important input in functional equations of (un-completed) Dirichlet L-functions.
-/

@[expose] public section

open Filter Topology Asymptotics Real Set MeasureTheory
open Complex

namespace Complex

/--
Definition of `GammaReal` / `GammaReal` 的定义

English:
definition GammaReal
  signature: (s : Complex)
  body: π ^ (-s / 2) * Gamma (s / 2)

中文:
定义 Gamma实数
  签名: (s : 复形)
  定义体: π ^ (-s / 2) * Gamma (s / 2)
-/
noncomputable def GammaReal (s : Complex) := π ^ (-s / 2) * Gamma (s / 2)

/--
lemma `GammaReal_def` / 引理 `GammaReal_def`

English:
lemma GammaReal_def
  given: (s : Complex)
  statement: GammaReal s = π ^ (-s / 2) * Gamma (s / 2)
  proof: rfl

中文:
引理 Gamma实数_def
  条件: (s : 复形)
  结论: Gamma实数 s = π ^ (-s / 2) * Gamma (s / 2)
  证明: rfl
-/
lemma GammaReal_def (s : Complex) : GammaReal s = π ^ (-s / 2) * Gamma (s / 2) := rfl

/--
Definition of `GammaComplex` / `GammaComplex` 的定义

English:
definition GammaComplex
  signature: (s : Complex)
  body: 2 * (2 * π) ^ (-s) * Gamma s

中文:
定义 GammaComplex
  签名: (s : 复形)
  定义体: 2 * (2 * π) ^ (-s) * Gamma s
-/
noncomputable def GammaComplex (s : Complex) := 2 * (2 * π) ^ (-s) * Gamma s

/--
lemma `GammaComplex_def` / 引理 `GammaComplex_def`

English:
lemma GammaComplex_def
  given: (s : Complex)
  statement: GammaComplex s = 2 * (2 * π) ^ (-s) * Gamma s
  proof: rfl

中文:
引理 GammaComplex_def
  条件: (s : 复形)
  结论: GammaComplex s = 2 * (2 * π) ^ (-s) * Gamma s
  证明: rfl
-/
lemma GammaComplex_def (s : Complex) : GammaComplex s = 2 * (2 * π) ^ (-s) * Gamma s := rfl

/--
lemma `GammaReal_add_two` / 引理 `GammaReal_add_two`

English:
lemma GammaReal_add_two
  given: {s : Complex} (hs : s != 0)
  statement: GammaReal (s + 2) = GammaReal s * s / 2 / π
  proof: by
  rw [GammaReal_def]; rw [GammaReal_def]; rw [neg_div]; rw [add_div]; rw [neg_add]; rw [div_self two_ne_zero]; rw [Gamma_add_one _ (div_ne_zero hs two_ne_zero)]; rw [cpow_add _ _ (ofReal_ne_zero.mpr pi_ne_zero)]; rw [cpow_neg_one]
  field_simp

中文:
引理 Gamma实数_add_two
  条件: {s : 复形} (hs : s != 0)
  结论: Gamma实数 (s + 2) = Gamma实数 s * s / 2 / π
  证明: by
  rw [GammaReal_def]; rw [GammaReal_def]; rw [neg_div]; rw [add_div]; rw [neg_add]; rw [div_self two_ne_zero]; rw [Gamma_add_one _ (div_ne_zero hs two_ne_zero)]; rw [cpow_add _ _ (ofReal_ne_zero.mpr pi_ne_zero)]; rw [cpow_neg_one]
  field_simp

Depends on / 依赖: GammaReal_def, Gamma_add_one, add_div, cpow_add, cpow_neg_one, div_ne_zero, div_self, neg_add, neg_div, ofReal_ne_zero, ofReal_ne_zero.mpr, pi_ne_zero, two_ne_zero
-/
lemma GammaReal_add_two {s : Complex} (hs : s != 0) : GammaReal (s + 2) = GammaReal s * s / 2 / π := by
  rw [GammaReal_def]; rw [GammaReal_def]; rw [neg_div]; rw [add_div]; rw [neg_add]; rw [div_self two_ne_zero]; rw [Gamma_add_one _ (div_ne_zero hs two_ne_zero)]; rw [cpow_add _ _ (ofReal_ne_zero.mpr pi_ne_zero)]; rw [cpow_neg_one]
  field_simp

/--
lemma `GammaComplex_add_one` / 引理 `GammaComplex_add_one`

English:
lemma GammaComplex_add_one
  given: {s : Complex} (hs : s != 0)
  statement: GammaComplex (s + 1) = GammaComplex s * s / 2 / π
  proof: by
  rw [GammaComplex_def]; rw [GammaComplex_def]; rw [Gamma_add_one _ hs]; rw [neg_add]; rw [cpow_add _ _ (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr pi_ne_zero))]; rw [cpow_neg_one]
  ring

中文:
引理 GammaComplex_add_one
  条件: {s : 复形} (hs : s != 0)
  结论: GammaComplex (s + 1) = GammaComplex s * s / 2 / π
  证明: by
  rw [GammaComplex_def]; rw [GammaComplex_def]; rw [Gamma_add_one _ hs]; rw [neg_add]; rw [cpow_add _ _ (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr pi_ne_zero))]; rw [cpow_neg_one]
  ring

Depends on / 依赖: GammaComplex_def, Gamma_add_one, cpow_add, cpow_neg_one, mul_ne_zero, neg_add, ofReal_ne_zero, ofReal_ne_zero.mpr, pi_ne_zero, two_ne_zero
-/
lemma GammaComplex_add_one {s : Complex} (hs : s != 0) : GammaComplex (s + 1) = GammaComplex s * s / 2 / π := by
  rw [GammaComplex_def]; rw [GammaComplex_def]; rw [Gamma_add_one _ hs]; rw [neg_add]; rw [cpow_add _ _ (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr pi_ne_zero))]; rw [cpow_neg_one]
  ring

/--
lemma `GammaReal_ne_zero_of_re_pos` / 引理 `GammaReal_ne_zero_of_re_pos`

English:
lemma GammaReal_ne_zero_of_re_pos
  given: {s : Complex} (hs : 0 < re s)
  statement: GammaReal s != 0
  proof: by
  apply mul_ne_zero
  · simp [pi_ne_zero]
  · apply Gamma_ne_zero_of_re_pos
    rw [div_ofNat_re]
    exact div_pos hs two_pos

中文:
引理 Gamma实数_ne_zero_of_re_pos
  条件: {s : 复形} (hs : 0 < re s)
  结论: Gamma实数 s != 0
  证明: by
  apply mul_ne_zero
  · simp [pi_ne_zero]
  · apply Gamma_ne_zero_of_re_pos
    rw [div_ofNat_re]
    exact div_pos hs two_pos

Depends on / 依赖: Gamma_ne_zero_of_re_pos, div_ofNat_re, div_pos, mul_ne_zero, pi_ne_zero, two_pos
-/
lemma GammaReal_ne_zero_of_re_pos {s : Complex} (hs : 0 < re s) : GammaReal s != 0 := by
  apply mul_ne_zero
  · simp [pi_ne_zero]
  · apply Gamma_ne_zero_of_re_pos
    rw [div_ofNat_re]
    exact div_pos hs two_pos

/--
lemma `GammaReal_eq_zero_iff` / 引理 `GammaReal_eq_zero_iff`

English:
lemma GammaReal_eq_zero_iff
  given: {s : Complex}
  statement: GammaReal s = 0 ↔ exists n : Nat, s = -(2 * n)
  proof: by
  simp [GammaReal_def, Complex.Gamma_eq_zero_iff, pi_ne_zero, div_eq_iff (two_ne_zero' Complex), mul_comm]

@[simp]

中文:
引理 Gamma实数_eq_zero_iff
  条件: {s : 复形}
  结论: Gamma实数 s = 0 ↔ 存在 n : 自然数, s = -(2 * n)
  证明: by
  simp [GammaReal_def, Complex.Gamma_eq_zero_iff, pi_ne_zero, div_eq_iff (two_ne_zero' Complex), mul_comm]

@[simp]

Depends on / 依赖: Complex.Gamma_eq_zero_iff, GammaReal_def, Gamma_eq_zero_iff, div_eq_iff, mul_comm, pi_ne_zero, two_ne_zero
-/
lemma GammaReal_eq_zero_iff {s : Complex} : GammaReal s = 0 ↔ exists n : Nat, s = -(2 * n) := by
  simp [GammaReal_def, Complex.Gamma_eq_zero_iff, pi_ne_zero, div_eq_iff (two_ne_zero' Complex), mul_comm]

@[simp]
/--
lemma `GammaReal_one` / 引理 `GammaReal_one`

English:
lemma GammaReal_one
  statement: GammaReal 1 = 1
  proof: by
  rw [GammaReal_def]; rw [Complex.Gamma_one_half_eq]
  simp [neg_div, cpow_neg, pi_ne_zero]

@[simp]

中文:
引理 Gamma实数_one
  结论: Gamma实数 1 = 1
  证明: by
  rw [GammaReal_def]; rw [Complex.Gamma_one_half_eq]
  simp [neg_div, cpow_neg, pi_ne_zero]

@[simp]

Depends on / 依赖: Complex.Gamma_one_half_eq, GammaReal_def, Gamma_one_half_eq, cpow_neg, neg_div, pi_ne_zero
-/
lemma GammaReal_one : GammaReal 1 = 1 := by
  rw [GammaReal_def]; rw [Complex.Gamma_one_half_eq]
  simp [neg_div, cpow_neg, pi_ne_zero]

@[simp]
/--
lemma `GammaComplex_one` / 引理 `GammaComplex_one`

English:
lemma GammaComplex_one
  statement: GammaComplex 1 = 1 / π
  proof: by
  rw [GammaComplex_def]; rw [cpow_neg_one]; rw [Complex.Gamma_one]
  ring

中文:
引理 GammaComplex_one
  结论: GammaComplex 1 = 1 / π
  证明: by
  rw [GammaComplex_def]; rw [cpow_neg_one]; rw [Complex.Gamma_one]
  ring

Depends on / 依赖: Complex.Gamma_one, GammaComplex_def, Gamma_one, cpow_neg_one
-/
lemma GammaComplex_one : GammaComplex 1 = 1 / π := by
  rw [GammaComplex_def]; rw [cpow_neg_one]; rw [Complex.Gamma_one]
  ring

section analyticity

@[fun_prop]
/--
lemma `differentiable_GammaReal_inv` / 引理 `differentiable_GammaReal_inv`

English:
lemma differentiable_GammaReal_inv
  statement: Differentiable Complex (fun s => (GammaReal s)⁻¹)
  proof: by
  conv => enter [2, s]; rw [GammaReal, mul_inv]
  refine Differentiable.mul (fun s => .inv ?_ (by simp)) ?_
  · refine ((differentiableAt_id.neg.div_const (2 : Complex)).const_cpow ?_)
    exact Or.inl (ofReal_ne_zero.mpr pi_ne_zero)
  · exact differentiable_one_div_Gamma.comp (differentiable_id.

中文:
引理 differentiable_Gamma实数_inv
  结论: 可微 复形 (fun s => (Gamma实数 s)⁻¹)
  证明: by
  conv => enter [2, s]; rw [GammaReal, mul_inv]
  refine Differentiable.mul (fun s => .inv ?_ (by simp)) ?_
  · refine ((differentiableAt_id.neg.div_const (2 : Complex)).const_cpow ?_)
    exact Or.inl (ofReal_ne_zero.mpr pi_ne_zero)
  · exact differentiable_one_div_Gamma.comp (differentiable_id.

Depends on / 依赖: Differentiable, Differentiable.mul, GammaReal, Or.inl, const_cpow, differentiableAt_id, differentiableAt_id.neg.div_const, differentiable_id, differentiable_id.div_const, differentiable_one_div_Gamma, differentiable_one_div_Gamma.comp, div_const, mul_inv, ofReal_ne_zero, ofReal_ne_zero.mpr, pi_ne_zero
-/
lemma differentiable_GammaReal_inv : Differentiable Complex (fun s => (GammaReal s)⁻¹) := by
  conv => enter [2, s]; rw [GammaReal, mul_inv]
  refine Differentiable.mul (fun s => .inv ?_ (by simp)) ?_
  · refine ((differentiableAt_id.neg.div_const (2 : Complex)).const_cpow ?_)
    exact Or.inl (ofReal_ne_zero.mpr pi_ne_zero)
  · exact differentiable_one_div_Gamma.comp (differentiable_id.div_const _)

@[fun_prop]
/--
lemma `differentiable_GammaComplex_inv` / 引理 `differentiable_GammaComplex_inv`

English:
lemma differentiable_GammaComplex_inv
  statement: Differentiable Complex (fun s => (GammaComplex s)⁻¹)
  proof: by
  conv => enter [2, s]; rw [GammaComplex, mul_inv]
  refine (Differentiable.inv ?_ (by simp)).mul differentiable_one_div_Gamma
  exact (differentiable_neg.const_cpow (by simp)).const_mul _

中文:
引理 differentiable_GammaComplex_inv
  结论: 可微 复形 (fun s => (GammaComplex s)⁻¹)
  证明: by
  conv => enter [2, s]; rw [GammaComplex, mul_inv]
  refine (Differentiable.inv ?_ (by simp)).mul differentiable_one_div_Gamma
  exact (differentiable_neg.const_cpow (by simp)).const_mul _

Depends on / 依赖: Differentiable, Differentiable.inv, GammaComplex, const_cpow, const_mul, differentiable_neg, differentiable_neg.const_cpow, differentiable_one_div_Gamma, mul_inv
-/
lemma differentiable_GammaComplex_inv : Differentiable Complex (fun s => (GammaComplex s)⁻¹) := by
  conv => enter [2, s]; rw [GammaComplex, mul_inv]
  refine (Differentiable.inv ?_ (by simp)).mul differentiable_one_div_Gamma
  exact (differentiable_neg.const_cpow (by simp)).const_mul _

/--
lemma `GammaReal_residue_zero` / 引理 `GammaReal_residue_zero`

English:
lemma GammaReal_residue_zero
  statement: Tendsto (fun s => s * GammaReal s) (𝓝[!=] 0) (𝓝 2)
  proof: by
  have h : Tendsto (fun z : Complex => z / 2 * Gamma (z / 2)) (𝓝[!=] 0) (𝓝 1) := by
    refine tendsto_self_mul_Gamma_nhds_zero.comp ?_
    rw [tendsto_nhdsWithin_iff]; rw [(by simp : 𝓝 (0 : Complex) = 𝓝 (0 / 2))]
    exact ⟨(tendsto_id.div_const _).mono_left nhdsWithin_le_nhds,
      eventually_

中文:
引理 Gamma实数_residue_zero
  结论: 收敛 (fun s => s * Gamma实数 s) (𝓝[!=] 0) (𝓝 2)
  证明: by
  have h : Tendsto (fun z : Complex => z / 2 * Gamma (z / 2)) (𝓝[!=] 0) (𝓝 1) := by
    refine tendsto_self_mul_Gamma_nhds_zero.comp ?_
    rw [tendsto_nhdsWithin_iff]; rw [(by simp : 𝓝 (0 : Complex) = 𝓝 (0 / 2))]
    exact ⟨(tendsto_id.div_const _).mono_left nhdsWithin_le_nhds,
      eventually_

Depends on / 依赖: Tendsto, div_const, div_ne_zero, eventually_of_mem, mono_left, nhdsWithin_le_nhds, self_mem_nhdsWithin, tendsto_id, tendsto_id.div_const, tendsto_nhdsWithin_iff, tendsto_self_mul_Gamma_nhds_zero, tendsto_self_mul_Gamma_nhds_zero.comp, two_ne_zero
-/
lemma GammaReal_residue_zero : Tendsto (fun s => s * GammaReal s) (𝓝[!=] 0) (𝓝 2) := by
  have h : Tendsto (fun z : Complex => z / 2 * Gamma (z / 2)) (𝓝[!=] 0) (𝓝 1) := by
    refine tendsto_self_mul_Gamma_nhds_zero.comp ?_
    rw [tendsto_nhdsWithin_iff]; rw [(by simp : 𝓝 (0 : Complex) = 𝓝 (0 / 2))]
    exact ⟨(tendsto_id.div_const _).mono_left nhdsWithin_le_nhds,
      eventually_of_mem self_mem_nhdsWithin fun x hx => div_ne_zero hx two_ne_zero⟩
  have h' : Tendsto (fun s : Complex => 2 * (π : Complex) ^ (-s / 2)) (𝓝[!=] 0) (𝓝 2) := by
    rw [(by simp : 𝓝 2 = 𝓝 (2 * (π : Complex) ^ (-(0 : Complex) / 2)))]
    refine Tendsto.mono_left (ContinuousAt.tendsto ?_) nhdsWithin_le_nhds
    exact continuousAt_const.mul ((continuousAt_const_cpow (ofReal_ne_zero.mpr pi_ne_zero)).comp
      (by fun_prop))
  convert! mul_one (2 : Complex) ▸ (h'.mul h) using 2 with z
  rw [GammaReal]
  ring_nf

end analyticity

section reflection

/--
lemma `GammaReal_mul_GammaReal_add_one` / 引理 `GammaReal_mul_GammaReal_add_one`

English:
lemma GammaReal_mul_GammaReal_add_one
  given: (s : Complex)
  statement: GammaReal s * GammaReal (s + 1) = GammaComplex s
  proof: by
  simp only [GammaReal_def, GammaComplex_def]
  calc
  _ = (π ^ (-s / 2) * π ^ (-(s + 1) / 2)) * (Gamma (s / 2) * Gamma (s / 2 + 1 / 2)) := by ring_nf
  _ = 2 ^ (1 - s) * (π ^ (-1 / 2 - s) * π ^ (1 / 2 : Complex)) * Gamma s := by
    rw [← cpow_add _ _ (ofReal_ne_zero.mpr pi_ne_zero)]; rw [Comple

中文:
引理 Gamma实数_mul_Gamma实数_add_one
  条件: (s : 复形)
  结论: Gamma实数 s * Gamma实数 (s + 1) = GammaComplex s
  证明: by
  simp only [GammaReal_def, GammaComplex_def]
  calc
  _ = (π ^ (-s / 2) * π ^ (-(s + 1) / 2)) * (Gamma (s / 2) * Gamma (s / 2 + 1 / 2)) := by ring_nf
  _ = 2 ^ (1 - s) * (π ^ (-1 / 2 - s) * π ^ (1 / 2 : Complex)) * Gamma s := by
    rw [← cpow_add _ _ (ofReal_ne_zero.mpr pi_ne_zero)]; rw [Comple

Depends on / 依赖: Complex.Gamma_mul_Gamma_add_half, GammaComplex_def, GammaReal_def, Gamma_mul_Gamma_add_half, cpow_add, ofReal_cpow, ofReal_div, ofReal_ne_zero, ofReal_ne_zero.mpr, ofReal_ofNat, ofReal_one, pi_ne_zero, pi_pos, pi_pos.le, ring_nf, sqrt_eq_rpow, sub_eq_add_neg
-/
lemma GammaReal_mul_GammaReal_add_one (s : Complex) : GammaReal s * GammaReal (s + 1) = GammaComplex s := by
  simp only [GammaReal_def, GammaComplex_def]
  calc
  _ = (π ^ (-s / 2) * π ^ (-(s + 1) / 2)) * (Gamma (s / 2) * Gamma (s / 2 + 1 / 2)) := by ring_nf
  _ = 2 ^ (1 - s) * (π ^ (-1 / 2 - s) * π ^ (1 / 2 : Complex)) * Gamma s := by
    rw [← cpow_add _ _ (ofReal_ne_zero.mpr pi_ne_zero)]; rw [Complex.Gamma_mul_Gamma_add_half]; rw [sqrt_eq_rpow]; rw [ofReal_cpow pi_pos.le]; rw [ofReal_div]; rw [ofReal_one]; rw [ofReal_ofNat]
    ring_nf
  _ = 2 * ((2 : Real) ^ (-s) * π ^ (-s)) * Gamma s := by
    rw [sub_eq_add_neg]; rw [cpow_add _ _ two_ne_zero]; rw [cpow_one]; rw [← cpow_add _ _ (ofReal_ne_zero.mpr pi_ne_zero)]; rw [ofReal_ofNat]
    ring_nf
  _ = 2 * (2 * π) ^ (-s) * Gamma s := by
    rw [← mul_cpow_ofReal_nonneg two_pos.le pi_pos.le]; rw [ofReal_ofNat]

/--
lemma `GammaReal_one_sub_mul_GammaReal_one_add` / 引理 `GammaReal_one_sub_mul_GammaReal_one_add`

English:
lemma GammaReal_one_sub_mul_GammaReal_one_add
  given: (s : Complex)
  proof: calc GammaReal (1 - s) * GammaReal (1 + s)
  _ = (π ^ ((s - 1) / 2) * π ^ ((-1 - s) / 2)) *
        (Gamma ((1 - s) / 2) * Gamma (1 - (1 - s) / 2)) := by
    simp only [GammaReal_def]
    ring_nf
  _ = (π ^ ((s - 1) / 2) * π ^ ((-1 - s) / 2) * π ^ (1 : Complex)) / sin (π / 2 - π * s / 2) := by
    r

中文:
引理 Gamma实数_one_sub_mul_Gamma实数_one_add
  条件: (s : 复形)
  证明: calc GammaReal (1 - s) * GammaReal (1 + s)
  _ = (π ^ ((s - 1) / 2) * π ^ ((-1 - s) / 2)) *
        (Gamma ((1 - s) / 2) * Gamma (1 - (1 - s) / 2)) := by
    simp only [GammaReal_def]
    ring_nf
  _ = (π ^ ((s - 1) / 2) * π ^ ((-1 - s) / 2) * π ^ (1 : Complex)) / sin (π / 2 - π * s / 2) := by
    r

Depends on / 依赖: Complex.Gamma_mul_Gamma_one_sub, Complex.sin_pi_div_two_sub, GammaReal, GammaReal_def, Gamma_mul_Gamma_one_sub, cpow_add, cpow_one, cpow_zero, ofReal_ne_zero, ofReal_ne_zero.mpr, one_mul, pi_ne_zero, ring_nf, simp_rw, sin_pi_div_two_sub
-/
lemma GammaReal_one_sub_mul_GammaReal_one_add (s : Complex) :
    GammaReal (1 - s) * GammaReal (1 + s) = (cos (π * s / 2))⁻¹ :=
  calc GammaReal (1 - s) * GammaReal (1 + s)
  _ = (π ^ ((s - 1) / 2) * π ^ ((-1 - s) / 2)) *
        (Gamma ((1 - s) / 2) * Gamma (1 - (1 - s) / 2)) := by
    simp only [GammaReal_def]
    ring_nf
  _ = (π ^ ((s - 1) / 2) * π ^ ((-1 - s) / 2) * π ^ (1 : Complex)) / sin (π / 2 - π * s / 2) := by
    rw [Complex.Gamma_mul_Gamma_one_sub]; rw [cpow_one]
    ring_nf
  _ = _ := by
    simp_rw [← cpow_add _ _ (ofReal_ne_zero.mpr pi_ne_zero),
      Complex.sin_pi_div_two_sub]
    ring_nf
    rw [cpow_zero]; rw [one_mul]

/--
lemma `GammaReal_div_GammaReal_one_sub` / 引理 `GammaReal_div_GammaReal_one_sub`

English:
lemma GammaReal_div_GammaReal_one_sub
  given: {s : Complex} (hs : forall (n : Nat), s != -(2 * n + 1))
  proof: by
  have : GammaReal (s + 1) != 0 := by
    simpa only [Ne, GammaReal_eq_zero_iff, not_exists, ← eq_sub_iff_add_eq,
      sub_eq_add_neg, ← neg_add]
  calc GammaReal s / GammaReal (1 - s)
  _ = (GammaReal s * GammaReal (s + 1)) / (GammaReal (1 - s) * GammaReal (1 + s)) := by
    rw [add_comm 1 s]; 

中文:
引理 Gamma实数_div_Gamma实数_one_sub
  条件: {s : 复形} (hs : 对任意 (n : 自然数), s != -(2 * n + 1))
  证明: by
  have : GammaReal (s + 1) != 0 := by
    simpa only [Ne, GammaReal_eq_zero_iff, not_exists, ← eq_sub_iff_add_eq,
      sub_eq_add_neg, ← neg_add]
  calc GammaReal s / GammaReal (1 - s)
  _ = (GammaReal s * GammaReal (s + 1)) / (GammaReal (1 - s) * GammaReal (1 + s)) := by
    rw [add_comm 1 s]; 

Depends on / 依赖: GammaReal, GammaReal_eq_zero_iff, GammaReal_one_sub_mul_GammaReal_one_add, add_comm, div_div, eq_sub_iff_add_eq, mul_comm, neg_add, not_exists, sub_eq_add_neg
-/
lemma GammaReal_div_GammaReal_one_sub {s : Complex} (hs : forall (n : Nat), s != -(2 * n + 1)) :
    GammaReal s / GammaReal (1 - s) = GammaComplex s * cos (π * s / 2) := by
  have : GammaReal (s + 1) != 0 := by
    simpa only [Ne, GammaReal_eq_zero_iff, not_exists, ← eq_sub_iff_add_eq,
      sub_eq_add_neg, ← neg_add]
  calc GammaReal s / GammaReal (1 - s)
  _ = (GammaReal s * GammaReal (s + 1)) / (GammaReal (1 - s) * GammaReal (1 + s)) := by
    rw [add_comm 1 s]; rw [mul_comm (GammaReal (1 - s)) (GammaReal (s + 1))]; rw [← div_div]; rw [mul_div_cancel_right₀ _ this]
  _ = (2 * (2 * π) ^ (-s) * Gamma s) / ((cos (π * s / 2))⁻¹) := by
    rw [GammaReal_one_sub_mul_GammaReal_one_add]; rw [GammaReal_mul_GammaReal_add_one]; rw [GammaComplex_def]
  _ = _ := by rw [GammaComplex_def, div_eq_mul_inv, inv_inv]

/--
lemma `inv_GammaReal_one_sub` / 引理 `inv_GammaReal_one_sub`

English:
lemma inv_GammaReal_one_sub
  given: {s : Complex} (hs : forall (n : Nat), s != -n)
  proof: by
  have h1 : GammaReal s != 0 := by
    rw [Ne]; rw [GammaReal_eq_zero_iff]; rw [not_exists]
    intro n h
    specialize hs (2 * n)
    simp_all
  have h2 : forall (n : Nat), s != -(2 * ↑n + 1) := by
    intro n h
    specialize hs (2 * n + 1)
    simp_all
  rw [← GammaReal_div_GammaReal_one_sub 

中文:
引理 inv_Gamma实数_one_sub
  条件: {s : 复形} (hs : 对任意 (n : 自然数), s != -n)
  证明: by
  have h1 : GammaReal s != 0 := by
    rw [Ne]; rw [GammaReal_eq_zero_iff]; rw [not_exists]
    intro n h
    specialize hs (2 * n)
    simp_all
  have h2 : forall (n : Nat), s != -(2 * ↑n + 1) := by
    intro n h
    specialize hs (2 * n + 1)
    simp_all
  rw [← GammaReal_div_GammaReal_one_sub 

Depends on / 依赖: GammaReal, GammaReal_div_GammaReal_one_sub, GammaReal_eq_zero_iff, div_eq_mul_inv, div_right_comm, div_self, not_exists, one_div, specialize
-/
lemma inv_GammaReal_one_sub {s : Complex} (hs : forall (n : Nat), s != -n) :
    (GammaReal (1 - s))⁻¹ = GammaComplex s * cos (π * s / 2) * (GammaReal s)⁻¹ := by
  have h1 : GammaReal s != 0 := by
    rw [Ne]; rw [GammaReal_eq_zero_iff]; rw [not_exists]
    intro n h
    specialize hs (2 * n)
    simp_all
  have h2 : forall (n : Nat), s != -(2 * ↑n + 1) := by
    intro n h
    specialize hs (2 * n + 1)
    simp_all
  rw [← GammaReal_div_GammaReal_one_sub h2]; rw [← div_eq_mul_inv]; rw [div_right_comm]; rw [div_self h1]; rw [one_div]

/--
lemma `inv_GammaReal_two_sub` / 引理 `inv_GammaReal_two_sub`

English:
lemma inv_GammaReal_two_sub
  given: {s : Complex} (hs : forall (n : Nat), s != -n)
  proof: by
  by_cases h : s = 1
  · rw [h, (by ring : 2 - 1 = (1 : Complex)), GammaReal_one, GammaReal,
    neg_div, (by simp : (1 + 1) / 2 = (1 : Complex)), Complex.Gamma_one, GammaComplex_one,
    mul_one, Complex.sin_pi_div_two, mul_one, cpow_neg_one, mul_one, inv_inv,
    div_mul_cancel₀ _ (ofReal_ne_ze

中文:
引理 inv_Gamma实数_two_sub
  条件: {s : 复形} (hs : 对任意 (n : 自然数), s != -n)
  证明: by
  by_cases h : s = 1
  · rw [h, (by ring : 2 - 1 = (1 : Complex)), GammaReal_one, GammaReal,
    neg_div, (by simp : (1 + 1) / 2 = (1 : Complex)), Complex.Gamma_one, GammaComplex_one,
    mul_one, Complex.sin_pi_div_two, mul_one, cpow_neg_one, mul_one, inv_inv,
    div_mul_cancel₀ _ (ofReal_ne_ze

Depends on / 依赖: Complex.Gamma_one, Complex.sin_pi_div_two, GammaComplex_one, GammaReal, GammaReal_one, Gamma_one, Nat.cast_zero, cast_zero, convert, cpow_neg_one, inv_inv, inv_one, mul_one, neg_div, neg_zero, ofReal_ne_zero, ofReal_ne_zero.mpr, pi_ne_zero, sin_pi_div_two, sub_eq_iff_eq_add
-/
lemma inv_GammaReal_two_sub {s : Complex} (hs : forall (n : Nat), s != -n) :
    (GammaReal (2 - s))⁻¹ = GammaComplex s * sin (π * s / 2) * (GammaReal (s + 1))⁻¹ := by
  by_cases h : s = 1
  · rw [h, (by ring : 2 - 1 = (1 : Complex)), GammaReal_one, GammaReal,
    neg_div, (by simp : (1 + 1) / 2 = (1 : Complex)), Complex.Gamma_one, GammaComplex_one,
    mul_one, Complex.sin_pi_div_two, mul_one, cpow_neg_one, mul_one, inv_inv,
    div_mul_cancel₀ _ (ofReal_ne_zero.mpr pi_ne_zero), inv_one]
  rw [← Ne]; rw [← sub_ne_zero] at h
  have h' (n : Nat) : s - 1 != -n := by
    rcases n with - | m
    · rwa [Nat.cast_zero, neg_zero]
    · rw [Ne, sub_eq_iff_eq_add]
      convert! hs m using 2
      push_cast
      ring
  rw [(by ring : 2 - s = 1 - (s - 1))]; rw [inv_GammaReal_one_sub h']; rw [(by rw [sub_add_cancel] : GammaComplex s = GammaComplex (s - 1 + 1)), GammaComplex_add_one h,
    (by ring : s + 1 = (s - 1) + 2), GammaReal_add_two h, mul_sub, sub_div, mul_one,
      Complex.cos_sub_pi_div_two]
  simp_rw [mul_div_assoc, mul_inv]
  generalize (GammaReal (s - 1))⁻¹ = A
  field

end reflection

end Complex
