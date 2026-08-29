/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Nat
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics

/-!
# The Dedekind zeta function of a number field

In this file, we define and prove results about the Dedekind zeta function of a number field.

## Main definitions and results

* `NumberField.dedekindZeta`: the Dedekind zeta function.
* `NumberField.dedekindZeta_residue`: the value of the residue at `s = 1` of the Dedekind
  zeta function.
* `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`: **Dirichlet class number formula**
  computation of the residue of the Dedekind zeta function at `s = 1`, see Chap. 7 of
  [D. Marcus, *Number Fields*][marcus1977number]

## TODO

Generalize the construction of the Dedekind zeta function.
-/

@[expose] public section

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

open Filter Ideal NumberField.InfinitePlace NumberField.Units Topology nonZeroDivisors

namespace NumberField

open scoped Real

/--
Definition of `dedekindZeta` / `dedekindZeta` 的定义

English:
definition dedekindZeta
  signature: (s : Complex)
  body: LSeries (fun n => Nat.card {I : Ideal (𝓞 K) // absNorm I = n}) s

中文:
定义 dedekindZeta
  签名: (s : Complex)
  定义体: LSeries (fun n => Nat.card {I : Ideal (𝓞 K) // absNorm I = n}) s

Depends on / 依赖: LSeries, Nat.card, absNorm
-/
def dedekindZeta (s : Complex) :=
  LSeries (fun n => Nat.card {I : Ideal (𝓞 K) // absNorm I = n}) s

/--
Definition of `dedekindZeta_residue` / `dedekindZeta_residue` 的定义

English:
definition dedekindZeta_residue
  signature: : Real
  body: (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
    (torsionOrder K * Real.sqrt |discr K|)

中文:
定义 dedekindZeta_residue
  签名: : 实数
  定义体: (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
    (torsionOrder K * Real.sqrt |discr K|)

Depends on / 依赖: Real.sqrt, classNumber, nrComplexPlaces, nrRealPlaces, regulator, torsionOrder
-/
def dedekindZeta_residue : Real :=
  (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
    (torsionOrder K * Real.sqrt |discr K|)

/--
theorem `dedekindZeta_residue_def` / 定理 `dedekindZeta_residue_def`

English:
theorem dedekindZeta_residue_def
  proof: rfl

中文:
定理 dedekindZeta_residue_def
  证明: rfl
-/
theorem dedekindZeta_residue_def :
    dedekindZeta_residue K =
      (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
      (torsionOrder K * Real.sqrt |discr K|) := rfl

/--
theorem `dedekindZeta_residue_pos` / 定理 `dedekindZeta_residue_pos`

English:
theorem dedekindZeta_residue_pos
  statement: 0 < dedekindZeta_residue K
  proof: by
  refine div_pos ?_ ?_
  · exact mul_pos (mul_pos (by positivity) (regulator_pos K)) (Nat.cast_pos.mpr (classNumber_pos K))
· exact mul_pos (Nat.cast_pos.mpr (torsionOrder_pos K))
Real.sqrt_pos_of_pos abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))

中文:
定理 dedekindZeta_residue_pos
  结论: 0 < dedekindZeta_residue K
  证明: by
  refine div_pos ?_ ?_
  · exact mul_pos (mul_pos (by positivity) (regulator_pos K)) (Nat.cast_pos.mpr (classNumber_pos K))
· exact mul_pos (Nat.cast_pos.mpr (torsionOrder_pos K))
Real.sqrt_pos_of_pos abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))

Depends on / 依赖: Int.cast_ne_zero.mpr, Nat.cast_pos.mpr, Real.sqrt_pos_of_pos, abs_pos, abs_pos.mpr, cast_ne_zero, cast_pos, classNumber_pos, discr_ne_zero, div_pos, mul_pos, regulator_pos, sqrt_pos_of_pos, torsionOrder_pos
-/
theorem dedekindZeta_residue_pos : 0 < dedekindZeta_residue K := by
  refine div_pos ?_ ?_
  · exact mul_pos (mul_pos (by positivity) (regulator_pos K)) (Nat.cast_pos.mpr (classNumber_pos K))
· exact mul_pos (Nat.cast_pos.mpr (torsionOrder_pos K))
Real.sqrt_pos_of_pos abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))

/--
theorem `dedekindZeta_residue_ne_zero` / 定理 `dedekindZeta_residue_ne_zero`

English:
theorem dedekindZeta_residue_ne_zero
  statement: dedekindZeta_residue K != 0
  proof: (dedekindZeta_residue_pos K).ne'

中文:
定理 dedekindZeta_residue_ne_zero
  结论: dedekindZeta_residue K != 0
  证明: (dedekindZeta_residue_pos K).ne'

Depends on / 依赖: dedekindZeta_residue_pos
-/
theorem dedekindZeta_residue_ne_zero : dedekindZeta_residue K != 0 :=
  (dedekindZeta_residue_pos K).ne'

/--
theorem `tendsto_sub_one_mul_dedekindZeta_nhdsGT` / 定理 `tendsto_sub_one_mul_dedekindZeta_nhdsGT`

English:
theorem tendsto_sub_one_mul_dedekindZeta_nhdsGT
  proof: by
  refine LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg _ ?_
    (fun _ => Nat.cast_nonneg _)
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_

中文:
定理 tendsto_sub_one_mul_dedekindZeta_nhdsGT
  证明: by
  refine LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg _ ?_
    (fun _ => Nat.cast_nonneg _)
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_

Depends on / 依赖: Finset, Finset.Icc, Finset.Icc_succ_left_eq_Ioc, Finset.Ioc, Function, Function.comp_apply, Icc_succ_left_eq_Ioc, Ideal.absNorm_e, Ideal.tendsto_norm_le_div_atTop, LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg, Nat.card, Nat.cast_le, Nat.cast_nonneg, Nat.cast_sum, absNorm, absNorm_e, add_left_inj, card_norm_le_eq_card_norm_le_add_one, cast_le, cast_nonneg
-/
theorem tendsto_sub_one_mul_dedekindZeta_nhdsGT :
    Tendsto (fun s : Real => (s - 1) * dedekindZeta K s) (𝓝[>] 1) (𝓝 (dedekindZeta_residue K)) := by
  refine LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg _ ?_
    (fun _ => Nat.cast_nonneg _)
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1]; rw [← card_norm_le_eq_card_norm_le_add_one]; rw [show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _]; rw [show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ => finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

end NumberField
