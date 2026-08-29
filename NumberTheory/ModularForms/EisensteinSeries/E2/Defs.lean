/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.ConditionalInt

/-!
# Eisenstein Series E2

We define the Eisenstein series `E2` of weight `2` and level `1` as a limit of partial sums
over non-symmetric intervals.

-/

open UpperHalfPlane hiding I

open ModularForm EisensteinSeries Matrix.SpecialLinearGroup Filter Complex MatrixGroups
  SummationFilter Real

@[expose] public noncomputable section

namespace EisensteinSeries

/--
Definition of `e2Summand` / `e2Summand` 的定义

English:
definition e2Summand
  signature: (m : Int) (z : ℍ)
  body: ∑' n, eisSummand 2 ![m, n] z

中文:
定义 e2Summand
  签名: (m : 整数) (z : ℍ)
  定义体: ∑' n, eisSummand 2 ![m, n] z

Depends on / 依赖: eisSummand
-/
def e2Summand (m : Int) (z : ℍ) : Complex := ∑' n, eisSummand 2 ![m, n] z

/--
lemma `e2Summand_summable` / 引理 `e2Summand_summable`

English:
lemma e2Summand_summable
  given: (m : Int) (z : ℍ)
  statement: Summable (fun n => eisSummand 2 ![m, n] z)
  proof: by
  apply (linear_right_summable z m (k := 2) (by grind)).congr
  simp [eisSummand]

@[simp]

中文:
引理 e2Summand_summable
  条件: (m : 整数) (z : ℍ)
  结论: Summable (fun n => eisSummand 2 ![m, n] z)
  证明: by
  apply (linear_right_summable z m (k := 2) (by grind)).congr
  simp [eisSummand]

@[simp]

Depends on / 依赖: eisSummand, linear_right_summable
-/
lemma e2Summand_summable (m : Int) (z : ℍ) : Summable (fun n => eisSummand 2 ![m, n] z) := by
  apply (linear_right_summable z m (k := 2) (by grind)).congr
  simp [eisSummand]

@[simp]
/--
lemma `e2Summand_zero_eq_two_riemannZeta_two` / 引理 `e2Summand_zero_eq_two_riemannZeta_two`

English:
lemma e2Summand_zero_eq_two_riemannZeta_two
  given: (z : ℍ)
  statement: e2Summand 0 z = 2 * riemannZeta 2
  proof: by
  simpa [e2Summand, eisSummand] using!
    (two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (k := 2) (by grind) (by simp)).symm

中文:
引理 e2Summand_zero_eq_two_riemannZeta_two
  条件: (z : ℍ)
  结论: e2Summand 0 z = 2 * riemannZeta 2
  证明: by
  simpa [e2Summand, eisSummand] using!
    (two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (k := 2) (by grind) (by simp)).symm

Depends on / 依赖: e2Summand, eisSummand, two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even
-/
lemma e2Summand_zero_eq_two_riemannZeta_two (z : ℍ) : e2Summand 0 z = 2 * riemannZeta 2 := by
  simpa [e2Summand, eisSummand] using!
    (two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (k := 2) (by grind) (by simp)).symm

/--
lemma `e2Summand_even` / 引理 `e2Summand_even`

English:
lemma e2Summand_even
  given: (z : ℍ)
  statement: (e2Summand · z).Even
  proof: by
  intro n
  simp only [e2Summand, ← tsum_comp_neg (fun a => eisSummand 2 ![-n, a] z)]
  apply tsum_congr (fun b => ?_)
  simp only [eisSummand, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.reduceNeg, zpow_neg, Int.cast_neg, neg_mul, inv_inj]
  rw_mod_ca

中文:
引理 e2Summand_even
  条件: (z : ℍ)
  结论: (e2Summand · z).Even
  证明: by
  intro n
  simp only [e2Summand, ← tsum_comp_neg (fun a => eisSummand 2 ![-n, a] z)]
  apply tsum_congr (fun b => ?_)
  simp only [eisSummand, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.reduceNeg, zpow_neg, Int.cast_neg, neg_mul, inv_inj]
  rw_mod_ca

Depends on / 依赖: Fin.isValue, Int.cast_neg, Int.reduceNeg, Matrix, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val_zero, cast_neg, cons_val_fin_one, cons_val_one, cons_val_zero, e2Summand, eisSummand, inv_inj, isValue, neg_mul, reduceNeg, rw_mod_cast, tsum_comp_neg, tsum_congr
-/
lemma e2Summand_even (z : ℍ) : (e2Summand · z).Even := by
  intro n
  simp only [e2Summand, ← tsum_comp_neg (fun a => eisSummand 2 ![-n, a] z)]
  apply tsum_congr (fun b => ?_)
  simp only [eisSummand, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.reduceNeg, zpow_neg, Int.cast_neg, neg_mul, inv_inj]
  rw_mod_cast [Int.cast_neg]
  ring

/--
Definition of `G2` / `G2` 的定义

English:
definition G2
  signature: : ℍ -> Complex
  body: fun z => ∑'[symmetricIcc Int] m, e2Summand m z

中文:
定义 G2
  签名: : ℍ -> Complex
  定义体: fun z => ∑'[symmetricIcc Int] m, e2Summand m z

Depends on / 依赖: e2Summand, symmetricIcc
-/
def G2 : ℍ -> Complex := fun z => ∑'[symmetricIcc Int] m, e2Summand m z

/--
Definition of `E2` / `E2` 的定义

English:
definition E2
  signature: : ℍ -> Complex
  body: (1 / (2 * riemannZeta 2)) • G2

中文:
定义 E2
  签名: : ℍ -> Complex
  定义体: (1 / (2 * riemannZeta 2)) • G2

Depends on / 依赖: riemannZeta
-/
def E2 : ℍ -> Complex := (1 / (2 * riemannZeta 2)) • G2

/--
Definition of `D2` / `D2` 的定义

English:
definition D2
  signature: (γ : SL(2, Int))
  body: fun z => (2 * π * I * γ 1 0) / (denom γ z)

@[simp]

中文:
定义 D2
  签名: (γ : SL(2, 整数))
  定义体: fun z => (2 * π * I * γ 1 0) / (denom γ z)

@[simp]
-/
def D2 (γ : SL(2, Int)) : ℍ -> Complex := fun z => (2 * π * I * γ 1 0) / (denom γ z)

@[simp]
/--
lemma `D2_one` / 引理 `D2_one`

English:
lemma D2_one
  statement: D2 1 = 0
  proof: by
  ext z
  simp [D2]

中文:
引理 D2_one
  结论: D2 1 = 0
  证明: by
  ext z
  simp [D2]
-/
lemma D2_one : D2 1 = 0 := by
  ext z
  simp [D2]

/--
lemma `denom_aux` / 引理 `denom_aux`

English:
lemma denom_aux
  given: (A B : SL(2, Int)) (z : ℍ)
  statement: ((A * B) 1 0) * (denom B z) =
  proof: by
  have h0 := Matrix.two_mul_expl A.1 B.1
  simp only [Fin.isValue, coe_mul, h0.2.2.1, Int.cast_add, Int.cast_mul, ModularGroup.denom_apply,
    Matrix.det_fin_two B.1, Int.cast_sub, ← map_mul, h0.2.2.2]
  ring

local notation "φ" => Matrix.SpecialLinearGroup.map (Int.castRingHom Real)

中文:
引理 denom_aux
  条件: (A B : SL(2, 整数)) (z : ℍ)
  结论: ((A * B) 1 0) * (denom B z) =
  证明: by
  have h0 := Matrix.two_mul_expl A.1 B.1
  simp only [Fin.isValue, coe_mul, h0.2.2.1, Int.cast_add, Int.cast_mul, ModularGroup.denom_apply,
    Matrix.det_fin_two B.1, Int.cast_sub, ← map_mul, h0.2.2.2]
  ring

local notation "φ" => Matrix.SpecialLinearGroup.map (Int.castRingHom Real)
-/
private lemma denom_aux (A B : SL(2, Int)) (z : ℍ) : ((A * B) 1 0) * (denom B z) =
    (A 1 0) * B.1.det + (B 1 0) * denom (A * B) z := by
  have h0 := Matrix.two_mul_expl A.1 B.1
  simp only [Fin.isValue, coe_mul, h0.2.2.1, Int.cast_add, Int.cast_mul, ModularGroup.denom_apply,
    Matrix.det_fin_two B.1, Int.cast_sub, ← map_mul, h0.2.2.2]
  ring

local notation "φ" => Matrix.SpecialLinearGroup.map (Int.castRingHom Real)
/--
lemma `D2_mul` / 引理 `D2_mul`

English:
lemma D2_mul
  given: (A B : SL(2, Int))
  statement: D2 (A * B) = (D2 A) ∣[(2 : Int)] B + D2 B
  proof: by
  ext z
  simp only [D2, mul_assoc, coe_mul, map_mul, ← mul_div, SL_slash_def,
    ModularGroup.sl_moeb, Int.reduceNeg, zpow_neg, Pi.add_apply, ← mul_add, mul_eq_mul_left_iff,
    I_ne_zero, or_false, ofReal_eq_zero, pi_ne_zero, OfNat.ofNat_ne_zero]
  have hd : (A.1 * B.1) 1 0 * denom (φ B) z - B

中文:
引理 D2_mul
  条件: (A B : SL(2, 整数))
  结论: D2 (A * B) = (D2 A) ∣[(2 : 整数)] B + D2 B
  证明: by
  ext z
  simp only [D2, mul_assoc, coe_mul, map_mul, ← mul_div, SL_slash_def,
    ModularGroup.sl_moeb, Int.reduceNeg, zpow_neg, Pi.add_apply, ← mul_add, mul_eq_mul_left_iff,
    I_ne_zero, or_false, ofReal_eq_zero, pi_ne_zero, OfNat.ofNat_ne_zero]
  have hd : (A.1 * B.1) 1 0 * denom (φ B) z - B

Depends on / 依赖: I_ne_zero, Int.reduceNeg, ModularGroup, ModularGroup.sl_moeb, OfNat.ofNat_ne_zero, Pi.add_apply, SL_slash_def, add_apply, coe_mul, denom_aux, intros, map_mul, mul_add, mul_assoc, mul_div, mul_eq_mul_left_iff, ofNat_ne_zero, ofReal_eq_zero, or_false, pi_ne_zero
-/
lemma D2_mul (A B : SL(2, Int)) : D2 (A * B) = (D2 A) ∣[(2 : Int)] B + D2 B := by
  ext z
  simp only [D2, mul_assoc, coe_mul, map_mul, ← mul_div, SL_slash_def,
    ModularGroup.sl_moeb, Int.reduceNeg, zpow_neg, Pi.add_apply, ← mul_add, mul_eq_mul_left_iff,
    I_ne_zero, or_false, ofReal_eq_zero, pi_ne_zero, OfNat.ofNat_ne_zero]
  have hd : (A.1 * B.1) 1 0 * denom (φ B) z - B 1 0 * denom (φ A * φ B) z = A 1 0 := by
    simpa [sub_eq_iff_eq_add] using denom_aux A B z
  have : denom A (num B z / denom B z) = denom A ↑(B • z) := by
    simp [specialLinearGroup_apply, denom, num]
  rw [(by intros; field_simp : forall {a b c d f e : Complex} (he : e != 0)]; rw [a / b =
    c / d * (e ^ (2 : Int))⁻¹ + f / e ↔ a * e ^ 2 / b = c / d + e * f) (denom_ne_zero B z)]
  simp only [pow_two, ← mul_assoc, denom_cocycle A B z.im_ne_zero, this,
    ModularGroup.sl_moeb, ← hd]
  field_simp [denom_ne_zero A (toGL (φ B) • z)]
  ring

/--
lemma `D2_inv` / 引理 `D2_inv`

English:
lemma D2_inv
  given: (A)
  statement: (D2 A) ∣[(2 : Int)] A⁻¹ = -D2 A⁻¹
  proof: by
  simpa [eq_neg_iff_add_eq_zero] using (D2_mul A A⁻¹).symm

中文:
引理 D2_inv
  条件: (A)
  结论: (D2 A) ∣[(2 : 整数)] A⁻¹ = -D2 A⁻¹
  证明: by
  simpa [eq_neg_iff_add_eq_zero] using (D2_mul A A⁻¹).symm

Depends on / 依赖: D2_mul, eq_neg_iff_add_eq_zero
-/
lemma D2_inv (A) : (D2 A) ∣[(2 : Int)] A⁻¹ = -D2 A⁻¹ := by
  simpa [eq_neg_iff_add_eq_zero] using (D2_mul A A⁻¹).symm

/--
lemma `D2_T` / 引理 `D2_T`

English:
lemma D2_T
  statement: D2 ModularGroup.T = 0
  proof: by
  ext z
  simp [D2, ModularGroup.T]

中文:
引理 D2_T
  结论: D2 ModularGroup.T = 0
  证明: by
  ext z
  simp [D2, ModularGroup.T]

Depends on / 依赖: ModularGroup, ModularGroup.T
-/
lemma D2_T : D2 ModularGroup.T = 0 := by
  ext z
  simp [D2, ModularGroup.T]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `D2_S` / 引理 `D2_S`

English:
lemma D2_S
  given: (z : ℍ)
  statement: D2 ModularGroup.S z = 2 * π * I / z
  proof: by
  simp [D2, ModularGroup.S, ModularGroup.denom_apply]

中文:
引理 D2_S
  条件: (z : ℍ)
  结论: D2 ModularGroup.S z = 2 * π * I / z
  证明: by
  simp [D2, ModularGroup.S, ModularGroup.denom_apply]

Depends on / 依赖: ModularGroup, ModularGroup.S, ModularGroup.denom_apply, denom_apply
-/
lemma D2_S (z : ℍ) : D2 ModularGroup.S z = 2 * π * I / z := by
  simp [D2, ModularGroup.S, ModularGroup.denom_apply]

end EisensteinSeries
