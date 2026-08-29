/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/

module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# Summability of E2

We collect here lemmas about the summability of the Eisenstein series `E2` that will be used to
prove how it transforms under the slash action.

## Main Results

The key results concern the difference between two different orders of summation for the
telescoping series `∑_{m,n} (1/(mz + n) - 1/(mz + n + 1))`:

1. **`tsum_symmetricIco_tsum_sub_eq`**: Summing first over `n` (in symmetric intervals), then `m`:
   `∑'[symmetricIco] n : ℤ, ∑' m : ℤ, (1/(mz+n) - 1/(mz+n+1)) = -2πi/z`

2. **`tsum_tsum_symmetricIco_sub_eq`**: Summing first over `m`, then `n` (in symmetric intervals):
   `∑' m : ℤ, ∑'[symmetricIco] n : ℤ, (1/(mz+n) - 1/(mz+n+1)) = 0`

The difference `-2πi/z` between these two orderings is precisely the correction term
`D2` that appears in the transformation formula for `G2` under the action of `S`.

## Proof Strategy

1. For fixed `m ≠ 0`, the inner sum over `n` telescopes to zero (each term cancels with its
   neighbor), establishing the first identity.

2. For fixed `n`, the inner sum over `m` can be computed using the cotangent series expansion.
   As `n → ±∞` in symmetric intervals, these sums contribute `-2πi/z`.

-/

open UpperHalfPlane hiding I σ

open Filter Complex Finset SummationFilter

open scoped Interval Real Topology Nat ArithmeticFunction.sigma

@[expose] public noncomputable section

namespace EisensteinSeries

variable (z : ℍ)

local notation "𝕢" z:100 => cexp (2 * π * I * z)

/--
lemma `G2_partial_sum_eq` / 引理 `G2_partial_sum_eq`

English:
lemma G2_partial_sum_eq
  given: (N : Nat)
  statement: ∑ m in Icc (-N : Int) N, e2Summand m z =
  proof: by
  rw [sum_Icc_of_even_eq_range (e2Summand_even z)]; rw [Finset.sum_range_succ']; rw [smul_add]; rw [nsmul_eq_mul]; rw [Nat.cast_zero]; rw [e2Summand_zero_eq_two_riemannZeta_two]
  ring_nf
  simp only [e2Summand, eisSummand, add_comm, Nat.cast_add, Nat.cast_one, Fin.isValue,
    Matrix.cons_val_ze

中文:
引理 G2_partial_sum_eq
  条件: (N : 自然数)
  结论: ∑ m in 闭区间 (-N : 整数) N, e2Summand m z =
  证明: by
  rw [sum_Icc_of_even_eq_range (e2Summand_even z)]; rw [Finset.sum_range_succ']; rw [smul_add]; rw [nsmul_eq_mul]; rw [Nat.cast_zero]; rw [e2Summand_zero_eq_two_riemannZeta_two]
  ring_nf
  simp only [e2Summand, eisSummand, add_comm, Nat.cast_add, Nat.cast_one, Fin.isValue,
    Matrix.cons_val_ze
-/
private lemma G2_partial_sum_eq (N : Nat) : ∑ m in Icc (-N : Int) N, e2Summand m z =
    2 * riemannZeta 2 + ∑ m in range N, -8 * π ^ 2 *
      ∑' n : Nat+, n * 𝕢 z ^ ((m + 1) * n) := by
  rw [sum_Icc_of_even_eq_range (e2Summand_even z)]; rw [Finset.sum_range_succ']; rw [smul_add]; rw [nsmul_eq_mul]; rw [Nat.cast_zero]; rw [e2Summand_zero_eq_two_riemannZeta_two]
  ring_nf
  simp only [e2Summand, eisSummand, add_comm, Nat.cast_add, Nat.cast_one, Fin.isValue,
    Matrix.cons_val_zero, Int.cast_add, Int.cast_natCast, Int.cast_one, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.reduceNeg, zpow_neg, mul_comm, mul_sum]
  congr with a
  have H2 := qExpansion_identity_pnat (k := 1) (by grind)
    ⟨(a + 1) * z, by simpa [show 0 < ((a + 1) : Real) by positivity] using z.2⟩
  simp only [add_comm, Nat.reduceAdd, one_div, mul_comm, mul_neg, even_two,
    Even.neg_pow, Nat.factorial_one, Nat.cast_one, div_one, pow_one] at H2
  simp_rw [zpow_ofNat, H2, ← tsum_mul_left, ← tsum_neg, ← exp_nsmul]
  refine tsum_congr fun b => ?_
  ring_nf
  grind [I_sq, exp_add]

/--
lemma `aux_G2_tendsto` / 引理 `aux_G2_tendsto`

English:
lemma aux_G2_tendsto
  statement: Tendsto
  proof: by
  have : -8 * π ^ 2 * ∑' n : Nat+, σ 1 n * 𝕢 z ^ (n : Nat) =
      ∑' m : Nat, (-8 * π ^ 2 * ∑' n : Nat+, n * 𝕢 z ^ ((m + 1) * n)) := by
    have := tsum_prod_pow_eq_tsum_sigma 1 (norm_exp_two_pi_I_lt_one z)
    rw [tsum_pnat_eq_tsum_succ (f := fun d => ∑' c : Nat+]; rw [c ^ 1 * 𝕢 z ^ (d * c : Na

中文:
引理 aux_G2_tendsto
  结论: 收敛
  证明: by
  have : -8 * π ^ 2 * ∑' n : Nat+, σ 1 n * 𝕢 z ^ (n : Nat) =
      ∑' m : Nat, (-8 * π ^ 2 * ∑' n : Nat+, n * 𝕢 z ^ ((m + 1) * n)) := by
    have := tsum_prod_pow_eq_tsum_sigma 1 (norm_exp_two_pi_I_lt_one z)
    rw [tsum_pnat_eq_tsum_succ (f := fun d => ∑' c : Nat+]; rw [c ^ 1 * 𝕢 z ^ (d * c : Na
-/
private lemma aux_G2_tendsto : Tendsto
    (fun N => ∑ m in range N, -8 * π ^ 2 * ∑' n : Nat+, n * 𝕢 z ^ ((m + 1) * n)) atTop
    (𝓝 (-8 * π ^ 2 * ∑' n : Nat+, σ 1 n * 𝕢 z ^ (n : Nat))) := by
  have : -8 * π ^ 2 * ∑' n : Nat+, σ 1 n * 𝕢 z ^ (n : Nat) =
      ∑' m : Nat, (-8 * π ^ 2 * ∑' n : Nat+, n * 𝕢 z ^ ((m + 1) * n)) := by
    have := tsum_prod_pow_eq_tsum_sigma 1 (norm_exp_two_pi_I_lt_one z)
    rw [tsum_pnat_eq_tsum_succ (f := fun d => ∑' c : Nat+]; rw [c ^ 1 * 𝕢 z ^ (d * c : Nat))] at this
    simp [← tsum_mul_left, ← this]
  rw [this]
  refine (Summable.mul_left _ ?_).hasSum.comp tendsto_finset_range
  rw [← summable_pnat_iff_summable_succ (f := fun b => ∑' c : Nat+]; rw [c * 𝕢 z ^ (b * c : Nat))]
  apply (summable_prod_mul_pow 1 (norm_exp_two_pi_I_lt_one z)).prod.congr
  simp [← exp_nsmul]

/--
lemma `hasSum_e2Summand_symmetricIcc` / 引理 `hasSum_e2Summand_symmetricIcc`

English:
lemma hasSum_e2Summand_symmetricIcc
  statement: HasSum (e2Summand · z)
  proof: by
  simpa [HasSum, -symmetricIcc_filter, symmetricIcc_eq_map_Icc_nat, Function.comp_def,
    G2_partial_sum_eq] using! (aux_G2_tendsto z).const_add _

中文:
引理 hasSum_e2Summand_symmetricIcc
  结论: HasSum (e2Summand · z)
  证明: by
  simpa [HasSum, -symmetricIcc_filter, symmetricIcc_eq_map_Icc_nat, Function.comp_def,
    G2_partial_sum_eq] using! (aux_G2_tendsto z).const_add _

Depends on / 依赖: Function, Function.comp_def, G2_partial_sum_eq, HasSum, aux_G2_tendsto, comp_def, const_add, symmetricIcc_eq_map_Icc_nat, symmetricIcc_filter
-/
lemma hasSum_e2Summand_symmetricIcc : HasSum (e2Summand · z)
    (2 * riemannZeta 2 - 8 * π ^ 2 * ∑' n : Nat+, σ 1 n * 𝕢 z ^ (n : Nat)) (symmetricIcc Int) := by
  simpa [HasSum, -symmetricIcc_filter, symmetricIcc_eq_map_Icc_nat, Function.comp_def,
    G2_partial_sum_eq] using! (aux_G2_tendsto z).const_add _

/--
lemma `summable_e2Summand_symmetricIcc` / 引理 `summable_e2Summand_symmetricIcc`

English:
lemma summable_e2Summand_symmetricIcc
  statement: Summable (e2Summand · z) (symmetricIcc Int)
  proof: (hasSum_e2Summand_symmetricIcc z).summable

中文:
引理 summable_e2Summand_symmetricIcc
  结论: Summable (e2Summand · z) (symmetricIcc 整数)
  证明: (hasSum_e2Summand_symmetricIcc z).summable

Depends on / 依赖: hasSum_e2Summand_symmetricIcc, summable
-/
lemma summable_e2Summand_symmetricIcc : Summable (e2Summand · z) (symmetricIcc Int) :=
  (hasSum_e2Summand_symmetricIcc z).summable

/--
lemma `G2_eq_tsum_cexp` / 引理 `G2_eq_tsum_cexp`

English:
lemma G2_eq_tsum_cexp
  statement: G2 z = 2 * riemannZeta 2 - 8 * π ^ 2 * ∑' n : Nat+, σ 1 n * 𝕢 z ^ (n : Nat)
  proof: (hasSum_e2Summand_symmetricIcc z).tsum_eq

中文:
引理 G2_eq_tsum_cexp
  结论: G2 z = 2 * riemannZeta 2 - 8 * π ^ 2 * ∑' n : 自然数+, σ 1 n * 𝕢 z ^ (n : 自然数)
  证明: (hasSum_e2Summand_symmetricIcc z).tsum_eq

Depends on / 依赖: hasSum_e2Summand_symmetricIcc, tsum_eq
-/
lemma G2_eq_tsum_cexp : G2 z = 2 * riemannZeta 2 - 8 * π ^ 2 * ∑' n : Nat+, σ 1 n * 𝕢 z ^ (n : Nat) :=
  (hasSum_e2Summand_symmetricIcc z).tsum_eq

/--
lemma `E2_eq_tsum_cexp` / 引理 `E2_eq_tsum_cexp`

English:
lemma E2_eq_tsum_cexp
  statement: E2 z = 1 - 24 * ∑' n : Nat+, σ 1 n * 𝕢 z ^ (n : Nat)
  proof: by
  simp [E2, G2_eq_tsum_cexp, riemannZeta_two]
  field

中文:
引理 E2_eq_tsum_cexp
  结论: E2 z = 1 - 24 * ∑' n : 自然数+, σ 1 n * 𝕢 z ^ (n : 自然数)
  证明: by
  simp [E2, G2_eq_tsum_cexp, riemannZeta_two]
  field

Depends on / 依赖: G2_eq_tsum_cexp, riemannZeta_two
-/
lemma E2_eq_tsum_cexp : E2 z = 1 - 24 * ∑' n : Nat+, σ 1 n * 𝕢 z ^ (n : Nat) := by
  simp [E2, G2_eq_tsum_cexp, riemannZeta_two]
  field

/--
theorem `hasSum_qExpansion_E2` / 定理 `hasSum_qExpansion_E2`

English:
theorem hasSum_qExpansion_E2
  proof: by
  have hS : Summable fun n : Nat => σ 1 (n + 1) * 𝕢 z ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr (summable_sigma_mul_cexp_pow (k := 2) (one_le_two) z)
  rw [← hasSum_nat_add_iff' 1]
  convert! (hS.mul_left (-24)).hasSum using 1
  · ext : 1
    simp [mul_assoc]
  · rw [E2_eq_tsum_cexp, tsum_pna

中文:
定理 hasSum_qExpansion_E2
  证明: by
  have hS : Summable fun n : Nat => σ 1 (n + 1) * 𝕢 z ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr (summable_sigma_mul_cexp_pow (k := 2) (one_le_two) z)
  rw [← hasSum_nat_add_iff' 1]
  convert! (hS.mul_left (-24)).hasSum using 1
  · ext : 1
    simp [mul_assoc]
  · rw [E2_eq_tsum_cexp, tsum_pna

Depends on / 依赖: E2_eq_tsum_cexp, Summable, convert, hS.mul_left, hasSum, hasSum_nat_add_iff, mul_assoc, mul_left, one_le_two, summable_nat_add_iff, summable_sigma_mul_cexp_pow, tsum_mul_left, tsum_pnat_eq_tsum_succ
-/
theorem hasSum_qExpansion_E2 :
    HasSum (fun m : Nat => (if m = 0 then 1 else -24 * σ 1 m : Complex) • 𝕢 z ^ m) (E2 z) := by
  have hS : Summable fun n : Nat => σ 1 (n + 1) * 𝕢 z ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr (summable_sigma_mul_cexp_pow (k := 2) (one_le_two) z)
  rw [← hasSum_nat_add_iff' 1]
  convert! (hS.mul_left (-24)).hasSum using 1
  · ext : 1
    simp [mul_assoc]
  · rw [E2_eq_tsum_cexp, tsum_pnat_eq_tsum_succ (f := fun n => σ 1 n * 𝕢 z ^ n), tsum_mul_left]
    simp

/--
theorem `isBoundedAtImInfty_E2` / 定理 `isBoundedAtImInfty_E2`

English:
theorem isBoundedAtImInfty_E2
  statement: IsBoundedAtImInfty E2
  proof: isBoundedAtImInfty_of_hasSum_qExpansion one_pos fun τ => by
    simpa only [Function.Periodic.qParam, ofReal_one, div_one] using hasSum_qExpansion_E2 (z := τ)

中文:
定理 isBoundedAtImInfty_E2
  结论: IsBoundedAtImInfty E2
  证明: isBoundedAtImInfty_of_hasSum_qExpansion one_pos fun τ => by
    simpa only [Function.Periodic.qParam, ofReal_one, div_one] using hasSum_qExpansion_E2 (z := τ)

Depends on / 依赖: Function, Function.Periodic.qParam, Periodic, div_one, hasSum_qExpansion_E2, isBoundedAtImInfty_of_hasSum_qExpansion, ofReal_one, one_pos, qParam
-/
theorem isBoundedAtImInfty_E2 : IsBoundedAtImInfty E2 :=
  isBoundedAtImInfty_of_hasSum_qExpansion one_pos fun τ => by
    simpa only [Function.Periodic.qParam, ofReal_one, div_one] using hasSum_qExpansion_E2 (z := τ)

/--
lemma `tendsto_e2Summand_atTop_nhds_zero` / 引理 `tendsto_e2Summand_atTop_nhds_zero`

English:
lemma tendsto_e2Summand_atTop_nhds_zero
  statement: Tendsto (e2Summand · z) atTop (𝓝 0)
  proof: (summable_e2Summand_symmetricIcc z).tendsto_zero_of_even_summable_symmetricIcc (e2Summand_even _)

中文:
引理 tendsto_e2Summand_atTop_nhds_zero
  结论: 收敛 (e2Summand · z) atTop (𝓝 0)
  证明: (summable_e2Summand_symmetricIcc z).tendsto_zero_of_even_summable_symmetricIcc (e2Summand_even _)

Depends on / 依赖: e2Summand_even, summable_e2Summand_symmetricIcc, tendsto_zero_of_even_summable_symmetricIcc
-/
lemma tendsto_e2Summand_atTop_nhds_zero : Tendsto (e2Summand · z) atTop (𝓝 0) :=
  (summable_e2Summand_symmetricIcc z).tendsto_zero_of_even_summable_symmetricIcc (e2Summand_even _)

/--
lemma `hasSum_e2Summand_symmetricIco` / 引理 `hasSum_e2Summand_symmetricIco`

English:
lemma hasSum_e2Summand_symmetricIco
  statement: HasSum (e2Summand · z)
  proof: by
  apply (hasSum_e2Summand_symmetricIcc z).hasSum_symmetricIco_of_hasSum_symmetricIcc
  simpa using! (tendsto_e2Summand_atTop_nhds_zero z).neg.comp tendsto_natCast_atTop_atTop

中文:
引理 hasSum_e2Summand_symmetricIco
  结论: HasSum (e2Summand · z)
  证明: by
  apply (hasSum_e2Summand_symmetricIcc z).hasSum_symmetricIco_of_hasSum_symmetricIcc
  simpa using! (tendsto_e2Summand_atTop_nhds_zero z).neg.comp tendsto_natCast_atTop_atTop

Depends on / 依赖: hasSum_e2Summand_symmetricIcc, hasSum_symmetricIco_of_hasSum_symmetricIcc, neg.comp, tendsto_e2Summand_atTop_nhds_zero, tendsto_natCast_atTop_atTop
-/
lemma hasSum_e2Summand_symmetricIco : HasSum (e2Summand · z)
    (2 * riemannZeta 2 - 8 * π ^ 2 * ∑' n : Nat+, σ 1 n * 𝕢 z ^ (n : Nat)) (symmetricIco Int) := by
  apply (hasSum_e2Summand_symmetricIcc z).hasSum_symmetricIco_of_hasSum_symmetricIcc
  simpa using! (tendsto_e2Summand_atTop_nhds_zero z).neg.comp tendsto_natCast_atTop_atTop

/--
lemma `summable_e2Summand_symmetricIco` / 引理 `summable_e2Summand_symmetricIco`

English:
lemma summable_e2Summand_symmetricIco
  statement: Summable (e2Summand · z) (symmetricIco Int)
  proof: (hasSum_e2Summand_symmetricIco z).summable

中文:
引理 summable_e2Summand_symmetricIco
  结论: Summable (e2Summand · z) (symmetricIco 整数)
  证明: (hasSum_e2Summand_symmetricIco z).summable

Depends on / 依赖: hasSum_e2Summand_symmetricIco, summable
-/
lemma summable_e2Summand_symmetricIco : Summable (e2Summand · z) (symmetricIco Int) :=
  (hasSum_e2Summand_symmetricIco z).summable

/--
lemma `G2_eq_tsum_symmetricIco` / 引理 `G2_eq_tsum_symmetricIco`

English:
lemma G2_eq_tsum_symmetricIco
  statement: G2 z = ∑'[symmetricIco Int] m, e2Summand m z
  proof: by
  rw [G2]; rw [tsum_symmetricIcc_eq_tsum_symmetricIco (summable_e2Summand_symmetricIcc z)]
  simpa using! (tendsto_e2Summand_atTop_nhds_zero z).neg.comp tendsto_natCast_atTop_atTop

中文:
引理 G2_eq_tsum_symmetricIco
  结论: G2 z = ∑'[symmetricIco 整数] m, e2Summand m z
  证明: by
  rw [G2]; rw [tsum_symmetricIcc_eq_tsum_symmetricIco (summable_e2Summand_symmetricIcc z)]
  simpa using! (tendsto_e2Summand_atTop_nhds_zero z).neg.comp tendsto_natCast_atTop_atTop

Depends on / 依赖: neg.comp, summable_e2Summand_symmetricIcc, tendsto_e2Summand_atTop_nhds_zero, tendsto_natCast_atTop_atTop, tsum_symmetricIcc_eq_tsum_symmetricIco
-/
lemma G2_eq_tsum_symmetricIco : G2 z = ∑'[symmetricIco Int] m, e2Summand m z := by
  rw [G2]; rw [tsum_symmetricIcc_eq_tsum_symmetricIco (summable_e2Summand_symmetricIcc z)]
  simpa using! (tendsto_e2Summand_atTop_nhds_zero z).neg.comp tendsto_natCast_atTop_atTop

section Auxiliary

open ModularGroup

variable (z : ℍ)

/--
lemma `one_div_linear_sub_one_div_linear_eq` / 引理 `one_div_linear_sub_one_div_linear_eq`

English:
lemma one_div_linear_sub_one_div_linear_eq
  given: (a b m : Int) (hm : m != 0 ∨ (a != 0 ∧ b != 0))
  proof: by
  rw [← one_div_mul_sub_mul_one_div_eq_one_div_add_one_div]
  · grind [one_div, add_sub_add_left_eq_sub, mul_inv_rev]
  · simpa using linear_ne_zero z (cd := ![m, a]) (by aesop)
  · simpa using linear_ne_zero z (cd := ![m, b]) (by aesop)

中文:
引理 one_div_linear_sub_one_div_linear_eq
  条件: (a b m : 整数) (hm : m != 0 ∨ (a != 0 ∧ b != 0))
  证明: by
  rw [← one_div_mul_sub_mul_one_div_eq_one_div_add_one_div]
  · grind [one_div, add_sub_add_left_eq_sub, mul_inv_rev]
  · simpa using linear_ne_zero z (cd := ![m, a]) (by aesop)
  · simpa using linear_ne_zero z (cd := ![m, b]) (by aesop)
-/
private lemma one_div_linear_sub_one_div_linear_eq (a b m : Int) (hm : m != 0 ∨ (a != 0 ∧ b != 0)) :
    1 / ((m : Complex) * z + a) - 1 / (m * z + b) = (b - a) * (1 / ((m * z + a) * (m * z + b))) := by
  rw [← one_div_mul_sub_mul_one_div_eq_one_div_add_one_div]
  · grind [one_div, add_sub_add_left_eq_sub, mul_inv_rev]
  · simpa using linear_ne_zero z (cd := ![m, a]) (by aesop)
  · simpa using linear_ne_zero z (cd := ![m, b]) (by aesop)

/--
lemma `summable_left_one_div_linear_sub_one_div_linear` / 引理 `summable_left_one_div_linear_sub_one_div_linear`

English:
lemma summable_left_one_div_linear_sub_one_div_linear
  given: (a b : Int)
  proof: by
  have := Summable.mul_left (b - a : Complex) (summable_linear_left_mul_linear_left (ne_zero z) a b)
  rw [← Finset.summable_compl_iff (s := {0})] at *
  apply this.congr (fun m => ?_)
  grind [one_div_linear_sub_one_div_linear_eq z a b m (by grind)]

中文:
引理 summable_left_one_div_linear_sub_one_div_linear
  条件: (a b : 整数)
  证明: by
  have := Summable.mul_left (b - a : Complex) (summable_linear_left_mul_linear_left (ne_zero z) a b)
  rw [← Finset.summable_compl_iff (s := {0})] at *
  apply this.congr (fun m => ?_)
  grind [one_div_linear_sub_one_div_linear_eq z a b m (by grind)]

Depends on / 依赖: Finset, Finset.summable_compl_iff, Summable, Summable.mul_left, mul_left, ne_zero, one_div_linear_sub_one_div_linear_eq, summable_compl_iff, summable_linear_left_mul_linear_left, this.congr
-/
lemma summable_left_one_div_linear_sub_one_div_linear (a b : Int) :
    Summable fun m : Int => 1 / (m * (z : Complex) + a) - 1 / (m * z + b) := by
  have := Summable.mul_left (b - a : Complex) (summable_linear_left_mul_linear_left (ne_zero z) a b)
  rw [← Finset.summable_compl_iff (s := {0})] at *
  apply this.congr (fun m => ?_)
  grind [one_div_linear_sub_one_div_linear_eq z a b m (by grind)]

/--
lemma `summable_right_one_div_linear_sub_one_div_linear_succ` / 引理 `summable_right_one_div_linear_sub_one_div_linear_succ`

English:
lemma summable_right_one_div_linear_sub_one_div_linear_succ
  given: (m : Int)
  proof: by
  have := summable_linear_right_add_one_mul_linear_right z m m
  rw [← Finset.summable_compl_iff (s := {0]; rw [-1})] at *
  apply this.congr (fun b => ?_)
  simpa [add_assoc, mul_comm] using
    (one_div_linear_sub_one_div_linear_eq z b (b + 1) m (by grind)).symm

中文:
引理 summable_right_one_div_linear_sub_one_div_linear_succ
  条件: (m : 整数)
  证明: by
  have := summable_linear_right_add_one_mul_linear_right z m m
  rw [← Finset.summable_compl_iff (s := {0]; rw [-1})] at *
  apply this.congr (fun b => ?_)
  simpa [add_assoc, mul_comm] using
    (one_div_linear_sub_one_div_linear_eq z b (b + 1) m (by grind)).symm

Depends on / 依赖: Finset, Finset.summable_compl_iff, add_assoc, mul_comm, one_div_linear_sub_one_div_linear_eq, summable_compl_iff, summable_linear_right_add_one_mul_linear_right, this.congr
-/
lemma summable_right_one_div_linear_sub_one_div_linear_succ (m : Int) :
    Summable fun b : Int => 1 / (m * (z : Complex) + b) - 1 / (m * z + b + 1) := by
  have := summable_linear_right_add_one_mul_linear_right z m m
  rw [← Finset.summable_compl_iff (s := {0]; rw [-1})] at *
  apply this.congr (fun b => ?_)
  simpa [add_assoc, mul_comm] using
    (one_div_linear_sub_one_div_linear_eq z b (b + 1) m (by grind)).symm

/--
lemma `aux_sum_Ico_S_identity` / 引理 `aux_sum_Ico_S_identity`

English:
lemma aux_sum_Ico_S_identity
  given: (N : Nat)
  proof: by
  simp_rw [inv_neg, mul_neg, mul_sum, pow_two, ← zpow_two]
  rw [Summable.tsum_finsetSum (fun i hi => linear_left_summable (ne_zero z) i le_rfl)]
  apply sum_congr rfl fun n hn => ?_
  rw [← tsum_mul_left]; rw [← tsum_comp_neg]
  apply tsum_congr (by grind [zpow_two, ne_zero z])

中文:
引理 aux_sum_Ico_S_identity
  条件: (N : 自然数)
  证明: by
  simp_rw [inv_neg, mul_neg, mul_sum, pow_two, ← zpow_two]
  rw [Summable.tsum_finsetSum (fun i hi => linear_left_summable (ne_zero z) i le_rfl)]
  apply sum_congr rfl fun n hn => ?_
  rw [← tsum_mul_left]; rw [← tsum_comp_neg]
  apply tsum_congr (by grind [zpow_two, ne_zero z])
-/
private lemma aux_sum_Ico_S_identity (N : Nat) :
    ((z : Complex) ^ 2)⁻¹ * (∑ x in Ico (-N : Int) N, ∑' (n : Int), (((x : Complex) * (-↑z)⁻¹ + n) ^ 2)⁻¹) =
    ∑' (n : Int), ∑ x in Ico (-N : Int) N, (((n : Complex) * z + x) ^ 2)⁻¹ := by
  simp_rw [inv_neg, mul_neg, mul_sum, pow_two, ← zpow_two]
  rw [Summable.tsum_finsetSum (fun i hi => linear_left_summable (ne_zero z) i le_rfl)]
  apply sum_congr rfl fun n hn => ?_
  rw [← tsum_mul_left]; rw [← tsum_comp_neg]
  apply tsum_congr (by grind [zpow_two, ne_zero z])

/--
lemma `tendsto_double_sum_S_act` / 引理 `tendsto_double_sum_S_act`

English:
lemma tendsto_double_sum_S_act
  proof: by
  rw [G2_eq_tsum_symmetricIco]; rw [← tsum_mul_left]
  have := ((summable_e2Summand_symmetricIco (S • z)).mul_left (z.1 ^ 2)⁻¹).hasSum
  simp only [HasSum, symmetricIco, tendsto_map'_iff, modular_S_smul, ← Nat.map_cast_int_atTop] at *
  apply this.congr (fun N => ?_)
  simpa [e2Summand, eisSumman

中文:
引理 tendsto_double_sum_S_act
  证明: by
  rw [G2_eq_tsum_symmetricIco]; rw [← tsum_mul_left]
  have := ((summable_e2Summand_symmetricIco (S • z)).mul_left (z.1 ^ 2)⁻¹).hasSum
  simp only [HasSum, symmetricIco, tendsto_map'_iff, modular_S_smul, ← Nat.map_cast_int_atTop] at *
  apply this.congr (fun N => ?_)
  simpa [e2Summand, eisSumman

Depends on / 依赖: G2_eq_tsum_symmetricIco, HasSum, Nat.map_cast_int_atTop, _iff, aux_sum_Ico_S_identity, e2Summand, eisSummand, hasSum, map_cast_int_atTop, modular_S_smul, mul_left, mul_sum, summable_e2Summand_symmetricIco, symmetricIco, tendsto_map, this.congr, tsum_mul_left
-/
lemma tendsto_double_sum_S_act :
    Tendsto (fun N : Nat => (∑' (n : Int), ∑ m in Ico (-N : Int) N, (1 / ((n : Complex) * z + m) ^ 2))) atTop
    (𝓝 ((z.1 ^ 2)⁻¹ * G2 (S • z))) := by
  rw [G2_eq_tsum_symmetricIco]; rw [← tsum_mul_left]
  have := ((summable_e2Summand_symmetricIco (S • z)).mul_left (z.1 ^ 2)⁻¹).hasSum
  simp only [HasSum, symmetricIco, tendsto_map'_iff, modular_S_smul, ← Nat.map_cast_int_atTop] at *
  apply this.congr (fun N => ?_)
  simpa [e2Summand, eisSummand, ← mul_sum] using! aux_sum_Ico_S_identity z N

/--
lemma `tsum_symmetricIco_tsum_eq_S_act` / 引理 `tsum_symmetricIco_tsum_eq_S_act`

English:
lemma tsum_symmetricIco_tsum_eq_S_act
  proof: by
  apply HasSum.tsum_eq
  rw [hasSum_symmetricIco_int_iff]
  apply (tendsto_double_sum_S_act z).congr (fun x => ?_)
  rw [Summable.tsum_finsetSum]
  exact fun i hi => by simpa using! linear_left_summable (ne_zero z) i le_rfl

中文:
引理 tsum_symmetricIco_tsum_eq_S_act
  证明: by
  apply HasSum.tsum_eq
  rw [hasSum_symmetricIco_int_iff]
  apply (tendsto_double_sum_S_act z).congr (fun x => ?_)
  rw [Summable.tsum_finsetSum]
  exact fun i hi => by simpa using! linear_left_summable (ne_zero z) i le_rfl

Depends on / 依赖: HasSum, HasSum.tsum_eq, Summable, Summable.tsum_finsetSum, hasSum_symmetricIco_int_iff, le_rfl, linear_left_summable, ne_zero, tendsto_double_sum_S_act, tsum_eq, tsum_finsetSum
-/
lemma tsum_symmetricIco_tsum_eq_S_act :
    ∑'[symmetricIco Int] n : Int, ∑' m : Int, 1 / ((m : Complex) * z + n) ^ 2 =
    ((z : Complex) ^ 2)⁻¹ * G2 (S • z) := by
  apply HasSum.tsum_eq
  rw [hasSum_symmetricIco_int_iff]
  apply (tendsto_double_sum_S_act z).congr (fun x => ?_)
  rw [Summable.tsum_finsetSum]
  exact fun i hi => by simpa using! linear_left_summable (ne_zero z) i le_rfl

/--
lemma `telescope_aux` / 引理 `telescope_aux`

English:
lemma telescope_aux
  given: (z : Complex) (m : Int) (b : Nat)
  proof: by
  convert! sum_Ico_int_sub b (fun n => 1 / ((m : Complex) * z + n)) using 2 <;>
  simp [add_assoc, sub_eq_add_neg]

中文:
引理 telescope_aux
  条件: (z : 复形) (m : 整数) (b : 自然数)
  证明: by
  convert! sum_Ico_int_sub b (fun n => 1 / ((m : Complex) * z + n)) using 2 <;>
  simp [add_assoc, sub_eq_add_neg]
-/
private lemma telescope_aux (z : Complex) (m : Int) (b : Nat) :
    ∑ n in Ico (-b : Int) b, (1 / ((m : Complex) * z + n) - 1 / (m * z + n + 1)) =
    1 / (m * z - b) - 1 / (m * z + b) := by
  convert! sum_Ico_int_sub b (fun n => 1 / ((m : Complex) * z + n)) using 2 <;>
  simp [add_assoc, sub_eq_add_neg]

/--
lemma `tsum_symmetricIco_linear_sub_linear_add_one_eq_zero` / 引理 `tsum_symmetricIco_linear_sub_linear_add_one_eq_zero`

English:
lemma tsum_symmetricIco_linear_sub_linear_add_one_eq_zero
  given: (m : Int)
  proof: by
  apply HasSum.tsum_eq
  simp_rw [hasSum_symmetricIco_int_iff, telescope_aux z m]
  simpa using (tendsto_zero_inv_linear_sub z m).sub (tendsto_zero_inv_linear z m)

中文:
引理 tsum_symmetricIco_linear_sub_linear_add_one_eq_zero
  条件: (m : 整数)
  证明: by
  apply HasSum.tsum_eq
  simp_rw [hasSum_symmetricIco_int_iff, telescope_aux z m]
  simpa using (tendsto_zero_inv_linear_sub z m).sub (tendsto_zero_inv_linear z m)

Depends on / 依赖: HasSum, HasSum.tsum_eq, hasSum_symmetricIco_int_iff, simp_rw, telescope_aux, tendsto_zero_inv_linear, tendsto_zero_inv_linear_sub, tsum_eq
-/
lemma tsum_symmetricIco_linear_sub_linear_add_one_eq_zero (m : Int) :
    ∑'[symmetricIco Int] n : Int, (1 / ((m : Complex) * z + n) - 1 / (m * z + n + 1)) = 0 := by
  apply HasSum.tsum_eq
  simp_rw [hasSum_symmetricIco_int_iff, telescope_aux z m]
  simpa using (tendsto_zero_inv_linear_sub z m).sub (tendsto_zero_inv_linear z m)

/--
lemma `aux_tsum_identity_1` / 引理 `aux_tsum_identity_1`

English:
lemma aux_tsum_identity_1
  given: (d : Nat+)
  proof: by
  rw [eq_neg_add_iff_add_eq (b := 2 / (d : Complex))]; rw [tsum_int_eq_zero_add_tsum_pnat]
  · simp only [Int.cast_zero, zero_mul, zero_sub, one_div, zero_add, Int.cast_natCast, Int.cast_neg,
      neg_mul]
    ring_nf
    rw [← Summable.tsum_add]
    · grind
    · apply (summable_pnat_iff_summab

中文:
引理 aux_tsum_identity_1
  条件: (d : 自然数+)
  证明: by
  rw [eq_neg_add_iff_add_eq (b := 2 / (d : Complex))]; rw [tsum_int_eq_zero_add_tsum_pnat]
  · simp only [Int.cast_zero, zero_mul, zero_sub, one_div, zero_add, Int.cast_natCast, Int.cast_neg,
      neg_mul]
    ring_nf
    rw [← Summable.tsum_add]
    · grind
    · apply (summable_pnat_iff_summab
-/
private lemma aux_tsum_identity_1 (d : Nat+) :
    ∑' (m : Int), (1 / ((m : Complex) * z - d) - 1 / (m * z + d)) = -(2 / d) +
    ∑' m : Nat+, (1 / ((m : Complex) * z - d) + 1 / (-m * z + -d) - 1 / (m * z + d) -1 / (-m * z + d)) := by
  rw [eq_neg_add_iff_add_eq (b := 2 / (d : Complex))]; rw [tsum_int_eq_zero_add_tsum_pnat]
  · simp only [Int.cast_zero, zero_mul, zero_sub, one_div, zero_add, Int.cast_natCast, Int.cast_neg,
      neg_mul]
    ring_nf
    rw [← Summable.tsum_add]
    · grind
    · apply (summable_pnat_iff_summable_nat.mpr ((summable_int_iff_summable_nat_and_neg.mp
        (summable_left_one_div_linear_sub_one_div_linear z (-d) d)).1)).congr
      grind [Int.cast_natCast]
    · apply (summable_pnat_iff_summable_nat.mpr ((summable_int_iff_summable_nat_and_neg.mp
        (summable_left_one_div_linear_sub_one_div_linear z (-d) d)).2)).congr
      grind [Int.cast_neg, Int.cast_natCast, neg_mul, one_div]
  · simpa using! summable_left_one_div_linear_sub_one_div_linear z (-d) d

/--
lemma `aux_tsum_identity_2` / 引理 `aux_tsum_identity_2`

English:
lemma aux_tsum_identity_2
  given: (d : Nat+)
  proof: by
  rw [← Summable.tsum_mul_left]
  · apply tsum_congr (by grind [sub_eq_add_neg, ← div_neg, ne_zero z])
  · have := summable_cotTerm (by simpa using z.int_div_mem_integerComplement (n := -d) (by aesop))
    simp only [cotTerm, one_div] at *
    simp only [← Nat.cast_add_one] at this
    rw [summab

中文:
引理 aux_tsum_identity_2
  条件: (d : 自然数+)
  证明: by
  rw [← Summable.tsum_mul_left]
  · apply tsum_congr (by grind [sub_eq_add_neg, ← div_neg, ne_zero z])
  · have := summable_cotTerm (by simpa using z.int_div_mem_integerComplement (n := -d) (by aesop))
    simp only [cotTerm, one_div] at *
    simp only [← Nat.cast_add_one] at this
    rw [summab
-/
private lemma aux_tsum_identity_2 (d : Nat+) :
    ∑' m : Nat+, (1 / ((m : Complex) * z - d) + 1 / (-m * z + -d) - (1 / (m * z + d)) -
    1 / (-m * z + d)) = 2 / z * ∑' m : Nat+, (1 / (-(d : Complex) / z - m) + 1 / (-d / z + m)) := by
  rw [← Summable.tsum_mul_left]
  · apply tsum_congr (by grind [sub_eq_add_neg, ← div_neg, ne_zero z])
  · have := summable_cotTerm (by simpa using z.int_div_mem_integerComplement (n := -d) (by aesop))
    simp only [cotTerm, one_div] at *
    simp only [← Nat.cast_add_one] at this
    rw [summable_nat_add_iff (f := fun n => (-d / (z : Complex) - n)⁻¹ + (-d / (z : Complex) + n)⁻¹)] at this
    apply this.subtype

/--
lemma `aux_tendsto_tsum_cexp_pnat` / 引理 `aux_tendsto_tsum_cexp_pnat`

English:
lemma aux_tendsto_tsum_cexp_pnat
  proof: by
  have := tendsto_zero_geometric_tsum_pnat (norm_exp_two_pi_I_lt_one ⟨_, im_pnat_div_pos 1 z⟩)
  simp only [← exp_nsmul, nsmul_eq_mul, Nat.cast_mul] at *
exact this.congr by grind

中文:
引理 aux_tendsto_tsum_cexp_pnat
  证明: by
  have := tendsto_zero_geometric_tsum_pnat (norm_exp_two_pi_I_lt_one ⟨_, im_pnat_div_pos 1 z⟩)
  simp only [← exp_nsmul, nsmul_eq_mul, Nat.cast_mul] at *
exact this.congr by grind
-/
private lemma aux_tendsto_tsum_cexp_pnat :
    Tendsto (fun N : Nat+ => ∑' (n : Nat+), cexp (2 * π * I * (-N / z)) ^ (n : Nat)) atTop (𝓝 0) := by
  have := tendsto_zero_geometric_tsum_pnat (norm_exp_two_pi_I_lt_one ⟨_, im_pnat_div_pos 1 z⟩)
  simp only [← exp_nsmul, nsmul_eq_mul, Nat.cast_mul] at *
exact this.congr by grind

/--
lemma `aux_tendsto_tsum` / 引理 `aux_tendsto_tsum`

English:
lemma aux_tendsto_tsum
  statement: Tendsto (fun n : Nat => 2 / z *
  proof: by
  rw [← PNat.tendsto_comp_val_iff]
  have H0 : (fun n : Nat+ => (2 / z * ∑' (m : Nat+), (1 / (-(n : Complex) / z - m) + 1 / (-n / z + m)))) =
      (fun n : Nat+ => (-2 * π * I / z) - (2 / z * (2 * π * I)) *
      (∑' m : Nat+, cexp (2 * π * I * (-n / z)) ^ (m : Nat)) + 2 / n) := by
    ext N
hav

中文:
引理 aux_tendsto_tsum
  结论: 收敛 (fun n : 自然数 => 2 / z *
  证明: by
  rw [← PNat.tendsto_comp_val_iff]
  have H0 : (fun n : Nat+ => (2 / z * ∑' (m : Nat+), (1 / (-(n : Complex) / z - m) + 1 / (-n / z + m)))) =
      (fun n : Nat+ => (-2 * π * I / z) - (2 / z * (2 * π * I)) *
      (∑' m : Nat+, cexp (2 * π * I * (-n / z)) ^ (m : Nat)) + 2 / n) := by
    ext N
hav
-/
private lemma aux_tendsto_tsum : Tendsto (fun n : Nat => 2 / z *
    ∑' (m : Nat+), (1 / (-(n : Complex) / z - m) + 1 / (-n / z + m))) atTop (𝓝 (-2 * π * I / z)) := by
  rw [← PNat.tendsto_comp_val_iff]
  have H0 : (fun n : Nat+ => (2 / z * ∑' (m : Nat+), (1 / (-(n : Complex) / z - m) + 1 / (-n / z + m)))) =
      (fun n : Nat+ => (-2 * π * I / z) - (2 / z * (2 * π * I)) *
      (∑' m : Nat+, cexp (2 * π * I * (-n / z)) ^ (m : Nat)) + 2 / n) := by
    ext N
have h2 := cot_series_rep coe_mem_integerComplement ⟨-N / z, im_pnat_div_pos N z⟩
    rw [pi_mul_cot_pi_q_exp]; rw [← sub_eq_iff_eq_add']; rw [one_div]; rw [inv_div]; rw [neg_mul]; rw [← h2]; rw [← tsum_zero_pnat_eq_tsum_nat
      (by simpa using norm_exp_two_pi_I_lt_one ⟨-N / z]; rw [im_pnat_div_pos N z⟩)] at *
    field [ne_zero z]
  rw [H0]
  nth_rw 2 [show -2 * π * I / z = (-2 * π * I / z) - (2 / z * (2 * π * I)) * 0 + 2 * 0 by ring]
.add (.const_mul _ ?_) .const_sub _ .const_mul _ refine aux_tendsto_tsum_cexp_pnat z
  exact PNat.tendsto_comp_val_iff.mpr tendsto_inv_atTop_nhds_zero_nat

/--
lemma `tendsto_tsum_one_div_linear_sub_succ_eq` / 引理 `tendsto_tsum_one_div_linear_sub_succ_eq`

English:
lemma tendsto_tsum_one_div_linear_sub_succ_eq
  proof: by
  have (N : Nat+) :
      ∑ n in Ico (-N : Int) N, ∑' m : Int, (1 / ((m : Complex) * z + n) - 1 / (m * z + n + 1))
      = ∑' m : Int, ∑ n in Ico (-N : Int) N, (1 / ((m : Complex) * z + n) - 1 / (m * z + n + 1)) := by
    rw [Summable.tsum_finsetSum (fun i hi => ?_)]
    apply (summable_left_one_

中文:
引理 tendsto_tsum_one_div_linear_sub_succ_eq
  证明: by
  have (N : Nat+) :
      ∑ n in Ico (-N : Int) N, ∑' m : Int, (1 / ((m : Complex) * z + n) - 1 / (m * z + n + 1))
      = ∑' m : Int, ∑ n in Ico (-N : Int) N, (1 / ((m : Complex) * z + n) - 1 / (m * z + n + 1)) := by
    rw [Summable.tsum_finsetSum (fun i hi => ?_)]
    apply (summable_left_one_

Depends on / 依赖: PNat.tendst, Summable, Summable.tsum_finsetSum, Tendsto, Tendsto.add, aux_tsum_identity_1, summable_left_one_div_linear_sub_one_div_linear, telescope_aux, tendst, tsum_finsetSum
-/
lemma tendsto_tsum_one_div_linear_sub_succ_eq :
    Tendsto (fun N : Nat+ => ∑ n in Ico (-N : Int) N,
    ∑' m : Int, (1 / ((m : Complex) * z + n) - 1 / (m * z + n + 1))) atTop (𝓝 (-2 * π * I / z)) := by
  have (N : Nat+) :
      ∑ n in Ico (-N : Int) N, ∑' m : Int, (1 / ((m : Complex) * z + n) - 1 / (m * z + n + 1))
      = ∑' m : Int, ∑ n in Ico (-N : Int) N, (1 / ((m : Complex) * z + n) - 1 / (m * z + n + 1)) := by
    rw [Summable.tsum_finsetSum (fun i hi => ?_)]
    apply (summable_left_one_div_linear_sub_one_div_linear z i (i + 1)).congr
    grind
  simp only [telescope_aux, aux_tsum_identity_1] at this
  rw [funext this]; rw [show -2 * π * I / z = 0 + -2 * π * I / z by ring]
  apply Tendsto.add
  · simpa [← PNat.tendsto_comp_val_iff] using!
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := Complex)).const_mul (-2)
  · simpa only [aux_tsum_identity_2, ← PNat.tendsto_comp_val_iff] using! aux_tendsto_tsum z

/--
lemma `tsum_symmetricIco_tsum_sub_eq` / 引理 `tsum_symmetricIco_tsum_sub_eq`

English:
lemma tsum_symmetricIco_tsum_sub_eq
  proof: by
  apply HasSum.tsum_eq
  simpa [HasSum, ← Nat.map_cast_int_atTop, ← PNat.tendsto_comp_val_iff]
    using tendsto_tsum_one_div_linear_sub_succ_eq z

中文:
引理 tsum_symmetricIco_tsum_sub_eq
  证明: by
  apply HasSum.tsum_eq
  simpa [HasSum, ← Nat.map_cast_int_atTop, ← PNat.tendsto_comp_val_iff]
    using tendsto_tsum_one_div_linear_sub_succ_eq z

Depends on / 依赖: HasSum, HasSum.tsum_eq, Nat.map_cast_int_atTop, PNat.tendsto_comp_val_iff, map_cast_int_atTop, tendsto_comp_val_iff, tendsto_tsum_one_div_linear_sub_succ_eq, tsum_eq
-/
lemma tsum_symmetricIco_tsum_sub_eq :
    ∑'[symmetricIco Int] n : Int, ∑' m : Int, (1 / ((m : Complex) * z + n) - 1 / (m * z + n + 1)) =
    -2 * π * I / z := by
  apply HasSum.tsum_eq
  simpa [HasSum, ← Nat.map_cast_int_atTop, ← PNat.tendsto_comp_val_iff]
    using tendsto_tsum_one_div_linear_sub_succ_eq z

/--
lemma `tsum_tsum_symmetricIco_sub_eq` / 引理 `tsum_tsum_symmetricIco_sub_eq`

English:
lemma tsum_tsum_symmetricIco_sub_eq
  proof: by
  convert! tsum_zero
  exact tsum_symmetricIco_linear_sub_linear_add_one_eq_zero z _

中文:
引理 tsum_tsum_symmetricIco_sub_eq
  证明: by
  convert! tsum_zero
  exact tsum_symmetricIco_linear_sub_linear_add_one_eq_zero z _

Depends on / 依赖: convert, tsum_symmetricIco_linear_sub_linear_add_one_eq_zero, tsum_zero
-/
lemma tsum_tsum_symmetricIco_sub_eq :
    ∑' m : Int, ∑'[symmetricIco Int] n : Int, (1 / ((m : Complex) * z + n) - 1 / (m * z + n + 1)) = 0 := by
  convert! tsum_zero
  exact tsum_symmetricIco_linear_sub_linear_add_one_eq_zero z _

end Auxiliary

end EisensteinSeries
