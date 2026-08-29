/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
public import Mathlib.NumberTheory.LSeries.HurwitzZetaOdd
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The Hurwitz zeta function

This file gives the definition and properties of the following two functions:

* The **Hurwitz zeta function**, which is the meromorphic continuation to all `s ∈ ℂ` of the
  function defined for `1 < re s` by the series

  `∑' n, 1 / (n + a) ^ s`

  for a parameter `a ∈ ℝ`, with the sum taken over all `n` such that `n + a > 0`;

* the related sum, which we call the "**exponential zeta function**" (does it have a standard name?)

  `∑' n : ℕ, exp (2 * π * I * n * a) / n ^ s`.

## Main definitions and results

* `hurwitzZeta`: the Hurwitz zeta function (defined to be periodic in `a` with period 1)
* `expZeta`: the exponential zeta function
* `hasSum_hurwitzZeta_of_one_lt_re` and `hasSum_expZeta_of_one_lt_re`:
  relation to Dirichlet series for `1 < re s`
* ` hurwitzZeta_residue_one` shows that the residue at `s = 1` equals `1`
* `differentiableAt_hurwitzZeta` and `differentiableAt_expZeta`: analyticity away from `s = 1`
* `hurwitzZeta_one_sub` and `expZeta_one_sub`: functional equations `s ↔ 1 - s`.
-/

@[expose] public section

open Set Real Complex Filter Topology

namespace HurwitzZeta

/-!
## The Hurwitz zeta function
-/

/--
Definition of `hurwitzZeta` / `hurwitzZeta` 的定义

English:
definition hurwitzZeta
  signature: (a : UnitAddCircle) (s : Complex)
  body: hurwitzZetaEven a s + hurwitzZetaOdd a s

中文:
定义 hurwitzZeta
  签名: (a : UnitAddCircle) (s : 复形)
  定义体: hurwitzZetaEven a s + hurwitzZetaOdd a s

Depends on / 依赖: hurwitzZetaEven, hurwitzZetaOdd
-/
noncomputable def hurwitzZeta (a : UnitAddCircle) (s : Complex) :=
  hurwitzZetaEven a s + hurwitzZetaOdd a s

/--
lemma `hurwitzZetaEven_eq` / 引理 `hurwitzZetaEven_eq`

English:
lemma hurwitzZetaEven_eq
  given: (a : UnitAddCircle) (s : Complex)
  proof: by
  simp only [hurwitzZeta, hurwitzZetaEven_neg, hurwitzZetaOdd_neg]
  ring_nf

中文:
引理 hurwitzZetaEven_eq
  条件: (a : UnitAddCircle) (s : 复形)
  证明: by
  simp only [hurwitzZeta, hurwitzZetaEven_neg, hurwitzZetaOdd_neg]
  ring_nf

Depends on / 依赖: hurwitzZeta, hurwitzZetaEven_neg, hurwitzZetaOdd_neg, ring_nf
-/
lemma hurwitzZetaEven_eq (a : UnitAddCircle) (s : Complex) :
    hurwitzZetaEven a s = (hurwitzZeta a s + hurwitzZeta (-a) s) / 2 := by
  simp only [hurwitzZeta, hurwitzZetaEven_neg, hurwitzZetaOdd_neg]
  ring_nf

/--
lemma `hurwitzZetaOdd_eq` / 引理 `hurwitzZetaOdd_eq`

English:
lemma hurwitzZetaOdd_eq
  given: (a : UnitAddCircle) (s : Complex)
  proof: by
  simp only [hurwitzZeta, hurwitzZetaEven_neg, hurwitzZetaOdd_neg]
  ring_nf

中文:
引理 hurwitzZetaOdd_eq
  条件: (a : UnitAddCircle) (s : 复形)
  证明: by
  simp only [hurwitzZeta, hurwitzZetaEven_neg, hurwitzZetaOdd_neg]
  ring_nf

Depends on / 依赖: hurwitzZeta, hurwitzZetaEven_neg, hurwitzZetaOdd_neg, ring_nf
-/
lemma hurwitzZetaOdd_eq (a : UnitAddCircle) (s : Complex) :
    hurwitzZetaOdd a s = (hurwitzZeta a s - hurwitzZeta (-a) s) / 2 := by
  simp only [hurwitzZeta, hurwitzZetaEven_neg, hurwitzZetaOdd_neg]
  ring_nf

/--
lemma `differentiableAt_hurwitzZeta` / 引理 `differentiableAt_hurwitzZeta`

English:
lemma differentiableAt_hurwitzZeta
  given: (a : UnitAddCircle) {s : Complex} (hs : s != 1)
  proof: (differentiableAt_hurwitzZetaEven a hs).add (differentiable_hurwitzZetaOdd a s)

中文:
引理 differentiableAt_hurwitzZeta
  条件: (a : UnitAddCircle) {s : 复形} (hs : s != 1)
  证明: (differentiableAt_hurwitzZetaEven a hs).add (differentiable_hurwitzZetaOdd a s)

Depends on / 依赖: Icc_subset_Ici_iff, Ico_subset_Ici_self, Ico_subset_Ico_left, Logical, differentiableAt_hurwitzZetaEven, differentiable_hurwitzZetaOdd, equivalences, however, stated
-/
lemma differentiableAt_hurwitzZeta (a : UnitAddCircle) {s : Complex} (hs : s != 1) :
    DifferentiableAt Complex (hurwitzZeta a) s :=
  (differentiableAt_hurwitzZetaEven a hs).add (differentiable_hurwitzZetaOdd a s)

/--
lemma `hasSum_hurwitzZeta_of_one_lt_re` / 引理 `hasSum_hurwitzZeta_of_one_lt_re`

English:
lemma hasSum_hurwitzZeta_of_one_lt_re
  given: {a : Real} (ha : a in Icc 0 1) {s : Complex} (hs : 1 < re s)
  proof: by
  convert!
    (hasSum_nat_hurwitzZetaEven_of_mem_Icc ha hs).add (hasSum_nat_hurwitzZetaOdd_of_mem_Icc ha hs)
    using 1
  ext1 n
  -- plain `ring_nf` works here, but the following is faster:
  apply show forall (x y : Complex), x = (x + y) / 2 + (x - y) / 2 by intros; ring

中文:
引理 hasSum_hurwitzZeta_of_one_lt_re
  条件: {a : 实数} (ha : a in 闭区间 0 1) {s : 复形} (hs : 1 < re s)
  证明: by
  convert!
    (hasSum_nat_hurwitzZetaEven_of_mem_Icc ha hs).add (hasSum_nat_hurwitzZetaOdd_of_mem_Icc ha hs)
    using 1
  ext1 n
  -- plain `ring_nf` works here, but the following is faster:
  apply show forall (x y : Complex), x = (x + y) / 2 + (x - y) / 2 by intros; ring

Depends on / 依赖: convert, hasSum_nat_hurwitzZetaEven_of_mem_Icc, hasSum_nat_hurwitzZetaOdd_of_mem_Icc
-/
lemma hasSum_hurwitzZeta_of_one_lt_re {a : Real} (ha : a in Icc 0 1) {s : Complex} (hs : 1 < re s) :
    HasSum (fun n : Nat => 1 / (n + a : Complex) ^ s) (hurwitzZeta a s) := by
  convert!
    (hasSum_nat_hurwitzZetaEven_of_mem_Icc ha hs).add (hasSum_nat_hurwitzZetaOdd_of_mem_Icc ha hs)
    using 1
  ext1 n
  -- plain `ring_nf` works here, but the following is faster:
  apply show forall (x y : Complex), x = (x + y) / 2 + (x - y) / 2 by intros; ring

/--
lemma `hurwitzZeta_residue_one` / 引理 `hurwitzZeta_residue_one`

English:
lemma hurwitzZeta_residue_one
  given: (a : UnitAddCircle)
  proof: by
  simp only [hurwitzZeta, mul_add, (by simp : 𝓝 (1 : Complex) = 𝓝 (1 + (1 - 1) * hurwitzZetaOdd a 1))]
  refine (hurwitzZetaEven_residue_one a).add ((Tendsto.mul ?_ ?_).mono_left nhdsWithin_le_nhds)
  exacts [tendsto_id.sub_const _, (differentiable_hurwitzZetaOdd a).continuous.tendsto _]

中文:
引理 hurwitzZeta_residue_one
  条件: (a : UnitAddCircle)
  证明: by
  simp only [hurwitzZeta, mul_add, (by simp : 𝓝 (1 : Complex) = 𝓝 (1 + (1 - 1) * hurwitzZetaOdd a 1))]
  refine (hurwitzZetaEven_residue_one a).add ((Tendsto.mul ?_ ?_).mono_left nhdsWithin_le_nhds)
  exacts [tendsto_id.sub_const _, (differentiable_hurwitzZetaOdd a).continuous.tendsto _]

Depends on / 依赖: Tendsto, Tendsto.mul, continuous, continuous.tendsto, differentiable_hurwitzZetaOdd, exacts, hurwitzZeta, hurwitzZetaEven_residue_one, hurwitzZetaOdd, mono_left, mul_add, nhdsWithin_le_nhds, sub_const, tendsto, tendsto_id, tendsto_id.sub_const
-/
lemma hurwitzZeta_residue_one (a : UnitAddCircle) :
    Tendsto (fun s => (s - 1) * hurwitzZeta a s) (𝓝[!=] 1) (𝓝 1) := by
  simp only [hurwitzZeta, mul_add, (by simp : 𝓝 (1 : Complex) = 𝓝 (1 + (1 - 1) * hurwitzZetaOdd a 1))]
  refine (hurwitzZetaEven_residue_one a).add ((Tendsto.mul ?_ ?_).mono_left nhdsWithin_le_nhds)
  exacts [tendsto_id.sub_const _, (differentiable_hurwitzZetaOdd a).continuous.tendsto _]

/--
lemma `differentiableAt_hurwitzZeta_sub_one_div` / 引理 `differentiableAt_hurwitzZeta_sub_one_div`

English:
lemma differentiableAt_hurwitzZeta_sub_one_div
  given: (a : UnitAddCircle)
  proof: by
  simp only [hurwitzZeta, add_sub_right_comm]
  exact (differentiableAt_hurwitzZetaEven_sub_one_div a).add (differentiable_hurwitzZetaOdd a 1)

中文:
引理 differentiableAt_hurwitzZeta_sub_one_div
  条件: (a : UnitAddCircle)
  证明: by
  simp only [hurwitzZeta, add_sub_right_comm]
  exact (differentiableAt_hurwitzZetaEven_sub_one_div a).add (differentiable_hurwitzZetaOdd a 1)

Depends on / 依赖: add_sub_right_comm, differentiableAt_hurwitzZetaEven_sub_one_div, differentiable_hurwitzZetaOdd, hurwitzZeta
-/
lemma differentiableAt_hurwitzZeta_sub_one_div (a : UnitAddCircle) :
    DifferentiableAt Complex (fun s => hurwitzZeta a s - 1 / (s - 1) / GammaReal s) 1 := by
  simp only [hurwitzZeta, add_sub_right_comm]
  exact (differentiableAt_hurwitzZetaEven_sub_one_div a).add (differentiable_hurwitzZetaOdd a 1)

/--
lemma `tendsto_hurwitzZeta_sub_one_div_nhds_one` / 引理 `tendsto_hurwitzZeta_sub_one_div_nhds_one`

English:
lemma tendsto_hurwitzZeta_sub_one_div_nhds_one
  given: (a : UnitAddCircle)
  proof: by
  simp only [hurwitzZeta, add_sub_right_comm]
  refine (tendsto_hurwitzZetaEven_sub_one_div_nhds_one a).add
    (differentiable_hurwitzZetaOdd a 1).continuousAt.tendsto

中文:
引理 tendsto_hurwitzZeta_sub_one_div_nhds_one
  条件: (a : UnitAddCircle)
  证明: by
  simp only [hurwitzZeta, add_sub_right_comm]
  refine (tendsto_hurwitzZetaEven_sub_one_div_nhds_one a).add
    (differentiable_hurwitzZetaOdd a 1).continuousAt.tendsto

Depends on / 依赖: add_sub_right_comm, continuousAt, continuousAt.tendsto, differentiable_hurwitzZetaOdd, hurwitzZeta, tendsto, tendsto_hurwitzZetaEven_sub_one_div_nhds_one
-/
lemma tendsto_hurwitzZeta_sub_one_div_nhds_one (a : UnitAddCircle) :
    Tendsto (fun s => hurwitzZeta a s - 1 / (s - 1) / GammaReal s) (𝓝 1) (𝓝 (hurwitzZeta a 1)) := by
  simp only [hurwitzZeta, add_sub_right_comm]
  refine (tendsto_hurwitzZetaEven_sub_one_div_nhds_one a).add
    (differentiable_hurwitzZetaOdd a 1).continuousAt.tendsto

/--
lemma `differentiable_hurwitzZeta_sub_hurwitzZeta` / 引理 `differentiable_hurwitzZeta_sub_hurwitzZeta`

English:
lemma differentiable_hurwitzZeta_sub_hurwitzZeta
  given: (a b : UnitAddCircle)
  proof: by
  simp only [hurwitzZeta, add_sub_add_comm]
  refine (differentiable_hurwitzZetaEven_sub_hurwitzZetaEven a b).add (.sub ?_ ?_)
  all_goals apply differentiable_hurwitzZetaOdd

中文:
引理 differentiable_hurwitzZeta_sub_hurwitzZeta
  条件: (a b : UnitAddCircle)
  证明: by
  simp only [hurwitzZeta, add_sub_add_comm]
  refine (differentiable_hurwitzZetaEven_sub_hurwitzZetaEven a b).add (.sub ?_ ?_)
  all_goals apply differentiable_hurwitzZetaOdd

Depends on / 依赖: add_sub_add_comm, all_goals, differentiable_hurwitzZetaEven_sub_hurwitzZetaEven, differentiable_hurwitzZetaOdd, hurwitzZeta
-/
lemma differentiable_hurwitzZeta_sub_hurwitzZeta (a b : UnitAddCircle) :
    Differentiable Complex (fun s => hurwitzZeta a s - hurwitzZeta b s) := by
  simp only [hurwitzZeta, add_sub_add_comm]
  refine (differentiable_hurwitzZetaEven_sub_hurwitzZetaEven a b).add (.sub ?_ ?_)
  all_goals apply differentiable_hurwitzZetaOdd

/-!
## The exponential zeta function
-/

/--
Definition of `expZeta` / `expZeta` 的定义

English:
definition expZeta
  signature: (a : UnitAddCircle) (s : Complex)
  body: cosZeta a s + I * sinZeta a s

中文:
定义 expZeta
  签名: (a : UnitAddCircle) (s : 复形)
  定义体: cosZeta a s + I * sinZeta a s

Depends on / 依赖: cosZeta, sinZeta
-/
noncomputable def expZeta (a : UnitAddCircle) (s : Complex) :=
  cosZeta a s + I * sinZeta a s

/--
lemma `cosZeta_eq` / 引理 `cosZeta_eq`

English:
lemma cosZeta_eq
  given: (a : UnitAddCircle) (s : Complex)
  proof: by
  rw [expZeta]; rw [expZeta]; rw [cosZeta_neg]; rw [sinZeta_neg]
  ring_nf

中文:
引理 cosZeta_eq
  条件: (a : UnitAddCircle) (s : 复形)
  证明: by
  rw [expZeta]; rw [expZeta]; rw [cosZeta_neg]; rw [sinZeta_neg]
  ring_nf

Depends on / 依赖: cosZeta_neg, expZeta, ring_nf, sinZeta_neg
-/
lemma cosZeta_eq (a : UnitAddCircle) (s : Complex) :
    cosZeta a s = (expZeta a s + expZeta (-a) s) / 2 := by
  rw [expZeta]; rw [expZeta]; rw [cosZeta_neg]; rw [sinZeta_neg]
  ring_nf

/--
lemma `sinZeta_eq` / 引理 `sinZeta_eq`

English:
lemma sinZeta_eq
  given: (a : UnitAddCircle) (s : Complex)
  proof: by
  rw [expZeta]; rw [expZeta]; rw [cosZeta_neg]; rw [sinZeta_neg]
  field

中文:
引理 sinZeta_eq
  条件: (a : UnitAddCircle) (s : 复形)
  证明: by
  rw [expZeta]; rw [expZeta]; rw [cosZeta_neg]; rw [sinZeta_neg]
  field

Depends on / 依赖: cosZeta_neg, expZeta, sinZeta_neg
-/
lemma sinZeta_eq (a : UnitAddCircle) (s : Complex) :
    sinZeta a s = (expZeta a s - expZeta (-a) s) / (2 * I) := by
  rw [expZeta]; rw [expZeta]; rw [cosZeta_neg]; rw [sinZeta_neg]
  field

/--
lemma `hasSum_expZeta_of_one_lt_re` / 引理 `hasSum_expZeta_of_one_lt_re`

English:
lemma hasSum_expZeta_of_one_lt_re
  given: (a : Real) {s : Complex} (hs : 1 < re s)
  proof: by
  convert! (hasSum_nat_cosZeta a hs).add ((hasSum_nat_sinZeta a hs).mul_left I) using 1
  ext1 n
  simp only [mul_right_comm _ I, ← cos_add_sin_I, push_cast]
  rw [add_div]; rw [mul_div]; rw [mul_comm _ I]

中文:
引理 hasSum_expZeta_of_one_lt_re
  条件: (a : 实数) {s : 复形} (hs : 1 < re s)
  证明: by
  convert! (hasSum_nat_cosZeta a hs).add ((hasSum_nat_sinZeta a hs).mul_left I) using 1
  ext1 n
  simp only [mul_right_comm _ I, ← cos_add_sin_I, push_cast]
  rw [add_div]; rw [mul_div]; rw [mul_comm _ I]

Depends on / 依赖: add_div, convert, cos_add_sin_I, hasSum_nat_cosZeta, hasSum_nat_sinZeta, mul_comm, mul_div, mul_left, mul_right_comm
-/
lemma hasSum_expZeta_of_one_lt_re (a : Real) {s : Complex} (hs : 1 < re s) :
    HasSum (fun n : Nat => cexp (2 * π * I * a * n) / n ^ s) (expZeta a s) := by
  convert! (hasSum_nat_cosZeta a hs).add ((hasSum_nat_sinZeta a hs).mul_left I) using 1
  ext1 n
  simp only [mul_right_comm _ I, ← cos_add_sin_I, push_cast]
  rw [add_div]; rw [mul_div]; rw [mul_comm _ I]

/--
lemma `differentiableAt_expZeta` / 引理 `differentiableAt_expZeta`

English:
lemma differentiableAt_expZeta
  given: (a : UnitAddCircle) (s : Complex) (hs : s != 1 ∨ a != 0)
  proof: by
  apply DifferentiableAt.add
  · exact differentiableAt_cosZeta a hs
  · apply (differentiableAt_const _).mul (differentiableAt_sinZeta a s)

中文:
引理 differentiableAt_expZeta
  条件: (a : UnitAddCircle) (s : 复形) (hs : s != 1 ∨ a != 0)
  证明: by
  apply DifferentiableAt.add
  · exact differentiableAt_cosZeta a hs
  · apply (differentiableAt_const _).mul (differentiableAt_sinZeta a s)

Depends on / 依赖: DifferentiableAt, DifferentiableAt.add, differentiableAt_const, differentiableAt_cosZeta, differentiableAt_sinZeta
-/
lemma differentiableAt_expZeta (a : UnitAddCircle) (s : Complex) (hs : s != 1 ∨ a != 0) :
    DifferentiableAt Complex (expZeta a) s := by
  apply DifferentiableAt.add
  · exact differentiableAt_cosZeta a hs
  · apply (differentiableAt_const _).mul (differentiableAt_sinZeta a s)

/--
lemma `differentiable_expZeta_of_ne_zero` / 引理 `differentiable_expZeta_of_ne_zero`

English:
lemma differentiable_expZeta_of_ne_zero
  given: {a : UnitAddCircle} (ha : a != 0)
  proof: (differentiableAt_expZeta a · (Or.inr ha))

中文:
引理 differentiable_expZeta_of_ne_zero
  条件: {a : UnitAddCircle} (ha : a != 0)
  证明: (differentiableAt_expZeta a · (Or.inr ha))

Depends on / 依赖: Or.inr, differentiableAt_expZeta
-/
lemma differentiable_expZeta_of_ne_zero {a : UnitAddCircle} (ha : a != 0) :
    Differentiable Complex (expZeta a) :=
  (differentiableAt_expZeta a · (Or.inr ha))

/--
lemma `LSeriesHasSum_exp` / 引理 `LSeriesHasSum_exp`

English:
lemma LSeriesHasSum_exp
  given: (a : Real) {s : Complex} (hs : 1 < re s)
  proof: (hasSum_expZeta_of_one_lt_re a hs).congr_fun
    (LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs) _)

中文:
引理 LSeriesHasSum_exp
  条件: (a : 实数) {s : 复形} (hs : 1 < re s)
  证明: (hasSum_expZeta_of_one_lt_re a hs).congr_fun
    (LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs) _)

Depends on / 依赖: LSeries, LSeries.term_of_ne_zero, congr_fun, hasSum_expZeta_of_one_lt_re, ne_zero_of_one_lt_re, term_of_ne_zero
-/
lemma LSeriesHasSum_exp (a : Real) {s : Complex} (hs : 1 < re s) :
    LSeriesHasSum (cexp <| 2 * π * I * a * ·) s (expZeta a s) :=
  (hasSum_expZeta_of_one_lt_re a hs).congr_fun
    (LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs) _)


/--
lemma `hurwitzZeta_one_sub` / 引理 `hurwitzZeta_one_sub`

English:
lemma hurwitzZeta_one_sub
  statement: (a : UnitAddCircle) {s : Complex}
  proof: by
  rw [hurwitzZeta]; rw [hurwitzZetaEven_one_sub a hs hs']; rw [hurwitzZetaOdd_one_sub a hs]; rw [expZeta]; rw [expZeta]; rw [Complex.cos]; rw [Complex.sin]; rw [sinZeta_neg]; rw [cosZeta_neg]
  rw [show ↑π * I * s / 2 = ↑π * s / 2 * I by ring]; rw [show -↑π * I * s / 2 = -(↑π * s / 2) * I by ring]
  -- these `generalize` commands are not strictly needed for the `ring_nf` call to succeed, but
  -- make it run faster:
  generalize (2 * π : Complex) ^ (-s) = x
  generalize (↑π * s / 2 * I).exp = y
  generalize (-(↑π * s / 2) * I).exp = z
  ring_nf

中文:
引理 hurwitzZeta_one_sub
  结论: (a : UnitAddCircle) {s : 复形}
  证明: by
  rw [hurwitzZeta]; rw [hurwitzZetaEven_one_sub a hs hs']; rw [hurwitzZetaOdd_one_sub a hs]; rw [expZeta]; rw [expZeta]; rw [Complex.cos]; rw [Complex.sin]; rw [sinZeta_neg]; rw [cosZeta_neg]
  rw [show ↑π * I * s / 2 = ↑π * s / 2 * I by ring]; rw [show -↑π * I * s / 2 = -(↑π * s / 2) * I by ring]
  -- these `generalize` commands are not strictly needed for the `ring_nf` call to succeed, but
  -- make it run faster:
  generalize (2 * π : Complex) ^ (-s) = x
  generalize (↑π * s / 2 * I).exp = y
  generalize (-(↑π * s / 2) * I).exp = z
  ring_nf

Depends on / 依赖: Complex.cos, Complex.sin, cosZeta_neg, expZeta, hurwitzZeta, hurwitzZetaEven_one_sub, hurwitzZetaOdd_one_sub, sinZeta_neg
-/
lemma hurwitzZeta_one_sub (a : UnitAddCircle) {s : Complex}
    (hs : forall (n : Nat), s != -n) (hs' : a != 0 ∨ s != 1) :
    hurwitzZeta a (1 - s) = (2 * π) ^ (-s) * Gamma s *
    (exp (-π * I * s / 2) * expZeta a s + exp (π * I * s / 2) * expZeta (-a) s) := by
  rw [hurwitzZeta]; rw [hurwitzZetaEven_one_sub a hs hs']; rw [hurwitzZetaOdd_one_sub a hs]; rw [expZeta]; rw [expZeta]; rw [Complex.cos]; rw [Complex.sin]; rw [sinZeta_neg]; rw [cosZeta_neg]
  rw [show ↑π * I * s / 2 = ↑π * s / 2 * I by ring]; rw [show -↑π * I * s / 2 = -(↑π * s / 2) * I by ring]
  -- these `generalize` commands are not strictly needed for the `ring_nf` call to succeed, but
  -- make it run faster:
  generalize (2 * π : Complex) ^ (-s) = x
  generalize (↑π * s / 2 * I).exp = y
  generalize (-(↑π * s / 2) * I).exp = z
  ring_nf

/--
lemma `expZeta_one_sub` / 引理 `expZeta_one_sub`

English:
lemma expZeta_one_sub
  given: (a : UnitAddCircle) {s : Complex} (hs : forall (n : Nat), s != 1 - n)
  proof: by
  have hs' (n : Nat) : s != -↑n := by
    convert! hs (n + 1) using 1
    push_cast
    ring
  rw [expZeta]; rw [cosZeta_one_sub a hs]; rw [sinZeta_one_sub a hs']; rw [hurwitzZeta]; rw [hurwitzZeta]; rw [hurwitzZetaEven_neg]; rw [hurwitzZetaOdd_neg]; rw [Complex.cos]; rw [Complex.sin]
  rw [show ↑π * I * s / 2 = ↑π * s / 2 * I by ring]; rw [show -↑π * I * s / 2 = -(↑π * s / 2) * I by ring]
  -- these `generalize` commands are not strictly needed for the `ring_nf` call to succeed, but
  -- make it run faster:
  generalize (2 * π : Complex) ^ (-s) = x
  generalize (↑π * s / 2 * I).exp = y
  generalize (-(↑π * s / 2) * I).exp = z
  ring_nf
  rw [I_sq]
  ring_nf

中文:
引理 expZeta_one_sub
  条件: (a : UnitAddCircle) {s : 复形} (hs : 对任意 (n : 自然数), s != 1 - n)
  证明: by
  have hs' (n : Nat) : s != -↑n := by
    convert! hs (n + 1) using 1
    push_cast
    ring
  rw [expZeta]; rw [cosZeta_one_sub a hs]; rw [sinZeta_one_sub a hs']; rw [hurwitzZeta]; rw [hurwitzZeta]; rw [hurwitzZetaEven_neg]; rw [hurwitzZetaOdd_neg]; rw [Complex.cos]; rw [Complex.sin]
  rw [show ↑π * I * s / 2 = ↑π * s / 2 * I by ring]; rw [show -↑π * I * s / 2 = -(↑π * s / 2) * I by ring]
  -- these `generalize` commands are not strictly needed for the `ring_nf` call to succeed, but
  -- make it run faster:
  generalize (2 * π : Complex) ^ (-s) = x
  generalize (↑π * s / 2 * I).exp = y
  generalize (-(↑π * s / 2) * I).exp = z
  ring_nf
  rw [I_sq]
  ring_nf

Depends on / 依赖: Complex.cos, Complex.sin, convert, cosZeta_one_sub, expZeta, hurwitzZeta, hurwitzZetaEven_neg, hurwitzZetaOdd_neg, sinZeta_one_sub
-/
lemma expZeta_one_sub (a : UnitAddCircle) {s : Complex} (hs : forall (n : Nat), s != 1 - n) :
    expZeta a (1 - s) = (2 * π) ^ (-s) * Gamma s *
    (exp (π * I * s / 2) * hurwitzZeta a s + exp (-π * I * s / 2) * hurwitzZeta (-a) s) := by
  have hs' (n : Nat) : s != -↑n := by
    convert! hs (n + 1) using 1
    push_cast
    ring
  rw [expZeta]; rw [cosZeta_one_sub a hs]; rw [sinZeta_one_sub a hs']; rw [hurwitzZeta]; rw [hurwitzZeta]; rw [hurwitzZetaEven_neg]; rw [hurwitzZetaOdd_neg]; rw [Complex.cos]; rw [Complex.sin]
  rw [show ↑π * I * s / 2 = ↑π * s / 2 * I by ring]; rw [show -↑π * I * s / 2 = -(↑π * s / 2) * I by ring]
  -- these `generalize` commands are not strictly needed for the `ring_nf` call to succeed, but
  -- make it run faster:
  generalize (2 * π : Complex) ^ (-s) = x
  generalize (↑π * s / 2 * I).exp = y
  generalize (-(↑π * s / 2) * I).exp = z
  ring_nf
  rw [I_sq]
  ring_nf

end HurwitzZeta
