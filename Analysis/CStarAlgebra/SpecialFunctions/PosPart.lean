/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-! # C⋆-algebraic facts about `a⁺` and `a⁻`. -/

public section

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace CStarAlgebra

section SpanNonneg

open Submodule

/--
lemma `span_nonneg_inter_closedBall` / 引理 `span_nonneg_inter_closedBall`

English:
lemma span_nonneg_inter_closedBall
  given: {r : Real} (hr : 0 < r)
  proof: by
  rw [eq_top_iff]; rw [← span_nonneg]; rw [span_le]
  intro x hx
  obtain (rfl | hx_pos) := eq_zero_or_norm_pos x
  · exact zero_mem _
  · suffices (r * ‖x‖⁻¹ : Complex)⁻¹ • ((r * ‖x‖⁻¹ : Complex) • x) = x by
      rw [← this]
      refine smul_mem _ _ (subset_span <| Set.mem_inter ?_ ?_)
      ·

中文:
引理 span_nonneg_inter_closedBall
  条件: {r : 实数} (hr : 0 < r)
  证明: by
  rw [eq_top_iff]; rw [← span_nonneg]; rw [span_le]
  intro x hx
  obtain (rfl | hx_pos) := eq_zero_or_norm_pos x
  · exact zero_mem _
  · suffices (r * ‖x‖⁻¹ : Complex)⁻¹ • ((r * ‖x‖⁻¹ : Complex) • x) = x by
      rw [← this]
      refine smul_mem _ _ (subset_span <| Set.mem_inter ?_ ?_)
      ·

Depends on / 依赖: Set.mem_inter, abs_of_pos, eq_top_iff, eq_zero_or_norm_pos, hx_pos, hx_pos.ne, mem_inter, mul_smul, norm_smul, smul_mem, smul_nonneg, span_le, span_nonneg, subset_span, zero_mem
-/
lemma span_nonneg_inter_closedBall {r : Real} (hr : 0 < r) :
    span Complex ({x : A | 0 <= x} inter Metric.closedBall 0 r) = ⊤ := by
  rw [eq_top_iff]; rw [← span_nonneg]; rw [span_le]
  intro x hx
  obtain (rfl | hx_pos) := eq_zero_or_norm_pos x
  · exact zero_mem _
  · suffices (r * ‖x‖⁻¹ : Complex)⁻¹ • ((r * ‖x‖⁻¹ : Complex) • x) = x by
      rw [← this]
      refine smul_mem _ _ (subset_span <| Set.mem_inter ?_ ?_)
      · norm_cast
        exact smul_nonneg (by positivity) hx
      · simp [mul_smul, norm_smul, abs_of_pos hr, inv_mul_cancel₀ hx_pos.ne']
    apply inv_smul_smul₀
    norm_cast
    positivity

/--
lemma `span_nonneg_inter_ball` / 引理 `span_nonneg_inter_ball`

English:
lemma span_nonneg_inter_ball
  given: {r : Real} (hr : 0 < r)
  proof: by
  rw [eq_top_iff]; rw [← span_nonneg_inter_closedBall (half_pos hr)]
  gcongr
exact Metric.closedBall_subset_ball half_lt_self hr

中文:
引理 span_nonneg_inter_ball
  条件: {r : 实数} (hr : 0 < r)
  证明: by
  rw [eq_top_iff]; rw [← span_nonneg_inter_closedBall (half_pos hr)]
  gcongr
exact Metric.closedBall_subset_ball half_lt_self hr

Depends on / 依赖: Metric, Metric.closedBall_subset_ball, closedBall_subset_ball, eq_top_iff, half_lt_self, half_pos, span_nonneg_inter_closedBall
-/
lemma span_nonneg_inter_ball {r : Real} (hr : 0 < r) :
    span Complex ({x : A | 0 <= x} inter Metric.ball 0 r) = ⊤ := by
  rw [eq_top_iff]; rw [← span_nonneg_inter_closedBall (half_pos hr)]
  gcongr
exact Metric.closedBall_subset_ball half_lt_self hr

/--
lemma `span_nonneg_inter_unitClosedBall` / 引理 `span_nonneg_inter_unitClosedBall`

English:
lemma span_nonneg_inter_unitClosedBall
  proof: span_nonneg_inter_closedBall zero_lt_one

中文:
引理 span_nonneg_inter_unitClosedBall
  证明: span_nonneg_inter_closedBall zero_lt_one

Depends on / 依赖: NNNorm, SeminormedGroup, SeminormedGroup.toNNNorm, span_nonneg_inter_closedBall, toNNNorm, zero_lt_one
-/
lemma span_nonneg_inter_unitClosedBall :
    span Complex ({x : A | 0 <= x} inter Metric.closedBall 0 1) = ⊤ :=
  span_nonneg_inter_closedBall zero_lt_one

/--
lemma `span_nonneg_inter_unitBall` / 引理 `span_nonneg_inter_unitBall`

English:
lemma span_nonneg_inter_unitBall
  proof: span_nonneg_inter_ball zero_lt_one

中文:
引理 span_nonneg_inter_unitBall
  证明: span_nonneg_inter_ball zero_lt_one

Depends on / 依赖: span_nonneg_inter_ball, zero_lt_one
-/
lemma span_nonneg_inter_unitBall :
    span Complex ({x : A | 0 <= x} inter Metric.ball 0 1) = ⊤ :=
  span_nonneg_inter_ball zero_lt_one

end SpanNonneg

open Complex in
/--
lemma `exists_sum_four_nonneg` / 引理 `exists_sum_four_nonneg`

English:
lemma exists_sum_four_nonneg
  statement: {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
  proof: by
  use ![(realPart a)⁺, (imaginaryPart a)⁺, (realPart a)⁻, (imaginaryPart a)⁻]
  rw [← and_assoc]; rw [← forall_and]
  constructor
  · intro i
    fin_cases i
    all_goals
      constructor
      · simp
        cfc_tac
.trans realPart.norm_le a · exact CStarAlgebra.norm_posPart_le _
.trans imagin

中文:
引理 存在_sum_four_nonneg
  结论: {A : 类型} [非幺CStar代数 A] [偏序 A]
  证明: by
  use ![(realPart a)⁺, (imaginaryPart a)⁺, (realPart a)⁻, (imaginaryPart a)⁻]
  rw [← and_assoc]; rw [← forall_and]
  constructor
  · intro i
    fin_cases i
    all_goals
      constructor
      · simp
        cfc_tac
.trans realPart.norm_le a · exact CStarAlgebra.norm_posPart_le _
.trans imagin

Depends on / 依赖: CStarAlgebra, CStarAlgebra.linear_combinatio, CStarAlgebra.norm_negPart_le, CStarAlgebra.norm_posPart_le, all_goals, and_assoc, cfc_tac, fin_cases, forall_and, imaginaryPart, imaginaryPart.norm_le, linear_combinatio, norm_le, norm_negPart_le, norm_posPart_le, nth_rw, realPart, realPart.norm_le
-/
lemma exists_sum_four_nonneg {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (a : A) :
    exists x : Fin 4 -> A, (forall i, 0 <= x i) ∧ (forall i, ‖x i‖ <= ‖a‖) ∧ a = ∑ i : Fin 4, I ^ (i : Nat) • x i := by
  use ![(realPart a)⁺, (imaginaryPart a)⁺, (realPart a)⁻, (imaginaryPart a)⁻]
  rw [← and_assoc]; rw [← forall_and]
  constructor
  · intro i
    fin_cases i
    all_goals
      constructor
      · simp
        cfc_tac
.trans realPart.norm_le a · exact CStarAlgebra.norm_posPart_le _
.trans imaginaryPart.norm_le a · exact CStarAlgebra.norm_posPart_le _
.trans realPart.norm_le a · exact CStarAlgebra.norm_negPart_le _
.trans imaginaryPart.norm_le a · exact CStarAlgebra.norm_negPart_le _
  · nth_rw 1 [← CStarAlgebra.linear_combination_nonneg a]
    simp only [Fin.sum_univ_four, Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod, I_sq,
      I_pow_three]
    module

end CStarAlgebra
