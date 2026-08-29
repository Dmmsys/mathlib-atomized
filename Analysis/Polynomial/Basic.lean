/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Devon Tuma
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Limits related to polynomial and rational functions

This file proves basic facts about limits of polynomial and rational functions.
The main result is `Polynomial.isEquivalent_atTop_lead`, which states that for
any polynomial `P` of degree `n` with leading coefficient `a`, the corresponding
polynomial function is equivalent to `a * x^n` as `x` goes to +∞.

We can then use this result to prove various limits for polynomial and rational
functions, depending on the degrees and leading coefficients of the considered
polynomials.
-/

public section


open Filter Finset Asymptotics

open Asymptotics Polynomial Topology

namespace Polynomial

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] (P Q : 𝕜[X])

/--
theorem `eventually_atTop_not_isRoot` / 定理 `eventually_atTop_not_isRoot`

English:
theorem eventually_atTop_not_isRoot
  given: (hP : P != 0)
  statement: forallᶠ x in atTop, ¬P.IsRoot x
  proof: atTop_le_cofinite (finite_setOfPred_isRoot hP).compl_mem_cofinite

@[deprecated (since := "2026-02-05")] alias eventually_no_roots := eventually_atTop_not_isRoot

中文:
定理 eventually_atTop_not_isRoot
  条件: (hP : P != 0)
  结论: 对任意ᶠ x in atTop, ¬P.IsRoot x
  证明: atTop_le_cofinite (finite_setOfPred_isRoot hP).compl_mem_cofinite

@[deprecated (since := "2026-02-05")] alias eventually_no_roots := eventually_atTop_not_isRoot

Depends on / 依赖: atTop_le_cofinite, compl_mem_cofinite, finite_setOfPred_isRoot
-/
theorem eventually_atTop_not_isRoot (hP : P != 0) : forallᶠ x in atTop, ¬P.IsRoot x :=
atTop_le_cofinite (finite_setOfPred_isRoot hP).compl_mem_cofinite

@[deprecated (since := "2026-02-05")] alias eventually_no_roots := eventually_atTop_not_isRoot

/--
theorem `eventually_atBot_not_isRoot` / 定理 `eventually_atBot_not_isRoot`

English:
theorem eventually_atBot_not_isRoot
  given: (hP : P != 0)
  statement: forallᶠ x in atBot, ¬P.IsRoot x
  proof: atBot_le_cofinite (finite_setOfPred_isRoot hP).compl_mem_cofinite

中文:
定理 eventually_atBot_not_isRoot
  条件: (hP : P != 0)
  结论: 对任意ᶠ x in atBot, ¬P.IsRoot x
  证明: atBot_le_cofinite (finite_setOfPred_isRoot hP).compl_mem_cofinite

Depends on / 依赖: atBot_le_cofinite, compl_mem_cofinite, finite_setOfPred_isRoot
-/
theorem eventually_atBot_not_isRoot (hP : P != 0) : forallᶠ x in atBot, ¬P.IsRoot x :=
atBot_le_cofinite (finite_setOfPred_isRoot hP).compl_mem_cofinite

variable [OrderTopology 𝕜]

section PolynomialAtTop

/--
theorem `isEquivalent_atTop_lead` / 定理 `isEquivalent_atTop_lead`

English:
theorem isEquivalent_atTop_lead
  proof: by
  by_cases h : P = 0
  · simp [h, IsEquivalent.refl]
  · simp only [Polynomial.eval_eq_sum_range, sum_range_succ]
    exact
      IsLittleO.add_isEquivalent
        (IsLittleO.fun_sum fun i hi =>
          IsLittleO.const_mul_left
            ((IsLittleO.const_mul_right fun hz => h <| leadingCoeff_eq_zero.mp hz) <|
              isLittleO_pow_pow_atTop_of_lt (mem_range.mp hi))
            _)
        IsEquivalent.refl

中文:
定理 isEquivalent_atTop_lead
  证明: by
  by_cases h : P = 0
  · simp [h, IsEquivalent.refl]
  · simp only [Polynomial.eval_eq_sum_range, sum_range_succ]
    exact
      IsLittleO.add_isEquivalent
        (IsLittleO.fun_sum fun i hi =>
          IsLittleO.const_mul_left
            ((IsLittleO.const_mul_right fun hz => h <| leadingCoeff_eq_zero.mp hz) <|
              isLittleO_pow_pow_atTop_of_lt (mem_range.mp hi))
            _)
        IsEquivalent.refl

Depends on / 依赖: IsEquivalent, IsEquivalent.refl, IsLittleO, IsLittleO.add_isEquivalent, IsLittleO.const_mul_left, IsLittleO.const_mul_right, IsLittleO.fun_sum, Polynomial, Polynomial.eval_eq_sum_range, add_isEquivalent, const_mul_left, const_mul_right, eval_eq_sum_range, fun_sum, isLittleO_pow_pow_atTop_of_lt, leadingCoeff_eq_zero, leadingCoeff_eq_zero.mp, mem_range, mem_range.mp, sum_range_succ
-/
theorem isEquivalent_atTop_lead :
    (fun x => eval x P) ~[atTop] fun x => P.leadingCoeff * x ^ P.natDegree := by
  by_cases h : P = 0
  · simp [h, IsEquivalent.refl]
  · simp only [Polynomial.eval_eq_sum_range, sum_range_succ]
    exact
      IsLittleO.add_isEquivalent
        (IsLittleO.fun_sum fun i hi =>
          IsLittleO.const_mul_left
            ((IsLittleO.const_mul_right fun hz => h <| leadingCoeff_eq_zero.mp hz) <|
              isLittleO_pow_pow_atTop_of_lt (mem_range.mp hi))
            _)
        IsEquivalent.refl

/--
theorem `tendsto_atTop_of_leadingCoeff_nonneg` / 定理 `tendsto_atTop_of_leadingCoeff_nonneg`

English:
theorem tendsto_atTop_of_leadingCoeff_nonneg
  given: (hdeg : 0 < P.degree) (hnng : 0 <= P.leadingCoeff)
  proof: P.isEquivalent_atTop_lead.symm.tendsto_atTop
tendsto_const_mul_pow_atTop (natDegree_pos_iff_degree_pos.2 hdeg).ne'
hnng.lt_of_ne' leadingCoeff_ne_zero.mpr ne_zero_of_degree_gt hdeg

中文:
定理 tendsto_atTop_of_leadingCoeff_nonneg
  条件: (hdeg : 0 < P.degree) (hnng : 0 <= P.leadingCoeff)
  证明: P.isEquivalent_atTop_lead.symm.tendsto_atTop
tendsto_const_mul_pow_atTop (natDegree_pos_iff_degree_pos.2 hdeg).ne'
hnng.lt_of_ne' leadingCoeff_ne_zero.mpr ne_zero_of_degree_gt hdeg

Depends on / 依赖: P.isEquivalent_atTop_lead.symm.tendsto_atTop, hnng.lt_of_ne, isEquivalent_atTop_lead, leadingCoeff_ne_zero, leadingCoeff_ne_zero.mpr, lt_of_ne, natDegree_pos_iff_degree_pos, ne_zero_of_degree_gt, tendsto_atTop, tendsto_const_mul_pow_atTop
-/
theorem tendsto_atTop_of_leadingCoeff_nonneg (hdeg : 0 < P.degree) (hnng : 0 <= P.leadingCoeff) :
    Tendsto (fun x => eval x P) atTop atTop :=
P.isEquivalent_atTop_lead.symm.tendsto_atTop
tendsto_const_mul_pow_atTop (natDegree_pos_iff_degree_pos.2 hdeg).ne'
hnng.lt_of_ne' leadingCoeff_ne_zero.mpr ne_zero_of_degree_gt hdeg

/--
theorem `tendsto_atTop_iff_leadingCoeff_nonneg` / 定理 `tendsto_atTop_iff_leadingCoeff_nonneg`

English:
theorem tendsto_atTop_iff_leadingCoeff_nonneg
  proof: by
  refine ⟨fun h => ?_, fun h => tendsto_atTop_of_leadingCoeff_nonneg P h.1 h.2⟩
  have : Tendsto (fun x => P.leadingCoeff * x ^ P.natDegree) atTop atTop :=
    (isEquivalent_atTop_lead P).tendsto_atTop h
  rw [tendsto_const_mul_pow_atTop_iff]; rw [← pos_iff_ne_zero]; rw [natDegree_pos_iff_degree_pos] at this
  exact ⟨this.1, this.2.le⟩

中文:
定理 tendsto_atTop_iff_leadingCoeff_nonneg
  证明: by
  refine ⟨fun h => ?_, fun h => tendsto_atTop_of_leadingCoeff_nonneg P h.1 h.2⟩
  have : Tendsto (fun x => P.leadingCoeff * x ^ P.natDegree) atTop atTop :=
    (isEquivalent_atTop_lead P).tendsto_atTop h
  rw [tendsto_const_mul_pow_atTop_iff]; rw [← pos_iff_ne_zero]; rw [natDegree_pos_iff_degree_pos] at this
  exact ⟨this.1, this.2.le⟩

Depends on / 依赖: P.leadingCoeff, P.natDegree, Tendsto, isEquivalent_atTop_lead, leadingCoeff, natDegree, natDegree_pos_iff_degree_pos, pos_iff_ne_zero, tendsto_atTop, tendsto_atTop_of_leadingCoeff_nonneg, tendsto_const_mul_pow_atTop_iff
-/
theorem tendsto_atTop_iff_leadingCoeff_nonneg :
    Tendsto (fun x => eval x P) atTop atTop ↔ 0 < P.degree ∧ 0 <= P.leadingCoeff := by
  refine ⟨fun h => ?_, fun h => tendsto_atTop_of_leadingCoeff_nonneg P h.1 h.2⟩
  have : Tendsto (fun x => P.leadingCoeff * x ^ P.natDegree) atTop atTop :=
    (isEquivalent_atTop_lead P).tendsto_atTop h
  rw [tendsto_const_mul_pow_atTop_iff]; rw [← pos_iff_ne_zero]; rw [natDegree_pos_iff_degree_pos] at this
  exact ⟨this.1, this.2.le⟩

/--
theorem `tendsto_atBot_iff_leadingCoeff_nonpos` / 定理 `tendsto_atBot_iff_leadingCoeff_nonpos`

English:
theorem tendsto_atBot_iff_leadingCoeff_nonpos
  proof: by
  simp only [← tendsto_neg_atTop_iff, ← eval_neg, tendsto_atTop_iff_leadingCoeff_nonneg,
    degree_neg, leadingCoeff_neg, neg_nonneg]

中文:
定理 tendsto_atBot_iff_leadingCoeff_nonpos
  证明: by
  simp only [← tendsto_neg_atTop_iff, ← eval_neg, tendsto_atTop_iff_leadingCoeff_nonneg,
    degree_neg, leadingCoeff_neg, neg_nonneg]

Depends on / 依赖: degree_neg, eval_neg, leadingCoeff_neg, neg_nonneg, tendsto_atTop_iff_leadingCoeff_nonneg, tendsto_neg_atTop_iff
-/
theorem tendsto_atBot_iff_leadingCoeff_nonpos :
    Tendsto (fun x => eval x P) atTop atBot ↔ 0 < P.degree ∧ P.leadingCoeff <= 0 := by
  simp only [← tendsto_neg_atTop_iff, ← eval_neg, tendsto_atTop_iff_leadingCoeff_nonneg,
    degree_neg, leadingCoeff_neg, neg_nonneg]

/--
theorem `tendsto_atBot_of_leadingCoeff_nonpos` / 定理 `tendsto_atBot_of_leadingCoeff_nonpos`

English:
theorem tendsto_atBot_of_leadingCoeff_nonpos
  given: (hdeg : 0 < P.degree) (hnps : P.leadingCoeff <= 0)
  proof: P.tendsto_atBot_iff_leadingCoeff_nonpos.2 ⟨hdeg, hnps⟩

中文:
定理 tendsto_atBot_of_leadingCoeff_nonpos
  条件: (hdeg : 0 < P.degree) (hnps : P.leadingCoeff <= 0)
  证明: P.tendsto_atBot_iff_leadingCoeff_nonpos.2 ⟨hdeg, hnps⟩

Depends on / 依赖: P.tendsto_atBot_iff_leadingCoeff_nonpos, tendsto_atBot_iff_leadingCoeff_nonpos
-/
theorem tendsto_atBot_of_leadingCoeff_nonpos (hdeg : 0 < P.degree) (hnps : P.leadingCoeff <= 0) :
    Tendsto (fun x => eval x P) atTop atBot :=
  P.tendsto_atBot_iff_leadingCoeff_nonpos.2 ⟨hdeg, hnps⟩

/--
theorem `abs_tendsto_atTop` / 定理 `abs_tendsto_atTop`

English:
theorem abs_tendsto_atTop
  given: (hdeg : 0 < P.degree)
  proof: by
  rcases le_total 0 P.leadingCoeff with hP | hP
  · exact tendsto_abs_atTop_atTop.comp (P.tendsto_atTop_of_leadingCoeff_nonneg hdeg hP)
  · exact tendsto_abs_atBot_atTop.comp (P.tendsto_atBot_of_leadingCoeff_nonpos hdeg hP)

中文:
定理 abs_tendsto_atTop
  条件: (hdeg : 0 < P.degree)
  证明: by
  rcases le_total 0 P.leadingCoeff with hP | hP
  · exact tendsto_abs_atTop_atTop.comp (P.tendsto_atTop_of_leadingCoeff_nonneg hdeg hP)
  · exact tendsto_abs_atBot_atTop.comp (P.tendsto_atBot_of_leadingCoeff_nonpos hdeg hP)

Depends on / 依赖: P.leadingCoeff, P.tendsto_atBot_of_leadingCoeff_nonpos, P.tendsto_atTop_of_leadingCoeff_nonneg, le_total, leadingCoeff, tendsto_abs_atBot_atTop, tendsto_abs_atBot_atTop.comp, tendsto_abs_atTop_atTop, tendsto_abs_atTop_atTop.comp, tendsto_atBot_of_leadingCoeff_nonpos, tendsto_atTop_of_leadingCoeff_nonneg
-/
theorem abs_tendsto_atTop (hdeg : 0 < P.degree) :
    Tendsto (fun x => abs <| eval x P) atTop atTop := by
  rcases le_total 0 P.leadingCoeff with hP | hP
  · exact tendsto_abs_atTop_atTop.comp (P.tendsto_atTop_of_leadingCoeff_nonneg hdeg hP)
  · exact tendsto_abs_atBot_atTop.comp (P.tendsto_atBot_of_leadingCoeff_nonpos hdeg hP)

/--
theorem `isBoundedUnder_abs_atTop_iff` / 定理 `isBoundedUnder_abs_atTop_iff`

English:
theorem isBoundedUnder_abs_atTop_iff
  proof: by
  refine ⟨fun h => ?_, fun h => ⟨|P.coeff 0|, eventually_map.mpr (Eventually.of_forall
    (forall_imp (fun _ => le_of_eq) fun x => congr_arg abs <| _root_.trans (congr_arg (eval x)
    (eq_C_of_degree_le_zero h)) eval_C))⟩⟩
  contrapose! h
  exact not_isBoundedUnder_of_tendsto_atTop (abs_tendsto_atTop P h)

@[deprecated (since := "2026-02-05")] alias abs_isBoundedUnder_iff := isBoundedUnder_abs_atTop_iff

中文:
定理 isBoundedUnder_abs_atTop_iff
  证明: by
  refine ⟨fun h => ?_, fun h => ⟨|P.coeff 0|, eventually_map.mpr (Eventually.of_forall
    (forall_imp (fun _ => le_of_eq) fun x => congr_arg abs <| _root_.trans (congr_arg (eval x)
    (eq_C_of_degree_le_zero h)) eval_C))⟩⟩
  contrapose! h
  exact not_isBoundedUnder_of_tendsto_atTop (abs_tendsto_atTop P h)

@[deprecated (since := "2026-02-05")] alias abs_isBoundedUnder_iff := isBoundedUnder_abs_atTop_iff

Depends on / 依赖: Eventually, Eventually.of_forall, P.coeff, _root_, _root_.trans, abs_tendsto_atTop, congr_arg, contrapose, eq_C_of_degree_le_zero, eval_C, eventually_map, eventually_map.mpr, forall_imp, le_of_eq, not_isBoundedUnder_of_tendsto_atTop, of_forall
-/
theorem isBoundedUnder_abs_atTop_iff :
    (IsBoundedUnder (· <= ·) atTop fun x => |eval x P|) ↔ P.degree <= 0 := by
  refine ⟨fun h => ?_, fun h => ⟨|P.coeff 0|, eventually_map.mpr (Eventually.of_forall
    (forall_imp (fun _ => le_of_eq) fun x => congr_arg abs <| _root_.trans (congr_arg (eval x)
    (eq_C_of_degree_le_zero h)) eval_C))⟩⟩
  contrapose! h
  exact not_isBoundedUnder_of_tendsto_atTop (abs_tendsto_atTop P h)

@[deprecated (since := "2026-02-05")] alias abs_isBoundedUnder_iff := isBoundedUnder_abs_atTop_iff

/--
theorem `abs_tendsto_atTop_iff` / 定理 `abs_tendsto_atTop_iff`

English:
theorem abs_tendsto_atTop_iff
  statement: Tendsto (fun x => abs <| eval x P) atTop atTop ↔ 0 < P.degree
  proof: ⟨fun h => not_le.mp (mt (isBoundedUnder_abs_atTop_iff P).mpr
    (not_isBoundedUnder_of_tendsto_atTop h)), abs_tendsto_atTop P⟩

中文:
定理 abs_tendsto_atTop_iff
  结论: 收敛 (fun x => abs <| eval x P) atTop atTop ↔ 0 < P.degree
  证明: ⟨fun h => not_le.mp (mt (isBoundedUnder_abs_atTop_iff P).mpr
    (not_isBoundedUnder_of_tendsto_atTop h)), abs_tendsto_atTop P⟩

Depends on / 依赖: abs_tendsto_atTop, isBoundedUnder_abs_atTop_iff, not_isBoundedUnder_of_tendsto_atTop, not_le, not_le.mp
-/
theorem abs_tendsto_atTop_iff : Tendsto (fun x => abs <| eval x P) atTop atTop ↔ 0 < P.degree :=
  ⟨fun h => not_le.mp (mt (isBoundedUnder_abs_atTop_iff P).mpr
    (not_isBoundedUnder_of_tendsto_atTop h)), abs_tendsto_atTop P⟩

/--
theorem `tendsto_nhds_iff` / 定理 `tendsto_nhds_iff`

English:
theorem tendsto_nhds_iff
  given: {c : 𝕜}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := P.isEquivalent_atTop_lead.tendsto_nhds h
    by_cases hP : P.leadingCoeff = 0
    · simp only [hP, zero_mul, tendsto_const_nhds_iff] at this
      exact ⟨_root_.trans hP this, by simp [leadingCoeff_eq_zero.1 hP]⟩
    · rw [tendsto_const_mul_pow_nhds_iff hP, natDegree_eq_zero_iff_degree_le_zero] at this
      exact this.symm
  · refine P.isEquivalent_atTop_lead.symm.tendsto_nhds ?_
    have : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.2 h.2
    simp only [h.1, this, pow_zero, mul_one]
    exact tendsto_const_nhds

中文:
定理 tendsto_nhds_iff
  条件: {c : 𝕜}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := P.isEquivalent_atTop_lead.tendsto_nhds h
    by_cases hP : P.leadingCoeff = 0
    · simp only [hP, zero_mul, tendsto_const_nhds_iff] at this
      exact ⟨_root_.trans hP this, by simp [leadingCoeff_eq_zero.1 hP]⟩
    · rw [tendsto_const_mul_pow_nhds_iff hP, natDegree_eq_zero_iff_degree_le_zero] at this
      exact this.symm
  · refine P.isEquivalent_atTop_lead.symm.tendsto_nhds ?_
    have : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.2 h.2
    simp only [h.1, this, pow_zero, mul_one]
    exact tendsto_const_nhds

Depends on / 依赖: P.isEquivalent_atTop_lead.symm.tendsto_nhds, P.isEquivalent_atTop_lead.tendsto_nhds, P.leadingCoeff, P.natDegree, _root_, _root_.trans, isEquivalent_atTop_lead, leadingCoeff, leadingCoeff_eq_zero, natDegree, natDegree_eq_zero_iff_degree_le_zero, pow_, tendsto_const_mul_pow_nhds_iff, tendsto_const_nhds_iff, tendsto_nhds, this.symm, zero_mul
-/
theorem tendsto_nhds_iff {c : 𝕜} :
    Tendsto (fun x => eval x P) atTop (𝓝 c) ↔ P.leadingCoeff = c ∧ P.degree <= 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := P.isEquivalent_atTop_lead.tendsto_nhds h
    by_cases hP : P.leadingCoeff = 0
    · simp only [hP, zero_mul, tendsto_const_nhds_iff] at this
      exact ⟨_root_.trans hP this, by simp [leadingCoeff_eq_zero.1 hP]⟩
    · rw [tendsto_const_mul_pow_nhds_iff hP, natDegree_eq_zero_iff_degree_le_zero] at this
      exact this.symm
  · refine P.isEquivalent_atTop_lead.symm.tendsto_nhds ?_
    have : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.2 h.2
    simp only [h.1, this, pow_zero, mul_one]
    exact tendsto_const_nhds

end PolynomialAtTop

section PolynomialAtBot

/--
theorem `isEquivalent_atBot_lead` / 定理 `isEquivalent_atBot_lead`

English:
theorem isEquivalent_atBot_lead
  statement: P.eval ~[atBot] (P.leadingCoeff * · ^ P.natDegree)
  proof: by
  convert! (P.comp (-X)).isEquivalent_atTop_lead.comp_tendsto tendsto_neg_atBot_atTop using 2
  · simp
  · rw [Function.comp_apply, comp_neg_X_leadingCoeff_eq, ← mul_rotate]
    simp [natDegree_comp, ← mul_pow, mul_comm]

中文:
定理 isEquivalent_atBot_lead
  结论: P.eval ~[atBot] (P.leadingCoeff * · ^ P.natDegree)
  证明: by
  convert! (P.comp (-X)).isEquivalent_atTop_lead.comp_tendsto tendsto_neg_atBot_atTop using 2
  · simp
  · rw [Function.comp_apply, comp_neg_X_leadingCoeff_eq, ← mul_rotate]
    simp [natDegree_comp, ← mul_pow, mul_comm]

Depends on / 依赖: Function, Function.comp_apply, P.comp, comp_apply, comp_neg_X_leadingCoeff_eq, comp_tendsto, convert, isEquivalent_atTop_lead, isEquivalent_atTop_lead.comp_tendsto, mul_comm, mul_pow, mul_rotate, natDegree_comp, tendsto_neg_atBot_atTop
-/
theorem isEquivalent_atBot_lead : P.eval ~[atBot] (P.leadingCoeff * · ^ P.natDegree) := by
  convert! (P.comp (-X)).isEquivalent_atTop_lead.comp_tendsto tendsto_neg_atBot_atTop using 2
  · simp
  · rw [Function.comp_apply, comp_neg_X_leadingCoeff_eq, ← mul_rotate]
    simp [natDegree_comp, ← mul_pow, mul_comm]

/--
theorem `abs_tendsto_atBot` / 定理 `abs_tendsto_atBot`

English:
theorem abs_tendsto_atBot
  given: (hdeg : 0 < P.degree)
  statement: Tendsto (|P.eval ·|) atBot atTop
  proof: by
  convert! ((P.comp (-X)).abs_tendsto_atTop (by simp [hdeg])).comp tendsto_neg_atBot_atTop using 2
  simp

中文:
定理 abs_tendsto_atBot
  条件: (hdeg : 0 < P.degree)
  结论: 收敛 (|P.eval ·|) atBot atTop
  证明: by
  convert! ((P.comp (-X)).abs_tendsto_atTop (by simp [hdeg])).comp tendsto_neg_atBot_atTop using 2
  simp

Depends on / 依赖: P.comp, abs_tendsto_atTop, convert, tendsto_neg_atBot_atTop
-/
theorem abs_tendsto_atBot (hdeg : 0 < P.degree) : Tendsto (|P.eval ·|) atBot atTop := by
  convert! ((P.comp (-X)).abs_tendsto_atTop (by simp [hdeg])).comp tendsto_neg_atBot_atTop using 2
  simp

/--
theorem `isBoundedUnder_abs_atBot_iff` / 定理 `isBoundedUnder_abs_atBot_iff`

English:
theorem isBoundedUnder_abs_atBot_iff
  proof: by
  refine ⟨fun h => ?_, fun h => ⟨|P.coeff 0|, eventually_map.mpr (Eventually.of_forall
    (forall_imp (fun _ => le_of_eq) fun x => congr_arg abs <| _root_.trans (congr_arg (eval x)
    (eq_C_of_degree_le_zero h)) eval_C))⟩⟩
  contrapose! h
  exact not_isBoundedUnder_of_tendsto_atTop (abs_tendsto_atBot P h)

中文:
定理 isBoundedUnder_abs_atBot_iff
  证明: by
  refine ⟨fun h => ?_, fun h => ⟨|P.coeff 0|, eventually_map.mpr (Eventually.of_forall
    (forall_imp (fun _ => le_of_eq) fun x => congr_arg abs <| _root_.trans (congr_arg (eval x)
    (eq_C_of_degree_le_zero h)) eval_C))⟩⟩
  contrapose! h
  exact not_isBoundedUnder_of_tendsto_atTop (abs_tendsto_atBot P h)

Depends on / 依赖: Eventually, Eventually.of_forall, P.coeff, _root_, _root_.trans, abs_tendsto_atBot, congr_arg, contrapose, eq_C_of_degree_le_zero, eval_C, eventually_map, eventually_map.mpr, forall_imp, le_of_eq, not_isBoundedUnder_of_tendsto_atTop, of_forall
-/
theorem isBoundedUnder_abs_atBot_iff :
    (IsBoundedUnder (· <= ·) atBot (|P.eval ·|)) ↔ P.degree <= 0 := by
  refine ⟨fun h => ?_, fun h => ⟨|P.coeff 0|, eventually_map.mpr (Eventually.of_forall
    (forall_imp (fun _ => le_of_eq) fun x => congr_arg abs <| _root_.trans (congr_arg (eval x)
    (eq_C_of_degree_le_zero h)) eval_C))⟩⟩
  contrapose! h
  exact not_isBoundedUnder_of_tendsto_atTop (abs_tendsto_atBot P h)

/--
theorem `abs_tendsto_atBot_iff` / 定理 `abs_tendsto_atBot_iff`

English:
theorem abs_tendsto_atBot_iff
  statement: Tendsto (|P.eval ·|) atBot atTop ↔ 0 < P.degree
  proof: ⟨fun h => not_le.mp (mt (isBoundedUnder_abs_atBot_iff P).mpr
    (not_isBoundedUnder_of_tendsto_atTop h)), abs_tendsto_atBot P⟩

中文:
定理 abs_tendsto_atBot_iff
  结论: 收敛 (|P.eval ·|) atBot atTop ↔ 0 < P.degree
  证明: ⟨fun h => not_le.mp (mt (isBoundedUnder_abs_atBot_iff P).mpr
    (not_isBoundedUnder_of_tendsto_atTop h)), abs_tendsto_atBot P⟩

Depends on / 依赖: abs_tendsto_atBot, isBoundedUnder_abs_atBot_iff, not_isBoundedUnder_of_tendsto_atTop, not_le, not_le.mp
-/
theorem abs_tendsto_atBot_iff : Tendsto (|P.eval ·|) atBot atTop ↔ 0 < P.degree :=
  ⟨fun h => not_le.mp (mt (isBoundedUnder_abs_atBot_iff P).mpr
    (not_isBoundedUnder_of_tendsto_atTop h)), abs_tendsto_atBot P⟩

end PolynomialAtBot

section PolynomialDivAtTop

/--
theorem `isEquivalent_atTop_div` / 定理 `isEquivalent_atTop_div`

English:
theorem isEquivalent_atTop_div
  proof: by
  by_cases hP : P = 0
  · simp [hP, IsEquivalent.refl]
  by_cases hQ : Q = 0
  · simp [hQ, IsEquivalent.refl]
  refine
    (P.isEquivalent_atTop_lead.symm.div Q.isEquivalent_atTop_lead.symm).symm.trans
      (EventuallyEq.isEquivalent ((eventually_gt_atTop 0).mono fun x hx => ?_))
  simp [← div_mul_div_comm, zpow_sub₀ hx.ne.symm]

中文:
定理 isEquivalent_atTop_div
  证明: by
  by_cases hP : P = 0
  · simp [hP, IsEquivalent.refl]
  by_cases hQ : Q = 0
  · simp [hQ, IsEquivalent.refl]
  refine
    (P.isEquivalent_atTop_lead.symm.div Q.isEquivalent_atTop_lead.symm).symm.trans
      (EventuallyEq.isEquivalent ((eventually_gt_atTop 0).mono fun x hx => ?_))
  simp [← div_mul_div_comm, zpow_sub₀ hx.ne.symm]

Depends on / 依赖: EventuallyEq, EventuallyEq.isEquivalent, IsEquivalent, IsEquivalent.refl, P.isEquivalent_atTop_lead.symm.div, Q.isEquivalent_atTop_lead.symm, div_mul_div_comm, eventually_gt_atTop, hx.ne.symm, isEquivalent, isEquivalent_atTop_lead, symm.trans
-/
theorem isEquivalent_atTop_div :
    (fun x => eval x P / eval x Q) ~[atTop] fun x =>
      P.leadingCoeff / Q.leadingCoeff * x ^ (P.natDegree - Q.natDegree : Int) := by
  by_cases hP : P = 0
  · simp [hP, IsEquivalent.refl]
  by_cases hQ : Q = 0
  · simp [hQ, IsEquivalent.refl]
  refine
    (P.isEquivalent_atTop_lead.symm.div Q.isEquivalent_atTop_lead.symm).symm.trans
      (EventuallyEq.isEquivalent ((eventually_gt_atTop 0).mono fun x hx => ?_))
  simp [← div_mul_div_comm, zpow_sub₀ hx.ne.symm]

/--
theorem `div_tendsto_atTop_zero_of_degree_lt` / 定理 `div_tendsto_atTop_zero_of_degree_lt`

English:
theorem div_tendsto_atTop_zero_of_degree_lt
  given: (hdeg : P.degree < Q.degree)
  proof: by
  by_cases hP : P = 0
  · simp [hP]
  rw [← natDegree_lt_natDegree_iff hP] at hdeg
  refine (isEquivalent_atTop_div P Q).symm.tendsto_nhds ?_
  rw [← mul_zero]
  refine (tendsto_zpow_atTop_zero ?_).const_mul _
  lia

@[deprecated (since := "2026-02-05")]
alias div_tendsto_zero_of_degree_lt := div_tendsto_atTop_zero_of_degree_lt

中文:
定理 div_tendsto_atTop_zero_of_degree_lt
  条件: (hdeg : P.degree < Q.degree)
  证明: by
  by_cases hP : P = 0
  · simp [hP]
  rw [← natDegree_lt_natDegree_iff hP] at hdeg
  refine (isEquivalent_atTop_div P Q).symm.tendsto_nhds ?_
  rw [← mul_zero]
  refine (tendsto_zpow_atTop_zero ?_).const_mul _
  lia

@[deprecated (since := "2026-02-05")]
alias div_tendsto_zero_of_degree_lt := div_tendsto_atTop_zero_of_degree_lt

Depends on / 依赖: const_mul, isEquivalent_atTop_div, mul_zero, natDegree_lt_natDegree_iff, symm.tendsto_nhds, tendsto_nhds, tendsto_zpow_atTop_zero
-/
theorem div_tendsto_atTop_zero_of_degree_lt (hdeg : P.degree < Q.degree) :
    Tendsto (fun x => eval x P / eval x Q) atTop (𝓝 0) := by
  by_cases hP : P = 0
  · simp [hP]
  rw [← natDegree_lt_natDegree_iff hP] at hdeg
  refine (isEquivalent_atTop_div P Q).symm.tendsto_nhds ?_
  rw [← mul_zero]
  refine (tendsto_zpow_atTop_zero ?_).const_mul _
  lia

@[deprecated (since := "2026-02-05")]
alias div_tendsto_zero_of_degree_lt := div_tendsto_atTop_zero_of_degree_lt

/--
theorem `div_tendsto_atTop_zero_iff_degree_lt` / 定理 `div_tendsto_atTop_zero_iff_degree_lt`

English:
theorem div_tendsto_atTop_zero_iff_degree_lt
  given: (hQ : Q != 0)
  proof: by
  refine ⟨fun h => ?_, div_tendsto_atTop_zero_of_degree_lt P Q⟩
  by_cases hPQ : P.leadingCoeff / Q.leadingCoeff = 0
  · simp only [div_eq_mul_inv, inv_eq_zero, mul_eq_zero] at hPQ
    rcases hPQ with hP0 | hQ0
    · rw [leadingCoeff_eq_zero.1 hP0, degree_zero]
      exact bot_lt_iff_ne_bot.2 fun hQ' => hQ (degree_eq_bot.1 hQ')
    · exact absurd (leadingCoeff_eq_zero.1 hQ0) hQ
  · have := (isEquivalent_atTop_div P Q).tendsto_nhds h
    rw [tendsto_const_mul_zpow_atTop_nhds_iff hPQ] at this
    rcases this with h | h
    · exact absurd h.2 hPQ
    · rw [sub_lt_iff_lt_add, zero_add, Int.ofNat_lt] at h
      exact degree_lt_degree h.1

@[deprecated (since := "2026-02-05")]
alias div_tendsto_zero_iff_degree_lt := div_tendsto_atTop_zero_iff_degree_lt

中文:
定理 div_tendsto_atTop_zero_iff_degree_lt
  条件: (hQ : Q != 0)
  证明: by
  refine ⟨fun h => ?_, div_tendsto_atTop_zero_of_degree_lt P Q⟩
  by_cases hPQ : P.leadingCoeff / Q.leadingCoeff = 0
  · simp only [div_eq_mul_inv, inv_eq_zero, mul_eq_zero] at hPQ
    rcases hPQ with hP0 | hQ0
    · rw [leadingCoeff_eq_zero.1 hP0, degree_zero]
      exact bot_lt_iff_ne_bot.2 fun hQ' => hQ (degree_eq_bot.1 hQ')
    · exact absurd (leadingCoeff_eq_zero.1 hQ0) hQ
  · have := (isEquivalent_atTop_div P Q).tendsto_nhds h
    rw [tendsto_const_mul_zpow_atTop_nhds_iff hPQ] at this
    rcases this with h | h
    · exact absurd h.2 hPQ
    · rw [sub_lt_iff_lt_add, zero_add, Int.ofNat_lt] at h
      exact degree_lt_degree h.1

@[deprecated (since := "2026-02-05")]
alias div_tendsto_zero_iff_degree_lt := div_tendsto_atTop_zero_iff_degree_lt

Depends on / 依赖: P.leadingCoeff, Q.leadingCoeff, absurd, bot_lt_iff_ne_bot, degree_eq_bot, degree_zero, div_eq_mul_inv, div_tendsto_atTop_zero_of_degree_lt, inv_eq_zero, isEquivalent_atTop_div, leadingCoeff, leadingCoeff_eq_zero, mul_eq_zero, tendsto_const_mul_zpow_atTop_nhds_iff, tendsto_nhds
-/
theorem div_tendsto_atTop_zero_iff_degree_lt (hQ : Q != 0) :
    Tendsto (fun x => eval x P / eval x Q) atTop (𝓝 0) ↔ P.degree < Q.degree := by
  refine ⟨fun h => ?_, div_tendsto_atTop_zero_of_degree_lt P Q⟩
  by_cases hPQ : P.leadingCoeff / Q.leadingCoeff = 0
  · simp only [div_eq_mul_inv, inv_eq_zero, mul_eq_zero] at hPQ
    rcases hPQ with hP0 | hQ0
    · rw [leadingCoeff_eq_zero.1 hP0, degree_zero]
      exact bot_lt_iff_ne_bot.2 fun hQ' => hQ (degree_eq_bot.1 hQ')
    · exact absurd (leadingCoeff_eq_zero.1 hQ0) hQ
  · have := (isEquivalent_atTop_div P Q).tendsto_nhds h
    rw [tendsto_const_mul_zpow_atTop_nhds_iff hPQ] at this
    rcases this with h | h
    · exact absurd h.2 hPQ
    · rw [sub_lt_iff_lt_add, zero_add, Int.ofNat_lt] at h
      exact degree_lt_degree h.1

@[deprecated (since := "2026-02-05")]
alias div_tendsto_zero_iff_degree_lt := div_tendsto_atTop_zero_iff_degree_lt

/--
theorem `div_tendsto_atTop_leadingCoeff_div_of_degree_eq` / 定理 `div_tendsto_atTop_leadingCoeff_div_of_degree_eq`

English:
theorem div_tendsto_atTop_leadingCoeff_div_of_degree_eq
  given: (hdeg : P.degree = Q.degree)
  proof: by
  refine (isEquivalent_atTop_div P Q).symm.tendsto_nhds ?_
  rw [show (P.natDegree : Int) = Q.natDegree by simp [hdeg]; rw [natDegree]]
  simp

@[deprecated (since := "2026-02-05")]
alias div_tendsto_leadingCoeff_div_of_degree_eq := div_tendsto_atTop_leadingCoeff_div_of_degree_eq

中文:
定理 div_tendsto_atTop_leadingCoeff_div_of_degree_eq
  条件: (hdeg : P.degree = Q.degree)
  证明: by
  refine (isEquivalent_atTop_div P Q).symm.tendsto_nhds ?_
  rw [show (P.natDegree : Int) = Q.natDegree by simp [hdeg]; rw [natDegree]]
  simp

@[deprecated (since := "2026-02-05")]
alias div_tendsto_leadingCoeff_div_of_degree_eq := div_tendsto_atTop_leadingCoeff_div_of_degree_eq

Depends on / 依赖: P.natDegree, Q.natDegree, isEquivalent_atTop_div, natDegree, symm.tendsto_nhds, tendsto_nhds
-/
theorem div_tendsto_atTop_leadingCoeff_div_of_degree_eq (hdeg : P.degree = Q.degree) :
    Tendsto (fun x => eval x P / eval x Q) atTop (𝓝 <| P.leadingCoeff / Q.leadingCoeff) := by
  refine (isEquivalent_atTop_div P Q).symm.tendsto_nhds ?_
  rw [show (P.natDegree : Int) = Q.natDegree by simp [hdeg]; rw [natDegree]]
  simp

@[deprecated (since := "2026-02-05")]
alias div_tendsto_leadingCoeff_div_of_degree_eq := div_tendsto_atTop_leadingCoeff_div_of_degree_eq

/--
theorem `div_tendsto_atTop_of_degree_gt'` / 定理 `div_tendsto_atTop_of_degree_gt'`

English:
theorem div_tendsto_atTop_of_degree_gt'
  statement: (hdeg : Q.degree < P.degree)
  proof: by
  have hQ : Q != 0 := fun h => by
    simp only [h, div_zero, leadingCoeff_zero] at hpos
    exact hpos.false
  rw [← natDegree_lt_natDegree_iff hQ] at hdeg
  refine (isEquivalent_atTop_div P Q).symm.tendsto_atTop ?_
  apply Tendsto.const_mul_atTop hpos
  apply tendsto_zpow_atTop_atTop
  lia

中文:
定理 div_tendsto_atTop_of_degree_gt'
  结论: (hdeg : Q.degree < P.degree)
  证明: by
  have hQ : Q != 0 := fun h => by
    simp only [h, div_zero, leadingCoeff_zero] at hpos
    exact hpos.false
  rw [← natDegree_lt_natDegree_iff hQ] at hdeg
  refine (isEquivalent_atTop_div P Q).symm.tendsto_atTop ?_
  apply Tendsto.const_mul_atTop hpos
  apply tendsto_zpow_atTop_atTop
  lia

Depends on / 依赖: Tendsto, Tendsto.const_mul_atTop, const_mul_atTop, div_zero, hpos.false, isEquivalent_atTop_div, leadingCoeff_zero, natDegree_lt_natDegree_iff, symm.tendsto_atTop, tendsto_atTop, tendsto_zpow_atTop_atTop
-/
theorem div_tendsto_atTop_of_degree_gt' (hdeg : Q.degree < P.degree)
    (hpos : 0 < P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x => eval x P / eval x Q) atTop atTop := by
  have hQ : Q != 0 := fun h => by
    simp only [h, div_zero, leadingCoeff_zero] at hpos
    exact hpos.false
  rw [← natDegree_lt_natDegree_iff hQ] at hdeg
  refine (isEquivalent_atTop_div P Q).symm.tendsto_atTop ?_
  apply Tendsto.const_mul_atTop hpos
  apply tendsto_zpow_atTop_atTop
  lia

/--
theorem `div_tendsto_atTop_of_degree_gt` / 定理 `div_tendsto_atTop_of_degree_gt`

English:
theorem div_tendsto_atTop_of_degree_gt
  statement: (hdeg : Q.degree < P.degree) (hQ : Q != 0)
  proof: have ratio_pos : 0 < P.leadingCoeff / Q.leadingCoeff :=
    lt_of_le_of_ne hnng
      (div_ne_zero (fun h => ne_zero_of_degree_gt hdeg <| leadingCoeff_eq_zero.mp h) fun h =>
hQ leadingCoeff_eq_zero.mp h).symm
  div_tendsto_atTop_of_degree_gt' P Q hdeg ratio_pos

中文:
定理 div_tendsto_atTop_of_degree_gt
  结论: (hdeg : Q.degree < P.degree) (hQ : Q != 0)
  证明: have ratio_pos : 0 < P.leadingCoeff / Q.leadingCoeff :=
    lt_of_le_of_ne hnng
      (div_ne_zero (fun h => ne_zero_of_degree_gt hdeg <| leadingCoeff_eq_zero.mp h) fun h =>
hQ leadingCoeff_eq_zero.mp h).symm
  div_tendsto_atTop_of_degree_gt' P Q hdeg ratio_pos

Depends on / 依赖: P.leadingCoeff, Q.leadingCoeff, div_ne_zero, div_tendsto_atTop_of_degree_gt, leadingCoeff, leadingCoeff_eq_zero, leadingCoeff_eq_zero.mp, lt_of_le_of_ne, ne_zero_of_degree_gt, ratio_pos
-/
theorem div_tendsto_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q != 0)
    (hnng : 0 <= P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x => eval x P / eval x Q) atTop atTop :=
  have ratio_pos : 0 < P.leadingCoeff / Q.leadingCoeff :=
    lt_of_le_of_ne hnng
      (div_ne_zero (fun h => ne_zero_of_degree_gt hdeg <| leadingCoeff_eq_zero.mp h) fun h =>
hQ leadingCoeff_eq_zero.mp h).symm
  div_tendsto_atTop_of_degree_gt' P Q hdeg ratio_pos

/--
theorem `div_tendsto_atBot_of_degree_gt'` / 定理 `div_tendsto_atBot_of_degree_gt'`

English:
theorem div_tendsto_atBot_of_degree_gt'
  statement: (hdeg : Q.degree < P.degree)
  proof: by
  have hQ : Q != 0 := fun h => by
    simp only [h, div_zero, leadingCoeff_zero] at hneg
    exact hneg.false
  rw [← natDegree_lt_natDegree_iff hQ] at hdeg
  refine (isEquivalent_atTop_div P Q).symm.tendsto_atBot ?_
  apply Tendsto.const_mul_atTop_of_neg hneg
  apply tendsto_zpow_atTop_atTop
  lia

中文:
定理 div_tendsto_atBot_of_degree_gt'
  结论: (hdeg : Q.degree < P.degree)
  证明: by
  have hQ : Q != 0 := fun h => by
    simp only [h, div_zero, leadingCoeff_zero] at hneg
    exact hneg.false
  rw [← natDegree_lt_natDegree_iff hQ] at hdeg
  refine (isEquivalent_atTop_div P Q).symm.tendsto_atBot ?_
  apply Tendsto.const_mul_atTop_of_neg hneg
  apply tendsto_zpow_atTop_atTop
  lia

Depends on / 依赖: Tendsto, Tendsto.const_mul_atTop_of_neg, const_mul_atTop_of_neg, div_zero, hneg.false, isEquivalent_atTop_div, leadingCoeff_zero, natDegree_lt_natDegree_iff, symm.tendsto_atBot, tendsto_atBot, tendsto_zpow_atTop_atTop
-/
theorem div_tendsto_atBot_of_degree_gt' (hdeg : Q.degree < P.degree)
    (hneg : P.leadingCoeff / Q.leadingCoeff < 0) :
    Tendsto (fun x => eval x P / eval x Q) atTop atBot := by
  have hQ : Q != 0 := fun h => by
    simp only [h, div_zero, leadingCoeff_zero] at hneg
    exact hneg.false
  rw [← natDegree_lt_natDegree_iff hQ] at hdeg
  refine (isEquivalent_atTop_div P Q).symm.tendsto_atBot ?_
  apply Tendsto.const_mul_atTop_of_neg hneg
  apply tendsto_zpow_atTop_atTop
  lia

/--
theorem `div_tendsto_atBot_of_degree_gt` / 定理 `div_tendsto_atBot_of_degree_gt`

English:
theorem div_tendsto_atBot_of_degree_gt
  statement: (hdeg : Q.degree < P.degree) (hQ : Q != 0)
  proof: have ratio_neg : P.leadingCoeff / Q.leadingCoeff < 0 :=
    lt_of_le_of_ne hnps
      (div_ne_zero (fun h => ne_zero_of_degree_gt hdeg <| leadingCoeff_eq_zero.mp h) fun h =>
hQ leadingCoeff_eq_zero.mp h)
  div_tendsto_atBot_of_degree_gt' P Q hdeg ratio_neg

中文:
定理 div_tendsto_atBot_of_degree_gt
  结论: (hdeg : Q.degree < P.degree) (hQ : Q != 0)
  证明: have ratio_neg : P.leadingCoeff / Q.leadingCoeff < 0 :=
    lt_of_le_of_ne hnps
      (div_ne_zero (fun h => ne_zero_of_degree_gt hdeg <| leadingCoeff_eq_zero.mp h) fun h =>
hQ leadingCoeff_eq_zero.mp h)
  div_tendsto_atBot_of_degree_gt' P Q hdeg ratio_neg

Depends on / 依赖: P.leadingCoeff, Q.leadingCoeff, div_ne_zero, div_tendsto_atBot_of_degree_gt, leadingCoeff, leadingCoeff_eq_zero, leadingCoeff_eq_zero.mp, lt_of_le_of_ne, ne_zero_of_degree_gt, ratio_neg
-/
theorem div_tendsto_atBot_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q != 0)
    (hnps : P.leadingCoeff / Q.leadingCoeff <= 0) :
    Tendsto (fun x => eval x P / eval x Q) atTop atBot :=
  have ratio_neg : P.leadingCoeff / Q.leadingCoeff < 0 :=
    lt_of_le_of_ne hnps
      (div_ne_zero (fun h => ne_zero_of_degree_gt hdeg <| leadingCoeff_eq_zero.mp h) fun h =>
hQ leadingCoeff_eq_zero.mp h)
  div_tendsto_atBot_of_degree_gt' P Q hdeg ratio_neg

/--
theorem `abs_div_tendsto_atTop_atTop_of_degree_gt` / 定理 `abs_div_tendsto_atTop_atTop_of_degree_gt`

English:
theorem abs_div_tendsto_atTop_atTop_of_degree_gt
  given: (hdeg : Q.degree < P.degree) (hQ : Q != 0)
  proof: by
  by_cases! h : 0 <= P.leadingCoeff / Q.leadingCoeff
  · exact tendsto_abs_atTop_atTop.comp (P.div_tendsto_atTop_of_degree_gt Q hdeg hQ h)
  · exact tendsto_abs_atBot_atTop.comp (P.div_tendsto_atBot_of_degree_gt Q hdeg hQ h.le)

@[deprecated (since := "2026-02-05")]
alias abs_div_tendsto_atTop_of_degree_gt := abs_div_tendsto_atTop_atTop_of_degree_gt

中文:
定理 abs_div_tendsto_atTop_atTop_of_degree_gt
  条件: (hdeg : Q.degree < P.degree) (hQ : Q != 0)
  证明: by
  by_cases! h : 0 <= P.leadingCoeff / Q.leadingCoeff
  · exact tendsto_abs_atTop_atTop.comp (P.div_tendsto_atTop_of_degree_gt Q hdeg hQ h)
  · exact tendsto_abs_atBot_atTop.comp (P.div_tendsto_atBot_of_degree_gt Q hdeg hQ h.le)

@[deprecated (since := "2026-02-05")]
alias abs_div_tendsto_atTop_of_degree_gt := abs_div_tendsto_atTop_atTop_of_degree_gt

Depends on / 依赖: P.div_tendsto_atBot_of_degree_gt, P.div_tendsto_atTop_of_degree_gt, P.leadingCoeff, Q.leadingCoeff, div_tendsto_atBot_of_degree_gt, div_tendsto_atTop_of_degree_gt, h.le, leadingCoeff, tendsto_abs_atBot_atTop, tendsto_abs_atBot_atTop.comp, tendsto_abs_atTop_atTop, tendsto_abs_atTop_atTop.comp
-/
theorem abs_div_tendsto_atTop_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q != 0) :
    Tendsto (fun x => |eval x P / eval x Q|) atTop atTop := by
  by_cases! h : 0 <= P.leadingCoeff / Q.leadingCoeff
  · exact tendsto_abs_atTop_atTop.comp (P.div_tendsto_atTop_of_degree_gt Q hdeg hQ h)
  · exact tendsto_abs_atBot_atTop.comp (P.div_tendsto_atBot_of_degree_gt Q hdeg hQ h.le)

@[deprecated (since := "2026-02-05")]
alias abs_div_tendsto_atTop_of_degree_gt := abs_div_tendsto_atTop_atTop_of_degree_gt

end PolynomialDivAtTop

section PolynomialDivAtBot

/--
theorem `isEquivalent_atBot_div` / 定理 `isEquivalent_atBot_div`

English:
theorem isEquivalent_atBot_div
  proof: by
  by_cases hP : P = 0
  · simp [hP, IsEquivalent.refl]
  by_cases hQ : Q = 0
  · simp [hQ, IsEquivalent.refl]
  refine
    (P.isEquivalent_atBot_lead.symm.div Q.isEquivalent_atBot_lead.symm).symm.trans
      (EventuallyEq.isEquivalent ((eventually_lt_atBot 0).mono fun x hx => ?_))
  simp [← div_mul_div_comm, zpow_sub₀ hx.ne]

中文:
定理 isEquivalent_atBot_div
  证明: by
  by_cases hP : P = 0
  · simp [hP, IsEquivalent.refl]
  by_cases hQ : Q = 0
  · simp [hQ, IsEquivalent.refl]
  refine
    (P.isEquivalent_atBot_lead.symm.div Q.isEquivalent_atBot_lead.symm).symm.trans
      (EventuallyEq.isEquivalent ((eventually_lt_atBot 0).mono fun x hx => ?_))
  simp [← div_mul_div_comm, zpow_sub₀ hx.ne]

Depends on / 依赖: EventuallyEq, EventuallyEq.isEquivalent, IsEquivalent, IsEquivalent.refl, P.isEquivalent_atBot_lead.symm.div, Q.isEquivalent_atBot_lead.symm, div_mul_div_comm, eventually_lt_atBot, hx.ne, isEquivalent, isEquivalent_atBot_lead, symm.trans
-/
theorem isEquivalent_atBot_div :
    (fun x => P.eval x / Q.eval x) ~[atBot] fun x =>
      P.leadingCoeff / Q.leadingCoeff * x ^ (P.natDegree - Q.natDegree : Int) := by
  by_cases hP : P = 0
  · simp [hP, IsEquivalent.refl]
  by_cases hQ : Q = 0
  · simp [hQ, IsEquivalent.refl]
  refine
    (P.isEquivalent_atBot_lead.symm.div Q.isEquivalent_atBot_lead.symm).symm.trans
      (EventuallyEq.isEquivalent ((eventually_lt_atBot 0).mono fun x hx => ?_))
  simp [← div_mul_div_comm, zpow_sub₀ hx.ne]

/--
theorem `div_tendsto_atBot_zero_of_degree_lt` / 定理 `div_tendsto_atBot_zero_of_degree_lt`

English:
theorem div_tendsto_atBot_zero_of_degree_lt
  given: (hdeg : P.degree < Q.degree)
  proof: by
  rw [← P.degree_comp_neg_X]; rw [← Q.degree_comp_neg_X] at hdeg
  convert! (div_tendsto_atTop_zero_of_degree_lt _ _ hdeg).comp tendsto_neg_atBot_atTop using 2
  simp

中文:
定理 div_tendsto_atBot_zero_of_degree_lt
  条件: (hdeg : P.degree < Q.degree)
  证明: by
  rw [← P.degree_comp_neg_X]; rw [← Q.degree_comp_neg_X] at hdeg
  convert! (div_tendsto_atTop_zero_of_degree_lt _ _ hdeg).comp tendsto_neg_atBot_atTop using 2
  simp

Depends on / 依赖: P.degree_comp_neg_X, Q.degree_comp_neg_X, convert, degree_comp_neg_X, div_tendsto_atTop_zero_of_degree_lt, tendsto_neg_atBot_atTop
-/
theorem div_tendsto_atBot_zero_of_degree_lt (hdeg : P.degree < Q.degree) :
    Tendsto (fun x => eval x P / eval x Q) atBot (𝓝 0) := by
  rw [← P.degree_comp_neg_X]; rw [← Q.degree_comp_neg_X] at hdeg
  convert! (div_tendsto_atTop_zero_of_degree_lt _ _ hdeg).comp tendsto_neg_atBot_atTop using 2
  simp

/--
theorem `div_tendsto_atBot_zero_iff_degree_lt` / 定理 `div_tendsto_atBot_zero_iff_degree_lt`

English:
theorem div_tendsto_atBot_zero_iff_degree_lt
  given: (hQ : Q != 0)
  proof: by
  refine ⟨fun h => ?_, div_tendsto_atBot_zero_of_degree_lt P Q⟩
  rw [← P.degree_comp_neg_X]; rw [← Q.degree_comp_neg_X]
  replace hQ : Q.comp (-X) != 0 := by
    rw [Ne]; rw [comp_eq_zero_iff]
    simp [hQ]
  rw [← div_tendsto_atTop_zero_iff_degree_lt _ _ hQ]
  convert! h.comp tendsto_neg_atTop_atBot using 2
  simp

中文:
定理 div_tendsto_atBot_zero_iff_degree_lt
  条件: (hQ : Q != 0)
  证明: by
  refine ⟨fun h => ?_, div_tendsto_atBot_zero_of_degree_lt P Q⟩
  rw [← P.degree_comp_neg_X]; rw [← Q.degree_comp_neg_X]
  replace hQ : Q.comp (-X) != 0 := by
    rw [Ne]; rw [comp_eq_zero_iff]
    simp [hQ]
  rw [← div_tendsto_atTop_zero_iff_degree_lt _ _ hQ]
  convert! h.comp tendsto_neg_atTop_atBot using 2
  simp

Depends on / 依赖: P.degree_comp_neg_X, Q.comp, Q.degree_comp_neg_X, comp_eq_zero_iff, convert, degree_comp_neg_X, div_tendsto_atBot_zero_of_degree_lt, div_tendsto_atTop_zero_iff_degree_lt, h.comp, replace, tendsto_neg_atTop_atBot
-/
theorem div_tendsto_atBot_zero_iff_degree_lt (hQ : Q != 0) :
    Tendsto (fun x => eval x P / eval x Q) atBot (𝓝 0) ↔ P.degree < Q.degree := by
  refine ⟨fun h => ?_, div_tendsto_atBot_zero_of_degree_lt P Q⟩
  rw [← P.degree_comp_neg_X]; rw [← Q.degree_comp_neg_X]
  replace hQ : Q.comp (-X) != 0 := by
    rw [Ne]; rw [comp_eq_zero_iff]
    simp [hQ]
  rw [← div_tendsto_atTop_zero_iff_degree_lt _ _ hQ]
  convert! h.comp tendsto_neg_atTop_atBot using 2
  simp

/--
theorem `div_tendsto_atBot_leadingCoeff_div_of_degree_eq` / 定理 `div_tendsto_atBot_leadingCoeff_div_of_degree_eq`

English:
theorem div_tendsto_atBot_leadingCoeff_div_of_degree_eq
  given: (hdeg : P.degree = Q.degree)
  proof: by
  refine (isEquivalent_atBot_div P Q).symm.tendsto_nhds ?_
  simp [natDegree_eq_natDegree hdeg]

中文:
定理 div_tendsto_atBot_leadingCoeff_div_of_degree_eq
  条件: (hdeg : P.degree = Q.degree)
  证明: by
  refine (isEquivalent_atBot_div P Q).symm.tendsto_nhds ?_
  simp [natDegree_eq_natDegree hdeg]

Depends on / 依赖: isEquivalent_atBot_div, natDegree_eq_natDegree, symm.tendsto_nhds, tendsto_nhds
-/
theorem div_tendsto_atBot_leadingCoeff_div_of_degree_eq (hdeg : P.degree = Q.degree) :
    Tendsto (fun x => eval x P / eval x Q) atBot (𝓝 (P.leadingCoeff / Q.leadingCoeff)) := by
  refine (isEquivalent_atBot_div P Q).symm.tendsto_nhds ?_
  simp [natDegree_eq_natDegree hdeg]

/--
theorem `abs_div_tendsto_atBot_atTop_of_degree_gt` / 定理 `abs_div_tendsto_atBot_atTop_of_degree_gt`

English:
theorem abs_div_tendsto_atBot_atTop_of_degree_gt
  given: (hdeg : Q.degree < P.degree) (hQ : Q != 0)
  proof: by
  rw [← P.degree_comp_neg_X]; rw [← Q.degree_comp_neg_X] at hdeg
  replace hQ : Q.comp (-X) != 0 := by
    rw [Ne]; rw [comp_eq_zero_iff]
    simp [hQ]
  convert! (abs_div_tendsto_atTop_atTop_of_degree_gt _ _ hdeg hQ).comp tendsto_neg_atBot_atTop
    using 2
  simp

中文:
定理 abs_div_tendsto_atBot_atTop_of_degree_gt
  条件: (hdeg : Q.degree < P.degree) (hQ : Q != 0)
  证明: by
  rw [← P.degree_comp_neg_X]; rw [← Q.degree_comp_neg_X] at hdeg
  replace hQ : Q.comp (-X) != 0 := by
    rw [Ne]; rw [comp_eq_zero_iff]
    simp [hQ]
  convert! (abs_div_tendsto_atTop_atTop_of_degree_gt _ _ hdeg hQ).comp tendsto_neg_atBot_atTop
    using 2
  simp

Depends on / 依赖: P.degree_comp_neg_X, Q.comp, Q.degree_comp_neg_X, abs_div_tendsto_atTop_atTop_of_degree_gt, comp_eq_zero_iff, convert, degree_comp_neg_X, replace, tendsto_neg_atBot_atTop
-/
theorem abs_div_tendsto_atBot_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q != 0) :
    Tendsto (fun x => |eval x P / eval x Q|) atBot atTop := by
  rw [← P.degree_comp_neg_X]; rw [← Q.degree_comp_neg_X] at hdeg
  replace hQ : Q.comp (-X) != 0 := by
    rw [Ne]; rw [comp_eq_zero_iff]
    simp [hQ]
  convert! (abs_div_tendsto_atTop_atTop_of_degree_gt _ _ hdeg hQ).comp tendsto_neg_atBot_atTop
    using 2
  simp

end PolynomialDivAtBot

/--
theorem `isLittleO_atTop_of_degree_lt` / 定理 `isLittleO_atTop_of_degree_lt`

English:
theorem isLittleO_atTop_of_degree_lt
  given: (h : P.degree < Q.degree)
  statement: P.eval =o[atTop] Q.eval
  proof: by
  by_cases hp : P = 0
  · simp [hp]
  · have hq : Q != 0 := ne_zero_of_degree_ge_degree h.le hp
    have hPQ : forallᶠ x in atTop, Q.eval x = 0 -> P.eval x = 0 :=
      mem_of_superset (eventually_atTop_not_isRoot Q hq) fun x h h' => absurd h' h
    exact isLittleO_of_tendsto' hPQ (div_tendsto_atTop_zero_of_degree_lt P Q h)

中文:
定理 isLittleO_atTop_of_degree_lt
  条件: (h : P.degree < Q.degree)
  结论: P.eval =o[atTop] Q.eval
  证明: by
  by_cases hp : P = 0
  · simp [hp]
  · have hq : Q != 0 := ne_zero_of_degree_ge_degree h.le hp
    have hPQ : forallᶠ x in atTop, Q.eval x = 0 -> P.eval x = 0 :=
      mem_of_superset (eventually_atTop_not_isRoot Q hq) fun x h h' => absurd h' h
    exact isLittleO_of_tendsto' hPQ (div_tendsto_atTop_zero_of_degree_lt P Q h)

Depends on / 依赖: P.eval, Q.eval, absurd, div_tendsto_atTop_zero_of_degree_lt, eventually_atTop_not_isRoot, h.le, isLittleO_of_tendsto, mem_of_superset, ne_zero_of_degree_ge_degree
-/
theorem isLittleO_atTop_of_degree_lt (h : P.degree < Q.degree) : P.eval =o[atTop] Q.eval := by
  by_cases hp : P = 0
  · simp [hp]
  · have hq : Q != 0 := ne_zero_of_degree_ge_degree h.le hp
    have hPQ : forallᶠ x in atTop, Q.eval x = 0 -> P.eval x = 0 :=
      mem_of_superset (eventually_atTop_not_isRoot Q hq) fun x h h' => absurd h' h
    exact isLittleO_of_tendsto' hPQ (div_tendsto_atTop_zero_of_degree_lt P Q h)

/--
theorem `isLittleO_atBot_of_degree_lt` / 定理 `isLittleO_atBot_of_degree_lt`

English:
theorem isLittleO_atBot_of_degree_lt
  given: (h : P.degree < Q.degree)
  statement: P.eval =o[atBot] Q.eval
  proof: by
  rw [← P.degree_comp_neg_X]; rw [← Q.degree_comp_neg_X] at h
  convert! (isLittleO_atTop_of_degree_lt _ _ h).comp_tendsto tendsto_neg_atBot_atTop using 2
  all_goals simp

中文:
定理 isLittleO_atBot_of_degree_lt
  条件: (h : P.degree < Q.degree)
  结论: P.eval =o[atBot] Q.eval
  证明: by
  rw [← P.degree_comp_neg_X]; rw [← Q.degree_comp_neg_X] at h
  convert! (isLittleO_atTop_of_degree_lt _ _ h).comp_tendsto tendsto_neg_atBot_atTop using 2
  all_goals simp

Depends on / 依赖: P.degree_comp_neg_X, Q.degree_comp_neg_X, all_goals, comp_tendsto, convert, degree_comp_neg_X, isLittleO_atTop_of_degree_lt, tendsto_neg_atBot_atTop
-/
theorem isLittleO_atBot_of_degree_lt (h : P.degree < Q.degree) : P.eval =o[atBot] Q.eval := by
  rw [← P.degree_comp_neg_X]; rw [← Q.degree_comp_neg_X] at h
  convert! (isLittleO_atTop_of_degree_lt _ _ h).comp_tendsto tendsto_neg_atBot_atTop using 2
  all_goals simp

/--
theorem `isBigO_atTop_of_degree_le` / 定理 `isBigO_atTop_of_degree_le`

English:
theorem isBigO_atTop_of_degree_le
  given: (h : P.degree <= Q.degree)
  statement: P.eval =O[atTop] Q.eval
  proof: by
  by_cases hp : P = 0
  · simpa [hp] using isBigO_zero Q.eval atTop
  · have hq : Q != 0 := ne_zero_of_degree_ge_degree h hp
    have hPQ : forallᶠ x in atTop, Q.eval x = 0 -> P.eval x = 0 :=
      mem_of_superset (eventually_atTop_not_isRoot Q hq) fun x h h' => absurd h' h
    rcases le_iff_lt_or_eq.mp h with h | h
    · exact isBigO_of_div_tendsto_nhds hPQ 0 (div_tendsto_atTop_zero_of_degree_lt P Q h)
    · exact isBigO_of_div_tendsto_nhds hPQ _ (div_tendsto_atTop_leadingCoeff_div_of_degree_eq P Q h)

中文:
定理 isBigO_atTop_of_degree_le
  条件: (h : P.degree <= Q.degree)
  结论: P.eval =O[atTop] Q.eval
  证明: by
  by_cases hp : P = 0
  · simpa [hp] using isBigO_zero Q.eval atTop
  · have hq : Q != 0 := ne_zero_of_degree_ge_degree h hp
    have hPQ : forallᶠ x in atTop, Q.eval x = 0 -> P.eval x = 0 :=
      mem_of_superset (eventually_atTop_not_isRoot Q hq) fun x h h' => absurd h' h
    rcases le_iff_lt_or_eq.mp h with h | h
    · exact isBigO_of_div_tendsto_nhds hPQ 0 (div_tendsto_atTop_zero_of_degree_lt P Q h)
    · exact isBigO_of_div_tendsto_nhds hPQ _ (div_tendsto_atTop_leadingCoeff_div_of_degree_eq P Q h)

Depends on / 依赖: P.eval, Q.eval, absurd, div_tendsto_atTop_leadingCoeff_div_of_degree_eq, div_tendsto_atTop_zero_of_degree_lt, eventually_atTop_not_isRoot, isBigO_of_div_tendsto_nhds, isBigO_zero, le_iff_lt_or_eq, le_iff_lt_or_eq.mp, mem_of_superset, ne_zero_of_degree_ge_degree
-/
theorem isBigO_atTop_of_degree_le (h : P.degree <= Q.degree) : P.eval =O[atTop] Q.eval := by
  by_cases hp : P = 0
  · simpa [hp] using isBigO_zero Q.eval atTop
  · have hq : Q != 0 := ne_zero_of_degree_ge_degree h hp
    have hPQ : forallᶠ x in atTop, Q.eval x = 0 -> P.eval x = 0 :=
      mem_of_superset (eventually_atTop_not_isRoot Q hq) fun x h h' => absurd h' h
    rcases le_iff_lt_or_eq.mp h with h | h
    · exact isBigO_of_div_tendsto_nhds hPQ 0 (div_tendsto_atTop_zero_of_degree_lt P Q h)
    · exact isBigO_of_div_tendsto_nhds hPQ _ (div_tendsto_atTop_leadingCoeff_div_of_degree_eq P Q h)

/--
theorem `isBigO_atBot_of_degree_le` / 定理 `isBigO_atBot_of_degree_le`

English:
theorem isBigO_atBot_of_degree_le
  given: (h : P.degree <= Q.degree)
  statement: P.eval =O[atBot] Q.eval
  proof: by
  rw [← P.degree_comp_neg_X]; rw [← Q.degree_comp_neg_X] at h
  convert! (isBigO_atTop_of_degree_le _ _ h).comp_tendsto tendsto_neg_atBot_atTop using 2
  all_goals simp

@[deprecated (since := "2026-02-05")] alias isBigO_of_degree_le := isBigO_atTop_of_degree_le

中文:
定理 isBigO_atBot_of_degree_le
  条件: (h : P.degree <= Q.degree)
  结论: P.eval =O[atBot] Q.eval
  证明: by
  rw [← P.degree_comp_neg_X]; rw [← Q.degree_comp_neg_X] at h
  convert! (isBigO_atTop_of_degree_le _ _ h).comp_tendsto tendsto_neg_atBot_atTop using 2
  all_goals simp

@[deprecated (since := "2026-02-05")] alias isBigO_of_degree_le := isBigO_atTop_of_degree_le

Depends on / 依赖: P.degree_comp_neg_X, Q.degree_comp_neg_X, all_goals, comp_tendsto, convert, degree_comp_neg_X, isBigO_atTop_of_degree_le, tendsto_neg_atBot_atTop
-/
theorem isBigO_atBot_of_degree_le (h : P.degree <= Q.degree) : P.eval =O[atBot] Q.eval := by
  rw [← P.degree_comp_neg_X]; rw [← Q.degree_comp_neg_X] at h
  convert! (isBigO_atTop_of_degree_le _ _ h).comp_tendsto tendsto_neg_atBot_atTop using 2
  all_goals simp

@[deprecated (since := "2026-02-05")] alias isBigO_of_degree_le := isBigO_atTop_of_degree_le

section Cobounded

/--
lemma `eventually_cofinite_not_isRoot` / 引理 `eventually_cofinite_not_isRoot`

English:
lemma eventually_cofinite_not_isRoot
  given: {R : Type*} [CommRing R] [IsDomain R] {P : R[X]} (hP : P != 0)
  proof: (finite_setOfPred_isRoot hP).compl_mem_cofinite

中文:
引理 eventually_cofinite_not_isRoot
  条件: {R : 类型} [交换环 R] [是整环 R] {P : R[X]} (hP : P != 0)
  证明: (finite_setOfPred_isRoot hP).compl_mem_cofinite

Depends on / 依赖: compl_mem_cofinite, finite_setOfPred_isRoot
-/
lemma eventually_cofinite_not_isRoot {R : Type*} [CommRing R] [IsDomain R] {P : R[X]} (hP : P != 0) :
    forallᶠ x in cofinite, ¬P.IsRoot x :=
  (finite_setOfPred_isRoot hP).compl_mem_cofinite

open Bornology

variable {R : Type*} [NormedRing R] [NormMulClass R] {P Q : R[X]}

/--
lemma `isEquivalent_cobounded_leading_monomial` / 引理 `isEquivalent_cobounded_leading_monomial`

English:
lemma isEquivalent_cobounded_leading_monomial
  proof: by
  by_cases h : P = 0
  · simp [h, IsEquivalent.refl]
  · simp only [eval_eq_sum_range, sum_range_succ]
    exact (IsLittleO.fun_sum fun i hi =>
      ((isLittleO_pow_pow_cobounded_of_lt (mem_range.mp hi)).const_mul_right
        (leadingCoeff_ne_zero.mpr h)).const_mul_left _).add_isEquivalent .refl

中文:
引理 isEquivalent_cobounded_leading_monomial
  证明: by
  by_cases h : P = 0
  · simp [h, IsEquivalent.refl]
  · simp only [eval_eq_sum_range, sum_range_succ]
    exact (IsLittleO.fun_sum fun i hi =>
      ((isLittleO_pow_pow_cobounded_of_lt (mem_range.mp hi)).const_mul_right
        (leadingCoeff_ne_zero.mpr h)).const_mul_left _).add_isEquivalent .refl

Depends on / 依赖: IsEquivalent, IsEquivalent.refl, IsLittleO, IsLittleO.fun_sum, add_isEquivalent, const_mul_left, const_mul_right, eval_eq_sum_range, fun_sum, isLittleO_pow_pow_cobounded_of_lt, leadingCoeff_ne_zero, leadingCoeff_ne_zero.mpr, mem_range, mem_range.mp, sum_range_succ
-/
lemma isEquivalent_cobounded_leading_monomial :
    P.eval ~[cobounded R] (P.leadingCoeff * · ^ P.natDegree) := by
  by_cases h : P = 0
  · simp [h, IsEquivalent.refl]
  · simp only [eval_eq_sum_range, sum_range_succ]
    exact (IsLittleO.fun_sum fun i hi =>
      ((isLittleO_pow_pow_cobounded_of_lt (mem_range.mp hi)).const_mul_right
        (leadingCoeff_ne_zero.mpr h)).const_mul_left _).add_isEquivalent .refl

/--
theorem `isLittleO_cobounded_of_degree_lt` / 定理 `isLittleO_cobounded_of_degree_lt`

English:
theorem isLittleO_cobounded_of_degree_lt
  given: (h : P.degree < Q.degree)
  proof: by
  by_cases hP : P = 0
  · simp [hP]
· refine isEquivalent_cobounded_leading_monomial.trans_isLittleO
      ((IsLittleO.const_mul_right ?_ ?_).const_mul_left _).trans_isEquivalent
        isEquivalent_cobounded_leading_monomial.symm
    · exact leadingCoeff_ne_zero.mpr (ne_zero_of_degree_gt h)
    · exact isLittleO_pow_pow_cobounded_of_lt (natDegree_lt_natDegree hP h)

中文:
定理 isLittleO_cobounded_of_degree_lt
  条件: (h : P.degree < Q.degree)
  证明: by
  by_cases hP : P = 0
  · simp [hP]
· refine isEquivalent_cobounded_leading_monomial.trans_isLittleO
      ((IsLittleO.const_mul_right ?_ ?_).const_mul_left _).trans_isEquivalent
        isEquivalent_cobounded_leading_monomial.symm
    · exact leadingCoeff_ne_zero.mpr (ne_zero_of_degree_gt h)
    · exact isLittleO_pow_pow_cobounded_of_lt (natDegree_lt_natDegree hP h)

Depends on / 依赖: IsLittleO, IsLittleO.const_mul_right, const_mul_left, const_mul_right, isEquivalent_cobounded_leading_monomial, isEquivalent_cobounded_leading_monomial.symm, isEquivalent_cobounded_leading_monomial.trans_isLittleO, isLittleO_pow_pow_cobounded_of_lt, leadingCoeff_ne_zero, leadingCoeff_ne_zero.mpr, natDegree_lt_natDegree, ne_zero_of_degree_gt, trans_isEquivalent, trans_isLittleO
-/
theorem isLittleO_cobounded_of_degree_lt (h : P.degree < Q.degree) :
    P.eval =o[cobounded R] Q.eval := by
  by_cases hP : P = 0
  · simp [hP]
· refine isEquivalent_cobounded_leading_monomial.trans_isLittleO
      ((IsLittleO.const_mul_right ?_ ?_).const_mul_left _).trans_isEquivalent
        isEquivalent_cobounded_leading_monomial.symm
    · exact leadingCoeff_ne_zero.mpr (ne_zero_of_degree_gt h)
    · exact isLittleO_pow_pow_cobounded_of_lt (natDegree_lt_natDegree hP h)

/--
theorem `isBigO_cobounded_of_degree_le` / 定理 `isBigO_cobounded_of_degree_le`

English:
theorem isBigO_cobounded_of_degree_le
  given: (h : P.degree <= Q.degree)
  proof: by
  by_cases hQ : Q.leadingCoeff = 0
  · aesop
· refine isEquivalent_cobounded_leading_monomial.trans_isBigO
      ((IsBigO.const_mul_right hQ ?_).const_mul_left _).trans_isEquivalent
        isEquivalent_cobounded_leading_monomial.symm
    exact isBigO_pow_pow_cobounded_of_le (natDegree_le_natDegree h)

中文:
定理 isBigO_cobounded_of_degree_le
  条件: (h : P.degree <= Q.degree)
  证明: by
  by_cases hQ : Q.leadingCoeff = 0
  · aesop
· refine isEquivalent_cobounded_leading_monomial.trans_isBigO
      ((IsBigO.const_mul_right hQ ?_).const_mul_left _).trans_isEquivalent
        isEquivalent_cobounded_leading_monomial.symm
    exact isBigO_pow_pow_cobounded_of_le (natDegree_le_natDegree h)

Depends on / 依赖: IsBigO, IsBigO.const_mul_right, Q.leadingCoeff, const_mul_left, const_mul_right, isBigO_pow_pow_cobounded_of_le, isEquivalent_cobounded_leading_monomial, isEquivalent_cobounded_leading_monomial.symm, isEquivalent_cobounded_leading_monomial.trans_isBigO, leadingCoeff, natDegree_le_natDegree, trans_isBigO, trans_isEquivalent
-/
theorem isBigO_cobounded_of_degree_le (h : P.degree <= Q.degree) :
    P.eval =O[cobounded R] Q.eval := by
  by_cases hQ : Q.leadingCoeff = 0
  · aesop
· refine isEquivalent_cobounded_leading_monomial.trans_isBigO
      ((IsBigO.const_mul_right hQ ?_).const_mul_left _).trans_isEquivalent
        isEquivalent_cobounded_leading_monomial.symm
    exact isBigO_pow_pow_cobounded_of_le (natDegree_le_natDegree h)

end Cobounded

/--
lemma `finite_abs_eval_le_of_degree_lt` / 引理 `finite_abs_eval_le_of_degree_lt`

English:
lemma finite_abs_eval_le_of_degree_lt
  given: {P Q : Int[X]} (h : Q.degree < P.degree)
  proof: by
  have o := isLittleO_cobounded_of_degree_lt h
  rw [IsOrderBornology.cobounded_eq]; rw [← Int.cofinite_eq] at o
  have nr := eventually_cofinite_not_isRoot (ne_zero_of_degree_gt h)
  have key := o.eventuallyLT_norm_of_eventually_pos (nr.congr (.of_forall (by simp)))
  simp_rw [eventually_cofinite, not_lt, Int.norm_eq_abs] at key
  norm_cast at key

中文:
引理 finite_abs_eval_le_of_degree_lt
  条件: {P Q : 整数[X]} (h : Q.degree < P.degree)
  证明: by
  have o := isLittleO_cobounded_of_degree_lt h
  rw [IsOrderBornology.cobounded_eq]; rw [← Int.cofinite_eq] at o
  have nr := eventually_cofinite_not_isRoot (ne_zero_of_degree_gt h)
  have key := o.eventuallyLT_norm_of_eventually_pos (nr.congr (.of_forall (by simp)))
  simp_rw [eventually_cofinite, not_lt, Int.norm_eq_abs] at key
  norm_cast at key

Depends on / 依赖: Int.cofinite_eq, Int.norm_eq_abs, IsOrderBornology, IsOrderBornology.cobounded_eq, cobounded_eq, cofinite_eq, eventuallyLT_norm_of_eventually_pos, eventually_cofinite, eventually_cofinite_not_isRoot, isLittleO_cobounded_of_degree_lt, ne_zero_of_degree_gt, norm_eq_abs, not_lt, nr.congr, o.eventuallyLT_norm_of_eventually_pos, of_forall, simp_rw
-/
lemma finite_abs_eval_le_of_degree_lt {P Q : Int[X]} (h : Q.degree < P.degree) :
    {x | |P.eval x| <= |Q.eval x|}.Finite := by
  have o := isLittleO_cobounded_of_degree_lt h
  rw [IsOrderBornology.cobounded_eq]; rw [← Int.cofinite_eq] at o
  have nr := eventually_cofinite_not_isRoot (ne_zero_of_degree_gt h)
  have key := o.eventuallyLT_norm_of_eventually_pos (nr.congr (.of_forall (by simp)))
  simp_rw [eventually_cofinite, not_lt, Int.norm_eq_abs] at key
  norm_cast at key

/--
theorem `dvd_of_infinite_eval_dvd_eval` / 定理 `dvd_of_infinite_eval_dvd_eval`

English:
theorem dvd_of_infinite_eval_dvd_eval
  proof: by
  have eqR := modByMonic_add_div P Q
  have degR := degree_modByMonic_lt P mQ
  rw [← modByMonic_eq_zero_iff_dvd mQ]
  set R := P %ₘ Q
  apply eq_zero_of_infinite_isRoot
  refine (h.sdiff (finite_abs_eval_le_of_degree_lt degR)).mono fun x mx => ?_
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_le] at mx
  rw [← eqR]; rw [eval_add]; rw [eval_mul]; rw [Int.dvd_add_self_mul]; rw [← abs_dvd] at mx
  exact Int.eq_zero_of_abs_lt_dvd mx.1 mx.2

中文:
定理 dvd_of_infinite_eval_dvd_eval
  证明: by
  have eqR := modByMonic_add_div P Q
  have degR := degree_modByMonic_lt P mQ
  rw [← modByMonic_eq_zero_iff_dvd mQ]
  set R := P %ₘ Q
  apply eq_zero_of_infinite_isRoot
  refine (h.sdiff (finite_abs_eval_le_of_degree_lt degR)).mono fun x mx => ?_
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_le] at mx
  rw [← eqR]; rw [eval_add]; rw [eval_mul]; rw [Int.dvd_add_self_mul]; rw [← abs_dvd] at mx
  exact Int.eq_zero_of_abs_lt_dvd mx.1 mx.2

Depends on / 依赖: Int.dvd_add_self_mul, Int.eq_zero_of_abs_lt_dvd, Set.mem_ofPred_eq, Set.mem_sdiff, abs_dvd, degree_modByMonic_lt, dvd_add_self_mul, eq_zero_of_abs_lt_dvd, eq_zero_of_infinite_isRoot, eval_add, eval_mul, finite_abs_eval_le_of_degree_lt, h.sdiff, mem_ofPred_eq, mem_sdiff, modByMonic_add_div, modByMonic_eq_zero_iff_dvd, not_le
-/
theorem dvd_of_infinite_eval_dvd_eval
    {P Q : Int[X]} (mQ : Q.Monic) (h : {a | Q.eval a ∣ P.eval a}.Infinite) : Q ∣ P := by
  have eqR := modByMonic_add_div P Q
  have degR := degree_modByMonic_lt P mQ
  rw [← modByMonic_eq_zero_iff_dvd mQ]
  set R := P %ₘ Q
  apply eq_zero_of_infinite_isRoot
  refine (h.sdiff (finite_abs_eval_le_of_degree_lt degR)).mono fun x mx => ?_
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_le] at mx
  rw [← eqR]; rw [eval_add]; rw [eval_mul]; rw [Int.dvd_add_self_mul]; rw [← abs_dvd] at mx
  exact Int.eq_zero_of_abs_lt_dvd mx.1 mx.2

end Polynomial
