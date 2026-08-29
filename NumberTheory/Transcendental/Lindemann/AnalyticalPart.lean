/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Algebra.Polynomial.SumIteratedDerivative
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Analytic part of the Lindemann-Weierstrass theorem
-/

public section

namespace LindemannWeierstrass

noncomputable section

open scoped Nat
open Complex Polynomial

/--
theorem `hasDerivAt_cexp_mul_sumIDeriv` / 定理 `hasDerivAt_cexp_mul_sumIDeriv`

English:
theorem hasDerivAt_cexp_mul_sumIDeriv
  given: (p : Complex[X]) (s : Complex) (x : Real)
  proof: by
  have h₀ := (hasDerivAt_id' x).smul_const s
  have h₁ := h₀.fun_neg.cexp
  have h₂ := ((sumIDeriv p).hasDerivAt (x • s)).comp x h₀
  convert! (h₁.mul h₂).fun_neg using 1
  nth_rw 1 [sumIDeriv_eq_self_add p]
  simp only [one_smul, eval_add, Function.comp_apply]
  ring

中文:
定理 hasDerivAt_cexp_mul_sumIDeriv
  条件: (p : Complex[X]) (s : Complex) (x : 实数)
  证明: by
  have h₀ := (hasDerivAt_id' x).smul_const s
  have h₁ := h₀.fun_neg.cexp
  have h₂ := ((sumIDeriv p).hasDerivAt (x • s)).comp x h₀
  convert! (h₁.mul h₂).fun_neg using 1
  nth_rw 1 [sumIDeriv_eq_self_add p]
  simp only [one_smul, eval_add, Function.comp_apply]
  ring

Depends on / 依赖: Function, Function.comp_apply, comp_apply, convert, eval_add, fun_neg, fun_neg.cexp, hasDerivAt, hasDerivAt_id, nth_rw, one_smul, smul_const, sumIDeriv, sumIDeriv_eq_self_add
-/
theorem hasDerivAt_cexp_mul_sumIDeriv (p : Complex[X]) (s : Complex) (x : Real) :
    HasDerivAt (fun x : Real => -(cexp (-(x • s)) * p.sumIDeriv.eval (x • s)))
      (s * (cexp (-(x • s)) * p.eval (x • s))) x := by
  have h₀ := (hasDerivAt_id' x).smul_const s
  have h₁ := h₀.fun_neg.cexp
  have h₂ := ((sumIDeriv p).hasDerivAt (x • s)).comp x h₀
  convert! (h₁.mul h₂).fun_neg using 1
  nth_rw 1 [sumIDeriv_eq_self_add p]
  simp only [one_smul, eval_add, Function.comp_apply]
  ring

/--
theorem `integral_exp_mul_eval` / 定理 `integral_exp_mul_eval`

English:
theorem integral_exp_mul_eval
  given: (p : Complex[X]) (s : Complex)
  proof: by
  rw [← intervalIntegral.integral_const_mul]; rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hasDerivAt_cexp_mul_sumIDeriv p s x)
      (ContinuousOn.intervalIntegrable (by fun_prop))]
  simp

中文:
定理 integral_exp_mul_eval
  条件: (p : Complex[X]) (s : Complex)
  证明: by
  rw [← intervalIntegral.integral_const_mul]; rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hasDerivAt_cexp_mul_sumIDeriv p s x)
      (ContinuousOn.intervalIntegrable (by fun_prop))]
  simp

Depends on / 依赖: ContinuousOn, ContinuousOn.intervalIntegrable, fun_prop, hasDerivAt_cexp_mul_sumIDeriv, integral_const_mul, integral_eq_sub_of_hasDerivAt, intervalIntegrable, intervalIntegral, intervalIntegral.integral_const_mul, intervalIntegral.integral_eq_sub_of_hasDerivAt
-/
theorem integral_exp_mul_eval (p : Complex[X]) (s : Complex) :
    s * ∫ x in 0..1, exp (-(x • s)) * p.eval (x • s) =
      -(exp (-s) * p.sumIDeriv.eval s) + p.sumIDeriv.eval 0 := by
  rw [← intervalIntegral.integral_const_mul]; rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hasDerivAt_cexp_mul_sumIDeriv p s x)
      (ContinuousOn.intervalIntegrable (by fun_prop))]
  simp

/--
Definition of `P` / `P` 的定义

English:
definition P
  signature: (f : Complex[X]) (s : Complex)
  body: exp s * f.sumIDeriv.eval 0 - f.sumIDeriv.eval s

中文:
定义 P
  签名: (f : Complex[X]) (s : Complex)
  定义体: exp s * f.sumIDeriv.eval 0 - f.sumIDeriv.eval s
-/
private def P (f : Complex[X]) (s : Complex) :=
  exp s * f.sumIDeriv.eval 0 - f.sumIDeriv.eval s

/--
theorem `P_eq_integral_exp_mul_eval` / 定理 `P_eq_integral_exp_mul_eval`

English:
theorem P_eq_integral_exp_mul_eval
  given: (f : Complex[X]) (s : Complex)
  proof: by
  rw [integral_exp_mul_eval]; rw [mul_add]; rw [mul_neg]; rw [exp_neg]; rw [mul_inv_cancel_left₀ (exp_ne_zero s)]; rw [neg_add_eq_sub]; rw [P]

中文:
定理 P_eq_integral_exp_mul_eval
  条件: (f : Complex[X]) (s : Complex)
  证明: by
  rw [integral_exp_mul_eval]; rw [mul_add]; rw [mul_neg]; rw [exp_neg]; rw [mul_inv_cancel_left₀ (exp_ne_zero s)]; rw [neg_add_eq_sub]; rw [P]
-/
private theorem P_eq_integral_exp_mul_eval (f : Complex[X]) (s : Complex) :
    P f s = exp s * (s * ∫ x in 0..1, exp (-(x • s)) * f.eval (x • s)) := by
  rw [integral_exp_mul_eval]; rw [mul_add]; rw [mul_neg]; rw [exp_neg]; rw [mul_inv_cancel_left₀ (exp_ne_zero s)]; rw [neg_add_eq_sub]; rw [P]

/--
theorem `P_le_aux` / 定理 `P_le_aux`

English:
theorem P_le_aux
  statement: (f : Nat -> Complex[X]) (s : Complex) (c : Real)
  proof: by
  refine ⟨|c|, abs_nonneg _, fun p => ?_⟩
  rw [P_eq_integral_exp_mul_eval (f p) s]; rw [mul_comm s]; rw [norm_mul]; rw [norm_mul]; rw [norm_exp]
  gcongr
  rw [intervalIntegral.integral_of_le zero_le_one]; rw [← mul_one (_ * _)]
  convert! MeasureTheory.norm_setIntegral_le_of_norm_le_const _ _
 

中文:
定理 P_le_aux
  结论: (f : 自然数 -> Complex[X]) (s : Complex) (c : 实数)
  证明: by
  refine ⟨|c|, abs_nonneg _, fun p => ?_⟩
  rw [P_eq_integral_exp_mul_eval (f p) s]; rw [mul_comm s]; rw [norm_mul]; rw [norm_mul]; rw [norm_exp]
  gcongr
  rw [intervalIntegral.integral_of_le zero_le_one]; rw [← mul_one (_ * _)]
  convert! MeasureTheory.norm_setIntegral_le_of_norm_le_const _ _
 
-/
private theorem P_le_aux (f : Nat -> Complex[X]) (s : Complex) (c : Real)
    (hc : forall p : Nat, forall x in Set.Ioc (0 : Real) 1, ‖(f p).eval (x • s)‖ <= c ^ p) :
    exists c' >= 0, forall p : Nat,
      ‖P (f p) s‖ <=
        Real.exp s.re * (Real.exp ‖s‖ * c' ^ p * ‖s‖) := by
  refine ⟨|c|, abs_nonneg _, fun p => ?_⟩
  rw [P_eq_integral_exp_mul_eval (f p) s]; rw [mul_comm s]; rw [norm_mul]; rw [norm_mul]; rw [norm_exp]
  gcongr
  rw [intervalIntegral.integral_of_le zero_le_one]; rw [← mul_one (_ * _)]
  convert! MeasureTheory.norm_setIntegral_le_of_norm_le_const _ _
  · rw [Real.volume_real_Ioc_of_le zero_le_one, sub_zero]
  · rw [Real.volume_Ioc, sub_zero]; exact ENNReal.ofReal_lt_top
  intro x hx
  rw [norm_mul]; rw [norm_exp]
  gcongr
  · simp only [Set.mem_Ioc] at hx
    apply (re_le_norm _).trans
    rw [norm_neg]; rw [norm_smul]; rw [Real.norm_of_nonneg hx.1.le]
    exact mul_le_of_le_one_left (norm_nonneg _) hx.2
  · rw [← abs_pow]
    exact (hc p x hx).trans (le_abs_self _)

/--
theorem `P_le` / 定理 `P_le`

English:
theorem P_le
  statement: (f : Nat -> Complex[X]) (s : Complex) (c : Real)
  proof: by
  obtain ⟨c', hc', h'⟩ := P_le_aux f s c hc; clear c hc
  let c₁ := max (Real.exp s.re) 1
  let c₂ := max (Real.exp ‖s‖) 1
  let c₃ := max ‖s‖ 1
  use c₁ * (c₂ * c' * c₃), by positivity
  intro p hp
  refine (h' p).trans ?_
  simp_rw [mul_pow]
  have le_max_one_pow {x : Real} : x <= max x 1 ^ p :

中文:
定理 P_le
  结论: (f : 自然数 -> Complex[X]) (s : Complex) (c : 实数)
  证明: by
  obtain ⟨c', hc', h'⟩ := P_le_aux f s c hc; clear c hc
  let c₁ := max (Real.exp s.re) 1
  let c₂ := max (Real.exp ‖s‖) 1
  let c₃ := max ‖s‖ 1
  use c₁ * (c₂ * c' * c₃), by positivity
  intro p hp
  refine (h' p).trans ?_
  simp_rw [mul_pow]
  have le_max_one_pow {x : Real} : x <= max x 1 ^ p :
-/
private theorem P_le (f : Nat -> Complex[X]) (s : Complex) (c : Real)
    (hc : forall p : Nat, forall x in Set.Ioc (0 : Real) 1, ‖(f p).eval (x • s)‖ <= c ^ p) :
    exists c' >= 0, forall p != 0, ‖P (f p) s‖ <= c' ^ p := by
  obtain ⟨c', hc', h'⟩ := P_le_aux f s c hc; clear c hc
  let c₁ := max (Real.exp s.re) 1
  let c₂ := max (Real.exp ‖s‖) 1
  let c₃ := max ‖s‖ 1
  use c₁ * (c₂ * c' * c₃), by positivity
  intro p hp
  refine (h' p).trans ?_
  simp_rw [mul_pow]
  have le_max_one_pow {x : Real} : x <= max x 1 ^ p :=
    (max_cases x 1).elim (fun h => h.1.symm ▸ le_self_pow₀ h.2 hp)
      fun h => by rw [h.1, one_pow]; exact h.2.le
  gcongr <;> exact le_max_one_pow

/--
theorem `exp_polynomial_approx_aux` / 定理 `exp_polynomial_approx_aux`

English:
theorem exp_polynomial_approx_aux
  given: (f : Int[X]) (s : Complex)
  proof: by
  have : Bornology.IsBounded
      ((fun x : Real => max (x * ‖s‖) 1 * ‖aeval (x * s) f‖) '' Set.Ioc 0 1) := by
    have h :
      (fun x : Real => max (x * ‖s‖) 1 * ‖aeval (x * s) f‖) '' Set.Ioc 0 1 subseteq
        (fun x : Real => max (x * ‖s‖) 1 * ‖aeval (x * s) f‖) '' Set.Icc 0 1 :=
      Se

中文:
定理 exp_polynomial_approx_aux
  条件: (f : 整数[X]) (s : Complex)
  证明: by
  have : Bornology.IsBounded
      ((fun x : Real => max (x * ‖s‖) 1 * ‖aeval (x * s) f‖) '' Set.Ioc 0 1) := by
    have h :
      (fun x : Real => max (x * ‖s‖) 1 * ‖aeval (x * s) f‖) '' Set.Ioc 0 1 subseteq
        (fun x : Real => max (x * ‖s‖) 1 * ‖aeval (x * s) f‖) '' Set.Icc 0 1 :=
      Se
-/
private theorem exp_polynomial_approx_aux (f : Int[X]) (s : Complex) :
    exists c >= 0,
      forall p != 0, ‖P (map (algebraMap Int Complex) (X ^ (p - 1) * f ^ p)) s‖ <= c ^ p := by
  have : Bornology.IsBounded
      ((fun x : Real => max (x * ‖s‖) 1 * ‖aeval (x * s) f‖) '' Set.Ioc 0 1) := by
    have h :
      (fun x : Real => max (x * ‖s‖) 1 * ‖aeval (x * s) f‖) '' Set.Ioc 0 1 subseteq
        (fun x : Real => max (x * ‖s‖) 1 * ‖aeval (x * s) f‖) '' Set.Icc 0 1 :=
      Set.image_mono Set.Ioc_subset_Icc_self
    refine (IsCompact.image isCompact_Icc ?_).isBounded.subset h
    fun_prop
  obtain ⟨c, h⟩ := this.exists_norm_le
  simp_rw [Real.norm_eq_abs] at h
  refine P_le _ s c (fun p x hx => ?_)
  specialize h (max (x * ‖s‖) 1 * ‖aeval (x * s) f‖) (Set.mem_image_of_mem _ hx)
  grw [← h]
  simp_rw [Polynomial.map_mul, Polynomial.map_pow, map_X, eval_mul, eval_pow, eval_X, norm_mul,
    Complex.norm_pow, real_smul, norm_mul, norm_real, ← eval₂_eq_eval_map, ← aeval_def, abs_mul,
    abs_norm, mul_pow, Real.norm_of_nonneg hx.1.le]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg _) _)
  rw [← mul_pow]; rw [abs_of_nonneg (by positivity)]; rw [max_def]
  split_ifs with hx1
  · rw [one_pow]
    exact pow_le_one₀ (mul_nonneg hx.1.le (norm_nonneg _)) hx1
  · push Not at hx1
    exact pow_le_pow_right₀ hx1.le (Nat.sub_le _ _)

/--
theorem `exp_polynomial_approx` / 定理 `exp_polynomial_approx`

English:
theorem exp_polynomial_approx
  given: (f : Int[X]) (hf : f.eval 0 != 0)
  proof: by
  simp_rw [nsmul_eq_mul, zsmul_eq_mul]
  choose c' c'0 Pp'_le using exp_polynomial_approx_aux f
  use
    if h : ((f.aroots Complex).map c').toFinset.Nonempty then ((f.aroots Complex).map c').toFinset.max' h else 0
  intro p p_gt prime_p
  obtain ⟨gp', -, h'⟩ := eval_sumIDeriv_of_pos (X ^ (p - 1)

中文:
定理 exp_polynomial_approx
  条件: (f : 整数[X]) (hf : f.eval 0 != 0)
  证明: by
  simp_rw [nsmul_eq_mul, zsmul_eq_mul]
  choose c' c'0 Pp'_le using exp_polynomial_approx_aux f
  use
    if h : ((f.aroots Complex).map c').toFinset.Nonempty then ((f.aroots Complex).map c').toFinset.max' h else 0
  intro p p_gt prime_p
  obtain ⟨gp', -, h'⟩ := eval_sumIDeriv_of_pos (X ^ (p - 1)

Depends on / 依赖: Int.natAbs_pos.mpr, Nat.le_of_dvd, Nonempty, aroots, contrapose, dvd_add_left, dvd_mul_right, eval_sumIDeriv_of_pos, exp_polynomial_approx_aux, f.aroots, f.eval, le_of_dvd, natAbs_pos, nsmul_eq_mul, p_gt, prime_p, prime_p.pos, simp_rw, specialize, sub_zero
-/
theorem exp_polynomial_approx (f : Int[X]) (hf : f.eval 0 != 0) :
    exists c,
      forall p > (eval 0 f).natAbs, p.Prime ->
        exists n : Int, ¬ ↑p ∣ n ∧ exists gp : Int[X], gp.natDegree <= p * f.natDegree - 1 ∧
          forall {r : Complex}, r in f.aroots Complex ->
            ‖n • exp r - p • aeval r gp‖ <= c ^ p / (p - 1)! := by
  simp_rw [nsmul_eq_mul, zsmul_eq_mul]
  choose c' c'0 Pp'_le using exp_polynomial_approx_aux f
  use
    if h : ((f.aroots Complex).map c').toFinset.Nonempty then ((f.aroots Complex).map c').toFinset.max' h else 0
  intro p p_gt prime_p
  obtain ⟨gp', -, h'⟩ := eval_sumIDeriv_of_pos (X ^ (p - 1) * f ^ p) prime_p.pos
  specialize h' 0 (by rw [C_0, sub_zero])
  use f.eval 0 ^ p + p * gp'.eval 0
  constructor
  · rw [dvd_add_left (dvd_mul_right _ _)]
    contrapose! p_gt with h
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr hf) (Int.natCast_dvd.mp (Int.Prime.dvd_pow' prime_p h))
  obtain ⟨gp, gp'_le, h⟩ := aeval_sumIDeriv Complex (X ^ (p - 1) * f ^ p) p
  refine ⟨gp, ?_, ?_⟩
  · refine gp'_le.trans ((tsub_le_tsub_right natDegree_mul_le p).trans ?_)
    rw [natDegree_X_pow]; rw [natDegree_pow]; rw [tsub_add_eq_add_tsub prime_p.one_le]; rw [tsub_right_comm]; rw [add_tsub_cancel_left]
  intro r hr
  specialize h r _
  · rw [mem_roots'] at hr
    rw [Polynomial.map_mul]; rw [f.map_pow]
    exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr hr.2) _) _
  rw [nsmul_eq_mul] at h
  have :
      (↑(eval 0 f ^ p + p * eval 0 gp') * cexp r - p * (aeval r) gp) * (p - 1)! =
      ((eval 0 f ^ p * cexp r) * (p - 1)! +
        ↑(p * (p - 1)!) * (eval 0 gp' * cexp r - (aeval r) gp)) := by
    push_cast; ring
  rw [le_div_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos _) : (0 : Real) < _)]; rw [← norm_natCast]; rw [← norm_mul]; rw [this]; rw [Nat.mul_factorial_pred prime_p.ne_zero]; rw [mul_sub]; rw [← h]
  have :
      ↑(eval 0 f) ^ p * cexp r * ↑(p - 1)! +
        (↑p ! * (↑(eval 0 gp') * cexp r) - (aeval r) (sumIDeriv (X ^ (p - 1) * f ^ p))) =
      ((p - 1)! • ↑(eval 0 (f ^ p)) + p ! • ↑(eval 0 gp') : Int) * cexp r -
        (aeval r) (sumIDeriv (X ^ (p - 1) * f ^ p)) := by
    simp; ring
  rw [this]; rw [← h']; rw [mul_comm]; rw [← eq_intCast (algebraMap Int Complex)]; rw [← aeval_algebraMap_apply_eq_algebraMap_eval]; rw [map_zero]; rw [aeval_sumIDeriv_eq_eval]; rw [aeval_sumIDeriv_eq_eval]; rw [← P]
  refine (Pp'_le r p prime_p.ne_zero).trans (pow_le_pow_left₀ (c'0 r) ?_ _)
  have aux : c' r in (Multiset.map c' (f.aroots Complex)).toFinset := by
    simpa only [Multiset.mem_toFinset] using Multiset.mem_map_of_mem _ hr
  have h : ((f.aroots Complex).map c').toFinset.Nonempty := ⟨c' r, aux⟩
  simpa only [h, ↓reduceDIte] using Finset.le_max' _ _ aux

end

end LindemannWeierstrass
