/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler, Michael Stoll
-/
module

public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Complex.Positivity
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Positivity of values of L-series

The main results of this file are as follows.

* If `a : ℕ → ℂ` takes nonnegative real values and `a 1 > 0`, then `L a x > 0`
  when `x : ℝ` is in the open half-plane of absolute convergence; see
  `LSeries.positive` and `ArithmeticFunction.LSeries_positive`.

* If in addition the L-series of `a` agrees on some open right half-plane where it
  converges with an entire function `f`, then `f` is positive on the real axis;
  see `LSeries.positive_of_eq_differentiable` and
  `ArithmeticFunction.LSeries_positive_of_eq_differentiable`.
-/

public section

open scoped ComplexOrder

open Complex

namespace LSeries

/--
lemma `iteratedDeriv_alternating` / 引理 `iteratedDeriv_alternating`

English:
lemma iteratedDeriv_alternating
  statement: {a : Nat -> Complex} (hn : 0 <= a) {x : Real}
  proof: by
  rw [LSeries_iteratedDeriv _ h]; rw [LSeries]; rw [← mul_assoc]; rw [← pow_add]; rw [Even.neg_one_pow ⟨n]; rw [rfl⟩]; rw [one_mul]
  refine tsum_nonneg fun k => ?_
  rw [LSeries.term_def]
  split
  · exact le_rfl
· refine mul_nonneg ?_ (inv_natCast_cpow_ofReal_pos (by assumption) x).le
    induction n with
    | zero => simpa only [Function.iterate_zero, id_eq] using! hn k
    | succ n IH =>
        rw [Function.iterate_succ_apply']
        refine mul_nonneg ?_ IH
        simp only [← natCast_log, zero_le_real, Real.log_natCast_nonneg]

中文:
引理 iteratedDeriv_alternating
  结论: {a : 自然数 -> 复形} (hn : 0 <= a) {x : 实数}
  证明: by
  rw [LSeries_iteratedDeriv _ h]; rw [LSeries]; rw [← mul_assoc]; rw [← pow_add]; rw [Even.neg_one_pow ⟨n]; rw [rfl⟩]; rw [one_mul]
  refine tsum_nonneg fun k => ?_
  rw [LSeries.term_def]
  split
  · exact le_rfl
· refine mul_nonneg ?_ (inv_natCast_cpow_ofReal_pos (by assumption) x).le
    induction n with
    | zero => simpa only [Function.iterate_zero, id_eq] using! hn k
    | succ n IH =>
        rw [Function.iterate_succ_apply']
        refine mul_nonneg ?_ IH
        simp only [← natCast_log, zero_le_real, Real.log_natCast_nonneg]

Depends on / 依赖: Even.neg_one_pow, Function, Function.iterate_succ_apply, Function.iterate_zero, LSeries, LSeries.term_def, LSeries_iteratedDeriv, Real.log_natCast_nonneg, id_eq, inv_natCast_cpow_ofReal_pos, iterate_succ_apply, iterate_zero, le_rfl, log_natCast_nonneg, mul_assoc, mul_nonneg, natCast_log, neg_one_pow, one_mul, pow_add
-/
lemma iteratedDeriv_alternating {a : Nat -> Complex} (hn : 0 <= a) {x : Real}
    (h : LSeries.abscissaOfAbsConv a < x) (n : Nat) :
    0 <= (-1) ^ n * iteratedDeriv n (LSeries a) x := by
  rw [LSeries_iteratedDeriv _ h]; rw [LSeries]; rw [← mul_assoc]; rw [← pow_add]; rw [Even.neg_one_pow ⟨n]; rw [rfl⟩]; rw [one_mul]
  refine tsum_nonneg fun k => ?_
  rw [LSeries.term_def]
  split
  · exact le_rfl
· refine mul_nonneg ?_ (inv_natCast_cpow_ofReal_pos (by assumption) x).le
    induction n with
    | zero => simpa only [Function.iterate_zero, id_eq] using! hn k
    | succ n IH =>
        rw [Function.iterate_succ_apply']
        refine mul_nonneg ?_ IH
        simp only [← natCast_log, zero_le_real, Real.log_natCast_nonneg]

/--
lemma `positive` / 引理 `positive`

English:
lemma positive
  given: {a : Nat -> Complex} (ha₀ : 0 <= a) (ha₁ : 0 < a 1) {x : Real} (hx : abscissaOfAbsConv a < x)
  proof: by
  rw [LSeries]
refine Summable.tsum_pos ?_ (fun n => term_nonneg (ha₀ n) x) 1 term_pos one_ne_zero ha₁ x
exact LSeriesSummable_of_abscissaOfAbsConv_lt_re by simpa only [ofReal_re] using hx

中文:
引理 positive
  条件: {a : 自然数 -> 复形} (ha₀ : 0 <= a) (ha₁ : 0 < a 1) {x : 实数} (hx : abscissaOfAbsConv a < x)
  证明: by
  rw [LSeries]
refine Summable.tsum_pos ?_ (fun n => term_nonneg (ha₀ n) x) 1 term_pos one_ne_zero ha₁ x
exact LSeriesSummable_of_abscissaOfAbsConv_lt_re by simpa only [ofReal_re] using hx

Depends on / 依赖: LSeries, LSeriesSummable_of_abscissaOfAbsConv_lt_re, Summable, Summable.tsum_pos, ofReal_re, one_ne_zero, term_nonneg, term_pos, tsum_pos
-/
lemma positive {a : Nat -> Complex} (ha₀ : 0 <= a) (ha₁ : 0 < a 1) {x : Real} (hx : abscissaOfAbsConv a < x) :
    0 < LSeries a x := by
  rw [LSeries]
refine Summable.tsum_pos ?_ (fun n => term_nonneg (ha₀ n) x) 1 term_pos one_ne_zero ha₁ x
exact LSeriesSummable_of_abscissaOfAbsConv_lt_re by simpa only [ofReal_re] using hx

/--
lemma `positive_of_differentiable_of_eqOn` / 引理 `positive_of_differentiable_of_eqOn`

English:
lemma positive_of_differentiable_of_eqOn
  statement: {a : Nat -> Complex} (ha₀ : 0 <= a) (ha₁ : 0 < a 1) {f : Complex -> Complex}
  proof: by
  have hxy : x < max x y + 1 := (le_max_left x y).trans_lt (lt_add_one _)
have hxy' : abscissaOfAbsConv a < max x y + 1 := hx.trans_lt mod_cast hxy
  have hys : (max x y + 1 : Complex) in {s | x < s.re} := by
    simp only [Set.mem_ofPred_eq, add_re, ofReal_re, one_re, hxy]
  have hfx : 0 < f (max x y + 1) := by
    simpa only [hf' hys, ofReal_add, ofReal_one] using positive ha₀ ha₁ hxy'
  refine (hfx.trans_le <| hf.apply_le_of_iteratedDeriv_alternating (fun n _ => ?_) ?_)
  · have hs : IsOpen {s : Complex | x < s.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
    simpa only [hf'.iteratedDeriv_of_isOpen hs n hys, ofReal_add, ofReal_one] using
      iteratedDeriv_alternating ha₀ hxy' n
  · exact_mod_cast (le_max_right x y).trans (lt_add_one _).le

中文:
引理 positive_of_differentiable_of_eqOn
  结论: {a : 自然数 -> 复形} (ha₀ : 0 <= a) (ha₁ : 0 < a 1) {f : 复形 -> 复形}
  证明: by
  have hxy : x < max x y + 1 := (le_max_left x y).trans_lt (lt_add_one _)
have hxy' : abscissaOfAbsConv a < max x y + 1 := hx.trans_lt mod_cast hxy
  have hys : (max x y + 1 : Complex) in {s | x < s.re} := by
    simp only [Set.mem_ofPred_eq, add_re, ofReal_re, one_re, hxy]
  have hfx : 0 < f (max x y + 1) := by
    simpa only [hf' hys, ofReal_add, ofReal_one] using positive ha₀ ha₁ hxy'
  refine (hfx.trans_le <| hf.apply_le_of_iteratedDeriv_alternating (fun n _ => ?_) ?_)
  · have hs : IsOpen {s : Complex | x < s.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
    simpa only [hf'.iteratedDeriv_of_isOpen hs n hys, ofReal_add, ofReal_one] using
      iteratedDeriv_alternating ha₀ hxy' n
  · exact_mod_cast (le_max_right x y).trans (lt_add_one _).le

Depends on / 依赖: IsOpen, Set.mem_ofPred_eq, abscissaOfAbsConv, add_re, apply_le_of_iteratedDeriv_alternating, hf.apply_le_of_iteratedDeriv_alternating, hfx.trans_le, hx.trans_lt, le_max_left, lt_add_one, mem_ofPred_eq, mod_cast, ofReal_add, ofReal_one, ofReal_re, one_re, positive, s.re, trans_le, trans_lt
-/
lemma positive_of_differentiable_of_eqOn {a : Nat -> Complex} (ha₀ : 0 <= a) (ha₁ : 0 < a 1) {f : Complex -> Complex}
    (hf : Differentiable Complex f) {x : Real} (hx : abscissaOfAbsConv a <= x)
    (hf' : {s | x < s.re}.EqOn f (LSeries a)) (y : Real) :
    0 < f y := by
  have hxy : x < max x y + 1 := (le_max_left x y).trans_lt (lt_add_one _)
have hxy' : abscissaOfAbsConv a < max x y + 1 := hx.trans_lt mod_cast hxy
  have hys : (max x y + 1 : Complex) in {s | x < s.re} := by
    simp only [Set.mem_ofPred_eq, add_re, ofReal_re, one_re, hxy]
  have hfx : 0 < f (max x y + 1) := by
    simpa only [hf' hys, ofReal_add, ofReal_one] using positive ha₀ ha₁ hxy'
  refine (hfx.trans_le <| hf.apply_le_of_iteratedDeriv_alternating (fun n _ => ?_) ?_)
  · have hs : IsOpen {s : Complex | x < s.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
    simpa only [hf'.iteratedDeriv_of_isOpen hs n hys, ofReal_add, ofReal_one] using
      iteratedDeriv_alternating ha₀ hxy' n
  · exact_mod_cast (le_max_right x y).trans (lt_add_one _).le

end LSeries

namespace ArithmeticFunction

/--
lemma `iteratedDeriv_LSeries_alternating` / 引理 `iteratedDeriv_LSeries_alternating`

English:
lemma iteratedDeriv_LSeries_alternating
  statement: (a : ArithmeticFunction Complex) (hn : forall n, 0 <= a n) {x : Real}
  proof: LSeries.iteratedDeriv_alternating hn h n

中文:
引理 iteratedDeriv_LSeries_alternating
  结论: (a : ArithmeticFunction 复形) (hn : 对任意 n, 0 <= a n) {x : 实数}
  证明: LSeries.iteratedDeriv_alternating hn h n

Depends on / 依赖: LSeries, LSeries.iteratedDeriv_alternating, iteratedDeriv_alternating
-/
lemma iteratedDeriv_LSeries_alternating (a : ArithmeticFunction Complex) (hn : forall n, 0 <= a n) {x : Real}
    (h : LSeries.abscissaOfAbsConv a < x) (n : Nat) :
    0 <= (-1) ^ n * iteratedDeriv n (LSeries (a ·)) x :=
  LSeries.iteratedDeriv_alternating hn h n

/--
lemma `LSeries_positive` / 引理 `LSeries_positive`

English:
lemma LSeries_positive
  statement: {a : Nat -> Complex} (ha₀ : 0 <= a) (ha₁ : 0 < a 1) {x : Real}
  proof: LSeries.positive ha₀ ha₁ hx

中文:
引理 LSeries_positive
  结论: {a : 自然数 -> 复形} (ha₀ : 0 <= a) (ha₁ : 0 < a 1) {x : 实数}
  证明: LSeries.positive ha₀ ha₁ hx

Depends on / 依赖: LSeries, LSeries.positive, positive
-/
lemma LSeries_positive {a : Nat -> Complex} (ha₀ : 0 <= a) (ha₁ : 0 < a 1) {x : Real}
    (hx : LSeries.abscissaOfAbsConv a < x) :
    0 < LSeries a x :=
  LSeries.positive ha₀ ha₁ hx

/--
lemma `LSeries_positive_of_differentiable_of_eqOn` / 引理 `LSeries_positive_of_differentiable_of_eqOn`

English:
lemma LSeries_positive_of_differentiable_of_eqOn
  statement: {a : ArithmeticFunction Complex} (ha₀ : 0 <= (a ·))
  proof: LSeries.positive_of_differentiable_of_eqOn ha₀ ha₁ hf hx hf' y

中文:
引理 LSeries_positive_of_differentiable_of_eqOn
  结论: {a : ArithmeticFunction 复形} (ha₀ : 0 <= (a ·))
  证明: LSeries.positive_of_differentiable_of_eqOn ha₀ ha₁ hf hx hf' y

Depends on / 依赖: LSeries, LSeries.positive_of_differentiable_of_eqOn, positive_of_differentiable_of_eqOn
-/
lemma LSeries_positive_of_differentiable_of_eqOn {a : ArithmeticFunction Complex} (ha₀ : 0 <= (a ·))
    (ha₁ : 0 < a 1) {f : Complex -> Complex} (hf : Differentiable Complex f) {x : Real}
    (hx : LSeries.abscissaOfAbsConv a <= x) (hf' : {s | x < s.re}.EqOn f (LSeries a)) (y : Real) :
    0 < f y :=
  LSeries.positive_of_differentiable_of_eqOn ha₀ ha₁ hf hx hf' y

end ArithmeticFunction
