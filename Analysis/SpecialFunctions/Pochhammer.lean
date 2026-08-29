/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Piecewise
public import Mathlib.Analysis.Convex.Jensen

/-!
# Pochhammer polynomials

This file proves analysis theorems for Pochhammer polynomials.

## Main statements

* `Differentiable.descPochhammer_eval` is the proof that the descending Pochhammer polynomial
  `descPochhammer ℝ n` is differentiable.

* `ConvexOn.descPochhammer_eval` is the proof that the descending Pochhammer polynomial
  `descPochhammer ℝ n` is convex on `[n-1, ∞)`.

* `descPochhammer_eval_le_sum_descFactorial` is a special case of **Jensen's inequality**
  for `Nat.descFactorial`.

* `descPochhammer_eval_div_factorial_le_sum_choose` is a special case of **Jensen's inequality**
  for `Nat.choose`.
-/

public section


section DescPochhammer

variable {n : Nat} {𝕜 : Type*} {k : 𝕜} [NontriviallyNormedField 𝕜]

/--
theorem `differentiable_descPochhammer_eval` / 定理 `differentiable_descPochhammer_eval`

English:
theorem differentiable_descPochhammer_eval
  statement: Differentiable 𝕜 (descPochhammer 𝕜 n).eval
  proof: by
  simp [descPochhammer_eval_eq_prod_range, Differentiable.fun_finsetProd]

中文:
定理 differentiable_descPochhammer_eval
  结论: 可微 𝕜 (descPochhammer 𝕜 n).eval
  证明: by
  simp [descPochhammer_eval_eq_prod_range, Differentiable.fun_finsetProd]

Depends on / 依赖: Differentiable, Differentiable.fun_finsetProd, descPochhammer_eval_eq_prod_range, fun_finsetProd
-/
theorem differentiable_descPochhammer_eval : Differentiable 𝕜 (descPochhammer 𝕜 n).eval := by
  simp [descPochhammer_eval_eq_prod_range, Differentiable.fun_finsetProd]

/--
theorem `continuous_descPochhammer_eval` / 定理 `continuous_descPochhammer_eval`

English:
theorem continuous_descPochhammer_eval
  statement: Continuous (descPochhammer 𝕜 n).eval
  proof: by
  exact differentiable_descPochhammer_eval.continuous

中文:
定理 continuous_descPochhammer_eval
  结论: 连续 (descPochhammer 𝕜 n).eval
  证明: by
  exact differentiable_descPochhammer_eval.continuous

Depends on / 依赖: continuous, differentiable_descPochhammer_eval, differentiable_descPochhammer_eval.continuous
-/
theorem continuous_descPochhammer_eval : Continuous (descPochhammer 𝕜 n).eval := by
  exact differentiable_descPochhammer_eval.continuous

/--
lemma `deriv_descPochhammer_eval_eq_sum_prod_range_erase` / 引理 `deriv_descPochhammer_eval_eq_sum_prod_range_erase`

English:
lemma deriv_descPochhammer_eval_eq_sum_prod_range_erase
  given: (n : Nat) (k : 𝕜)
  proof: by
  simp [descPochhammer_eval_eq_prod_range, deriv_fun_finsetProd]

中文:
引理 deriv_descPochhammer_eval_eq_sum_prod_range_erase
  条件: (n : 自然数) (k : 𝕜)
  证明: by
  simp [descPochhammer_eval_eq_prod_range, deriv_fun_finsetProd]

Depends on / 依赖: deriv_fun_finsetProd, descPochhammer_eval_eq_prod_range
-/
lemma deriv_descPochhammer_eval_eq_sum_prod_range_erase (n : Nat) (k : 𝕜) :
    deriv (descPochhammer 𝕜 n).eval k
      = ∑ i in Finset.range n, ∏ j in (Finset.range n).erase i, (k - j) := by
  simp [descPochhammer_eval_eq_prod_range, deriv_fun_finsetProd]

/--
lemma `monotoneOn_deriv_descPochhammer_eval` / 引理 `monotoneOn_deriv_descPochhammer_eval`

English:
lemma monotoneOn_deriv_descPochhammer_eval
  given: (n : Nat)
  proof: by
  induction n with
  | zero => simp [monotoneOn_const]
  | succ n ih =>
    intro a ha b hb hab
    rw [Set.mem_Ioi]; rw [Nat.cast_add_one]; rw [add_sub_cancel_right] at ha hb
    simp_rw [deriv_descPochhammer_eval_eq_sum_prod_range_erase]
    gcongr with i hi
    intro j hj
    rw [Finset.mem_er

中文:
引理 monotoneOn_deriv_descPochhammer_eval
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => simp [monotoneOn_const]
  | succ n ih =>
    intro a ha b hb hab
    rw [Set.mem_Ioi]; rw [Nat.cast_add_one]; rw [add_sub_cancel_right] at ha hb
    simp_rw [deriv_descPochhammer_eval_eq_sum_prod_range_erase]
    gcongr with i hi
    intro j hj
    rw [Finset.mem_er

Depends on / 依赖: Finset, Finset.mem_erase, Finset.mem_range, Nat.cast_add_one, Nat.le_pred_of_lt, Set.mem_Ioi, add_sub_cancel_right, cast_add_one, deriv_descPochhammer_eval_eq_sum_prod_range_erase, ha.le.trans, le_pred_of_lt, mem_Ioi, mem_erase, mem_range, mod_cast, monotoneOn_const, simp_rw, sub_nonneg_of_le
-/
lemma monotoneOn_deriv_descPochhammer_eval (n : Nat) :
    MonotoneOn (deriv (descPochhammer Real n).eval) (Set.Ioi (n - 1 : Real)) := by
  induction n with
  | zero => simp [monotoneOn_const]
  | succ n ih =>
    intro a ha b hb hab
    rw [Set.mem_Ioi]; rw [Nat.cast_add_one]; rw [add_sub_cancel_right] at ha hb
    simp_rw [deriv_descPochhammer_eval_eq_sum_prod_range_erase]
    gcongr with i hi
    intro j hj
    rw [Finset.mem_erase]; rw [Finset.mem_range] at hj
    apply sub_nonneg_of_le
    exact ha.le.trans' (mod_cast Nat.le_pred_of_lt hj.2)

/--
theorem `convexOn_descPochhammer_eval` / 定理 `convexOn_descPochhammer_eval`

English:
theorem convexOn_descPochhammer_eval
  given: (n : Nat)
  proof: by
  rcases n.eq_zero_or_pos with h_eq | _
  · simp [h_eq, convexOn_const, convex_Ici]
  · apply MonotoneOn.convexOn_of_deriv (convex_Ici (n - 1 : Real))
      continuous_descPochhammer_eval.continuousOn
      differentiable_descPochhammer_eval.differentiableOn
    rw [interior_Ici]
    exact monoto

中文:
定理 convexOn_descPochhammer_eval
  条件: (n : 自然数)
  证明: by
  rcases n.eq_zero_or_pos with h_eq | _
  · simp [h_eq, convexOn_const, convex_Ici]
  · apply MonotoneOn.convexOn_of_deriv (convex_Ici (n - 1 : Real))
      continuous_descPochhammer_eval.continuousOn
      differentiable_descPochhammer_eval.differentiableOn
    rw [interior_Ici]
    exact monoto

Depends on / 依赖: MonotoneOn, MonotoneOn.convexOn_of_deriv, continuousOn, continuous_descPochhammer_eval, continuous_descPochhammer_eval.continuousOn, convexOn_const, convexOn_of_deriv, convex_Ici, differentiableOn, differentiable_descPochhammer_eval, differentiable_descPochhammer_eval.differentiableOn, eq_zero_or_pos, h_eq, interior_Ici, monotoneOn_deriv_descPochhammer_eval, n.eq_zero_or_pos
-/
theorem convexOn_descPochhammer_eval (n : Nat) :
    ConvexOn Real (Set.Ici (n - 1 : Real)) (descPochhammer Real n).eval := by
  rcases n.eq_zero_or_pos with h_eq | _
  · simp [h_eq, convexOn_const, convex_Ici]
  · apply MonotoneOn.convexOn_of_deriv (convex_Ici (n - 1 : Real))
      continuous_descPochhammer_eval.continuousOn
      differentiable_descPochhammer_eval.differentiableOn
    rw [interior_Ici]
    exact monotoneOn_deriv_descPochhammer_eval n

/--
lemma `piecewise_Ici_descPochhammer_eval_zero_eq_descFactorial` / 引理 `piecewise_Ici_descPochhammer_eval_zero_eq_descFactorial`

English:
lemma piecewise_Ici_descPochhammer_eval_zero_eq_descFactorial
  given: (k n : Nat)
  proof: by
  rw [Set.piecewise]; rw [descPochhammer_eval_eq_descFactorial]; rw [ite_eq_left_iff]; rw [Set.mem_Ici]; rw [not_le]; rw [eq_comm]; rw [Pi.zero_apply]; rw [Nat.cast_eq_zero]; rw [Nat.descFactorial_eq_zero_iff_lt]; rw [← @Nat.cast_lt Real]
  exact (sub_lt_self (n : Real) zero_lt_one).trans'

中文:
引理 piecewise_Ici_descPochhammer_eval_zero_eq_descFactorial
  条件: (k n : 自然数)
  证明: by
  rw [Set.piecewise]; rw [descPochhammer_eval_eq_descFactorial]; rw [ite_eq_left_iff]; rw [Set.mem_Ici]; rw [not_le]; rw [eq_comm]; rw [Pi.zero_apply]; rw [Nat.cast_eq_zero]; rw [Nat.descFactorial_eq_zero_iff_lt]; rw [← @Nat.cast_lt Real]
  exact (sub_lt_self (n : Real) zero_lt_one).trans'
-/
private lemma piecewise_Ici_descPochhammer_eval_zero_eq_descFactorial (k n : Nat) :
    (Set.Ici (n - 1 : Real)).piecewise (descPochhammer Real n).eval 0 k
      = k.descFactorial n := by
  rw [Set.piecewise]; rw [descPochhammer_eval_eq_descFactorial]; rw [ite_eq_left_iff]; rw [Set.mem_Ici]; rw [not_le]; rw [eq_comm]; rw [Pi.zero_apply]; rw [Nat.cast_eq_zero]; rw [Nat.descFactorial_eq_zero_iff_lt]; rw [← @Nat.cast_lt Real]
  exact (sub_lt_self (n : Real) zero_lt_one).trans'

/--
lemma `convexOn_piecewise_Ici_descPochhammer_eval_zero` / 引理 `convexOn_piecewise_Ici_descPochhammer_eval_zero`

English:
lemma convexOn_piecewise_Ici_descPochhammer_eval_zero
  given: (hn : n != 0)
  proof: by
  rw [← Nat.pos_iff_ne_zero] at hn
  apply convexOn_univ_piecewise_Ici_of_monotoneOn_Ici_antitoneOn_Iic
    (convexOn_descPochhammer_eval n) (convexOn_const 0 (convex_Iic (n - 1 : Real)))
    (monotoneOn_descPochhammer_eval n) antitoneOn_const
  simpa [← Nat.cast_pred hn] using descPochhammer_eva

中文:
引理 convexOn_piecewise_Ici_descPochhammer_eval_zero
  条件: (hn : n != 0)
  证明: by
  rw [← Nat.pos_iff_ne_zero] at hn
  apply convexOn_univ_piecewise_Ici_of_monotoneOn_Ici_antitoneOn_Iic
    (convexOn_descPochhammer_eval n) (convexOn_const 0 (convex_Iic (n - 1 : Real)))
    (monotoneOn_descPochhammer_eval n) antitoneOn_const
  simpa [← Nat.cast_pred hn] using descPochhammer_eva
-/
private lemma convexOn_piecewise_Ici_descPochhammer_eval_zero (hn : n != 0) :
    ConvexOn Real Set.univ ((Set.Ici (n - 1 : Real)).piecewise (descPochhammer Real n).eval 0) := by
  rw [← Nat.pos_iff_ne_zero] at hn
  apply convexOn_univ_piecewise_Ici_of_monotoneOn_Ici_antitoneOn_Iic
    (convexOn_descPochhammer_eval n) (convexOn_const 0 (convex_Iic (n - 1 : Real)))
    (monotoneOn_descPochhammer_eval n) antitoneOn_const
  simpa [← Nat.cast_pred hn] using descPochhammer_eval_coe_nat_of_lt (Nat.sub_one_lt_of_lt hn)

/--
theorem `descPochhammer_eval_le_sum_descFactorial` / 定理 `descPochhammer_eval_le_sum_descFactorial`

English:
theorem descPochhammer_eval_le_sum_descFactorial
  proof: by
  let f : Real -> Real := (Set.Ici (n - 1 : Real)).piecewise (descPochhammer Real n).eval 0
  suffices h_jensen : f (∑ i in t, w i • p i) <= ∑ i in t, w i • f (p i) by
    simpa only [smul_eq_mul, f, Set.piecewise_eq_of_mem (Set.Ici (n - 1 : Real)) _ _ h_avg,
      piecewise_Ici_descPochhammer_ev

中文:
定理 descPochhammer_eval_le_sum_descFactorial
  证明: by
  let f : Real -> Real := (Set.Ici (n - 1 : Real)).piecewise (descPochhammer Real n).eval 0
  suffices h_jensen : f (∑ i in t, w i • p i) <= ∑ i in t, w i • f (p i) by
    simpa only [smul_eq_mul, f, Set.piecewise_eq_of_mem (Set.Ici (n - 1 : Real)) _ _ h_avg,
      piecewise_Ici_descPochhammer_ev

Depends on / 依赖: ConvexOn, ConvexOn.map_sum_le, Set.Ici, Set.piecewise_eq_of_mem, convexOn_piecewise_Ici_descPochhammer_eval_zero, descPochhammer, h_avg, h_jensen, map_sum_le, piecewise, piecewise_Ici_descPochhammer_eval_zero_eq_descFactorial, piecewise_eq_of_mem, smul_eq_mul
-/
theorem descPochhammer_eval_le_sum_descFactorial
    (hn : n != 0) {ι : Type*} {t : Finset ι} (p : ι -> Nat) (w : ι -> Real)
    (h₀ : forall i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1) (h_avg : n - 1 <= ∑ i in t, w i * p i) :
    (descPochhammer Real n).eval (∑ i in t, w i * p i)
      <= ∑ i in t, w i * (p i).descFactorial n := by
  let f : Real -> Real := (Set.Ici (n - 1 : Real)).piecewise (descPochhammer Real n).eval 0
  suffices h_jensen : f (∑ i in t, w i • p i) <= ∑ i in t, w i • f (p i) by
    simpa only [smul_eq_mul, f, Set.piecewise_eq_of_mem (Set.Ici (n - 1 : Real)) _ _ h_avg,
      piecewise_Ici_descPochhammer_eval_zero_eq_descFactorial] using h_jensen
  exact ConvexOn.map_sum_le (convexOn_piecewise_Ici_descPochhammer_eval_zero hn) h₀ h₁ (by simp)

/--
theorem `descPochhammer_eval_div_factorial_le_sum_choose` / 定理 `descPochhammer_eval_div_factorial_le_sum_choose`

English:
theorem descPochhammer_eval_div_factorial_le_sum_choose
  proof: by
  simp_rw [Nat.cast_choose_eq_descPochhammer_div,
    mul_div, ← Finset.sum_div, descPochhammer_eval_eq_descFactorial]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact descPochhammer_eval_le_sum_descFactorial hn p w h₀ h₁ h_avg

中文:
定理 descPochhammer_eval_div_factorial_le_sum_choose
  证明: by
  simp_rw [Nat.cast_choose_eq_descPochhammer_div,
    mul_div, ← Finset.sum_div, descPochhammer_eval_eq_descFactorial]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact descPochhammer_eval_le_sum_descFactorial hn p w h₀ h₁ h_avg

Depends on / 依赖: Finset, Finset.sum_div, Nat.cast_choose_eq_descPochhammer_div, cast_choose_eq_descPochhammer_div, descPochhammer_eval_eq_descFactorial, descPochhammer_eval_le_sum_descFactorial, div_le_div_of_nonneg_right, h_avg, mul_div, simp_rw, sum_div
-/
theorem descPochhammer_eval_div_factorial_le_sum_choose
    (hn : n != 0) {ι : Type*} {t : Finset ι} (p : ι -> Nat) (w : ι -> Real)
    (h₀ : forall i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1) (h_avg : n - 1 <= ∑ i in t, w i * p i) :
    (descPochhammer Real n).eval (∑ i in t, w i * p i) / n.factorial
      <= ∑ i in t, w i * (p i).choose n := by
  simp_rw [Nat.cast_choose_eq_descPochhammer_div,
    mul_div, ← Finset.sum_div, descPochhammer_eval_eq_descFactorial]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact descPochhammer_eval_le_sum_descFactorial hn p w h₀ h₁ h_avg

end DescPochhammer
