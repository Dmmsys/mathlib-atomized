/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.NumberTheory.Real.Irrational

/-!
# `Real.pi` is irrational

The main result of this file is `irrational_pi`.

The proof is adapted from https://en.wikipedia.org/wiki/Proof_that_%CF%80_is_irrational#Cartwright's_proof.

The proof idea is as follows.
* Define a sequence of integrals `I n θ = ∫ x in (-1)..1, (1 - x ^ 2) ^ n * cos (x * θ)`.
* Give a recursion formula for `I (n + 2) θ * θ ^ 2` in terms of `I n θ` and `I (n + 1) θ`.
  Note we do not find it helpful to define `J` as in the above proof, and instead work directly
  with `I`.
* Define polynomials with integer coefficients `sinPoly n` and `cosPoly n` such that
  `I n θ * θ ^ (2 * n + 1) = n ! * (sinPoly n θ * sin θ + cosPoly n θ * cos θ)`.
  Note that in the informal proof, these polynomials are not defined explicitly, but we find it
  useful to define them by recursion.
* Show that both these polynomials have degree bounded by `n`.
* Show that `0 < I n (π / 2) ≤ 2` for all `n`.
* Now we can finish: if `π / 2` is rational, write it as `a / b` with `a, b > 0`. Then
  `b ^ (2 * n + 1) * sinPoly n (a / b)` is a positive integer by the degree bound. But it is equal
  to `a ^ (2 * n + 1) / n ! * I n (π / 2) ≤ 2 * a * (2 * n + 1) / n !`, which converges to 0 as
  `n → ∞`.

-/

public section

noncomputable section

open intervalIntegral MeasureTheory.MeasureSpace Set Polynomial Real
open scoped Nat

/--
Definition of `I` / `I` 的定义

English:
definition I
  signature: (n : Nat) (θ : Real)
  body: ∫ x in (-1)..1, (1 - x ^ 2) ^ n * cos (x * θ)

中文:
定义 I
  签名: (n : 自然数) (θ : 实数)
  定义体: ∫ x in (-1)..1, (1 - x ^ 2) ^ n * cos (x * θ)
-/
private def I (n : Nat) (θ : Real) : Real := ∫ x in (-1)..1, (1 - x ^ 2) ^ n * cos (x * θ)

variable {n : Nat} {θ : Real}

/--
lemma `I_zero` / 引理 `I_zero`

English:
lemma I_zero
  statement: I 0 θ * θ = 2 * sin θ
  proof: by
  rw [mul_comm]; rw [I]
  simp [mul_integral_comp_mul_right, two_mul]

中文:
引理 I_zero
  结论: I 0 θ * θ = 2 * sin θ
  证明: by
  rw [mul_comm]; rw [I]
  simp [mul_integral_comp_mul_right, two_mul]
-/
private lemma I_zero : I 0 θ * θ = 2 * sin θ := by
  rw [mul_comm]; rw [I]
  simp [mul_integral_comp_mul_right, two_mul]

/--
lemma `recursion'` / 引理 `recursion'`

English:
lemma recursion'
  given: (n : Nat)
  proof: by
  rw [I]
  let f (x : Real) : Real := 1 - x ^ 2
  let u₁ (x : Real) : Real := f x ^ (n + 1)
  let u₁' (x : Real) : Real := - (2 * (n + 1) * x * f x ^ n)
  let v₁ (x : Real) : Real := sin (x * θ)
  let v₁' (x : Real) : Real := cos (x * θ) * θ
  let u₂ (x : Real) : Real := x * (f x) ^ n
  let u₂' (

中文:
引理 recursion'
  条件: (n : 自然数)
  证明: by
  rw [I]
  let f (x : Real) : Real := 1 - x ^ 2
  let u₁ (x : Real) : Real := f x ^ (n + 1)
  let u₁' (x : Real) : Real := - (2 * (n + 1) * x * f x ^ n)
  let v₁ (x : Real) : Real := sin (x * θ)
  let v₁' (x : Real) : Real := cos (x * θ) * θ
  let u₂ (x : Real) : Real := x * (f x) ^ n
  let u₂' (
-/
private lemma recursion' (n : Nat) :
    I (n + 1) θ * θ ^ 2 = - (2 * 2 * ((n + 1) * (0 ^ n * cos θ))) +
      2 * (n + 1) * (2 * n + 1) * I n θ - 4 * (n + 1) * n * I (n - 1) θ := by
  rw [I]
  let f (x : Real) : Real := 1 - x ^ 2
  let u₁ (x : Real) : Real := f x ^ (n + 1)
  let u₁' (x : Real) : Real := - (2 * (n + 1) * x * f x ^ n)
  let v₁ (x : Real) : Real := sin (x * θ)
  let v₁' (x : Real) : Real := cos (x * θ) * θ
  let u₂ (x : Real) : Real := x * (f x) ^ n
  let u₂' (x : Real) : Real := (f x) ^ n - 2 * n * x ^ 2 * (f x) ^ (n - 1)
  let v₂ (x : Real) : Real := cos (x * θ)
  let v₂' (x : Real) : Real := -sin (x * θ) * θ
  have hfd : Continuous f := by fun_prop
  have hu₁d : Continuous u₁' := by fun_prop
  have hv₁d : Continuous v₁' := by fun_prop
  have hu₂d : Continuous u₂' := by fun_prop
  have hv₂d : Continuous v₂' := by fun_prop
  have hu₁_eval_one : u₁ 1 = 0 := by simp only [u₁, f]; simp
  have hu₁_eval_neg_one : u₁ (-1) = 0 := by simp only [u₁, f]; simp
  have t : u₂ 1 * v₂ 1 - u₂ (-1) * v₂ (-1) = 2 * (0 ^ n * cos θ) := by simp [u₂, v₂, f, ← two_mul]
  have hf (x) : HasDerivAt f (- 2 * x) x := by
    convert! (hasDerivAt_pow 2 x).const_sub 1 using 1
    simp
  have hu₁ (x) : HasDerivAt u₁ (u₁' x) x := by
    convert! (hf x).pow _ using 1
    simp only [Nat.add_succ_sub_one, u₁', Nat.cast_add_one]
    ring
  have hv₁ (x) : HasDerivAt v₁ (v₁' x) x := (hasDerivAt_mul_const θ).sin
  have hu₂ (x) : HasDerivAt u₂ (u₂' x) x := by
    convert! (hasDerivAt_id' x).fun_mul ((hf x).fun_pow _) using 1
    simp only [u₂']
    ring
  have hv₂ (x) : HasDerivAt v₂ (v₂' x) x := (hasDerivAt_mul_const θ).cos
  convert_to (∫ (x : Real) in (-1)..1, u₁ x * v₁' x) * θ = _ using 1
  · simp_rw [u₁, v₁', f, ← intervalIntegral.integral_mul_const, sq θ, mul_assoc]
  rw [integral_mul_deriv_eq_deriv_mul (fun x _ => hu₁ x) (fun x _ => hv₁ x)
    (hu₁d.intervalIntegrable _ _) (hv₁d.intervalIntegrable _ _)]; rw [hu₁_eval_one]; rw [hu₁_eval_neg_one]; rw [zero_mul]; rw [zero_mul]; rw [sub_zero]; rw [zero_sub]; rw [← integral_neg]; rw [← integral_mul_const]
  convert_to ((-2 : Real) * (n + 1)) * ∫ (x : Real) in (-1)..1, (u₂ x * v₂' x) = _ using 1
  · rw [← integral_const_mul]
    congr 1 with x
    dsimp [u₁', v₁, u₂, v₂']
    ring
  rw [integral_mul_deriv_eq_deriv_mul (fun x _ => hu₂ x) (fun x _ => hv₂ x)
    (hu₂d.intervalIntegrable _ _) (hv₂d.intervalIntegrable _ _)]; rw [mul_sub]; rw [t]; rw [neg_mul]; rw [neg_mul]; rw [neg_mul]; rw [sub_neg_eq_add]
  have (x : _) : u₂' x = (2 * n + 1) * f x ^ n - 2 * n * f x ^ (n - 1) := by
    cases n with
    | zero => simp [u₂']
    | succ n => ring!
  simp_rw [this, sub_mul, mul_assoc _ _ (v₂ _)]
  have : Continuous v₂ := by fun_prop
  rw [mul_mul_mul_comm]; rw [integral_sub]; rw [mul_sub]; rw [add_sub_assoc]
  · congr 1
    simp_rw [integral_const_mul]
    ring!
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

/--
lemma `recursion` / 引理 `recursion`

English:
lemma recursion
  given: (n : Nat)
  proof: by
  rw [recursion' (n + 1)]
  push_cast
  ring

中文:
引理 recursion
  条件: (n : 自然数)
  证明: by
  rw [recursion' (n + 1)]
  push_cast
  ring
-/
private lemma recursion (n : Nat) :
    I (n + 2) θ * θ ^ 2 =
      2 * (n + 2) * (2 * n + 3) * I (n + 1) θ - 4 * (n + 2) * (n + 1) * I n θ := by
  rw [recursion' (n + 1)]
  push_cast
  ring

/--
lemma `I_one` / 引理 `I_one`

English:
lemma I_one
  statement: I 1 θ * θ ^ 3 = 4 * sin θ - 4 * θ * cos θ
  proof: by
  rw [_root_.pow_succ]; rw [← mul_assoc]; rw [recursion' 0]; rw [sub_mul]; rw [add_mul]; rw [mul_assoc _ (I 0 θ)]; rw [I_zero]
  ring

中文:
引理 I_one
  结论: I 1 θ * θ ^ 3 = 4 * sin θ - 4 * θ * cos θ
  证明: by
  rw [_root_.pow_succ]; rw [← mul_assoc]; rw [recursion' 0]; rw [sub_mul]; rw [add_mul]; rw [mul_assoc _ (I 0 θ)]; rw [I_zero]
  ring
-/
private lemma I_one : I 1 θ * θ ^ 3 = 4 * sin θ - 4 * θ * cos θ := by
  rw [_root_.pow_succ]; rw [← mul_assoc]; rw [recursion' 0]; rw [sub_mul]; rw [add_mul]; rw [mul_assoc _ (I 0 θ)]; rw [I_zero]
  ring

/--
Definition of `sinPoly` / `sinPoly` 的定义

English:
definition sinPoly
  signature: : Nat -> Int[X]

中文:
定义 sinPoly
  签名: : 自然数 -> 整数[X]
-/
private def sinPoly : Nat -> Int[X]
  | 0 => C 2
  | 1 => C 4
  | n + 2 => ((2 : Int) * (2 * n + 3)) • sinPoly (n + 1) + monomial 2 (-4) * sinPoly n

/--
Definition of `cosPoly` / `cosPoly` 的定义

English:
definition cosPoly
  signature: : Nat -> Int[X]

中文:
定义 cosPoly
  签名: : 自然数 -> 整数[X]
-/
private def cosPoly : Nat -> Int[X]
  | 0 => 0
  | 1 => monomial 1 (-4)
  | n + 2 => ((2 : Int) * (2 * n + 3)) • cosPoly (n + 1) + monomial 2 (-4) * cosPoly n

/--
lemma `sinPoly_natDegree_le` / 引理 `sinPoly_natDegree_le`

English:
lemma sinPoly_natDegree_le
  statement: forall n : Nat, (sinPoly n).natDegree <= n

中文:
引理 sinPoly_natDegree_le
  结论: 对任意 n : 自然数, (sinPoly n).natDegree <= n
-/
private lemma sinPoly_natDegree_le : forall n : Nat, (sinPoly n).natDegree <= n
  | 0
  | 1 => by simp [sinPoly]
  | n + 2 => by
    rw [sinPoly]
    refine natDegree_add_le_of_degree_le ((natDegree_smul_le _ _).trans ?_) ?_
    · exact (sinPoly_natDegree_le (n + 1)).trans (by simp)
    refine natDegree_mul_le.trans ?_
    simpa [add_comm 2] using sinPoly_natDegree_le n

/--
lemma `cosPoly_natDegree_le` / 引理 `cosPoly_natDegree_le`

English:
lemma cosPoly_natDegree_le
  statement: forall n : Nat, (cosPoly n).natDegree <= n

中文:
引理 cosPoly_natDegree_le
  结论: 对任意 n : 自然数, (cosPoly n).natDegree <= n

Depends on / 依赖: infer_instance
-/
private lemma cosPoly_natDegree_le : forall n : Nat, (cosPoly n).natDegree <= n
  | 0 => by simp [cosPoly]
  | 1 => (natDegree_monomial_le _).trans (by simp)
  | n + 2 => by
      rw [cosPoly]
      refine natDegree_add_le_of_degree_le ((natDegree_smul_le _ _).trans ?_) ?_
      · exact (cosPoly_natDegree_le (n + 1)).trans (by simp)
      exact natDegree_mul_le.trans (by simp [add_comm 2, cosPoly_natDegree_le n])

/--
lemma `sinPoly_add_cosPoly_eval` / 引理 `sinPoly_add_cosPoly_eval`

English:
lemma sinPoly_add_cosPoly_eval
  given: (θ : Real)
  proof: by ring
        _ = 2 * (n + 2) * (2 * n + 3) * (I (n + 1) θ * θ ^ (2 * (n + 1) + 1)) -
            4 * (n + 2) * (n + 1) * θ ^ 2 * (I n θ * θ ^ (2 * n + 1)) := by rw [recursion]; ring
        _ = _ := by simp [sinPoly_add_cosPoly_eval, sinPoly, cosPoly, Nat.factorial_succ]; ring

中文:
引理 sinPoly_add_cosPoly_eval
  条件: (θ : 实数)
  证明: by ring
        _ = 2 * (n + 2) * (2 * n + 3) * (I (n + 1) θ * θ ^ (2 * (n + 1) + 1)) -
            4 * (n + 2) * (n + 1) * θ ^ 2 * (I n θ * θ ^ (2 * n + 1)) := by rw [recursion]; ring
        _ = _ := by simp [sinPoly_add_cosPoly_eval, sinPoly, cosPoly, Nat.factorial_succ]; ring
-/
private lemma sinPoly_add_cosPoly_eval (θ : Real) :
    forall n : Nat,
      I n θ * θ ^ (2 * n + 1) = n ! * ((sinPoly n).eval₂ (Int.castRingHom _) θ * sin θ +
        (cosPoly n).eval₂ (Int.castRingHom _) θ * cos θ)
  | 0 => by simp [sinPoly, cosPoly, I_zero]
  | 1 => by simp [I_one, sinPoly, cosPoly, sub_eq_add_neg]
  | n + 2 => by
      calc I (n + 2) θ * θ ^ (2 * (n + 2) + 1) = I (n + 2) θ * θ ^ 2 * θ ^ (2 * n + 3) := by ring
        _ = 2 * (n + 2) * (2 * n + 3) * (I (n + 1) θ * θ ^ (2 * (n + 1) + 1)) -
            4 * (n + 2) * (n + 1) * θ ^ 2 * (I n θ * θ ^ (2 * n + 1)) := by rw [recursion]; ring
        _ = _ := by simp [sinPoly_add_cosPoly_eval, sinPoly, cosPoly, Nat.factorial_succ]; ring

/--
lemma `is_integer` / 引理 `is_integer`

English:
lemma is_integer
  given: {p : Int[X]} (a b : Int) {k : Nat} (hp : p.natDegree <= k)
  proof: by
  rcases eq_or_ne b 0 with rfl | hb
  · rcases k.eq_zero_or_pos with rfl | hk
    · exact ⟨p.coeff 0, by simp⟩
    exact ⟨0, by simp [hk.ne']⟩
  refine ⟨∑ i in p.support, p.coeff i * a ^ i * b ^ (k - i), ?_⟩
  conv => lhs; rw [← sum_monomial_eq p]
  rw [eval₂_sum]; rw [sum]; rw [Finset.sum_mul]; 

中文:
引理 is_integer
  条件: {p : 整数[X]} (a b : 整数) {k : 自然数} (hp : p.natDegree <= k)
  证明: by
  rcases eq_or_ne b 0 with rfl | hb
  · rcases k.eq_zero_or_pos with rfl | hk
    · exact ⟨p.coeff 0, by simp⟩
    exact ⟨0, by simp [hk.ne']⟩
  refine ⟨∑ i in p.support, p.coeff i * a ^ i * b ^ (k - i), ?_⟩
  conv => lhs; rw [← sum_monomial_eq p]
  rw [eval₂_sum]; rw [sum]; rw [Finset.sum_mul]; 
-/
private lemma is_integer {p : Int[X]} (a b : Int) {k : Nat} (hp : p.natDegree <= k) :
    exists z : Int, p.eval₂ (Int.castRingHom Real) (a / b) * b ^ k = z := by
  rcases eq_or_ne b 0 with rfl | hb
  · rcases k.eq_zero_or_pos with rfl | hk
    · exact ⟨p.coeff 0, by simp⟩
    exact ⟨0, by simp [hk.ne']⟩
  refine ⟨∑ i in p.support, p.coeff i * a ^ i * b ^ (k - i), ?_⟩
  conv => lhs; rw [← sum_monomial_eq p]
  rw [eval₂_sum]; rw [sum]; rw [Finset.sum_mul]; rw [Int.cast_sum]
  simp only [eval₂_monomial, eq_intCast, div_pow, Int.cast_mul, Int.cast_pow]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have ik := (le_natDegree_of_mem_supp i hi).trans hp
  rw [mul_assoc]; rw [div_mul_comm]; rw [← Int.cast_pow]; rw [← Int.cast_pow]; rw [← Int.cast_pow]; rw [← pow_sub_mul_pow b ik]; rw [← Int.cast_div_charZero]; rw [Int.mul_ediv_cancel _ (pow_ne_zero _ hb)]; rw [← mul_assoc]; rw [mul_right_comm]; rw [← Int.cast_pow]
  exact dvd_mul_left _ _

open Filter

/--
lemma `I_pos` / 引理 `I_pos`

English:
lemma I_pos
  statement: 0 < I n (π / 2)
  proof: by
  refine integral_pos (by simp) (by fun_prop) ?_ ⟨0, by simp⟩
  refine fun x hx => mul_nonneg (pow_nonneg ?_ _) ?_
  · rw [sub_nonneg, sq_le_one_iff_abs_le_one, abs_le]
    exact ⟨hx.1.le, hx.2⟩
  refine cos_nonneg_of_neg_pi_div_two_le_of_le ?_ ?_ <;>
  nlinarith [hx.1, hx.2, pi_pos]

中文:
引理 I_pos
  结论: 0 < I n (π / 2)
  证明: by
  refine integral_pos (by simp) (by fun_prop) ?_ ⟨0, by simp⟩
  refine fun x hx => mul_nonneg (pow_nonneg ?_ _) ?_
  · rw [sub_nonneg, sq_le_one_iff_abs_le_one, abs_le]
    exact ⟨hx.1.le, hx.2⟩
  refine cos_nonneg_of_neg_pi_div_two_le_of_le ?_ ?_ <;>
  nlinarith [hx.1, hx.2, pi_pos]
-/
private lemma I_pos : 0 < I n (π / 2) := by
  refine integral_pos (by simp) (by fun_prop) ?_ ⟨0, by simp⟩
  refine fun x hx => mul_nonneg (pow_nonneg ?_ _) ?_
  · rw [sub_nonneg, sq_le_one_iff_abs_le_one, abs_le]
    exact ⟨hx.1.le, hx.2⟩
  refine cos_nonneg_of_neg_pi_div_two_le_of_le ?_ ?_ <;>
  nlinarith [hx.1, hx.2, pi_pos]

/--
lemma `I_le` / 引理 `I_le`

English:
lemma I_le
  given: (n : Nat)
  statement: I n (π / 2) <= 2
  proof: by
  rw [← norm_of_nonneg I_pos.le]
  refine (norm_integral_le_of_norm_le_const ?_).trans (show (1 : Real) * _ <= _ by norm_num)
  intro x hx
  simp only [uIoc_of_le, neg_le_self_iff, zero_le_one, mem_Ioc] at hx
  rw [norm_eq_abs]; rw [abs_mul]; rw [abs_pow]
  refine mul_le_one₀ (pow_le_one₀ (abs_no

中文:
引理 I_le
  条件: (n : 自然数)
  结论: I n (π / 2) <= 2
  证明: by
  rw [← norm_of_nonneg I_pos.le]
  refine (norm_integral_le_of_norm_le_const ?_).trans (show (1 : Real) * _ <= _ by norm_num)
  intro x hx
  simp only [uIoc_of_le, neg_le_self_iff, zero_le_one, mem_Ioc] at hx
  rw [norm_eq_abs]; rw [abs_mul]; rw [abs_pow]
  refine mul_le_one₀ (pow_le_one₀ (abs_no
-/
private lemma I_le (n : Nat) : I n (π / 2) <= 2 := by
  rw [← norm_of_nonneg I_pos.le]
  refine (norm_integral_le_of_norm_le_const ?_).trans (show (1 : Real) * _ <= _ by norm_num)
  intro x hx
  simp only [uIoc_of_le, neg_le_self_iff, zero_le_one, mem_Ioc] at hx
  rw [norm_eq_abs]; rw [abs_mul]; rw [abs_pow]
  refine mul_le_one₀ (pow_le_one₀ (abs_nonneg _) ?_) (abs_nonneg _) (abs_cos_le_one _)
  rw [abs_le]
  constructor <;> nlinarith

/--
lemma `tendsto_pow_div_factorial_at_top_aux` / 引理 `tendsto_pow_div_factorial_at_top_aux`

English:
lemma tendsto_pow_div_factorial_at_top_aux
  given: (a : Real)
  proof: by
  rw [← mul_zero a]
  refine ((FloorSemiring.tendsto_pow_div_factorial_atTop (a ^ 2)).const_mul a).congr (fun x => ?_)
  rw [← pow_mul]; rw [mul_div_assoc']; rw [_root_.pow_succ']

中文:
引理 tendsto_pow_div_factorial_at_top_aux
  条件: (a : 实数)
  证明: by
  rw [← mul_zero a]
  refine ((FloorSemiring.tendsto_pow_div_factorial_atTop (a ^ 2)).const_mul a).congr (fun x => ?_)
  rw [← pow_mul]; rw [mul_div_assoc']; rw [_root_.pow_succ']
-/
private lemma tendsto_pow_div_factorial_at_top_aux (a : Real) :
    Tendsto (fun n => (a : Real) ^ (2 * n + 1) / n !) atTop (nhds 0) := by
  rw [← mul_zero a]
  refine ((FloorSemiring.tendsto_pow_div_factorial_atTop (a ^ 2)).const_mul a).congr (fun x => ?_)
  rw [← pow_mul]; rw [mul_div_assoc']; rw [_root_.pow_succ']

/--
lemma `not_irrational_exists_rep` / 引理 `not_irrational_exists_rep`

English:
lemma not_irrational_exists_rep
  given: {x : Real}
  proof: by
  rw [Irrational]; rw [not_not]; rw [mem_range]
  rintro ⟨q, rfl⟩
  exact ⟨q.num, q.den, q.pos, by exact_mod_cast (Rat.num_div_den _).symm⟩

中文:
引理 not_irrational_存在_rep
  条件: {x : 实数}
  证明: by
  rw [Irrational]; rw [not_not]; rw [mem_range]
  rintro ⟨q, rfl⟩
  exact ⟨q.num, q.den, q.pos, by exact_mod_cast (Rat.num_div_den _).symm⟩
-/
private lemma not_irrational_exists_rep {x : Real} :
    ¬Irrational x -> exists (a : Int) (b : Nat), 0 < b ∧ x = a / b := by
  rw [Irrational]; rw [not_not]; rw [mem_range]
  rintro ⟨q, rfl⟩
  exact ⟨q.num, q.den, q.pos, by exact_mod_cast (Rat.num_div_den _).symm⟩

/--
theorem `irrational_pi` / 定理 `irrational_pi`

English:
theorem irrational_pi
  statement: Irrational π
  proof: by
  apply Irrational.of_div_natCast 2
  rw [Nat.cast_two]
  by_contra h'
  obtain ⟨a, b, hb, h⟩ := not_irrational_exists_rep h'
  have ha : (0 : Real) < a := by
    have : 0 < (a : Real) / b := h ▸ pi_div_two_pos
    rwa [lt_div_iff₀ (by positivity), zero_mul] at this
  have k (n : Nat) : 0 < (a : 

中文:
定理 irrational_pi
  结论: Irrational π
  证明: by
  apply Irrational.of_div_natCast 2
  rw [Nat.cast_two]
  by_contra h'
  obtain ⟨a, b, hb, h⟩ := not_irrational_exists_rep h'
  have ha : (0 : Real) < a := by
    have : 0 < (a : Real) / b := h ▸ pi_div_two_pos
    rwa [lt_div_iff₀ (by positivity), zero_mul] at this
  have k (n : Nat) : 0 < (a : 
-/
@[simp] theorem irrational_pi : Irrational π := by
  apply Irrational.of_div_natCast 2
  rw [Nat.cast_two]
  by_contra h'
  obtain ⟨a, b, hb, h⟩ := not_irrational_exists_rep h'
  have ha : (0 : Real) < a := by
    have : 0 < (a : Real) / b := h ▸ pi_div_two_pos
    rwa [lt_div_iff₀ (by positivity), zero_mul] at this
  have k (n : Nat) : 0 < (a : Real) ^ (2 * n + 1) / n ! := by positivity
  have j : forallᶠ n : Nat in atTop, (a : Real) ^ (2 * n + 1) / n ! * I n (π / 2) < 1 := by
    have := (tendsto_pow_div_factorial_at_top_aux a).eventually_lt_const
      (show (0 : Real) < 1 / 2 by simp)
    filter_upwards [this] with n hn
    rw [lt_div_iff₀ (zero_lt_two : (0 : Real) < 2)] at hn
    exact hn.trans_le' (mul_le_mul_of_nonneg_left (I_le _) (by positivity))
  obtain ⟨n, hn⟩ := j.exists
  have hn' : 0 < a ^ (2 * n + 1) / n ! * I n (π / 2) := mul_pos (k _) I_pos
  obtain ⟨z, hz⟩ : exists z : Int, (sinPoly n).eval₂ (Int.castRingHom Real) (a / b) * b ^ (2 * n + 1) = z :=
    is_integer a b ((sinPoly_natDegree_le _).trans (by lia))
  have e := sinPoly_add_cosPoly_eval (π / 2) n
  rw [cos_pi_div_two]; rw [sin_pi_div_two]; rw [mul_zero]; rw [mul_one]; rw [add_zero] at e
  have : a ^ (2 * n + 1) / n ! * I n (π / 2) =
      eval₂ (Int.castRingHom Real) (π / 2) (sinPoly n) * b ^ (2 * n + 1) := by
    nth_rw 2 [h] at e
    simp [field, div_pow] at e ⊢
    linear_combination e
  have : (0 : Real) < z ∧ (z : Real) < 1 := by simp [← hz, ← h, ← this, hn', hn]
  norm_cast at this
  lia

end
