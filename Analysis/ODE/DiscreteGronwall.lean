/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Discrete Grönwall inequality

Various forms of the discrete Grönwall inequality, bounding solutions to recurrence
inequalities `u (n+1) ≤ c n * u n + b n` and `u (n+1) ≤ (1 + c n) * u n + b n`.

## Main results

* `discrete_gronwall_prod_general`: product form, over any ordered commutative semiring.
* `discrete_gronwall`: classical exponential bound for the `(1 + c)` form, over `ℝ`.
* `discrete_gronwall_Ico`: uniform bound over an interval, over `ℝ`.

## References

* [T. H. Grönwall, *Note on the derivatives with respect to a parameter of the solutions of a
  system of differential equations*][Gronwall_1919]

## See also

* `Mathlib.Analysis.ODE.Gronwall` for the continuous Grönwall inequality for ODEs.
-/

@[expose] public section

open Real Finset

section General

/-! ### Generalized product form -/

variable {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {u b c : Nat -> R}

/--
theorem `discrete_gronwall_prod_general` / 定理 `discrete_gronwall_prod_general`

English:
theorem discrete_gronwall_prod_general
  statement: {n₀ : Nat} (hu : forall n >= n₀, u (n + 1) <= c n * u n + b n)
  proof: by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hck : 0 <= c k := hc k hk
    have heq : c k * ∑ j in Ico n₀ k, b j * ∏ i in Ico (j + 1) k, c i + b k =
        ∑ j in Ico n₀ (k + 1), b j * ∏ i in Ico (j + 1) (k + 1), c i := by
      rw [sum_Ico_succ_top hk]; rw [mul_sum]; rw [Ico_self]; rw [prod_empty]; rw [mul_one]
      refine congr_arg (· + b k) (sum_congr rfl fun j hj => ?_)
      rw [prod_Ico_succ_top (by have := mem_Ico.mp hj; omega)]; ring
    calc u (k + 1)
      _ <= c k * u k + b k := hu k hk
      _ <= c k * (u n₀ * ∏ i in Ico n₀ k, c i +
            ∑ j in Ico n₀ k, b j * ∏ i in Ico (j + 1) k, c i) + b k := by gcongr
      _ = u n₀ * ∏ i in Ico n₀ (k + 1), c i +
            ∑ j in Ico n₀ (k + 1), b j * ∏ i in Ico (j + 1) (k + 1), c i := by
          rw [← heq]; rw [← prod_Ico_mul_eq_prod_Ico_add_one hk]; ring

中文:
定理 discrete_gronwall_prod_general
  结论: {n₀ : 自然数} (hu : 对任意 n >= n₀, u (n + 1) <= c n * u n + b n)
  证明: by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hck : 0 <= c k := hc k hk
    have heq : c k * ∑ j in Ico n₀ k, b j * ∏ i in Ico (j + 1) k, c i + b k =
        ∑ j in Ico n₀ (k + 1), b j * ∏ i in Ico (j + 1) (k + 1), c i := by
      rw [sum_Ico_succ_top hk]; rw [mul_sum]; rw [Ico_self]; rw [prod_empty]; rw [mul_one]
      refine congr_arg (· + b k) (sum_congr rfl fun j hj => ?_)
      rw [prod_Ico_succ_top (by have := mem_Ico.mp hj; omega)]; ring
    calc u (k + 1)
      _ <= c k * u k + b k := hu k hk
      _ <= c k * (u n₀ * ∏ i in Ico n₀ k, c i +
            ∑ j in Ico n₀ k, b j * ∏ i in Ico (j + 1) k, c i) + b k := by gcongr
      _ = u n₀ * ∏ i in Ico n₀ (k + 1), c i +
            ∑ j in Ico n₀ (k + 1), b j * ∏ i in Ico (j + 1) (k + 1), c i := by
          rw [← heq]; rw [← prod_Ico_mul_eq_prod_Ico_add_one hk]; ring

Depends on / 依赖: Ico_self, Nat.le_induction, congr_arg, le_induction, mem_Ico, mem_Ico.mp, mul_one, mul_sum, prod_Ico_succ_top, prod_empty, sum_Ico_succ_top, sum_congr
-/
theorem discrete_gronwall_prod_general {n₀ : Nat} (hu : forall n >= n₀, u (n + 1) <= c n * u n + b n)
    (hc : forall n >= n₀, 0 <= c n) ⦃n : Nat⦄ (hn : n₀ <= n) :
    u n <= u n₀ * ∏ i in Ico n₀ n, c i +
      ∑ k in Ico n₀ n, b k * ∏ i in Ico (k + 1) n, c i := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hck : 0 <= c k := hc k hk
    have heq : c k * ∑ j in Ico n₀ k, b j * ∏ i in Ico (j + 1) k, c i + b k =
        ∑ j in Ico n₀ (k + 1), b j * ∏ i in Ico (j + 1) (k + 1), c i := by
      rw [sum_Ico_succ_top hk]; rw [mul_sum]; rw [Ico_self]; rw [prod_empty]; rw [mul_one]
      refine congr_arg (· + b k) (sum_congr rfl fun j hj => ?_)
      rw [prod_Ico_succ_top (by have := mem_Ico.mp hj; omega)]; ring
    calc u (k + 1)
      _ <= c k * u k + b k := hu k hk
      _ <= c k * (u n₀ * ∏ i in Ico n₀ k, c i +
            ∑ j in Ico n₀ k, b j * ∏ i in Ico (j + 1) k, c i) + b k := by gcongr
      _ = u n₀ * ∏ i in Ico n₀ (k + 1), c i +
            ∑ j in Ico n₀ (k + 1), b j * ∏ i in Ico (j + 1) (k + 1), c i := by
          rw [← heq]; rw [← prod_Ico_mul_eq_prod_Ico_add_one hk]; ring

end General

/-! ### Real-valued exponential form -/

variable {u b c : Nat -> Real}

/--
theorem `discrete_gronwall` / 定理 `discrete_gronwall`

English:
theorem discrete_gronwall
  statement: {n₀ : Nat} (hun₀ : 0 <= u n₀)
  proof: by
  calc u n
    _ <= u n₀ * ∏ i in Ico n₀ n, (1 + c i) +
          ∑ k in Ico n₀ n, b k * ∏ i in Ico (k + 1) n, (1 + c i) :=
        discrete_gronwall_prod_general hu (by grind) hn
    _ <= u n₀ * ∏ i in Ico n₀ n, (1 + c i) +
          ∑ k in Ico n₀ n, b k * ∏ i in Ico n₀ n, (1 + c i) := by
        gcongr <;> grind
    _ = (u n₀ + ∑ k in Ico n₀ n, b k) * ∏ i in Ico n₀ n, (1 + c i) := by rw [add_mul, sum_mul]
    _ <= (u n₀ + ∑ k in Ico n₀ n, b k) * exp (∑ i in Ico n₀ n, c i) := by
gcongr <;> try exact add_nonneg hun₀ sum_nonneg by grind
        simpa [exp_sum] using prod_le_prod (by grind) (by grind [add_one_le_exp])

中文:
定理 discrete_gronwall
  结论: {n₀ : 自然数} (hun₀ : 0 <= u n₀)
  证明: by
  calc u n
    _ <= u n₀ * ∏ i in Ico n₀ n, (1 + c i) +
          ∑ k in Ico n₀ n, b k * ∏ i in Ico (k + 1) n, (1 + c i) :=
        discrete_gronwall_prod_general hu (by grind) hn
    _ <= u n₀ * ∏ i in Ico n₀ n, (1 + c i) +
          ∑ k in Ico n₀ n, b k * ∏ i in Ico n₀ n, (1 + c i) := by
        gcongr <;> grind
    _ = (u n₀ + ∑ k in Ico n₀ n, b k) * ∏ i in Ico n₀ n, (1 + c i) := by rw [add_mul, sum_mul]
    _ <= (u n₀ + ∑ k in Ico n₀ n, b k) * exp (∑ i in Ico n₀ n, c i) := by
gcongr <;> try exact add_nonneg hun₀ sum_nonneg by grind
        simpa [exp_sum] using prod_le_prod (by grind) (by grind [add_one_le_exp])

Depends on / 依赖: add_mul, add_nonneg, discrete_gronwall_prod_general, sum_mul, sum_nonneg
-/
theorem discrete_gronwall {n₀ : Nat} (hun₀ : 0 <= u n₀)
    (hu : forall n >= n₀, u (n + 1) <= (1 + c n) * u n + b n) (hc : forall n >= n₀, 0 <= c n)
    (hb : forall n >= n₀, 0 <= b n) ⦃n : Nat⦄ (hn : n₀ <= n) :
    u n <= (u n₀ + ∑ k in Ico n₀ n, b k) * exp (∑ i in Ico n₀ n, c i) := by
  calc u n
    _ <= u n₀ * ∏ i in Ico n₀ n, (1 + c i) +
          ∑ k in Ico n₀ n, b k * ∏ i in Ico (k + 1) n, (1 + c i) :=
        discrete_gronwall_prod_general hu (by grind) hn
    _ <= u n₀ * ∏ i in Ico n₀ n, (1 + c i) +
          ∑ k in Ico n₀ n, b k * ∏ i in Ico n₀ n, (1 + c i) := by
        gcongr <;> grind
    _ = (u n₀ + ∑ k in Ico n₀ n, b k) * ∏ i in Ico n₀ n, (1 + c i) := by rw [add_mul, sum_mul]
    _ <= (u n₀ + ∑ k in Ico n₀ n, b k) * exp (∑ i in Ico n₀ n, c i) := by
gcongr <;> try exact add_nonneg hun₀ sum_nonneg by grind
        simpa [exp_sum] using prod_le_prod (by grind) (by grind [add_one_le_exp])

/--
theorem `discrete_gronwall_Ico` / 定理 `discrete_gronwall_Ico`

English:
theorem discrete_gronwall_Ico
  statement: {n₀ n₁ : Nat} (hun₀ : 0 <= u n₀)
  proof: by
have : 0 <= ∑ k in Ico n₀ n₁, b k := sum_nonneg by grind
  exact (discrete_gronwall hun₀ hu hc hb (mem_Ico.mp hn).1).trans (by gcongr <;> grind)

中文:
定理 discrete_gronwall_Ico
  结论: {n₀ n₁ : 自然数} (hun₀ : 0 <= u n₀)
  证明: by
have : 0 <= ∑ k in Ico n₀ n₁, b k := sum_nonneg by grind
  exact (discrete_gronwall hun₀ hu hc hb (mem_Ico.mp hn).1).trans (by gcongr <;> grind)

Depends on / 依赖: discrete_gronwall, mem_Ico, mem_Ico.mp, sum_nonneg
-/
theorem discrete_gronwall_Ico {n₀ n₁ : Nat} (hun₀ : 0 <= u n₀)
    (hu : forall n >= n₀, u (n + 1) <= (1 + c n) * u n + b n)
    (hc : forall n >= n₀, 0 <= c n) (hb : forall n >= n₀, 0 <= b n) ⦃n : Nat⦄ (hn : n in Ico n₀ n₁) :
    u n <= (u n₀ + ∑ k in Ico n₀ n₁, b k) * exp (∑ i in Ico n₀ n₁, c i) := by
have : 0 <= ∑ k in Ico n₀ n₁, b k := sum_nonneg by grind
  exact (discrete_gronwall hun₀ hu hc hb (mem_Ico.mp hn).1).trans (by gcongr <;> grind)
