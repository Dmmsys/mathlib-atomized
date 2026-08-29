/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.FieldTheory.KummerExtension

/-!
# More results on primitive roots of unity

(We put these in a separate file because of the `KummerExtension` import.)

Assume that `μ` is a primitive `n`th root of unity in an integral domain `R`. Then
$$ \prod_{k=1}^{n-1} (1 - \mu^k) = n \,; $$
see `IsPrimitiveRoot.prod_one_sub_pow_eq_order` and its variant
`IsPrimitiveRoot.prod_pow_sub_one_eq_order` in terms of `∏ (μ^k - 1)`.

We use this to deduce that `n` is divisible by `(μ - 1)^k` in `ℤ[μ] ⊆ R` when `k < n`.
-/

public section

variable {R : Type*} [CommRing R] [IsDomain R]

namespace IsPrimitiveRoot

open Finset Polynomial

/--
lemma `prod_one_sub_pow_eq_order` / 引理 `prod_one_sub_pow_eq_order`

English:
lemma prod_one_sub_pow_eq_order
  given: {n : Nat} {μ : R} (hμ : IsPrimitiveRoot μ (n + 1))
  proof: by
  have := X_pow_sub_C_eq_prod hμ n.zero_lt_succ (one_pow (n + 1))
  rw [C_1]; rw [← mul_geom_sum]; rw [prod_range_succ']; rw [pow_zero]; rw [mul_one]; rw [mul_comm]; rw [eq_comm] at this
  replace this := mul_right_cancel₀ (Polynomial.X_sub_C_ne_zero 1) this
  apply_fun Polynomial.eval 1 at this


中文:
引理 prod_one_sub_pow_eq_order
  条件: {n : 自然数} {μ : R} (hμ : 是PrimitiveRoot μ (n + 1))
  证明: by
  have := X_pow_sub_C_eq_prod hμ n.zero_lt_succ (one_pow (n + 1))
  rw [C_1]; rw [← mul_geom_sum]; rw [prod_range_succ']; rw [pow_zero]; rw [mul_one]; rw [mul_comm]; rw [eq_comm] at this
  replace this := mul_right_cancel₀ (Polynomial.X_sub_C_ne_zero 1) this
  apply_fun Polynomial.eval 1 at this


Depends on / 依赖: Nat.cast_add, Nat.cast_one, Polynomial, Polynomial.X_sub_C_ne_zero, Polynomial.eval, X_pow_sub_C_eq_prod, X_sub_C_ne_zero, apply_fun, card_range, cast_add, cast_one, eq_comm, eval_C, eval_X, eval_geom_sum, eval_pow, eval_prod, eval_sub, map_pow, mul_comm
-/
lemma prod_one_sub_pow_eq_order {n : Nat} {μ : R} (hμ : IsPrimitiveRoot μ (n + 1)) :
    ∏ k in range n, (1 - μ ^ (k + 1)) = n + 1 := by
  have := X_pow_sub_C_eq_prod hμ n.zero_lt_succ (one_pow (n + 1))
  rw [C_1]; rw [← mul_geom_sum]; rw [prod_range_succ']; rw [pow_zero]; rw [mul_one]; rw [mul_comm]; rw [eq_comm] at this
  replace this := mul_right_cancel₀ (Polynomial.X_sub_C_ne_zero 1) this
  apply_fun Polynomial.eval 1 at this
  simpa only [mul_one, map_pow, eval_prod, eval_sub, eval_X, eval_pow, eval_C, eval_geom_sum,
    one_pow, sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using this

/--
lemma `prod_pow_sub_one_eq_order` / 引理 `prod_pow_sub_one_eq_order`

English:
lemma prod_pow_sub_one_eq_order
  given: {n : Nat} {μ : R} (hμ : IsPrimitiveRoot μ (n + 1))
  proof: by
  have : (-1 : R) ^ n = ∏ k in range n, -1 := by rw [prod_const, card_range]
  simp only [this, ← prod_mul_distrib, neg_one_mul, neg_sub, ← prod_one_sub_pow_eq_order hμ]

中文:
引理 prod_pow_sub_one_eq_order
  条件: {n : 自然数} {μ : R} (hμ : 是PrimitiveRoot μ (n + 1))
  证明: by
  have : (-1 : R) ^ n = ∏ k in range n, -1 := by rw [prod_const, card_range]
  simp only [this, ← prod_mul_distrib, neg_one_mul, neg_sub, ← prod_one_sub_pow_eq_order hμ]

Depends on / 依赖: card_range, neg_one_mul, neg_sub, prod_const, prod_mul_distrib, prod_one_sub_pow_eq_order
-/
lemma prod_pow_sub_one_eq_order {n : Nat} {μ : R} (hμ : IsPrimitiveRoot μ (n + 1)) :
    (-1) ^ n * ∏ k in range n, (μ ^ (k + 1) - 1) = n + 1 := by
  have : (-1 : R) ^ n = ∏ k in range n, -1 := by rw [prod_const, card_range]
  simp only [this, ← prod_mul_distrib, neg_one_mul, neg_sub, ← prod_one_sub_pow_eq_order hμ]

open Algebra in
/--
lemma `self_sub_one_pow_dvd_order` / 引理 `self_sub_one_pow_dvd_order`

English:
lemma self_sub_one_pow_dvd_order
  given: {k n : Nat} (hn : k < n) {μ : R} (hμ : IsPrimitiveRoot μ n)
  proof: by
  let n' + 1 := n
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.le_of_lt_succ hn)
  have hdvd k : exists z in Int[μ], μ ^ k - 1 = z * (μ - 1) := by
    refine ⟨(Finset.range k).sum (μ ^ ·), ?_, (geom_sum_mul μ k).symm⟩
    exact Subalgebra.sum_mem _ fun m _ => Subalgebra.pow_mem _ (self_mem_

中文:
引理 self_sub_one_pow_dvd_order
  条件: {k n : 自然数} (hn : k < n) {μ : R} (hμ : 是PrimitiveRoot μ n)
  证明: by
  let n' + 1 := n
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.le_of_lt_succ hn)
  have hdvd k : exists z in Int[μ], μ ^ k - 1 = z * (μ - 1) := by
    refine ⟨(Finset.range k).sum (μ ^ ·), ?_, (geom_sum_mul μ k).symm⟩
    exact Subalgebra.sum_mem _ fun m _ => Subalgebra.pow_mem _ (self_mem_

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, Finset, Finset.range, Nat.exists_eq_add_of_le, Nat.le_of_lt_succ, Subalgebra, Subalgebra.pow_mem, Subalgebra.sum_mem, choose_spec, exists_eq_add_of_le, geom_sum_mul, le_of_lt_succ, pow_mem, self_mem_adjoin_singleton, sum_mem
-/
lemma self_sub_one_pow_dvd_order {k n : Nat} (hn : k < n) {μ : R} (hμ : IsPrimitiveRoot μ n) :
    exists z in Int[μ], n = z * (μ - 1) ^ k := by
  let n' + 1 := n
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.le_of_lt_succ hn)
  have hdvd k : exists z in Int[μ], μ ^ k - 1 = z * (μ - 1) := by
    refine ⟨(Finset.range k).sum (μ ^ ·), ?_, (geom_sum_mul μ k).symm⟩
    exact Subalgebra.sum_mem _ fun m _ => Subalgebra.pow_mem _ (self_mem_adjoin_singleton _ μ) _
let Z k := Classical.choose hdvd k
  have Zdef k : Z k in Int[μ] ∧ μ ^ k - 1 = Z k * (μ - 1) :=
Classical.choose_spec hdvd k
  refine ⟨(-1) ^ (m + k) * (∏ j in range k, Z (j + 1)) * ∏ j in Ico k (m + k), (μ ^ (j + 1) - 1),
    ?_, ?_⟩
  · apply Subalgebra.mul_mem
    · apply Subalgebra.mul_mem
      · exact Subalgebra.pow_mem _ (Subalgebra.neg_mem _ <| Subalgebra.one_mem _) _
      · exact Subalgebra.prod_mem _ fun _ _ => (Zdef _).1
    · refine Subalgebra.prod_mem _ fun _ _ => ?_
      apply Subalgebra.sub_mem
      · exact Subalgebra.pow_mem _ (self_mem_adjoin_singleton Int μ) _
      · exact Subalgebra.one_mem _
  · push_cast
    have := Nat.cast_add (R := R) m k ▸ hμ.prod_pow_sub_one_eq_order
    rw [← this]; rw [mul_assoc]; rw [mul_assoc]
    congr 1
    conv => enter [2, 2, 2]; rw [← card_range k]
    rw [← prod_range_mul_prod_Ico _ (Nat.le_add_left k m)]; rw [mul_comm _ (_ ^ #_)]; rw [← mul_assoc]; rw [prod_mul_pow_card]
    conv => enter [2, 1, 2, j]; rw [← (Zdef _).2]

end IsPrimitiveRoot
