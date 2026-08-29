/-
Copyright (c) 2025 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.CharP.Frobenius

/-!
# Results on `MvPolynomial.expand`

In this file we prove results about `MvPolynomial.expand` that require more than the basic API
available in `Mathlib.Algebra.*`.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R] (p : Nat) [ExpChar R p]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `map_frobenius_expand` / 定理 `map_frobenius_expand`

English:
theorem map_frobenius_expand
  given: {f : MvPolynomial σ R}
  proof: f.induction_on' fun _ _ => by simp [monomial_pow, frobenius]
    fun _ _ ha hb => by rw [map_add, map_add, ha, hb, add_pow_expChar]

中文:
定理 map_frobenius_expand
  条件: {f : 多元多项式 σ R}
  证明: f.induction_on' fun _ _ => by simp [monomial_pow, frobenius]
    fun _ _ ha hb => by rw [map_add, map_add, ha, hb, add_pow_expChar]

Depends on / 依赖: add_pow_expChar, f.induction_on, frobenius, induction_on, map_add, monomial_pow
-/
theorem map_frobenius_expand {f : MvPolynomial σ R} :
    (f.expand p).map (frobenius R p) = f ^ p :=
  f.induction_on' fun _ _ => by simp [monomial_pow, frobenius]
    fun _ _ ha hb => by rw [map_add, map_add, ha, hb, add_pow_expChar]

/--
theorem `map_iterateFrobenius_expand` / 定理 `map_iterateFrobenius_expand`

English:
theorem map_iterateFrobenius_expand
  given: (f : MvPolynomial σ R) (n : Nat)
  proof: by
  induction n with
  | zero => simp [map_id]
  | succ k n_ih =>
    symm
    conv_lhs => rw [pow_succ, pow_mul, ← n_ih]
    simp_rw [← map_frobenius_expand p, pow_succ', add_comm k, iterateFrobenius_add,
      ← map_map, ← map_expand, ← expand_mul, iterateFrobenius_one]

中文:
定理 map_iterateFrobenius_expand
  条件: (f : 多元多项式 σ R) (n : 自然数)
  证明: by
  induction n with
  | zero => simp [map_id]
  | succ k n_ih =>
    symm
    conv_lhs => rw [pow_succ, pow_mul, ← n_ih]
    simp_rw [← map_frobenius_expand p, pow_succ', add_comm k, iterateFrobenius_add,
      ← map_map, ← map_expand, ← expand_mul, iterateFrobenius_one]

Depends on / 依赖: add_comm, conv_lhs, expand_mul, iterateFrobenius_add, iterateFrobenius_one, map_expand, map_frobenius_expand, map_id, map_map, n_ih, pow_mul, pow_succ, simp_rw
-/
theorem map_iterateFrobenius_expand (f : MvPolynomial σ R) (n : Nat) :
    map (iterateFrobenius R p n) (expand (p ^ n) f) = f ^ p ^ n := by
  induction n with
  | zero => simp [map_id]
  | succ k n_ih =>
    symm
    conv_lhs => rw [pow_succ, pow_mul, ← n_ih]
    simp_rw [← map_frobenius_expand p, pow_succ', add_comm k, iterateFrobenius_add,
      ← map_map, ← map_expand, ← expand_mul, iterateFrobenius_one]

end MvPolynomial
