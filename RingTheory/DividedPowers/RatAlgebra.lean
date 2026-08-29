/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Data.Nat.Factorial.NatCast
public import Mathlib.RingTheory.DividedPowers.Basic

/-! # Examples of divided power structures

In this file we show that, for certain choices of a commutative (semi)ring `A` and an ideal `I` of
`A`, the family of maps `ℕ → A → A` given by `fun n x ↦ x^n/n!` is a divided power structure on `I`.

## Main Definitions

* `DividedPowers.OfInvertibleFactorial.dpow` : the family of functions `ℕ → A → A` given by
  `x^n/n!`.
* `DividedPowers.OfInvertibleFactorial.dividedPowers` : the divided power structure on `I` given by
  `fun x n ↦ x^n/n!`, assuming that there exists a natural number `n` such that `f (n-1)!` is
  invertible in `A` and `I^n = 0`.
* `DividedPowers.OfSquareZero.dividedPowers` : given an ideal `I` such that `I^2 =0`, this is
  the divided power structure on `I` given by `fun x n ↦ x^n/n!`.
* `DividedPowers.CharP.dividedPowers` : if `A` is a commutative ring of prime characteristic `p`
  and `I` is an ideal such that `I^p = 0`, , this is the divided power structure on `I` given by
  `fun x n ↦ x^n/n!`.
* `DividedPowers.RatAlgebra.dividedPowers` : if `I` is any ideal in a `ℚ`-algebra, this is the
  divided power structure on `I` given by `fun x n ↦ x^n/n!`.

## Main Results

* `DividedPowers.RatAlgebra.dividedPowers_unique`: there are no other divided power structures on an
  ideal of a `ℚ`-algebra.

## References

* [P. Berthelot (1974), *Cohomologie cristalline des schémas de
  caractéristique $p$ > 0*][Berthelot-1974]

* [P. Berthelot and A. Ogus (1978), *Notes on crystalline
  cohomology*][BerthelotOgus-1978]

* [N. Roby (1963), *Lois polynomes et lois formelles en théorie des
  modules*][Roby-1963]

* [N. Roby (1965), *Les algèbres à puissances dividées*][Roby-1965]

-/

@[expose] public section

open Nat Ring

namespace DividedPowers

namespace OfInvertibleFactorial

variable {A : Type*} [CommSemiring A] (I : Ideal A) [DecidablePred (fun x => x in I)]

/--
Definition of `dpow` / `dpow` 的定义

English:
definition dpow
  signature: : Nat -> A -> A
  body: fun m x => if x in I then inverse (m ! : A) * x ^ m else 0

中文:
定义 dpow
  签名: : 自然数 -> A -> A
  定义体: fun m x => if x in I then inverse (m ! : A) * x ^ m else 0

Depends on / 依赖: inverse
-/
noncomputable def dpow : Nat -> A -> A := fun m x => if x in I then inverse (m ! : A) * x ^ m else 0

variable {I}

/--
theorem `dpow_eq_of_mem` / 定理 `dpow_eq_of_mem`

English:
theorem dpow_eq_of_mem
  given: {m : Nat} {x : A} (hx : x in I)
  statement: dpow I m x = inverse (m ! : A) * x ^ m
  proof: by
  simp [dpow, hx]

中文:
定理 dpow_eq_of_mem
  条件: {m : 自然数} {x : A} (hx : x in I)
  结论: dpow I m x = inverse (m ! : A) * x ^ m
  证明: by
  simp [dpow, hx]
-/
theorem dpow_eq_of_mem {m : Nat} {x : A} (hx : x in I) : dpow I m x = inverse (m ! : A) * x ^ m := by
  simp [dpow, hx]

/--
theorem `dpow_eq_of_not_mem` / 定理 `dpow_eq_of_not_mem`

English:
theorem dpow_eq_of_not_mem
  given: {m : Nat} {x : A} (hx : x ∉ I)
  statement: dpow I m x = 0
  proof: by simp [dpow, hx]

中文:
定理 dpow_eq_of_not_mem
  条件: {m : 自然数} {x : A} (hx : x ∉ I)
  结论: dpow I m x = 0
  证明: by simp [dpow, hx]
-/
theorem dpow_eq_of_not_mem {m : Nat} {x : A} (hx : x ∉ I) : dpow I m x = 0 := by simp [dpow, hx]

/--
theorem `dpow_null` / 定理 `dpow_null`

English:
theorem dpow_null
  given: {m : Nat} {x : A} (hx : x ∉ I)
  statement: dpow I m x = 0
  proof: by simp [dpow, hx]

中文:
定理 dpow_null
  条件: {m : 自然数} {x : A} (hx : x ∉ I)
  结论: dpow I m x = 0
  证明: by simp [dpow, hx]
-/
theorem dpow_null {m : Nat} {x : A} (hx : x ∉ I) : dpow I m x = 0 := by simp [dpow, hx]

/--
theorem `dpow_zero` / 定理 `dpow_zero`

English:
theorem dpow_zero
  given: {x : A} (hx : x in I)
  statement: dpow I 0 x = 1
  proof: by simp [dpow, hx]

中文:
定理 dpow_zero
  条件: {x : A} (hx : x in I)
  结论: dpow I 0 x = 1
  证明: by simp [dpow, hx]
-/
theorem dpow_zero {x : A} (hx : x in I) : dpow I 0 x = 1 := by simp [dpow, hx]

/--
theorem `dpow_one` / 定理 `dpow_one`

English:
theorem dpow_one
  given: {x : A} (hx : x in I)
  statement: dpow I 1 x = x
  proof: by simp [dpow_eq_of_mem hx]

中文:
定理 dpow_one
  条件: {x : A} (hx : x in I)
  结论: dpow I 1 x = x
  证明: by simp [dpow_eq_of_mem hx]

Depends on / 依赖: dpow_eq_of_mem
-/
theorem dpow_one {x : A} (hx : x in I) : dpow I 1 x = x := by simp [dpow_eq_of_mem hx]

/--
theorem `dpow_mem` / 定理 `dpow_mem`

English:
theorem dpow_mem
  given: {m : Nat} (hm : m != 0) {x : A} (hx : x in I)
  statement: dpow I m x in I
  proof: by
  rw [dpow_eq_of_mem hx]
  exact Ideal.mul_mem_left I _ (Ideal.pow_mem_of_mem I hx _ (Nat.pos_of_ne_zero hm))

中文:
定理 dpow_mem
  条件: {m : 自然数} (hm : m != 0) {x : A} (hx : x in I)
  结论: dpow I m x in I
  证明: by
  rw [dpow_eq_of_mem hx]
  exact Ideal.mul_mem_left I _ (Ideal.pow_mem_of_mem I hx _ (Nat.pos_of_ne_zero hm))

Depends on / 依赖: Ideal.mul_mem_left, Ideal.pow_mem_of_mem, Nat.pos_of_ne_zero, dpow_eq_of_mem, mul_mem_left, pos_of_ne_zero, pow_mem_of_mem
-/
theorem dpow_mem {m : Nat} (hm : m != 0) {x : A} (hx : x in I) : dpow I m x in I := by
  rw [dpow_eq_of_mem hx]
  exact Ideal.mul_mem_left I _ (Ideal.pow_mem_of_mem I hx _ (Nat.pos_of_ne_zero hm))

/--
theorem `dpow_add_of_lt` / 定理 `dpow_add_of_lt`

English:
theorem dpow_add_of_lt
  statement: {n : Nat} (hn_fac : IsUnit ((n - 1)! : A)) {m : Nat} (hmn : m < n)
  proof: by
  rw [dpow_eq_of_mem (Ideal.add_mem I hx hy)]
  simp only [dpow]
  rw [inverse_mul_eq_iff_eq_mul _ _ _ (hn_fac.natCast_factorial_of_lt hmn)]; rw [Finset.mul_sum]; rw [Commute.add_pow' (Commute.all _ _)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [if_pos hx]; rw [if_pos hy]
  ring_nf
  simp on

中文:
定理 dpow_add_of_lt
  结论: {n : 自然数} (hn_fac : 是单位 ((n - 1)! : A)) {m : 自然数} (hmn : m < n)
  证明: by
  rw [dpow_eq_of_mem (Ideal.add_mem I hx hy)]
  simp only [dpow]
  rw [inverse_mul_eq_iff_eq_mul _ _ _ (hn_fac.natCast_factorial_of_lt hmn)]; rw [Finset.mul_sum]; rw [Commute.add_pow' (Commute.all _ _)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [if_pos hx]; rw [if_pos hy]
  ring_nf
  simp on

Depends on / 依赖: Commute, Commute.add_pow, Commute.all, Finset, Finset.mul_sum, Finset.sum_congr, Ideal.add_mem, add_mem, add_pow, castChoose_eq, dpow_eq_of_mem, hn_fac, hn_fac.natCast_factorial_of_lt, if_pos, inverse_mul_eq_iff_eq_mul, mul_assoc, mul_sum, natCast_factorial_of_lt, ring_nf, sum_congr
-/
theorem dpow_add_of_lt {n : Nat} (hn_fac : IsUnit ((n - 1)! : A)) {m : Nat} (hmn : m < n)
    {x y : A} (hx : x in I) (hy : y in I) :
    dpow I m (x + y) = (Finset.antidiagonal m).sum (fun k => dpow I k.1 x * dpow I k.2 y) := by
  rw [dpow_eq_of_mem (Ideal.add_mem I hx hy)]
  simp only [dpow]
  rw [inverse_mul_eq_iff_eq_mul _ _ _ (hn_fac.natCast_factorial_of_lt hmn)]; rw [Finset.mul_sum]; rw [Commute.add_pow' (Commute.all _ _)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [if_pos hx]; rw [if_pos hy]
  ring_nf
  simp only [mul_assoc]; congr; rw [← mul_assoc]
  exact castChoose_eq (hn_fac.natCast_factorial_of_lt hmn) hk

/--
theorem `dpow_add` / 定理 `dpow_add`

English:
theorem dpow_add
  statement: {n : Nat} (hn_fac : IsUnit ((n - 1)! : A)) (hnI : I ^ n = 0) {m : Nat} {x : A}
  proof: by
  by_cases! hmn : m < n
  · exact dpow_add_of_lt hn_fac hmn hx hy
  · have h_sub : I ^ m <= I ^ n := Ideal.pow_le_pow_right hmn
    rw [dpow_eq_of_mem (Ideal.add_mem I hx hy)]
    simp only [dpow]
    have hxy : (x + y) ^ m = 0 := by
      rw [← Ideal.mem_bot]; rw [← Ideal.zero_eq_bot]; rw [← hnI

中文:
定理 dpow_add
  结论: {n : 自然数} (hn_fac : 是单位 ((n - 1)! : A)) (hnI : I ^ n = 0) {m : 自然数} {x : A}
  证明: by
  by_cases! hmn : m < n
  · exact dpow_add_of_lt hn_fac hmn hx hy
  · have h_sub : I ^ m <= I ^ n := Ideal.pow_le_pow_right hmn
    rw [dpow_eq_of_mem (Ideal.add_mem I hx hy)]
    simp only [dpow]
    have hxy : (x + y) ^ m = 0 := by
      rw [← Ideal.mem_bot]; rw [← Ideal.zero_eq_bot]; rw [← hnI

Depends on / 依赖: Finset, Finset.sum_eq_zero, Ideal.add_mem, Ideal.mem_bot, Ideal.pow_le_pow_right, Ideal.pow_mem_pow, Ideal.zero_eq_bot, Set.mem_of_subset_of_mem, add_mem, dpow_add_of_lt, dpow_eq_of_mem, eq_comm, h_sub, hn_fac, if_pos, mem_bot, mem_of_subset_of_mem, mul_assoc, mul_comm, mul_zero
-/
theorem dpow_add {n : Nat} (hn_fac : IsUnit ((n - 1)! : A)) (hnI : I ^ n = 0) {m : Nat} {x : A}
    (hx : x in I) {y : A} (hy : y in I) :
    dpow I m (x + y) = (Finset.antidiagonal m).sum fun k => dpow I k.1 x * dpow I k.2 y := by
  by_cases! hmn : m < n
  · exact dpow_add_of_lt hn_fac hmn hx hy
  · have h_sub : I ^ m <= I ^ n := Ideal.pow_le_pow_right hmn
    rw [dpow_eq_of_mem (Ideal.add_mem I hx hy)]
    simp only [dpow]
    have hxy : (x + y) ^ m = 0 := by
      rw [← Ideal.mem_bot]; rw [← Ideal.zero_eq_bot]; rw [← hnI]
      exact Set.mem_of_subset_of_mem h_sub (Ideal.pow_mem_pow (Ideal.add_mem I hx hy) m)
    rw [hxy]; rw [mul_zero]; rw [eq_comm]
    apply Finset.sum_eq_zero
    intro k hk
    rw [if_pos hx]; rw [if_pos hy]; rw [mul_assoc]; rw [mul_comm (x ^ k.1)]; rw [mul_assoc]; rw [← mul_assoc]
    apply mul_eq_zero_of_right
    rw [← Ideal.mem_bot]; rw [← Ideal.zero_eq_bot]; rw [← hnI]
    apply Set.mem_of_subset_of_mem h_sub
    rw [← Finset.mem_antidiagonal.mp hk]; rw [add_comm]; rw [pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hy _) (Ideal.pow_mem_pow hx _)

/--
theorem `dpow_mul` / 定理 `dpow_mul`

English:
theorem dpow_mul
  given: {m : Nat} {a x : A} (hx : x in I)
  statement: dpow I m (a * x) = a ^ m * dpow I m x
  proof: by
  rw [dpow_eq_of_mem (Ideal.mul_mem_left I _ hx)]; rw [dpow_eq_of_mem hx]; rw [mul_pow]; rw [← mul_assoc]; rw [mul_comm _ (a ^ m)]; rw [mul_assoc]

中文:
定理 dpow_mul
  条件: {m : 自然数} {a x : A} (hx : x in I)
  结论: dpow I m (a * x) = a ^ m * dpow I m x
  证明: by
  rw [dpow_eq_of_mem (Ideal.mul_mem_left I _ hx)]; rw [dpow_eq_of_mem hx]; rw [mul_pow]; rw [← mul_assoc]; rw [mul_comm _ (a ^ m)]; rw [mul_assoc]

Depends on / 依赖: Ideal.mul_mem_left, dpow_eq_of_mem, mul_assoc, mul_comm, mul_mem_left, mul_pow
-/
theorem dpow_mul {m : Nat} {a x : A} (hx : x in I) : dpow I m (a * x) = a ^ m * dpow I m x := by
  rw [dpow_eq_of_mem (Ideal.mul_mem_left I _ hx)]; rw [dpow_eq_of_mem hx]; rw [mul_pow]; rw [← mul_assoc]; rw [mul_comm _ (a ^ m)]; rw [mul_assoc]

/--
theorem `dpow_mul_of_add_lt` / 定理 `dpow_mul_of_add_lt`

English:
theorem dpow_mul_of_add_lt
  statement: {n : Nat} (hn_fac : IsUnit ((n - 1)! : A)) {m k : Nat}
  proof: by
  have hm : m < n := lt_of_le_of_lt le_self_add hkm
  have hk : k < n := lt_of_le_of_lt le_add_self hkm
  rw [dpow_eq_of_mem hx]; rw [dpow_eq_of_mem hx]; rw [dpow_eq_of_mem hx]; rw [mul_assoc]; rw [← mul_assoc (x ^ m)]; rw [mul_comm (x ^ m)]; rw [mul_assoc _ (x ^ m)]; rw [← pow_add]; rw [← mul_as

中文:
定理 dpow_mul_of_add_lt
  结论: {n : 自然数} (hn_fac : 是单位 ((n - 1)! : A)) {m k : 自然数}
  证明: by
  have hm : m < n := lt_of_le_of_lt le_self_add hkm
  have hk : k < n := lt_of_le_of_lt le_add_self hkm
  rw [dpow_eq_of_mem hx]; rw [dpow_eq_of_mem hx]; rw [dpow_eq_of_mem hx]; rw [mul_assoc]; rw [← mul_assoc (x ^ m)]; rw [mul_comm (x ^ m)]; rw [mul_assoc _ (x ^ m)]; rw [← pow_add]; rw [← mul_as

Depends on / 依赖: dpow_eq_of_mem, eq_mul_inverse_iff_mul_eq, hn_fac, hn_fac.natCast_factorial_of_lt, inverse_mul_eq_iff_eq_mul, le_add_self, le_self_add, lt_of_le_of_lt, mul_assoc, mul_comm, natCast_factorial_of_lt, pow_add
-/
theorem dpow_mul_of_add_lt {n : Nat} (hn_fac : IsUnit ((n - 1)! : A)) {m k : Nat}
    (hkm : m + k < n) {x : A} (hx : x in I) :
    dpow I m x * dpow I k x = ↑((m + k).choose m) * dpow I (m + k) x := by
  have hm : m < n := lt_of_le_of_lt le_self_add hkm
  have hk : k < n := lt_of_le_of_lt le_add_self hkm
  rw [dpow_eq_of_mem hx]; rw [dpow_eq_of_mem hx]; rw [dpow_eq_of_mem hx]; rw [mul_assoc]; rw [← mul_assoc (x ^ m)]; rw [mul_comm (x ^ m)]; rw [mul_assoc _ (x ^ m)]; rw [← pow_add]; rw [← mul_assoc]; rw [← mul_assoc]
  apply congr_arg₂ _ _ rfl
  rw [eq_mul_inverse_iff_mul_eq _ _ _ (hn_fac.natCast_factorial_of_lt hkm)]; rw [mul_assoc]; rw [inverse_mul_eq_iff_eq_mul _ _ _ (hn_fac.natCast_factorial_of_lt hm)]; rw [inverse_mul_eq_iff_eq_mul _ _ _ (hn_fac.natCast_factorial_of_lt hk)]
  norm_cast; apply congr_arg
  rw [← Nat.add_choose_mul_factorial_mul_factorial]; rw [mul_comm]; rw [mul_comm _ (m !)]; rw [Nat.choose_symm_add]

/--
theorem `mul_dpow` / 定理 `mul_dpow`

English:
theorem mul_dpow
  statement: {n : Nat} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n = 0)
  proof: by
  by_cases! hkm : m + k < n
  · exact dpow_mul_of_add_lt hn_fac hkm hx
  · have hxmk : x ^ (m + k) = 0 := Ideal.pow_eq_zero_of_mem hnI hkm hx
    rw [dpow_eq_of_mem hx]; rw [dpow_eq_of_mem hx]; rw [dpow_eq_of_mem hx]; rw [mul_assoc]; rw [← mul_assoc (x ^ m)]; rw [mul_comm (x ^ m)]; rw [mul_assoc 

中文:
定理 mul_dpow
  结论: {n : 自然数} (hn_fac : 是单位 ((n - 1).factorial : A)) (hnI : I ^ n = 0)
  证明: by
  by_cases! hkm : m + k < n
  · exact dpow_mul_of_add_lt hn_fac hkm hx
  · have hxmk : x ^ (m + k) = 0 := Ideal.pow_eq_zero_of_mem hnI hkm hx
    rw [dpow_eq_of_mem hx]; rw [dpow_eq_of_mem hx]; rw [dpow_eq_of_mem hx]; rw [mul_assoc]; rw [← mul_assoc (x ^ m)]; rw [mul_comm (x ^ m)]; rw [mul_assoc 

Depends on / 依赖: Ideal.pow_eq_zero_of_mem, dpow_eq_of_mem, dpow_mul_of_add_lt, hn_fac, mul_assoc, mul_comm, mul_zero, pow_add, pow_eq_zero_of_mem
-/
theorem mul_dpow {n : Nat} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n = 0)
    {m k : Nat} {x : A} (hx : x in I) :
    dpow I m x * dpow I k x = ↑((m + k).choose m) * dpow I (m + k) x := by
  by_cases! hkm : m + k < n
  · exact dpow_mul_of_add_lt hn_fac hkm hx
  · have hxmk : x ^ (m + k) = 0 := Ideal.pow_eq_zero_of_mem hnI hkm hx
    rw [dpow_eq_of_mem hx]; rw [dpow_eq_of_mem hx]; rw [dpow_eq_of_mem hx]; rw [mul_assoc]; rw [← mul_assoc (x ^ m)]; rw [mul_comm (x ^ m)]; rw [mul_assoc _ (x ^ m)]; rw [← pow_add]; rw [hxmk]; rw [mul_zero]; rw [mul_zero]; rw [mul_zero]; rw [mul_zero]

/--
theorem `dpow_comp_of_mul_lt` / 定理 `dpow_comp_of_mul_lt`

English:
theorem dpow_comp_of_mul_lt
  statement: {n : Nat} (hn_fac : IsUnit ((n - 1)! : A)) {m k : Nat} (hk : k != 0)
  proof: by
  have hmn : m < n := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hk)) hkm
  rw [dpow_eq_of_mem (m := m * k) hx]; rw [dpow_eq_of_mem (dpow_mem hk hx)]
  by_cases hm0 : m = 0
  · simp only [hm0, zero_mul, _root_.pow_zero, mul_one, uniformBell_zero_left, cast_one, one_mul]
  · hav

中文:
定理 dpow_comp_of_mul_lt
  结论: {n : 自然数} (hn_fac : 是单位 ((n - 1)! : A)) {m k : 自然数} (hk : k != 0)
  证明: by
  have hmn : m < n := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hk)) hkm
  rw [dpow_eq_of_mem (m := m * k) hx]; rw [dpow_eq_of_mem (dpow_mem hk hx)]
  by_cases hm0 : m = 0
  · simp only [hm0, zero_mul, _root_.pow_zero, mul_one, uniformBell_zero_left, cast_one, one_mul]
  · hav

Depends on / 依赖: Nat.le_mul_of_pos_left, Nat.le_mul_of_pos_right, Nat.pos_of_ne_zero, _root_, _root_.pow_zero, cast_one, dpow_eq_of_mem, dpow_mem, le_mul_of_pos_left, le_mul_of_pos_right, lt_of_le_of_lt, mul_assoc, mul_comm, mul_one, mul_pow, one_mul, pos_of_ne_zero, pow_mul, pow_zero, uniformBell_zero_left
-/
theorem dpow_comp_of_mul_lt {n : Nat} (hn_fac : IsUnit ((n - 1)! : A)) {m k : Nat} (hk : k != 0)
    (hkm : m * k < n) {x : A} (hx : x in I) :
    dpow I m (dpow I k x) = ↑(uniformBell m k) * dpow I (m * k) x := by
  have hmn : m < n := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hk)) hkm
  rw [dpow_eq_of_mem (m := m * k) hx]; rw [dpow_eq_of_mem (dpow_mem hk hx)]
  by_cases hm0 : m = 0
  · simp only [hm0, zero_mul, _root_.pow_zero, mul_one, uniformBell_zero_left, cast_one, one_mul]
  · have hkn : k < n := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hm0)) hkm
    rw [dpow_eq_of_mem hx]; rw [mul_pow]; rw [← pow_mul]; rw [mul_comm k]; rw [← mul_assoc]; rw [← mul_assoc]
    apply congr_arg₂ _ _ rfl
    rw [eq_mul_inverse_iff_mul_eq _ _ _ (hn_fac.natCast_factorial_of_lt hkm)]; rw [mul_assoc]; rw [inverse_mul_eq_iff_eq_mul _ _ _ (hn_fac.natCast_factorial_of_lt hmn)]; rw [inverse_pow_mul_eq_iff_eq_mul _ _ (hn_fac.natCast_factorial_of_lt hkn)]; rw [← uniformBell_mul_eq _ hk]
    push_cast
    ring_nf

/--
theorem `dpow_comp` / 定理 `dpow_comp`

English:
theorem dpow_comp
  statement: {n : Nat} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n = 0)
  proof: by
  by_cases! hmk : m * k < n
  · exact dpow_comp_of_mul_lt hn_fac hk hmk hx
  · have hxmk : x ^ (m * k) = 0 := Ideal.pow_eq_zero_of_mem hnI hmk hx
    rw [dpow_eq_of_mem (dpow_mem hk hx)]; rw [dpow_eq_of_mem hx]; rw [dpow_eq_of_mem hx]; rw [mul_pow]; rw [← pow_mul]; rw [← mul_assoc]; rw [mul_comm 

中文:
定理 dpow_comp
  结论: {n : 自然数} (hn_fac : 是单位 ((n - 1).factorial : A)) (hnI : I ^ n = 0)
  证明: by
  by_cases! hmk : m * k < n
  · exact dpow_comp_of_mul_lt hn_fac hk hmk hx
  · have hxmk : x ^ (m * k) = 0 := Ideal.pow_eq_zero_of_mem hnI hmk hx
    rw [dpow_eq_of_mem (dpow_mem hk hx)]; rw [dpow_eq_of_mem hx]; rw [dpow_eq_of_mem hx]; rw [mul_pow]; rw [← pow_mul]; rw [← mul_assoc]; rw [mul_comm 

Depends on / 依赖: Ideal.pow_eq_zero_of_mem, dpow_comp_of_mul_lt, dpow_eq_of_mem, dpow_mem, hn_fac, mul_assoc, mul_comm, mul_pow, mul_zero, pow_eq_zero_of_mem, pow_mul
-/
theorem dpow_comp {n : Nat} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n = 0)
    {m k : Nat} (hk : k != 0) {x : A} (hx : x in I) :
    dpow I m (dpow I k x) = ↑(uniformBell m k) * dpow I (m * k) x := by
  by_cases! hmk : m * k < n
  · exact dpow_comp_of_mul_lt hn_fac hk hmk hx
  · have hxmk : x ^ (m * k) = 0 := Ideal.pow_eq_zero_of_mem hnI hmk hx
    rw [dpow_eq_of_mem (dpow_mem hk hx)]; rw [dpow_eq_of_mem hx]; rw [dpow_eq_of_mem hx]; rw [mul_pow]; rw [← pow_mul]; rw [← mul_assoc]; rw [mul_comm k]; rw [hxmk]; rw [mul_zero]; rw [mul_zero]; rw [mul_zero]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `dividedPowers` / `dividedPowers` 的定义

English:
definition dividedPowers
  signature: {n : Nat} (hn_fac : IsUnit ((n - 1).factorial : A))
  body: dpow I
  dpow_null hx := dpow_null hx
  dpow_zero hx := dpow_zero hx
  dpow_one hx := dpow_one hx
  dpow_mem hn hx := dpow_mem hn hx
  dpow_add hx hy := dpow_add hn_fac hnI hx hy
  dpow_mul := dpow_mul
  mul_dpow hx := mul_dpow hn_fac hnI hx
  dpow_comp hk hx := dpow_comp hn_fac hnI hk hx

中文:
定义 dividedPowers
  签名: {n : 自然数} (hn_fac : 是单位 ((n - 1).factorial : A))
  定义体: dpow I
  dpow_null hx := dpow_null hx
  dpow_zero hx := dpow_zero hx
  dpow_one hx := dpow_one hx
  dpow_mem hn hx := dpow_mem hn hx
  dpow_add hx hy := dpow_add hn_fac hnI hx hy
  dpow_mul := dpow_mul
  mul_dpow hx := mul_dpow hn_fac hnI hx
  dpow_comp hk hx := dpow_comp hn_fac hnI hk hx
-/
noncomputable def dividedPowers {n : Nat} (hn_fac : IsUnit ((n - 1).factorial : A))
    (hnI : I ^ n = 0) : DividedPowers I where
  dpow := dpow I
  dpow_null hx := dpow_null hx
  dpow_zero hx := dpow_zero hx
  dpow_one hx := dpow_one hx
  dpow_mem hn hx := dpow_mem hn hx
  dpow_add hx hy := dpow_add hn_fac hnI hx hy
  dpow_mul := dpow_mul
  mul_dpow hx := mul_dpow hn_fac hnI hx
  dpow_comp hk hx := dpow_comp hn_fac hnI hk hx

/--
lemma `dpow_apply` / 引理 `dpow_apply`

English:
lemma dpow_apply
  statement: {n : Nat} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n = 0)
  proof: rfl

中文:
引理 dpow_apply
  结论: {n : 自然数} (hn_fac : 是单位 ((n - 1).factorial : A)) (hnI : I ^ n = 0)
  证明: rfl
-/
lemma dpow_apply {n : Nat} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n = 0)
    {m : Nat} {x : A} :
  (dividedPowers hn_fac hnI).dpow m x =
    if x in I then inverse (m.factorial : A) * x ^ m else 0 := rfl

end OfInvertibleFactorial

namespace OfSquareZero

variable {A : Type*} [CommSemiring A] {I : Ideal A} [DecidablePred (fun x => x in I)]
  (hI2 : I ^ 2 = 0)

/--
Definition of `dividedPowers` / `dividedPowers` 的定义

English:
definition dividedPowers
  signature: : DividedPowers I
  body: OfInvertibleFactorial.dividedPowers (by norm_num) hI2

中文:
定义 dividedPowers
  签名: : DividedPowers I
  定义体: OfInvertibleFactorial.dividedPowers (by norm_num) hI2

Depends on / 依赖: OfInvertibleFactorial, OfInvertibleFactorial.dividedPowers, dividedPowers
-/
noncomputable def dividedPowers : DividedPowers I :=
  OfInvertibleFactorial.dividedPowers (by norm_num) hI2

/--
theorem `dpow_of_two_le` / 定理 `dpow_of_two_le`

English:
theorem dpow_of_two_le
  given: {n : Nat} (hn : 2 <= n) (a : A)
  proof: by
  simp only [dividedPowers, OfInvertibleFactorial.dpow_apply, ite_eq_right_iff]
  intro ha
  rw [Ideal.pow_eq_zero_of_mem hI2 hn ha]; rw [mul_zero]

中文:
定理 dpow_of_two_le
  条件: {n : 自然数} (hn : 2 <= n) (a : A)
  证明: by
  simp only [dividedPowers, OfInvertibleFactorial.dpow_apply, ite_eq_right_iff]
  intro ha
  rw [Ideal.pow_eq_zero_of_mem hI2 hn ha]; rw [mul_zero]

Depends on / 依赖: Ideal.pow_eq_zero_of_mem, OfInvertibleFactorial, OfInvertibleFactorial.dpow_apply, dividedPowers, dpow_apply, ite_eq_right_iff, mul_zero, pow_eq_zero_of_mem
-/
theorem dpow_of_two_le {n : Nat} (hn : 2 <= n) (a : A) :
    (dividedPowers hI2) n a = 0 := by
  simp only [dividedPowers, OfInvertibleFactorial.dpow_apply, ite_eq_right_iff]
  intro ha
  rw [Ideal.pow_eq_zero_of_mem hI2 hn ha]; rw [mul_zero]

end OfSquareZero

namespace IsNilpotent

variable {A : Type*} [CommRing A] {p : Nat} [Fact (Nat.Prime p)] (hp : IsNilpotent (p : A))
  {I : Ideal A} [DecidablePred (fun x => x in I)] (hIp : I ^ p = 0)

/--
Definition of `dividedPowers` / `dividedPowers` 的定义

English:
definition dividedPowers
  signature: : DividedPowers I
  body: OfInvertibleFactorial.dividedPowers (n := p)
    (IsUnit.natCast_factorial_of_isNilpotent hp (Nat.sub_one_lt (NeZero.ne' p).symm)) hIp

中文:
定义 dividedPowers
  签名: : DividedPowers I
  定义体: OfInvertibleFactorial.dividedPowers (n := p)
    (IsUnit.natCast_factorial_of_isNilpotent hp (Nat.sub_one_lt (NeZero.ne' p).symm)) hIp

Depends on / 依赖: IsUnit, IsUnit.natCast_factorial_of_isNilpotent, Nat.sub_one_lt, NeZero, NeZero.ne, OfInvertibleFactorial, OfInvertibleFactorial.dividedPowers, dividedPowers, natCast_factorial_of_isNilpotent, sub_one_lt
-/
noncomputable def dividedPowers : DividedPowers I :=
  OfInvertibleFactorial.dividedPowers (n := p)
    (IsUnit.natCast_factorial_of_isNilpotent hp (Nat.sub_one_lt (NeZero.ne' p).symm)) hIp

/--
theorem `dpow_of_prime_le` / 定理 `dpow_of_prime_le`

English:
theorem dpow_of_prime_le
  given: {n : Nat} (hn : p <= n) (a : A)
  statement: (dividedPowers hp hIp) n a = 0
  proof: by
  simp only [dividedPowers, OfInvertibleFactorial.dpow_apply, ite_eq_right_iff]
  intro ha
  rw [Ideal.pow_eq_zero_of_mem hIp hn ha]; rw [mul_zero]

中文:
定理 dpow_of_prime_le
  条件: {n : 自然数} (hn : p <= n) (a : A)
  结论: (dividedPowers hp hIp) n a = 0
  证明: by
  simp only [dividedPowers, OfInvertibleFactorial.dpow_apply, ite_eq_right_iff]
  intro ha
  rw [Ideal.pow_eq_zero_of_mem hIp hn ha]; rw [mul_zero]

Depends on / 依赖: Ideal.pow_eq_zero_of_mem, OfInvertibleFactorial, OfInvertibleFactorial.dpow_apply, dividedPowers, dpow_apply, ite_eq_right_iff, mul_zero, pow_eq_zero_of_mem
-/
theorem dpow_of_prime_le {n : Nat} (hn : p <= n) (a : A) : (dividedPowers hp hIp) n a = 0 := by
  simp only [dividedPowers, OfInvertibleFactorial.dpow_apply, ite_eq_right_iff]
  intro ha
  rw [Ideal.pow_eq_zero_of_mem hIp hn ha]; rw [mul_zero]

end IsNilpotent

namespace CharP

variable (A : Type*) [CommRing A] (p : Nat) [CharP A p] [Fact (Nat.Prime p)]
  {I : Ideal A} [DecidablePred (fun x => x in I)] (hIp : I ^ p = 0)

/--
Definition of `dividedPowers` / `dividedPowers` 的定义

English:
definition dividedPowers
  signature: : DividedPowers I
  body: IsNilpotent.dividedPowers ((CharP.cast_eq_zero A p) ▸ IsNilpotent.zero) hIp

中文:
定义 dividedPowers
  签名: : DividedPowers I
  定义体: IsNilpotent.dividedPowers ((CharP.cast_eq_zero A p) ▸ IsNilpotent.zero) hIp

Depends on / 依赖: CharP.cast_eq_zero, IsNilpotent, IsNilpotent.dividedPowers, IsNilpotent.zero, cast_eq_zero, dividedPowers
-/
noncomputable def dividedPowers : DividedPowers I :=
  IsNilpotent.dividedPowers ((CharP.cast_eq_zero A p) ▸ IsNilpotent.zero) hIp

/--
theorem `dpow_of_prime_le` / 定理 `dpow_of_prime_le`

English:
theorem dpow_of_prime_le
  given: {n : Nat} (hn : p <= n) (a : A)
  statement: (dividedPowers A p hIp) n a = 0
  proof: by
  simp only [dividedPowers, IsNilpotent.dividedPowers, OfInvertibleFactorial.dpow_apply,
    ite_eq_right_iff]
  intro ha
  rw [Ideal.pow_eq_zero_of_mem hIp hn ha]; rw [mul_zero]

中文:
定理 dpow_of_prime_le
  条件: {n : 自然数} (hn : p <= n) (a : A)
  结论: (dividedPowers A p hIp) n a = 0
  证明: by
  simp only [dividedPowers, IsNilpotent.dividedPowers, OfInvertibleFactorial.dpow_apply,
    ite_eq_right_iff]
  intro ha
  rw [Ideal.pow_eq_zero_of_mem hIp hn ha]; rw [mul_zero]

Depends on / 依赖: Ideal.pow_eq_zero_of_mem, IsNilpotent, IsNilpotent.dividedPowers, OfInvertibleFactorial, OfInvertibleFactorial.dpow_apply, dividedPowers, dpow_apply, ite_eq_right_iff, mul_zero, pow_eq_zero_of_mem
-/
theorem dpow_of_prime_le {n : Nat} (hn : p <= n) (a : A) : (dividedPowers A p hIp) n a = 0 := by
  simp only [dividedPowers, IsNilpotent.dividedPowers, OfInvertibleFactorial.dpow_apply,
    ite_eq_right_iff]
  intro ha
  rw [Ideal.pow_eq_zero_of_mem hIp hn ha]; rw [mul_zero]

end CharP

-- We formalize example 2 from [BO], Section 3.
namespace RatAlgebra

variable {R : Type*} [CommSemiring R] (I : Ideal R) [DecidablePred (fun x => x in I)]

/--
Definition of `dpow` / `dpow` 的定义

English:
definition dpow
  signature: : Nat -> R -> R
  body: OfInvertibleFactorial.dpow I

中文:
定义 dpow
  签名: : 自然数 -> R -> R
  定义体: OfInvertibleFactorial.dpow I

Depends on / 依赖: OfInvertibleFactorial, OfInvertibleFactorial.dpow
-/
noncomputable def dpow : Nat -> R -> R := OfInvertibleFactorial.dpow I

variable {I}

/--
theorem `dpow_eq_of_mem` / 定理 `dpow_eq_of_mem`

English:
theorem dpow_eq_of_mem
  given: (n : Nat) {x : R} (hx : x in I)
  proof: by
  rw [dpow]; rw [OfInvertibleFactorial.dpow_eq_of_mem hx]

中文:
定理 dpow_eq_of_mem
  条件: (n : 自然数) {x : R} (hx : x in I)
  证明: by
  rw [dpow]; rw [OfInvertibleFactorial.dpow_eq_of_mem hx]

Depends on / 依赖: OfInvertibleFactorial, OfInvertibleFactorial.dpow_eq_of_mem, dpow_eq_of_mem
-/
theorem dpow_eq_of_mem (n : Nat) {x : R} (hx : x in I) :
    dpow I n x = (inverse n.factorial : R) * x ^ n := by
  rw [dpow]; rw [OfInvertibleFactorial.dpow_eq_of_mem hx]

variable [Algebra Rat R]

variable (I)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `dividedPowers` / `dividedPowers` 的定义

English:
definition dividedPowers
  signature: : DividedPowers I where
  body: dpow I
  dpow_null hx := OfInvertibleFactorial.dpow_null hx
  dpow_zero hx := OfInvertibleFactorial.dpow_zero hx
  dpow_one hx := OfInvertibleFactorial.dpow_one hx
  dpow_mem hn hx := OfInvertibleFactorial.dpow_mem hn hx
  dpow_add {n} _ _ hx hy := OfInvertibleFactorial.dpow_add_of_lt
    (IsUnit.na

中文:
定义 dividedPowers
  签名: : DividedPowers I where
  定义体: dpow I
  dpow_null hx := OfInvertibleFactorial.dpow_null hx
  dpow_zero hx := OfInvertibleFactorial.dpow_zero hx
  dpow_one hx := OfInvertibleFactorial.dpow_one hx
  dpow_mem hn hx := OfInvertibleFactorial.dpow_mem hn hx
  dpow_add {n} _ _ hx hy := OfInvertibleFactorial.dpow_add_of_lt
    (IsUnit.na
-/
noncomputable def dividedPowers : DividedPowers I where
  dpow := dpow I
  dpow_null hx := OfInvertibleFactorial.dpow_null hx
  dpow_zero hx := OfInvertibleFactorial.dpow_zero hx
  dpow_one hx := OfInvertibleFactorial.dpow_one hx
  dpow_mem hn hx := OfInvertibleFactorial.dpow_mem hn hx
  dpow_add {n} _ _ hx hy := OfInvertibleFactorial.dpow_add_of_lt
    (IsUnit.natCast_factorial_of_algebra Rat _) (n.lt_succ_self) hx hy
  dpow_mul hx := OfInvertibleFactorial.dpow_mul hx
  mul_dpow {m} k _ hx := OfInvertibleFactorial.dpow_mul_of_add_lt
    (IsUnit.natCast_factorial_of_algebra Rat _) (m + k).lt_succ_self hx
  dpow_comp hk hx := OfInvertibleFactorial.dpow_comp_of_mul_lt
    (IsUnit.natCast_factorial_of_algebra Rat _) hk (lt_add_one _) hx

@[simp]
/--
lemma `dpow_apply` / 引理 `dpow_apply`

English:
lemma dpow_apply
  given: {n : Nat} {x : R}
  proof: rfl

omit [DecidablePred fun x => x in I] in

中文:
引理 dpow_apply
  条件: {n : 自然数} {x : R}
  证明: rfl

omit [DecidablePred fun x => x in I] in
-/
lemma dpow_apply {n : Nat} {x : R} :
    (dividedPowers I).dpow n x = if x in I then inverse (n.factorial : R) * x ^ n else 0 := rfl

omit [DecidablePred fun x => x in I] in
/--
theorem `dpow_eq_inv_fact_smul` / 定理 `dpow_eq_inv_fact_smul`

English:
theorem dpow_eq_inv_fact_smul
  given: (hI : DividedPowers I) {n : Nat} {x : R} (hx : x in I)
  proof: by
  rw [inverse_eq_inv']; rw [← factorial_mul_dpow_eq_pow hI hx]; rw [← smul_eq_mul]; rw [← smul_assoc]
  nth_rewrite 1 [← one_smul R (hI.dpow n x)]
  congr
  have aux : ((n !) : R) = (n ! : Rat) • (1 : R) := by
    rw [cast_smul_eq_nsmul]; rw [nsmul_eq_mul]; rw [mul_one]
  rw [aux]; rw [← mul_smul

中文:
定理 dpow_eq_inv_fact_smul
  条件: (hI : DividedPowers I) {n : 自然数} {x : R} (hx : x in I)
  证明: by
  rw [inverse_eq_inv']; rw [← factorial_mul_dpow_eq_pow hI hx]; rw [← smul_eq_mul]; rw [← smul_assoc]
  nth_rewrite 1 [← one_smul R (hI.dpow n x)]
  congr
  have aux : ((n !) : R) = (n ! : Rat) • (1 : R) := by
    rw [cast_smul_eq_nsmul]; rw [nsmul_eq_mul]; rw [mul_one]
  rw [aux]; rw [← mul_smul

Depends on / 依赖: Rat.inv_mul_cancel, cast_smul_eq_nsmul, cast_zero, factorial_mul_dpow_eq_pow, factorial_ne_zero, hI.dpow, inv_mul_cancel, inverse_eq_inv, mul_one, mul_smul, ne_eq, nsmul_eq_mul, nth_rewrite, one_smul, smul_assoc, smul_eq_mul
-/
theorem dpow_eq_inv_fact_smul (hI : DividedPowers I) {n : Nat} {x : R} (hx : x in I) :
    hI.dpow n x = (inverse (n.factorial : Rat)) • x ^ n := by
  rw [inverse_eq_inv']; rw [← factorial_mul_dpow_eq_pow hI hx]; rw [← smul_eq_mul]; rw [← smul_assoc]
  nth_rewrite 1 [← one_smul R (hI.dpow n x)]
  congr
  have aux : ((n !) : R) = (n ! : Rat) • (1 : R) := by
    rw [cast_smul_eq_nsmul]; rw [nsmul_eq_mul]; rw [mul_one]
  rw [aux]; rw [← mul_smul]
  suffices (n ! : Rat)⁻¹ * (n !) = 1 by
    rw [this]; rw [one_smul]
  apply Rat.inv_mul_cancel
  rw [← cast_zero]; rw [ne_eq]
  simp [factorial_ne_zero]

variable {I}

/--
theorem `dividedPowers_unique` / 定理 `dividedPowers_unique`

English:
theorem dividedPowers_unique
  given: (hI : DividedPowers I)
  statement: hI = dividedPowers I
  proof: hI.ext _ (fun n x hx => by rw [dpow_apply, if_pos hx, eq_comm, inverse_mul_eq_iff_eq_mul _ _ _
      (IsUnit.natCast_factorial_of_algebra Rat n), factorial_mul_dpow_eq_pow _ hx])

中文:
定理 dividedPowers_unique
  条件: (hI : DividedPowers I)
  结论: hI = dividedPowers I
  证明: hI.ext _ (fun n x hx => by rw [dpow_apply, if_pos hx, eq_comm, inverse_mul_eq_iff_eq_mul _ _ _
      (IsUnit.natCast_factorial_of_algebra Rat n), factorial_mul_dpow_eq_pow _ hx])

Depends on / 依赖: IsUnit, IsUnit.natCast_factorial_of_algebra, dpow_apply, eq_comm, factorial_mul_dpow_eq_pow, hI.ext, if_pos, inverse_mul_eq_iff_eq_mul, natCast_factorial_of_algebra
-/
theorem dividedPowers_unique (hI : DividedPowers I) : hI = dividedPowers I :=
  hI.ext _ (fun n x hx => by rw [dpow_apply, if_pos hx, eq_comm, inverse_mul_eq_iff_eq_mul _ _ _
      (IsUnit.natCast_factorial_of_algebra Rat n), factorial_mul_dpow_eq_pow _ hx])

end RatAlgebra

end DividedPowers
