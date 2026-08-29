/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.GenFun
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
# Glaisher's theorem

This file proves Glaisher's theorem: the number of partitions of an integer $n$ into parts not
divisible by $d$ is equal to the number of partitions in which no part is repeated $d$ or more
times.

## Main declarations
* `Nat.Partition.card_restricted_eq_card_countRestricted`: Glaisher's theorem.
* `Nat.Partition.card_odds_eq_card_distincts`: Euler's partition theorem, a special case
  of Glaisher's theorem when `m = 2`. This is also Theorem 45 from the
  [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

## Proof outline

The proof is based on the generating functions for `restricted` and `countRestricted` partitions,
which turn out to be equal:

$$\prod_{i=1,i\nmid m}^\infty\frac{1}{1-X^i}=\prod_{i=0}^\infty (1+X^{i+1}+\cdots+X^{(m-1)(i+1)})$$

## References
https://en.wikipedia.org/wiki/Glaisher%27s_theorem
-/

public section

variable (R) [TopologicalSpace R] [T2Space R]

namespace Nat.Partition
open PowerSeries PowerSeries.WithPiTopology Finset

section Semiring
variable [CommSemiring R]

/--
theorem `hasProd_powerSeriesMk_card_restricted` / 定理 `hasProd_powerSeriesMk_card_restricted`

English:
theorem hasProd_powerSeriesMk_card_restricted
  statement: [IsTopologicalSemiring R]
  proof: by
  convert! hasProd_genFun (fun i c => if p i then (1 : R) else 0) using 1
  · ext1 i
    split_ifs
    · rw [tsum_eq_zero_add' ?_]
      · simp
      simp_rw [pow_mul, pow_add]
      apply Summable.mul_right
      exact summable_pow_of_constantCoeff_eq_zero (by simp)
    · simp
  · simp_rw [genFu

中文:
定理 hasProd_powerSeriesMk_card_restricted
  结论: [是TopologicalSemiring R]
  证明: by
  convert! hasProd_genFun (fun i c => if p i then (1 : R) else 0) using 1
  · ext1 i
    split_ifs
    · rw [tsum_eq_zero_add' ?_]
      · simp
      simp_rw [pow_mul, pow_add]
      apply Summable.mul_right
      exact summable_pow_of_constantCoeff_eq_zero (by simp)
    · simp
  · simp_rw [genFu

Depends on / 依赖: Finsupp, Finsupp.prod, Summable, Summable.mul_right, card_filter, convert, genFun, hasProd_genFun, mul_right, pow_add, pow_mul, prod_boole, restricted, simp_rw, split_ifs, summable_pow_of_constantCoeff_eq_zero, tsum_eq_zero_add
-/
theorem hasProd_powerSeriesMk_card_restricted [IsTopologicalSemiring R]
    (p : Nat -> Prop) [DecidablePred p] :
    HasProd (fun i => if p (i + 1) then ∑' j : Nat, X ^ ((i + 1) * j) else 1)
    (PowerSeries.mk fun n => (#(restricted n p) : R)) := by
  convert! hasProd_genFun (fun i c => if p i then (1 : R) else 0) using 1
  · ext1 i
    split_ifs
    · rw [tsum_eq_zero_add' ?_]
      · simp
      simp_rw [pow_mul, pow_add]
      apply Summable.mul_right
      exact summable_pow_of_constantCoeff_eq_zero (by simp)
    · simp
  · simp_rw [genFun, restricted, card_filter, Finsupp.prod, prod_boole]
    simp

/--
theorem `multipliable_powerSeriesMk_card_restricted` / 定理 `multipliable_powerSeriesMk_card_restricted`

English:
theorem multipliable_powerSeriesMk_card_restricted
  statement: [IsTopologicalSemiring R]
  proof: (hasProd_powerSeriesMk_card_restricted R p).multipliable

中文:
定理 multipliable_powerSeriesMk_card_restricted
  结论: [是TopologicalSemiring R]
  证明: (hasProd_powerSeriesMk_card_restricted R p).multipliable

Depends on / 依赖: hasProd_powerSeriesMk_card_restricted, multipliable
-/
theorem multipliable_powerSeriesMk_card_restricted [IsTopologicalSemiring R]
    (p : Nat -> Prop) [DecidablePred p] :
    Multipliable (fun i => if p (i + 1) then ∑' j : Nat, (X ^ ((i + 1) * j) : R⟦X⟧) else 1) :=
  (hasProd_powerSeriesMk_card_restricted R p).multipliable

/--
theorem `powerSeriesMk_card_restricted_eq_tprod` / 定理 `powerSeriesMk_card_restricted_eq_tprod`

English:
theorem powerSeriesMk_card_restricted_eq_tprod
  statement: [IsTopologicalSemiring R]
  proof: (hasProd_powerSeriesMk_card_restricted R p).tprod_eq.symm

中文:
定理 powerSeriesMk_card_restricted_eq_tprod
  结论: [是TopologicalSemiring R]
  证明: (hasProd_powerSeriesMk_card_restricted R p).tprod_eq.symm

Depends on / 依赖: hasProd_powerSeriesMk_card_restricted, tprod_eq, tprod_eq.symm
-/
theorem powerSeriesMk_card_restricted_eq_tprod [IsTopologicalSemiring R]
    (p : Nat -> Prop) [DecidablePred p] :
    PowerSeries.mk (fun n => (#(restricted n p) : R)) =
    ∏' i, if p (i + 1) then ∑' j : Nat, X ^ ((i + 1) * j) else 1 :=
  (hasProd_powerSeriesMk_card_restricted R p).tprod_eq.symm

/--
theorem `hasProd_powerSeriesMk_card_countRestricted` / 定理 `hasProd_powerSeriesMk_card_countRestricted`

English:
theorem hasProd_powerSeriesMk_card_countRestricted
  given: {m : Nat} (hm : 0 < m)
  proof: by
  nontriviality R using Subsingleton.eq_one (α := R⟦X⟧)
  convert! hasProd_genFun (fun i c => if c < m then (1 : R) else 0) using 1
  · ext1 i
    rw [sum_range_eq_add_Ico _ hm]; rw [sum_Ico_eq_sum_range]
congrm (by simp) + ?_
    trans ∑ k in range (m - 1), (if k + 1 < m then (1 : R) else 0) • X

中文:
定理 hasProd_powerSeriesMk_card_countRestricted
  条件: {m : 自然数} (hm : 0 < m)
  证明: by
  nontriviality R using Subsingleton.eq_one (α := R⟦X⟧)
  convert! hasProd_genFun (fun i c => if c < m then (1 : R) else 0) using 1
  · ext1 i
    rw [sum_range_eq_add_Ico _ hm]; rw [sum_Ico_eq_sum_range]
congrm (by simp) + ?_
    trans ∑ k in range (m - 1), (if k + 1 < m then (1 : R) else 0) • X

Depends on / 依赖: Subsingleton, Subsingleton.eq_one, add_comm, congrm, convert, eq_one, hasProd_genFun, nontriviality, simp_rw, smul_eq_zero_of_left, sum_Ico_eq_sum_range, sum_congr, sum_range_eq_add_Ico, tsum_eq_sum
-/
theorem hasProd_powerSeriesMk_card_countRestricted {m : Nat} (hm : 0 < m) :
    HasProd (fun i => ∑ j in range m, X ^ ((i + 1) * j))
    (PowerSeries.mk fun n => (#(countRestricted n m) : R)) := by
  nontriviality R using Subsingleton.eq_one (α := R⟦X⟧)
  convert! hasProd_genFun (fun i c => if c < m then (1 : R) else 0) using 1
  · ext1 i
    rw [sum_range_eq_add_Ico _ hm]; rw [sum_Ico_eq_sum_range]
congrm (by simp) + ?_
    trans ∑ k in range (m - 1), (if k + 1 < m then (1 : R) else 0) • X ^ ((i + 1) * (k + 1))
    · refine sum_congr rfl fun b hn => ?_
      rw [add_comm 1 b]
      have : b + 1 < m := by grind
      simp [this]
    · exact (tsum_eq_sum (fun b hb => smul_eq_zero_of_left (by simpa using hb) _)).symm
  · simp_rw [genFun, countRestricted, card_filter, Finsupp.prod, prod_boole]
    simp

/--
theorem `multipliable_powerSeriesMk_card_countRestricted` / 定理 `multipliable_powerSeriesMk_card_countRestricted`

English:
theorem multipliable_powerSeriesMk_card_countRestricted
  given: (m : Nat)
  proof: by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using multipliable_of_exists_eq_zero ⟨0, rfl⟩
  · exact (hasProd_powerSeriesMk_card_countRestricted R hm).multipliable

中文:
定理 multipliable_powerSeriesMk_card_countRestricted
  条件: (m : 自然数)
  证明: by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using multipliable_of_exists_eq_zero ⟨0, rfl⟩
  · exact (hasProd_powerSeriesMk_card_countRestricted R hm).multipliable

Depends on / 依赖: Nat.eq_zero_or_pos, eq_zero_or_pos, hasProd_powerSeriesMk_card_countRestricted, multipliable, multipliable_of_exists_eq_zero
-/
theorem multipliable_powerSeriesMk_card_countRestricted (m : Nat) :
    Multipliable fun i => ∑ j in range m, (X ^ ((i + 1) * j) : R⟦X⟧) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using multipliable_of_exists_eq_zero ⟨0, rfl⟩
  · exact (hasProd_powerSeriesMk_card_countRestricted R hm).multipliable

/--
theorem `powerSeriesMk_card_countRestricted_eq_tprod` / 定理 `powerSeriesMk_card_countRestricted_eq_tprod`

English:
theorem powerSeriesMk_card_countRestricted_eq_tprod
  given: {m : Nat} (hm : 0 < m)
  proof: (hasProd_powerSeriesMk_card_countRestricted R hm).tprod_eq.symm

中文:
定理 powerSeriesMk_card_countRestricted_eq_tprod
  条件: {m : 自然数} (hm : 0 < m)
  证明: (hasProd_powerSeriesMk_card_countRestricted R hm).tprod_eq.symm

Depends on / 依赖: hasProd_powerSeriesMk_card_countRestricted, tprod_eq, tprod_eq.symm
-/
theorem powerSeriesMk_card_countRestricted_eq_tprod {m : Nat} (hm : 0 < m) :
    PowerSeries.mk (fun n => (#(countRestricted n m) : R)) =
    ∏' i, ∑ j in range m, X ^ ((i + 1) * j) :=
  (hasProd_powerSeriesMk_card_countRestricted R hm).tprod_eq.symm

end Semiring

section Ring
variable [CommRing R] [NoZeroDivisors R]

/--
theorem `aux_mul_one_sub_X_pow` / 定理 `aux_mul_one_sub_X_pow`

English:
theorem aux_mul_one_sub_X_pow
  given: [IsTopologicalRing R] {m : Nat} (hm : 0 < m)
  proof: by
  nontriviality R
  rw [← (multipliable_powerSeriesMk_card_restricted R (¬ m ∣ ·)).tprod_mul
    (multipliable_one_sub_X_pow _)]
  simp_rw [ite_not, ite_mul, pow_mul]
  conv in fun b => _ =>
    ext b
    rw [tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)]
  refine tprod_eq_tprod_of_ne_o

中文:
定理 aux_mul_one_sub_X_pow
  条件: [是拓扑环 R] {m : 自然数} (hm : 0 < m)
  证明: by
  nontriviality R
  rw [← (multipliable_powerSeriesMk_card_restricted R (¬ m ∣ ·)).tprod_mul
    (multipliable_one_sub_X_pow _)]
  simp_rw [ite_not, ite_mul, pow_mul]
  conv in fun b => _ =>
    ext b
    rw [tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)]
  refine tprod_eq_tprod_of_ne_o
-/
private theorem aux_mul_one_sub_X_pow [IsTopologicalRing R] {m : Nat} (hm : 0 < m) :
    (∏' i, if ¬m ∣ i + 1 then ∑' j, (X : R⟦X⟧) ^ ((i + 1) * j) else 1) * ∏' i, (1 - X ^ (i + 1)) =
    ∏' i, (1 - X ^ ((i + 1) * m)) := by
  nontriviality R
  rw [← (multipliable_powerSeriesMk_card_restricted R (¬ m ∣ ·)).tprod_mul
    (multipliable_one_sub_X_pow _)]
  simp_rw [ite_not, ite_mul, pow_mul]
  conv in fun b => _ =>
    ext b
    rw [tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)]
  refine tprod_eq_tprod_of_ne_one_bij (fun i => (i.val + 1) * m - 1) ?_ ?_ ?_
  · intro a b h
    rw [tsub_left_inj (by nlinarith) (by nlinarith)]; rw [mul_left_inj' (hm.ne.symm)]; rw [add_left_inj] at h
    exact SetCoe.ext h
  · suffices forall (i : Nat), m ∣ i + 1 -> exists j != 0, j * m - 1 = i by simpa
    intro i hi
    obtain ⟨j, hj⟩ := dvd_def.mp hi
    refine ⟨j, by grind, Nat.sub_eq_of_eq_add ?_⟩
    rw [hj]; rw [mul_comm m j]
  · intro i
    have : (i + 1) * m - 1 + 1 = (i + 1) * m := by grind
    simp [this, pow_mul]

omit [TopologicalSpace R] in
/--
theorem `powerSeriesMk_card_restricted_eq_powerSeriesMk_card_countRestricted` / 定理 `powerSeriesMk_card_restricted_eq_powerSeriesMk_card_countRestricted`

English:
theorem powerSeriesMk_card_restricted_eq_powerSeriesMk_card_countRestricted
  given: {m : Nat} (hm : 0 < m)
  proof: by
  nontriviality R
  let _ : TopologicalSpace R := ⊥
  have _ : DiscreteTopology R := ⟨rfl⟩
  rw [powerSeriesMk_card_restricted_eq_tprod R (¬ m ∣ ·)]
  rw [powerSeriesMk_card_countRestricted_eq_tprod R hm]
  apply mul_right_cancel₀ (tprod_one_sub_X_pow_ne_zero R)
  rw [aux_mul_one_sub_X_pow R hm]


中文:
定理 powerSeriesMk_card_restricted_eq_powerSeriesMk_card_countRestricted
  条件: {m : 自然数} (hm : 0 < m)
  证明: by
  nontriviality R
  let _ : TopologicalSpace R := ⊥
  have _ : DiscreteTopology R := ⟨rfl⟩
  rw [powerSeriesMk_card_restricted_eq_tprod R (¬ m ∣ ·)]
  rw [powerSeriesMk_card_countRestricted_eq_tprod R hm]
  apply mul_right_cancel₀ (tprod_one_sub_X_pow_ne_zero R)
  rw [aux_mul_one_sub_X_pow R hm]


Depends on / 依赖: DiscreteTopology, TopologicalSpace, aux_mul_one_sub_X_pow, geom_sum_mul_neg, multipliable_one_sub_X_pow, multipliable_powerSeriesMk_card_countRestricted, nontriviality, pow_mul, powerSeriesMk_card_countRestricted_eq_tprod, powerSeriesMk_card_restricted_eq_tprod, simp_rw, tprod_congr, tprod_mul, tprod_one_sub_X_pow_ne_zero
-/
theorem powerSeriesMk_card_restricted_eq_powerSeriesMk_card_countRestricted {m : Nat} (hm : 0 < m) :
    (PowerSeries.mk fun n => (#(restricted n (¬ m ∣ ·)) : R)) =
    PowerSeries.mk fun n => (#(countRestricted n m) : R) := by
  nontriviality R
  let _ : TopologicalSpace R := ⊥
  have _ : DiscreteTopology R := ⟨rfl⟩
  rw [powerSeriesMk_card_restricted_eq_tprod R (¬ m ∣ ·)]
  rw [powerSeriesMk_card_countRestricted_eq_tprod R hm]
  apply mul_right_cancel₀ (tprod_one_sub_X_pow_ne_zero R)
  rw [aux_mul_one_sub_X_pow R hm]
  rw [← (multipliable_powerSeriesMk_card_countRestricted R m).tprod_mul
    (multipliable_one_sub_X_pow _)]
  exact tprod_congr (fun i => by simp_rw [pow_mul, geom_sum_mul_neg])

end Ring

/--
theorem `card_restricted_eq_card_countRestricted` / 定理 `card_restricted_eq_card_countRestricted`

English:
theorem card_restricted_eq_card_countRestricted
  given: (n : Nat) {m : Nat} (hm : 0 < m)
  proof: by
  simpa using PowerSeries.ext_iff.mp
    (powerSeriesMk_card_restricted_eq_powerSeriesMk_card_countRestricted Int hm) n

中文:
定理 card_restricted_eq_card_countRestricted
  条件: (n : 自然数) {m : 自然数} (hm : 0 < m)
  证明: by
  simpa using PowerSeries.ext_iff.mp
    (powerSeriesMk_card_restricted_eq_powerSeriesMk_card_countRestricted Int hm) n

Depends on / 依赖: PowerSeries, PowerSeries.ext_iff.mp, ext_iff, powerSeriesMk_card_restricted_eq_powerSeriesMk_card_countRestricted
-/
theorem card_restricted_eq_card_countRestricted (n : Nat) {m : Nat} (hm : 0 < m) :
    #(restricted n (¬ m ∣ ·)) = #(countRestricted n m) := by
  simpa using PowerSeries.ext_iff.mp
    (powerSeriesMk_card_restricted_eq_powerSeriesMk_card_countRestricted Int hm) n

/--
theorem `card_odds_eq_card_distincts` / 定理 `card_odds_eq_card_distincts`

English:
theorem card_odds_eq_card_distincts
  given: (n : Nat)
  statement: #(odds n) = #(distincts n)
  proof: by
  simp_rw [← countRestricted_two, odds, even_iff_two_dvd]
  exact card_restricted_eq_card_countRestricted n (by norm_num)

中文:
定理 card_odds_eq_card_distincts
  条件: (n : 自然数)
  结论: #(odds n) = #(distincts n)
  证明: by
  simp_rw [← countRestricted_two, odds, even_iff_two_dvd]
  exact card_restricted_eq_card_countRestricted n (by norm_num)

Depends on / 依赖: card_restricted_eq_card_countRestricted, countRestricted_two, even_iff_two_dvd, simp_rw
-/
theorem card_odds_eq_card_distincts (n : Nat) : #(odds n) = #(distincts n) := by
  simp_rw [← countRestricted_two, odds, even_iff_two_dvd]
  exact card_restricted_eq_card_countRestricted n (by norm_num)

end Nat.Partition
