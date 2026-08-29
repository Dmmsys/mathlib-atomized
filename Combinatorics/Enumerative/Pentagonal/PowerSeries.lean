/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Combinatorics.Enumerative.Pentagonal.Basic
public import Mathlib.RingTheory.PowerSeries.PiTopology

import Mathlib.Combinatorics.Enumerative.Pentagonal.Ring
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Pentagonal number theorem for power series

This file proves the pentagonal number theorem for power series:

$$ \prod_{n = 0}^{\infty} (1 - x^{n + 1}) = \sum_{k=-\infty}^{\infty} (-1)^k x^{a_k} $$

where $a_k = k(3k - 1)/2$ are the pentagonal numbers. We state the theorem in two parts by
introducing the intermediate power series `PowerSeries.pentagonalSeries`, whose coefficients are
defined using pentagonal numbers. We then show that this series is equal to both sides.

## Main theorems

* `PowerSeries.WithPiTopology.hasProd_one_sub_X_pow`: `PowerSeries.pentagonalSeries` is equal to
  infinite product on the left-hand side of the formula.
* `PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq` restates the left-hand side without requiring
  topology.
* `PowerSeries.WithPiTopology.hasSum_pentagonalSeries`: `PowerSeries.pentagonalSeries` is equal to
  the infinite sum on the right-hand side of the formula.
* `PowerSeries.coeff_pentagonalSeries` restates the right-hand side without requiring topology.
-/

open Filter PowerSeries WithPiTopology Topology
variable (R : Type*) [CommRing R]

namespace Pentagonal
-- private auxiliary lemma

/--
theorem `tendsto_order_pow_mul_prod_one_sub_pow` / 定理 `tendsto_order_pow_mul_prod_one_sub_pow`

English:
theorem tendsto_order_pow_mul_prod_one_sub_pow
  given: (k : Nat)
  proof: by
  nontriviality R using Subsingleton.eq_zero (α := R⟦X⟧)
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n => eventually_atTop.mpr ⟨n + 1, ?_⟩
  intro m hm
  grw [← le_order_mul, order_X_pow]
  refine lt_add_of_lt_of_nonneg ?_ (by simp)
  norm_cast
  grind

中文:
定理 tendsto_order_pow_mul_prod_one_sub_pow
  条件: (k : 自然数)
  证明: by
  nontriviality R using Subsingleton.eq_zero (α := R⟦X⟧)
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n => eventually_atTop.mpr ⟨n + 1, ?_⟩
  intro m hm
  grw [← le_order_mul, order_X_pow]
  refine lt_add_of_lt_of_nonneg ?_ (by simp)
  norm_cast
  grind

Depends on / 依赖: ENat.tendsto_nhds_top_iff_natCast_lt.mpr, Subsingleton, Subsingleton.eq_zero, eq_zero, eventually_atTop, eventually_atTop.mpr, le_order_mul, lt_add_of_lt_of_nonneg, nontriviality, order_X_pow, tendsto_nhds_top_iff_natCast_lt
-/
theorem tendsto_order_pow_mul_prod_one_sub_pow (k : Nat) :
    Tendsto (fun n => (X ^ ((k + 1) * n) *
      ∏ i in Finset.range (n + 1), (1 - X ^ (k + i + 1)) : R⟦X⟧).order) atTop (𝓝 ⊤) := by
  nontriviality R using Subsingleton.eq_zero (α := R⟦X⟧)
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n => eventually_atTop.mpr ⟨n + 1, ?_⟩
  intro m hm
  grw [← le_order_mul, order_X_pow]
  refine lt_add_of_lt_of_nonneg ?_ (by simp)
  norm_cast
  grind

/--
theorem `tendsto_order_neg_X_pow` / 定理 `tendsto_order_neg_X_pow`

English:
theorem tendsto_order_neg_X_pow
  given: (k : Nat)
  proof: by
  nontriviality R using Subsingleton.eq_zero (α := R⟦X⟧)
  simp_rw [order_neg, order_X_pow, add_assoc]
  exact ENat.tendsto_natCast_nhds_top.comp (tendsto_add_atTop_nat _)

中文:
定理 tendsto_order_neg_X_pow
  条件: (k : 自然数)
  证明: by
  nontriviality R using Subsingleton.eq_zero (α := R⟦X⟧)
  simp_rw [order_neg, order_X_pow, add_assoc]
  exact ENat.tendsto_natCast_nhds_top.comp (tendsto_add_atTop_nat _)

Depends on / 依赖: ENat.tendsto_natCast_nhds_top.comp, Subsingleton, Subsingleton.eq_zero, add_assoc, eq_zero, nontriviality, order_X_pow, order_neg, simp_rw, tendsto_add_atTop_nat, tendsto_natCast_nhds_top
-/
theorem tendsto_order_neg_X_pow (k : Nat) :
    Tendsto (fun i => (-(X : R⟦X⟧) ^ (i + k + 1)).order) atTop (𝓝 ⊤) := by
  nontriviality R using Subsingleton.eq_zero (α := R⟦X⟧)
  simp_rw [order_neg, order_X_pow, add_assoc]
  exact ENat.tendsto_natCast_nhds_top.comp (tendsto_add_atTop_nat _)

variable [TopologicalSpace R]

/--
theorem `summable_pow_mul_prod_one_sub_pow` / 定理 `summable_pow_mul_prod_one_sub_pow`

English:
theorem summable_pow_mul_prod_one_sub_pow
  given: (k : Nat)
  proof: summable_of_tendsto_order_atTop_nhds_top R (tendsto_order_pow_mul_prod_one_sub_pow R k)

中文:
定理 summable_pow_mul_prod_one_sub_pow
  条件: (k : 自然数)
  证明: summable_of_tendsto_order_atTop_nhds_top R (tendsto_order_pow_mul_prod_one_sub_pow R k)

Depends on / 依赖: summable_of_tendsto_order_atTop_nhds_top, tendsto_order_pow_mul_prod_one_sub_pow
-/
theorem summable_pow_mul_prod_one_sub_pow (k : Nat) :
    Summable
      fun n => (X ^ ((k + 1) * n) * ∏ i in Finset.range (n + 1), (1 - X ^ (k + i + 1)) : R⟦X⟧) :=
  summable_of_tendsto_order_atTop_nhds_top R (tendsto_order_pow_mul_prod_one_sub_pow R k)

/--
theorem `multipliable_one_sub_X_pow` / 定理 `multipliable_one_sub_X_pow`

English:
theorem multipliable_one_sub_X_pow
  given: (k : Nat)
  statement: Multipliable fun n => (1 : R⟦X⟧) - X ^ (n + k + 1)
  proof: by
  simpa [sub_eq_add_neg] using
    multipliable_one_add_of_tendsto_order_atTop_nhds_top R (tendsto_order_neg_X_pow R k)

中文:
定理 multipliable_one_sub_X_pow
  条件: (k : 自然数)
  结论: Multipliable fun n => (1 : R⟦X⟧) - X ^ (n + k + 1)
  证明: by
  simpa [sub_eq_add_neg] using
    multipliable_one_add_of_tendsto_order_atTop_nhds_top R (tendsto_order_neg_X_pow R k)

Depends on / 依赖: multipliable_one_add_of_tendsto_order_atTop_nhds_top, sub_eq_add_neg, tendsto_order_neg_X_pow
-/
theorem multipliable_one_sub_X_pow (k : Nat) : Multipliable fun n => (1 : R⟦X⟧) - X ^ (n + k + 1) := by
  simpa [sub_eq_add_neg] using
    multipliable_one_add_of_tendsto_order_atTop_nhds_top R (tendsto_order_neg_X_pow R k)

end Pentagonal

public section Public
namespace PowerSeries

open Classical in
/-- The power series $\sum_{k=-\infty}^{\infty}(-1)^k x^{k * (3k - 1) / 2}$. -/
noncomputable
/--
Definition of `pentagonalSeries` / `pentagonalSeries` 的定义

English:
definition pentagonalSeries
  signature: : R⟦X⟧
  body: .mk fun n => if h : exists k, pentagonal k = n then
    Int.negOnePow h.choose
  else
    0

中文:
定义 pentagonalSeries
  签名: : R⟦X⟧
  定义体: .mk fun n => if h : exists k, pentagonal k = n then
    Int.negOnePow h.choose
  else
    0

Depends on / 依赖: Int.negOnePow, h.choose, negOnePow, pentagonal
-/
def pentagonalSeries : R⟦X⟧ :=
  .mk fun n => if h : exists k, pentagonal k = n then
    Int.negOnePow h.choose
  else
    0

/--
theorem `coeff_pentagonalSeries_eq_zero` / 定理 `coeff_pentagonalSeries_eq_zero`

English:
theorem coeff_pentagonalSeries_eq_zero
  given: {n : Nat} (h : n ∉ Set.range pentagonal)
  proof: dif_neg by simpa using h

@[simp]

中文:
定理 coeff_pentagonalSeries_eq_zero
  条件: {n : 自然数} (h : n ∉ Set.range pentagonal)
  证明: dif_neg by simpa using h

@[simp]

Depends on / 依赖: dif_neg
-/
theorem coeff_pentagonalSeries_eq_zero {n : Nat} (h : n ∉ Set.range pentagonal) :
(pentagonalSeries R).coeff n = 0 := dif_neg by simpa using h

@[simp]
/--
theorem `coeff_pentagonalSeries_pentagonal` / 定理 `coeff_pentagonalSeries_pentagonal`

English:
theorem coeff_pentagonalSeries_pentagonal
  given: (k : Int)
  proof: by
  simp [pentagonalSeries]

@[simp]

中文:
定理 coeff_pentagonalSeries_pentagonal
  条件: (k : 整数)
  证明: by
  simp [pentagonalSeries]

@[simp]

Depends on / 依赖: pentagonalSeries
-/
theorem coeff_pentagonalSeries_pentagonal (k : Int) :
    (pentagonalSeries R).coeff (pentagonal k) = Int.negOnePow k := by
  simp [pentagonalSeries]

@[simp]
/--
theorem `coeff_pentagonalSeries_eq_zero_iff` / 定理 `coeff_pentagonalSeries_eq_zero_iff`

English:
theorem coeff_pentagonalSeries_eq_zero_iff
  given: [Nontrivial R] {n : Nat}
  proof: by
  grind [pentagonalSeries, coeff_mk, neg_one_pow_ne_zero, Int.coe_negOnePow]

中文:
定理 coeff_pentagonalSeries_eq_zero_iff
  条件: [Nontrivial R] {n : 自然数}
  证明: by
  grind [pentagonalSeries, coeff_mk, neg_one_pow_ne_zero, Int.coe_negOnePow]

Depends on / 依赖: Int.coe_negOnePow, coe_negOnePow, coeff_mk, neg_one_pow_ne_zero, pentagonalSeries
-/
theorem coeff_pentagonalSeries_eq_zero_iff [Nontrivial R] {n : Nat} :
    (pentagonalSeries R).coeff n = 0 ↔ n ∉ Set.range pentagonal := by
  grind [pentagonalSeries, coeff_mk, neg_one_pow_ne_zero, Int.coe_negOnePow]

namespace WithPiTopology
variable [TopologicalSpace R]

/--
theorem `hasSum_pentagonalSeries` / 定理 `hasSum_pentagonalSeries`

English:
theorem hasSum_pentagonalSeries
  proof: by
  suffices HasSum ((fun n => C ((pentagonalSeries R).coeff n) * X ^ n) ∘ pentagonal)
      (pentagonalSeries R) by
    convert this
    simp
  rw [pentagonal_injective.hasSum_iff fun n hn => by simp [coeff_pentagonalSeries_eq_zero R hn]]
  simpa [monomial_eq_C_mul_X_pow] using (pentagonalSeries R

中文:
定理 hasSum_pentagonalSeries
  证明: by
  suffices HasSum ((fun n => C ((pentagonalSeries R).coeff n) * X ^ n) ∘ pentagonal)
      (pentagonalSeries R) by
    convert this
    simp
  rw [pentagonal_injective.hasSum_iff fun n hn => by simp [coeff_pentagonalSeries_eq_zero R hn]]
  simpa [monomial_eq_C_mul_X_pow] using (pentagonalSeries R

Depends on / 依赖: HasSum, coeff_pentagonalSeries_eq_zero, convert, hasSum_iff, hasSum_of_monomials_self, monomial_eq_C_mul_X_pow, pentagonal, pentagonalSeries, pentagonal_injective, pentagonal_injective.hasSum_iff
-/
theorem hasSum_pentagonalSeries :
    HasSum (fun k : Int => (Int.negOnePow k : R⟦X⟧) * X ^ pentagonal k) (pentagonalSeries R) := by
  suffices HasSum ((fun n => C ((pentagonalSeries R).coeff n) * X ^ n) ∘ pentagonal)
      (pentagonalSeries R) by
    convert this
    simp
  rw [pentagonal_injective.hasSum_iff fun n hn => by simp [coeff_pentagonalSeries_eq_zero R hn]]
  simpa [monomial_eq_C_mul_X_pow] using (pentagonalSeries R).hasSum_of_monomials_self

/--
theorem `pentagonalSeries_eq_tsum` / 定理 `pentagonalSeries_eq_tsum`

English:
theorem pentagonalSeries_eq_tsum
  given: [T2Space R]
  proof: (hasSum_pentagonalSeries R).tsum_eq.symm

中文:
定理 pentagonalSeries_eq_tsum
  条件: [T2Space R]
  证明: (hasSum_pentagonalSeries R).tsum_eq.symm

Depends on / 依赖: hasSum_pentagonalSeries, tsum_eq, tsum_eq.symm
-/
theorem pentagonalSeries_eq_tsum [T2Space R] :
    pentagonalSeries R = ∑' k, (Int.negOnePow k : R⟦X⟧) * X ^ pentagonal k :=
  (hasSum_pentagonalSeries R).tsum_eq.symm

/--
theorem `hasSum_pow_pentagonal_sub_pentagonalSeries` / 定理 `hasSum_pow_pentagonal_sub_pentagonalSeries`

English:
theorem hasSum_pow_pentagonal_sub_pentagonalSeries
  proof: by
  have h := hasSum_pentagonalSeries R
  rw [← neg_injective.hasSum_iff (fun x hx => by absurd hx; use -x; simp)] at h
  convert h.nat_add_neg_add_one using 2 with k
  simp_rw [Function.comp_apply, neg_neg, Int.negOnePow_add]
  simp
  ring

中文:
定理 hasSum_pow_pentagonal_sub_pentagonalSeries
  证明: by
  have h := hasSum_pentagonalSeries R
  rw [← neg_injective.hasSum_iff (fun x hx => by absurd hx; use -x; simp)] at h
  convert h.nat_add_neg_add_one using 2 with k
  simp_rw [Function.comp_apply, neg_neg, Int.negOnePow_add]
  simp
  ring

Depends on / 依赖: Function, Function.comp_apply, Int.negOnePow_add, absurd, comp_apply, convert, h.nat_add_neg_add_one, hasSum_iff, hasSum_pentagonalSeries, nat_add_neg_add_one, negOnePow_add, neg_injective, neg_injective.hasSum_iff, neg_neg, simp_rw
-/
theorem hasSum_pow_pentagonal_sub_pentagonalSeries :
    HasSum (fun k : Nat => (-1) ^ k * (X ^ pentagonal (-k) - X ^ pentagonal (k + 1)))
      (pentagonalSeries R) := by
  have h := hasSum_pentagonalSeries R
  rw [← neg_injective.hasSum_iff (fun x hx => by absurd hx; use -x; simp)] at h
  convert h.nat_add_neg_add_one using 2 with k
  simp_rw [Function.comp_apply, neg_neg, Int.negOnePow_add]
  simp
  ring

/--
theorem `pentagonalSeries_eq_tsum_pow_pentagonal_sub` / 定理 `pentagonalSeries_eq_tsum_pow_pentagonal_sub`

English:
theorem pentagonalSeries_eq_tsum_pow_pentagonal_sub
  given: [T2Space R]
  proof: (hasSum_pow_pentagonal_sub_pentagonalSeries R).tsum_eq.symm

中文:
定理 pentagonalSeries_eq_tsum_pow_pentagonal_sub
  条件: [T2Space R]
  证明: (hasSum_pow_pentagonal_sub_pentagonalSeries R).tsum_eq.symm

Depends on / 依赖: hasSum_pow_pentagonal_sub_pentagonalSeries, tsum_eq, tsum_eq.symm
-/
theorem pentagonalSeries_eq_tsum_pow_pentagonal_sub [T2Space R] :
    pentagonalSeries R = ∑' (k : Nat), (-1) ^ k * (X ^ pentagonal (-k) - X ^ pentagonal (k + 1)) :=
  (hasSum_pow_pentagonal_sub_pentagonalSeries R).tsum_eq.symm

/--
theorem `tprod_one_sub_X_pow'` / 定理 `tprod_one_sub_X_pow'`

English:
theorem tprod_one_sub_X_pow'
  given: [IsTopologicalRing R] [T2Space R]
  proof: by
  nontriviality R
  rw [pentagonalSeries_eq_tsum_pow_pentagonal_sub]
  refine Pentagonal.tprod_one_sub_pow ?_ ?_ ?_ ?_ ?_
  · rw [IsTopologicallyNilpotent, tendsto_iff_coeff_tendsto]
    refine fun d => tendsto_atTop_of_eventually_const fun i (hi : i >= d + 1) => ?_
    grind
  · exact Pentagonal

中文:
定理 tprod_one_sub_X_pow'
  条件: [IsTopologicalRing R] [T2Space R]
  证明: by
  nontriviality R
  rw [pentagonalSeries_eq_tsum_pow_pentagonal_sub]
  refine Pentagonal.tprod_one_sub_pow ?_ ?_ ?_ ?_ ?_
  · rw [IsTopologicallyNilpotent, tendsto_iff_coeff_tendsto]
    refine fun d => tendsto_atTop_of_eventually_const fun i (hi : i >= d + 1) => ?_
    grind
  · exact Pentagonal
-/
private theorem tprod_one_sub_X_pow' [IsTopologicalRing R] [T2Space R] :
    ∏' n, (1 - X ^ (n + 1) : R⟦X⟧) = pentagonalSeries R := by
  nontriviality R
  rw [pentagonalSeries_eq_tsum_pow_pentagonal_sub]
  refine Pentagonal.tprod_one_sub_pow ?_ ?_ ?_ ?_ ?_
  · rw [IsTopologicallyNilpotent, tendsto_iff_coeff_tendsto]
    refine fun d => tendsto_atTop_of_eventually_const fun i (hi : i >= d + 1) => ?_
    grind
  · exact Pentagonal.summable_pow_mul_prod_one_sub_pow R
  · exact Pentagonal.multipliable_one_sub_X_pow R
  · exact (hasSum_pow_pentagonal_sub_pentagonalSeries R).summable
  · rw [tendsto_iff_coeff_tendsto]
    refine fun n => tendsto_atTop_of_eventually_const fun k (hk : k >= n) => ?_
    rw [map_zero]
    apply coeff_of_lt_order
    grw [← le_order_mul, ← le_order_mul]
    refine (lt_add_of_lt_of_nonneg (lt_add_of_nonneg_of_lt (by simp) ?_) (by simp))
    rw [order_X_pow]; rw [Nat.cast_lt]; rw [← Nat.add_one_le_iff]; rw [Nat.le_div_iff_mul_le (by simp)]
    apply Nat.mul_le_mul <;> linarith

end WithPiTopology

/--
theorem `coeff_prod_one_sub_X_pow_eventually_eq` / 定理 `coeff_prod_one_sub_X_pow_eventually_eq`

English:
theorem coeff_prod_one_sub_X_pow_eventually_eq
  given: (n : Nat)
  proof: by
  let : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  have h := (multipliable_one_sub_X_pow R).hasProd
  rw [tprod_one_sub_X_pow' R]; rw [HasProd]; rw [tendsto_iff_coeff_tendsto] at h
  simpa using h n

中文:
定理 coeff_prod_one_sub_X_pow_eventually_eq
  条件: (n : 自然数)
  证明: by
  let : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  have h := (multipliable_one_sub_X_pow R).hasProd
  rw [tprod_one_sub_X_pow' R]; rw [HasProd]; rw [tendsto_iff_coeff_tendsto] at h
  simpa using h n

Depends on / 依赖: DiscreteTopology, HasProd, TopologicalSpace, hasProd, multipliable_one_sub_X_pow, tendsto_iff_coeff_tendsto, tprod_one_sub_X_pow
-/
theorem coeff_prod_one_sub_X_pow_eventually_eq (n : Nat) :
    forallᶠ s in atTop, (∏ n in s, (1 - X ^ (n + 1) : R⟦X⟧)).coeff n = (pentagonalSeries R).coeff n := by
  let : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  have h := (multipliable_one_sub_X_pow R).hasProd
  rw [tprod_one_sub_X_pow' R]; rw [HasProd]; rw [tendsto_iff_coeff_tendsto] at h
  simpa using h n

namespace WithPiTopology
variable [TopologicalSpace R]

/--
theorem `hasProd_one_sub_X_pow` / 定理 `hasProd_one_sub_X_pow`

English:
theorem hasProd_one_sub_X_pow
  proof: by
  rw [HasProd]; rw [tendsto_iff_coeff_tendsto]
  intro n
  apply tendsto_nhds_of_eventually_eq
  simpa using coeff_prod_one_sub_X_pow_eventually_eq R n

中文:
定理 hasProd_one_sub_X_pow
  证明: by
  rw [HasProd]; rw [tendsto_iff_coeff_tendsto]
  intro n
  apply tendsto_nhds_of_eventually_eq
  simpa using coeff_prod_one_sub_X_pow_eventually_eq R n

Depends on / 依赖: HasProd, coeff_prod_one_sub_X_pow_eventually_eq, tendsto_iff_coeff_tendsto, tendsto_nhds_of_eventually_eq
-/
theorem hasProd_one_sub_X_pow :
    HasProd (fun n => (1 - X ^ (n + 1) : R⟦X⟧)) (pentagonalSeries R) := by
  rw [HasProd]; rw [tendsto_iff_coeff_tendsto]
  intro n
  apply tendsto_nhds_of_eventually_eq
  simpa using coeff_prod_one_sub_X_pow_eventually_eq R n

/--
theorem `tprod_one_sub_X_pow` / 定理 `tprod_one_sub_X_pow`

English:
theorem tprod_one_sub_X_pow
  given: [T2Space R]
  statement: ∏' n, (1 - X ^ (n + 1) : R⟦X⟧) = pentagonalSeries R
  proof: (hasProd_one_sub_X_pow R).tprod_eq

中文:
定理 tprod_one_sub_X_pow
  条件: [T2Space R]
  结论: ∏' n, (1 - X ^ (n + 1) : R⟦X⟧) = pentagonalSeries R
  证明: (hasProd_one_sub_X_pow R).tprod_eq

Depends on / 依赖: hasProd_one_sub_X_pow, tprod_eq
-/
theorem tprod_one_sub_X_pow [T2Space R] : ∏' n, (1 - X ^ (n + 1) : R⟦X⟧) = pentagonalSeries R :=
  (hasProd_one_sub_X_pow R).tprod_eq

end WithPiTopology
end PowerSeries
end Public
