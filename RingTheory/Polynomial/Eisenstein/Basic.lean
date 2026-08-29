/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
public import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Eisenstein polynomials

Given an ideal `𝓟` of a commutative semiring `R`, we say that a polynomial `f : R[X]` is
*Eisenstein at `𝓟`* if `f.leadingCoeff ∉ 𝓟`, `∀ n, n < f.natDegree → f.coeff n ∈ 𝓟` and
`f.coeff 0 ∉ 𝓟 ^ 2`. In this file we gather miscellaneous results about Eisenstein polynomials.

## Main definitions
* `Polynomial.IsEisensteinAt f 𝓟`: the property of being Eisenstein at `𝓟`.

## Main results
* `Polynomial.IsEisensteinAt.irreducible`: if a primitive `f` satisfies `f.IsEisensteinAt 𝓟`,
  where `𝓟.IsPrime`, then `f` is irreducible.

## Implementation details
We also define a notion `IsWeaklyEisensteinAt` requiring only that
`∀ n < f.natDegree → f.coeff n ∈ 𝓟`. This makes certain results slightly more general and it is
useful since it is sometimes better behaved (for example it is stable under `Polynomial.map`).

-/

public section


universe u v w z

variable {R : Type u}

open Ideal Algebra Finset

open Polynomial

namespace Polynomial

/-- Given an ideal `𝓟` of a commutative semiring `R`, we say that a polynomial `f : R[X]`
is *weakly Eisenstein at `𝓟`* if `∀ n, n < f.natDegree → f.coeff n ∈ 𝓟`. -/
@[mk_iff]
/--
Definition of `IsWeaklyEisensteinAt` / `IsWeaklyEisensteinAt` 的定义

English:
structure IsWeaklyEisensteinAt
  parameters: [CommSemiring R] (f : R[X]) (𝓟 : Ideal R)
  axioms and operations (1):
    - mem : forall {n}, n < f.natDegree -> f.coeff n in 𝓟

中文:
结构 IsWeaklyEisensteinAt
  参数: [CommSemiring R] (f : R[X]) (𝓟 : Ideal R)
  公理与运算 (1 个):
    - mem : 对任意 {n}, n < f.natDegree -> f.coeff n in 𝓟
-/
structure IsWeaklyEisensteinAt [CommSemiring R] (f : R[X]) (𝓟 : Ideal R) : Prop where
  mem : forall {n}, n < f.natDegree -> f.coeff n in 𝓟

/-- Given an ideal `𝓟` of a commutative semiring `R`, we say that a polynomial `f : R[X]`
is *Eisenstein at `𝓟`* if `f.leadingCoeff ∉ 𝓟`, `∀ n, n < f.natDegree → f.coeff n ∈ 𝓟` and
`f.coeff 0 ∉ 𝓟 ^ 2`. -/
@[mk_iff]
/--
Definition of `IsEisensteinAt` / `IsEisensteinAt` 的定义

English:
structure IsEisensteinAt
  parameters: [CommSemiring R] (f : R[X]) (𝓟 : Ideal R)
  axioms and operations (3):
    - leading : f.leadingCoeff ∉ 𝓟
    - mem : forall {n}, n < f.natDegree -> f.coeff n in 𝓟
    - notMem : f.coeff 0 ∉ 𝓟 ^ 2

中文:
结构 IsEisensteinAt
  参数: [CommSemiring R] (f : R[X]) (𝓟 : Ideal R)
  公理与运算 (3 个):
    - leading : f.leadingCoeff ∉ 𝓟
    - mem : 对任意 {n}, n < f.natDegree -> f.coeff n in 𝓟
    - notMem : f.coeff 0 ∉ 𝓟 ^ 2

Depends on / 依赖: IsOrderedMonoid, IsOrderedMonoid.to_hasUpperLowerClosure, to_hasUpperLowerClosure
-/
structure IsEisensteinAt [CommSemiring R] (f : R[X]) (𝓟 : Ideal R) : Prop where
  leading : f.leadingCoeff ∉ 𝓟
  mem : forall {n}, n < f.natDegree -> f.coeff n in 𝓟
  notMem : f.coeff 0 ∉ 𝓟 ^ 2

namespace IsWeaklyEisensteinAt

section CommSemiring

variable [CommSemiring R] {𝓟 : Ideal R} {f f' : R[X]}

/--
theorem `map` / 定理 `map`

English:
theorem map
  given: (hf : f.IsWeaklyEisensteinAt 𝓟) {A : Type v} [CommSemiring A] (φ : R ->+* A)
  proof: by
  refine (isWeaklyEisensteinAt_iff _ _).2 fun hn => ?_
  rw [coeff_map]
  exact mem_map_of_mem _ (hf.mem (lt_of_lt_of_le hn natDegree_map_le))

中文:
定理 map
  条件: (hf : f.IsWeaklyEisensteinAt 𝓟) {A : 类型v} [CommSemiring A] (φ : R ->+* A)
  证明: by
  refine (isWeaklyEisensteinAt_iff _ _).2 fun hn => ?_
  rw [coeff_map]
  exact mem_map_of_mem _ (hf.mem (lt_of_lt_of_le hn natDegree_map_le))

Depends on / 依赖: coeff_map, hf.mem, isWeaklyEisensteinAt_iff, lt_of_lt_of_le, mem_map_of_mem, natDegree_map_le
-/
theorem map (hf : f.IsWeaklyEisensteinAt 𝓟) {A : Type v} [CommSemiring A] (φ : R ->+* A) :
    (f.map φ).IsWeaklyEisensteinAt (𝓟.map φ) := by
  refine (isWeaklyEisensteinAt_iff _ _).2 fun hn => ?_
  rw [coeff_map]
  exact mem_map_of_mem _ (hf.mem (lt_of_lt_of_le hn natDegree_map_le))

/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  given: (hf : f.IsWeaklyEisensteinAt 𝓟) (hf' : f'.IsWeaklyEisensteinAt 𝓟)
  proof: by
  rw [isWeaklyEisensteinAt_iff] at hf hf' ⊢
  intro n hn
  rw [coeff_mul]
  refine sum_mem _ fun x hx => ?_
  rcases lt_or_ge x.1 f.natDegree with hx1 | hx1
  · exact mul_mem_right _ _ (hf hx1)
  replace hx1 : x.2 < f'.natDegree := by
    by_contra!
    rw [HasAntidiagonal.mem_antidiagonal] at hx

中文:
定理 mul
  条件: (hf : f.IsWeaklyEisensteinAt 𝓟) (hf' : f'.IsWeaklyEisensteinAt 𝓟)
  证明: by
  rw [isWeaklyEisensteinAt_iff] at hf hf' ⊢
  intro n hn
  rw [coeff_mul]
  refine sum_mem _ fun x hx => ?_
  rcases lt_or_ge x.1 f.natDegree with hx1 | hx1
  · exact mul_mem_right _ _ (hf hx1)
  replace hx1 : x.2 < f'.natDegree := by
    by_contra!
    rw [HasAntidiagonal.mem_antidiagonal] at hx

Depends on / 依赖: ContinuousSMul, HasAntidiagonal, HasAntidiagonal.mem_antidiagonal, ProperSMul, ProperSMul.toContinuousSMul, coeff_mul, f.natDegree, hn.trans_le, isWeaklyEisensteinAt_iff, lt_or_ge, mem_antidiagonal, mul_mem_left, mul_mem_right, natDegree, natDegree_mul_le, replace, sum_mem, toContinuousSMul, trans_le
-/
theorem mul (hf : f.IsWeaklyEisensteinAt 𝓟) (hf' : f'.IsWeaklyEisensteinAt 𝓟) :
    (f * f').IsWeaklyEisensteinAt 𝓟 := by
  rw [isWeaklyEisensteinAt_iff] at hf hf' ⊢
  intro n hn
  rw [coeff_mul]
  refine sum_mem _ fun x hx => ?_
  rcases lt_or_ge x.1 f.natDegree with hx1 | hx1
  · exact mul_mem_right _ _ (hf hx1)
  replace hx1 : x.2 < f'.natDegree := by
    by_contra!
    rw [HasAntidiagonal.mem_antidiagonal] at hx
    replace hn := hn.trans_le natDegree_mul_le
    linarith
  exact mul_mem_left _ _ (hf' hx1)

end CommSemiring

section CommRing

variable [CommRing R] {𝓟 : Ideal R} {f : R[X]}
variable {S : Type v} [CommRing S] [Algebra R S]

section Principal

variable {p : R}

/--
theorem `exists_mem_adjoin_mul_eq_pow_natDegree` / 定理 `exists_mem_adjoin_mul_eq_pow_natDegree`

English:
theorem exists_mem_adjoin_mul_eq_pow_natDegree
  statement: {x : S} (hx : aeval x f = 0) (hmo : f.Monic)
  proof: by
  rw [aeval_def]; rw [Polynomial.eval₂_eq_eval_map]; rw [eval_eq_sum_range]; rw [range_add_one]; rw [sum_insert notMem_range_self]; rw [sum_range]; rw [(hmo.map (algebraMap R S)).coeff_natDegree]; rw [one_mul] at hx
  replace hx := eq_neg_of_add_eq_zero_left hx
  have : forall n < f.natDegree, p 

中文:
定理 exists_mem_adjoin_mul_eq_pow_natDegree
  结论: {x : S} (hx : aeval x f = 0) (hmo : f.Monic)
  证明: by
  rw [aeval_def]; rw [Polynomial.eval₂_eq_eval_map]; rw [eval_eq_sum_range]; rw [range_add_one]; rw [sum_insert notMem_range_self]; rw [sum_range]; rw [(hmo.map (algebraMap R S)).coeff_natDegree]; rw [one_mul] at hx
  replace hx := eq_neg_of_add_eq_zero_left hx
  have : forall n < f.natDegree, p 

Depends on / 依赖: Polynomial, Polynomial.eval, aeval_def, algebraMap, coeff_map, coeff_natDegree, conv_rhs, eq_neg_of_add_eq_zero_left, eval_eq_sum_range, f.coeff, f.natDegree, hf.mem, hmo.map, lt_of_lt_of_le, mem_span_singleton, natDegree, notMem_range_self, one_mul, range_add_one, replace
-/
theorem exists_mem_adjoin_mul_eq_pow_natDegree {x : S} (hx : aeval x f = 0) (hmo : f.Monic)
    (hf : f.IsWeaklyEisensteinAt (Submodule.span R {p})) : exists y in adjoin R ({x} : Set S),
    (algebraMap R S) p * y = x ^ (f.map (algebraMap R S)).natDegree := by
  rw [aeval_def]; rw [Polynomial.eval₂_eq_eval_map]; rw [eval_eq_sum_range]; rw [range_add_one]; rw [sum_insert notMem_range_self]; rw [sum_range]; rw [(hmo.map (algebraMap R S)).coeff_natDegree]; rw [one_mul] at hx
  replace hx := eq_neg_of_add_eq_zero_left hx
  have : forall n < f.natDegree, p ∣ f.coeff n := by
    intro n hn
    exact mem_span_singleton.1 (by simpa using hf.mem hn)
  choose! φ hφ using this
  conv_rhs at hx =>
    congr
    congr
    · skip
    ext i
    rw [coeff_map]; rw [hφ i.1 (lt_of_lt_of_le i.2 natDegree_map_le)]; rw [map_mul]; rw [mul_assoc]
  rw [hx]; rw [← mul_sum]; rw [neg_eq_neg_one_mul]; rw [← mul_assoc (-1 : S)]; rw [mul_comm (-1 : S)]; rw [mul_assoc]
  refine
    ⟨-1 * ∑ i : Fin (f.map (algebraMap R S)).natDegree, (algebraMap R S) (φ i.1) * x ^ i.1, ?_, rfl⟩
  exact
    Subalgebra.mul_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _))
      (Subalgebra.sum_mem _ fun i _ =>
        Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
          (Subalgebra.pow_mem _ (subset_adjoin (Set.mem_singleton x)) _))

/--
theorem `exists_mem_adjoin_mul_eq_pow_natDegree_le` / 定理 `exists_mem_adjoin_mul_eq_pow_natDegree_le`

English:
theorem exists_mem_adjoin_mul_eq_pow_natDegree_le
  statement: {x : S} (hx : aeval x f = 0) (hmo : f.Monic)
  proof: by
  intro i hi
  obtain ⟨k, hk⟩ := exists_add_of_le hi
  rw [hk]; rw [pow_add]
  obtain ⟨y, hy, H⟩ := exists_mem_adjoin_mul_eq_pow_natDegree hx hmo hf
  refine ⟨y * x ^ k, ?_, ?_⟩
  · exact Subalgebra.mul_mem _ hy (Subalgebra.pow_mem _ (subset_adjoin (Set.mem_singleton x)) _)
  · rw [← mul_assoc _ 

中文:
定理 exists_mem_adjoin_mul_eq_pow_natDegree_le
  结论: {x : S} (hx : aeval x f = 0) (hmo : f.Monic)
  证明: by
  intro i hi
  obtain ⟨k, hk⟩ := exists_add_of_le hi
  rw [hk]; rw [pow_add]
  obtain ⟨y, hy, H⟩ := exists_mem_adjoin_mul_eq_pow_natDegree hx hmo hf
  refine ⟨y * x ^ k, ?_, ?_⟩
  · exact Subalgebra.mul_mem _ hy (Subalgebra.pow_mem _ (subset_adjoin (Set.mem_singleton x)) _)
  · rw [← mul_assoc _ 

Depends on / 依赖: Set.mem_singleton, Subalgebra, Subalgebra.mul_mem, Subalgebra.pow_mem, exists_add_of_le, exists_mem_adjoin_mul_eq_pow_natDegree, mem_singleton, mul_assoc, mul_mem, pow_add, pow_mem, subset_adjoin
-/
theorem exists_mem_adjoin_mul_eq_pow_natDegree_le {x : S} (hx : aeval x f = 0) (hmo : f.Monic)
    (hf : f.IsWeaklyEisensteinAt (Submodule.span R {p})) :
    forall i, (f.map (algebraMap R S)).natDegree <= i ->
        exists y in adjoin R ({x} : Set S), (algebraMap R S) p * y = x ^ i := by
  intro i hi
  obtain ⟨k, hk⟩ := exists_add_of_le hi
  rw [hk]; rw [pow_add]
  obtain ⟨y, hy, H⟩ := exists_mem_adjoin_mul_eq_pow_natDegree hx hmo hf
  refine ⟨y * x ^ k, ?_, ?_⟩
  · exact Subalgebra.mul_mem _ hy (Subalgebra.pow_mem _ (subset_adjoin (Set.mem_singleton x)) _)
  · rw [← mul_assoc _ y, H]

end Principal

/--
theorem `pow_natDegree_le_of_root_of_monic_mem` / 定理 `pow_natDegree_le_of_root_of_monic_mem`

English:
theorem pow_natDegree_le_of_root_of_monic_mem
  statement: (hf : f.IsWeaklyEisensteinAt 𝓟)
  proof: by
  intro i hi
  obtain ⟨k, hk⟩ := exists_add_of_le hi
  rw [hk]; rw [pow_add]
  suffices x ^ f.natDegree in 𝓟 by exact mul_mem_right (x ^ k) 𝓟 this
  rw [IsRoot.def]; rw [eval_eq_sum_range]; rw [Finset.range_add_one]; rw [Finset.sum_insert Finset.notMem_range_self]; rw [Finset.sum_range]; rw [hmo.

中文:
定理 pow_natDegree_le_of_root_of_monic_mem
  结论: (hf : f.IsWeaklyEisensteinAt 𝓟)
  证明: by
  intro i hi
  obtain ⟨k, hk⟩ := exists_add_of_le hi
  rw [hk]; rw [pow_add]
  suffices x ^ f.natDegree in 𝓟 by exact mul_mem_right (x ^ k) 𝓟 this
  rw [IsRoot.def]; rw [eval_eq_sum_range]; rw [Finset.range_add_one]; rw [Finset.sum_insert Finset.notMem_range_self]; rw [Finset.sum_range]; rw [hmo.

Depends on / 依赖: Fin.is_lt, Finset, Finset.notMem_range_self, Finset.range_add_one, Finset.sum_insert, Finset.sum_range, IsRoot, IsRoot.def, Submodule, Submodule.sum_mem, coeff_natDegree, eq_neg_of_add_eq_zero_left, eval_eq_sum_range, exists_add_of_le, f.natDegree, hf.mem, hmo.coeff_natDegree, is_lt, mul_mem_right, natDegree
-/
theorem pow_natDegree_le_of_root_of_monic_mem (hf : f.IsWeaklyEisensteinAt 𝓟)
    {x : R} (hroot : IsRoot f x) (hmo : f.Monic) :
    forall i, f.natDegree <= i -> x ^ i in 𝓟 := by
  intro i hi
  obtain ⟨k, hk⟩ := exists_add_of_le hi
  rw [hk]; rw [pow_add]
  suffices x ^ f.natDegree in 𝓟 by exact mul_mem_right (x ^ k) 𝓟 this
  rw [IsRoot.def]; rw [eval_eq_sum_range]; rw [Finset.range_add_one]; rw [Finset.sum_insert Finset.notMem_range_self]; rw [Finset.sum_range]; rw [hmo.coeff_natDegree]; rw [one_mul] at
    *
  rw [eq_neg_of_add_eq_zero_left hroot]; rw [neg_mem_iff]
  exact Submodule.sum_mem _ fun i _ => mul_mem_right _ _ (hf.mem (Fin.is_lt i))

/--
theorem `pow_natDegree_le_of_aeval_zero_of_monic_mem_map` / 定理 `pow_natDegree_le_of_aeval_zero_of_monic_mem_map`

English:
theorem pow_natDegree_le_of_aeval_zero_of_monic_mem_map
  statement: (hf : f.IsWeaklyEisensteinAt 𝓟)
  proof: by
  suffices x ^ (f.map (algebraMap R S)).natDegree in 𝓟.map (algebraMap R S) by
    intro i hi
    obtain ⟨k, hk⟩ := exists_add_of_le hi
    rw [hk]; rw [pow_add]
    exact mul_mem_right _ _ this
  rw [aeval_def]; rw [eval₂_eq_eval_map]; rw [← IsRoot.def] at hx
  exact pow_natDegree_le_of_root_of_

中文:
定理 pow_natDegree_le_of_aeval_zero_of_monic_mem_map
  结论: (hf : f.IsWeaklyEisensteinAt 𝓟)
  证明: by
  suffices x ^ (f.map (algebraMap R S)).natDegree in 𝓟.map (algebraMap R S) by
    intro i hi
    obtain ⟨k, hk⟩ := exists_add_of_le hi
    rw [hk]; rw [pow_add]
    exact mul_mem_right _ _ this
  rw [aeval_def]; rw [eval₂_eq_eval_map]; rw [← IsRoot.def] at hx
  exact pow_natDegree_le_of_root_of_

Depends on / 依赖: IsRoot, IsRoot.def, aeval_def, algebraMap, exists_add_of_le, f.map, hf.map, hmo.map, mul_mem_right, natDegree, pow_add, pow_natDegree_le_of_root_of_monic_mem, rfl.le
-/
theorem pow_natDegree_le_of_aeval_zero_of_monic_mem_map (hf : f.IsWeaklyEisensteinAt 𝓟)
    {x : S} (hx : aeval x f = 0) (hmo : f.Monic) :
    forall i, (f.map (algebraMap R S)).natDegree <= i -> x ^ i in 𝓟.map (algebraMap R S) := by
  suffices x ^ (f.map (algebraMap R S)).natDegree in 𝓟.map (algebraMap R S) by
    intro i hi
    obtain ⟨k, hk⟩ := exists_add_of_le hi
    rw [hk]; rw [pow_add]
    exact mul_mem_right _ _ this
  rw [aeval_def]; rw [eval₂_eq_eval_map]; rw [← IsRoot.def] at hx
  exact pow_natDegree_le_of_root_of_monic_mem (hf.map _) hx (hmo.map _) _ rfl.le

end CommRing

end IsWeaklyEisensteinAt

section ScaleRoots

variable {A : Type*} [CommRing R] [CommRing A]

/--
theorem `scaleRoots.isWeaklyEisensteinAt` / 定理 `scaleRoots.isWeaklyEisensteinAt`

English:
theorem scaleRoots.isWeaklyEisensteinAt
  given: (p : R[X]) {x : R} {P : Ideal R} (hP : x in P)
  proof: by
  refine ⟨fun i => ?_⟩
  rw [coeff_scaleRoots]
  rw [natDegree_scaleRoots]; rw [← tsub_pos_iff_lt] at i
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem P hP _ i)

中文:
定理 scaleRoots.isWeaklyEisensteinAt
  条件: (p : R[X]) {x : R} {P : Ideal R} (hP : x in P)
  证明: by
  refine ⟨fun i => ?_⟩
  rw [coeff_scaleRoots]
  rw [natDegree_scaleRoots]; rw [← tsub_pos_iff_lt] at i
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem P hP _ i)

Depends on / 依赖: Ideal.mul_mem_left, Ideal.pow_mem_of_mem, coeff_scaleRoots, mul_mem_left, natDegree_scaleRoots, pow_mem_of_mem, tsub_pos_iff_lt
-/
theorem scaleRoots.isWeaklyEisensteinAt (p : R[X]) {x : R} {P : Ideal R} (hP : x in P) :
    (scaleRoots p x).IsWeaklyEisensteinAt P := by
  refine ⟨fun i => ?_⟩
  rw [coeff_scaleRoots]
  rw [natDegree_scaleRoots]; rw [← tsub_pos_iff_lt] at i
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem P hP _ i)

/--
theorem `dvd_pow_natDegree_of_eval₂_eq_zero` / 定理 `dvd_pow_natDegree_of_eval₂_eq_zero`

English:
theorem dvd_pow_natDegree_of_eval₂_eq_zero
  statement: {f : R ->+* A} (hf : Function.Injective f) {p : R[X]}
  proof: by
  rw [← natDegree_scaleRoots p x]; rw [← Ideal.mem_span_singleton]
  refine
    (scaleRoots.isWeaklyEisensteinAt _
          (Ideal.mem_span_singleton.mpr <| dvd_refl x)).pow_natDegree_le_of_root_of_monic_mem
      ?_ ((monic_scaleRoots_iff x).mpr hp) _ le_rfl
  rw [injective_iff_map_eq_zero'] at

中文:
定理 dvd_pow_natDegree_of_eval₂_eq_zero
  结论: {f : R ->+* A} (hf : Function.Injective f) {p : R[X]}
  证明: by
  rw [← natDegree_scaleRoots p x]; rw [← Ideal.mem_span_singleton]
  refine
    (scaleRoots.isWeaklyEisensteinAt _
          (Ideal.mem_span_singleton.mpr <| dvd_refl x)).pow_natDegree_le_of_root_of_monic_mem
      ?_ ((monic_scaleRoots_iff x).mpr hp) _ le_rfl
  rw [injective_iff_map_eq_zero'] at

Depends on / 依赖: H.subtype, H_closed, H_closed.isClosedEmbedding_subtypeVal, Ideal.mem_span_singleton, Ideal.mem_span_singleton.mpr, Polynomial, Polynomial.eval, dvd_refl, injective_iff_map_eq_zero, isClosedEmbedding_subtypeVal, isWeaklyEisensteinAt, le_rfl, mem_span_singleton, monic_scaleRoots_iff, natDegree_scaleRoots, p.scaleRoots, pow_natDegree_le_of_root_of_monic_mem, properSMul_of_isClosedEmbedding, scaleRoots, scaleRoots.isWeaklyEisensteinAt
-/
theorem dvd_pow_natDegree_of_eval₂_eq_zero {f : R ->+* A} (hf : Function.Injective f) {p : R[X]}
    (hp : p.Monic) (x y : R) (z : A) (h : p.eval₂ f z = 0) (hz : f x * z = f y) :
    x ∣ y ^ p.natDegree := by
  rw [← natDegree_scaleRoots p x]; rw [← Ideal.mem_span_singleton]
  refine
    (scaleRoots.isWeaklyEisensteinAt _
          (Ideal.mem_span_singleton.mpr <| dvd_refl x)).pow_natDegree_le_of_root_of_monic_mem
      ?_ ((monic_scaleRoots_iff x).mpr hp) _ le_rfl
  rw [injective_iff_map_eq_zero'] at hf
  have : eval₂ f _ (p.scaleRoots x) = 0 := scaleRoots_eval₂_eq_zero f h
  rwa [hz, Polynomial.eval₂_at_apply, hf] at this

/--
theorem `dvd_pow_natDegree_of_aeval_eq_zero` / 定理 `dvd_pow_natDegree_of_aeval_eq_zero`

English:
theorem dvd_pow_natDegree_of_aeval_eq_zero
  statement: [IsDomain R] [Algebra R A] [Nontrivial A]
  proof: dvd_pow_natDegree_of_eval₂_eq_zero (FaithfulSMul.algebraMap_injective R A) hp x y z h
    ((mul_comm _ _).trans hz)

中文:
定理 dvd_pow_natDegree_of_aeval_eq_zero
  结论: [IsDomain R] [Algebra R A] [Nontrivial A]
  证明: dvd_pow_natDegree_of_eval₂_eq_zero (FaithfulSMul.algebraMap_injective R A) hp x y z h
    ((mul_comm _ _).trans hz)

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, mul_comm
-/
theorem dvd_pow_natDegree_of_aeval_eq_zero [IsDomain R] [Algebra R A] [Nontrivial A]
    [Module.IsTorsionFree R A] {p : R[X]} (hp : p.Monic) (x y : R) (z : A) (h : p.aeval z = 0)
    (hz : z * algebraMap R A x = algebraMap R A y) : x ∣ y ^ p.natDegree :=
  dvd_pow_natDegree_of_eval₂_eq_zero (FaithfulSMul.algebraMap_injective R A) hp x y z h
    ((mul_comm _ _).trans hz)

end ScaleRoots

namespace IsEisensteinAt

section CommSemiring

variable [CommSemiring R] {𝓟 : Ideal R} {f : R[X]}

/--
theorem `_root_.Polynomial.Monic.leadingCoeff_notMem` / 定理 `_root_.Polynomial.Monic.leadingCoeff_notMem`

English:
theorem _root_.Polynomial.Monic.leadingCoeff_notMem
  given: (hf : f.Monic) (h : 𝓟 != ⊤)
  proof: hf.leadingCoeff.symm ▸ (Ideal.ne_top_iff_one _).1 h

中文:
定理 _root_.Polynomial.Monic.leadingCoeff_notMem
  条件: (hf : f.Monic) (h : 𝓟 != ⊤)
  证明: hf.leadingCoeff.symm ▸ (Ideal.ne_top_iff_one _).1 h

Depends on / 依赖: Ideal.ne_top_iff_one, hf.leadingCoeff.symm, leadingCoeff, ne_top_iff_one
-/
theorem _root_.Polynomial.Monic.leadingCoeff_notMem (hf : f.Monic) (h : 𝓟 != ⊤) :
    f.leadingCoeff ∉ 𝓟 := hf.leadingCoeff.symm ▸ (Ideal.ne_top_iff_one _).1 h

/--
theorem `_root_.Polynomial.Monic.isEisensteinAt_of_mem_of_notMem` / 定理 `_root_.Polynomial.Monic.isEisensteinAt_of_mem_of_notMem`

English:
theorem _root_.Polynomial.Monic.isEisensteinAt_of_mem_of_notMem
  statement: (hf : f.Monic) (h : 𝓟 != ⊤)
  proof: { leading := Polynomial.Monic.leadingCoeff_notMem hf h
    mem := fun hn => hmem hn
    notMem := hnotMem }

中文:
定理 _root_.Polynomial.Monic.isEisensteinAt_of_mem_of_notMem
  结论: (hf : f.Monic) (h : 𝓟 != ⊤)
  证明: { leading := Polynomial.Monic.leadingCoeff_notMem hf h
    mem := fun hn => hmem hn
    notMem := hnotMem }

Depends on / 依赖: Polynomial, Polynomial.Monic.leadingCoeff_notMem, hnotMem, leading, leadingCoeff_notMem, notMem
-/
theorem _root_.Polynomial.Monic.isEisensteinAt_of_mem_of_notMem (hf : f.Monic) (h : 𝓟 != ⊤)
    (hmem : forall {n}, n < f.natDegree -> f.coeff n in 𝓟) (hnotMem : f.coeff 0 ∉ 𝓟 ^ 2) :
    f.IsEisensteinAt 𝓟 :=
  { leading := Polynomial.Monic.leadingCoeff_notMem hf h
    mem := fun hn => hmem hn
    notMem := hnotMem }

/--
theorem `isWeaklyEisensteinAt` / 定理 `isWeaklyEisensteinAt`

English:
theorem isWeaklyEisensteinAt
  given: (hf : f.IsEisensteinAt 𝓟)
  statement: IsWeaklyEisensteinAt f 𝓟
  proof: ⟨fun h => hf.mem h⟩

中文:
定理 isWeaklyEisensteinAt
  条件: (hf : f.IsEisensteinAt 𝓟)
  结论: IsWeaklyEisensteinAt f 𝓟
  证明: ⟨fun h => hf.mem h⟩

Depends on / 依赖: hf.mem
-/
theorem isWeaklyEisensteinAt (hf : f.IsEisensteinAt 𝓟) : IsWeaklyEisensteinAt f 𝓟 :=
  ⟨fun h => hf.mem h⟩

/--
theorem `coeff_mem` / 定理 `coeff_mem`

English:
theorem coeff_mem
  given: (hf : f.IsEisensteinAt 𝓟) {n : Nat} (hn : n != f.natDegree)
  statement: f.coeff n in 𝓟
  proof: by
  rcases ne_iff_lt_or_gt.1 hn with h₁ | h₂
  · exact hf.mem h₁
  · rw [coeff_eq_zero_of_natDegree_lt h₂]
    exact Ideal.zero_mem _

中文:
定理 coeff_mem
  条件: (hf : f.IsEisensteinAt 𝓟) {n : 自然数} (hn : n != f.natDegree)
  结论: f.coeff n in 𝓟
  证明: by
  rcases ne_iff_lt_or_gt.1 hn with h₁ | h₂
  · exact hf.mem h₁
  · rw [coeff_eq_zero_of_natDegree_lt h₂]
    exact Ideal.zero_mem _

Depends on / 依赖: Ideal.zero_mem, coeff_eq_zero_of_natDegree_lt, hf.mem, ne_iff_lt_or_gt, zero_mem
-/
theorem coeff_mem (hf : f.IsEisensteinAt 𝓟) {n : Nat} (hn : n != f.natDegree) : f.coeff n in 𝓟 := by
  rcases ne_iff_lt_or_gt.1 hn with h₁ | h₂
  · exact hf.mem h₁
  · rw [coeff_eq_zero_of_natDegree_lt h₂]
    exact Ideal.zero_mem _

end CommSemiring

section IsDomain

variable [CommRing R] [IsDomain R] {𝓟 : Ideal R} {f : R[X]}

/--
theorem `irreducible` / 定理 `irreducible`

English:
theorem irreducible
  statement: (hf : f.IsEisensteinAt 𝓟) (hprime : 𝓟.IsPrime) (hu : f.IsPrimitive)
  proof: irreducible_of_eisenstein_criterion hprime hf.leading (fun _ hn => hf.mem (coe_lt_degree.1 hn))
    (natDegree_pos_iff_degree_pos.1 hfd0) hf.notMem hu

中文:
定理 irreducible
  结论: (hf : f.IsEisensteinAt 𝓟) (hprime : 𝓟.IsPrime) (hu : f.IsPrimitive)
  证明: irreducible_of_eisenstein_criterion hprime hf.leading (fun _ hn => hf.mem (coe_lt_degree.1 hn))
    (natDegree_pos_iff_degree_pos.1 hfd0) hf.notMem hu

Depends on / 依赖: coe_lt_degree, hf.leading, hf.mem, hf.notMem, hprime, irreducible_of_eisenstein_criterion, leading, natDegree_pos_iff_degree_pos, notMem
-/
theorem irreducible (hf : f.IsEisensteinAt 𝓟) (hprime : 𝓟.IsPrime) (hu : f.IsPrimitive)
    (hfd0 : 0 < f.natDegree) : Irreducible f :=
  irreducible_of_eisenstein_criterion hprime hf.leading (fun _ hn => hf.mem (coe_lt_degree.1 hn))
    (natDegree_pos_iff_degree_pos.1 hfd0) hf.notMem hu

end IsDomain

end IsEisensteinAt

end Polynomial
