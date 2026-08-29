/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Cyclotomic polynomials.

For `n : ℕ` and an integral domain `R`, we define a modified version of the `n`-th cyclotomic
polynomial with coefficients in `R`, denoted `cyclotomic' n R`, as `∏ (X - μ)`, where `μ` varies
over the primitive `n`th roots of unity. If there is a primitive `n`th root of unity in `R` then
this is the standard definition. We then define the standard cyclotomic polynomial `cyclotomic n R`
with coefficients in any ring `R`.

## Main definition

* `cyclotomic n R` : the `n`-th cyclotomic polynomial with coefficients in `R`.

## Main results

* `Polynomial.degree_cyclotomic` : The degree of `cyclotomic n` is `totient n`.
* `Polynomial.prod_cyclotomic_eq_X_pow_sub_one` : `X ^ n - 1 = ∏ (cyclotomic i)`, where `i`
  divides `n`.
* `Polynomial.cyclotomic_eq_prod_X_pow_sub_one_pow_moebius` : The Möbius inversion formula for
  `cyclotomic n R` over an abstract fraction field for `R[X]`.

## Implementation details

Our definition of `cyclotomic' n R` makes sense in any integral domain `R`, but the interesting
results hold if there is a primitive `n`-th root of unity in `R`. In particular, our definition is
not the standard one unless there is a primitive `n`th root of unity in `R`. For example,
`cyclotomic' 3 ℤ = 1`, since there are no primitive cube roots of unity in `ℤ`. The main example is
`R = ℂ`, we decided to work in general since the difficulties are essentially the same.
To get the standard cyclotomic polynomials, we use `unique_int_coeff_of_cycl`, with `R = ℂ`,
to get a polynomial with integer coefficients and then we map it to `R[X]`, for any ring `R`.
-/

@[expose] public section


open scoped Polynomial

noncomputable section

universe u

namespace Polynomial

section Cyclotomic'

section IsDomain

variable {R : Type*} [CommRing R] [IsDomain R]

/--
Definition of `cyclotomic'` / `cyclotomic'` 的定义

English:
definition cyclotomic'
  signature: (n : Nat) (R : Type*) [CommRing R] [IsDomain R]
  body: ∏ μ in primitiveRoots n R, (X - C μ)

中文:
定义 cyclotomic'
  签名: (n : 自然数) (R : 类型) [交换环 R] [是整环 R]
  定义体: ∏ μ in primitiveRoots n R, (X - C μ)

Depends on / 依赖: primitiveRoots
-/
def cyclotomic' (n : Nat) (R : Type*) [CommRing R] [IsDomain R] : R[X] :=
  ∏ μ in primitiveRoots n R, (X - C μ)

/-- The zeroth modified cyclotomic polynomial is `1`. -/
@[simp]
/--
theorem `cyclotomic'_zero` / 定理 `cyclotomic'_zero`

English:
theorem cyclotomic'_zero
  given: (R : Type*) [CommRing R] [IsDomain R]
  statement: cyclotomic' 0 R = 1
  proof: by
  simp only [cyclotomic', Finset.prod_empty, primitiveRoots_zero]

中文:
定理 cyclotomic'_zero
  条件: (R : 类型) [交换环 R] [是整环 R]
  结论: cyclotomic' 0 R = 1
  证明: by
  simp only [cyclotomic', Finset.prod_empty, primitiveRoots_zero]
-/
theorem cyclotomic'_zero (R : Type*) [CommRing R] [IsDomain R] : cyclotomic' 0 R = 1 := by
  simp only [cyclotomic', Finset.prod_empty, primitiveRoots_zero]

/-- The first modified cyclotomic polynomial is `X - 1`. -/
@[simp]
/--
theorem `cyclotomic'_one` / 定理 `cyclotomic'_one`

English:
theorem cyclotomic'_one
  given: (R : Type*) [CommRing R] [IsDomain R]
  statement: cyclotomic' 1 R = X - 1
  proof: by
  simp only [cyclotomic', Finset.prod_singleton, map_one, IsPrimitiveRoot.primitiveRoots_one]

中文:
定理 cyclotomic'_one
  条件: (R : 类型) [交换环 R] [是整环 R]
  结论: cyclotomic' 1 R = X - 1
  证明: by
  simp only [cyclotomic', Finset.prod_singleton, map_one, IsPrimitiveRoot.primitiveRoots_one]
-/
theorem cyclotomic'_one (R : Type*) [CommRing R] [IsDomain R] : cyclotomic' 1 R = X - 1 := by
  simp only [cyclotomic', Finset.prod_singleton, map_one, IsPrimitiveRoot.primitiveRoots_one]

-- Cannot be @[simp] because `p` cannot be inferred by `simp`.
/--
theorem `cyclotomic'_two` / 定理 `cyclotomic'_two`

English:
theorem cyclotomic'_two
  given: (R : Type*) [CommRing R] [IsDomain R] (p : Nat) [CharP R p] (hp : p != 2)
  proof: by
  rw [cyclotomic']
  have prim_root_two : primitiveRoots 2 R = {(-1 : R)} := by
    simp only [Finset.eq_singleton_iff_unique_mem, mem_primitiveRoots two_pos]
    exact ⟨IsPrimitiveRoot.neg_one p hp, fun x => IsPrimitiveRoot.eq_neg_one_of_two_right⟩
  simp only [prim_root_two, Finset.prod_singleton, map_neg, map_one, sub_neg_eq_add]

中文:
定理 cyclotomic'_two
  条件: (R : 类型) [交换环 R] [是整环 R] (p : 自然数) [特征p R p] (hp : p != 2)
  证明: by
  rw [cyclotomic']
  have prim_root_two : primitiveRoots 2 R = {(-1 : R)} := by
    simp only [Finset.eq_singleton_iff_unique_mem, mem_primitiveRoots two_pos]
    exact ⟨IsPrimitiveRoot.neg_one p hp, fun x => IsPrimitiveRoot.eq_neg_one_of_two_right⟩
  simp only [prim_root_two, Finset.prod_singleton, map_neg, map_one, sub_neg_eq_add]
-/
theorem cyclotomic'_two (R : Type*) [CommRing R] [IsDomain R] (p : Nat) [CharP R p] (hp : p != 2) :
    cyclotomic' 2 R = X + 1 := by
  rw [cyclotomic']
  have prim_root_two : primitiveRoots 2 R = {(-1 : R)} := by
    simp only [Finset.eq_singleton_iff_unique_mem, mem_primitiveRoots two_pos]
    exact ⟨IsPrimitiveRoot.neg_one p hp, fun x => IsPrimitiveRoot.eq_neg_one_of_two_right⟩
  simp only [prim_root_two, Finset.prod_singleton, map_neg, map_one, sub_neg_eq_add]

/--
theorem `cyclotomic'.monic` / 定理 `cyclotomic'.monic`

English:
theorem cyclotomic'.monic
  given: (n : Nat) (R : Type*) [CommRing R] [IsDomain R]
  proof: monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

中文:
定理 cyclotomic'.monic
  条件: (n : 自然数) (R : 类型) [交换环 R] [是整环 R]
  证明: monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _
-/
theorem cyclotomic'.monic (n : Nat) (R : Type*) [CommRing R] [IsDomain R] :
    (cyclotomic' n R).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

/--
theorem `cyclotomic'_ne_zero` / 定理 `cyclotomic'_ne_zero`

English:
theorem cyclotomic'_ne_zero
  given: (n : Nat) (R : Type*) [CommRing R] [IsDomain R]
  statement: cyclotomic' n R != 0
  proof: (cyclotomic'.monic n R).ne_zero

中文:
定理 cyclotomic'_ne_zero
  条件: (n : 自然数) (R : 类型) [交换环 R] [是整环 R]
  结论: cyclotomic' n R != 0
  证明: (cyclotomic'.monic n R).ne_zero
-/
theorem cyclotomic'_ne_zero (n : Nat) (R : Type*) [CommRing R] [IsDomain R] : cyclotomic' n R != 0 :=
  (cyclotomic'.monic n R).ne_zero

/--
theorem `natDegree_cyclotomic'` / 定理 `natDegree_cyclotomic'`

English:
theorem natDegree_cyclotomic'
  given: {ζ : R} {n : Nat} (h : IsPrimitiveRoot ζ n)
  proof: by
  rw [cyclotomic']
  rw [natDegree_prod (primitiveRoots n R) fun z : R => X - C z]
  · simp only [IsPrimitiveRoot.card_primitiveRoots h, mul_one, natDegree_X_sub_C, Nat.cast_id,
      Finset.sum_const, nsmul_eq_mul]
  intro z _
  exact X_sub_C_ne_zero z

中文:
定理 natDegree_cyclotomic'
  条件: {ζ : R} {n : 自然数} (h : 是PrimitiveRoot ζ n)
  证明: by
  rw [cyclotomic']
  rw [natDegree_prod (primitiveRoots n R) fun z : R => X - C z]
  · simp only [IsPrimitiveRoot.card_primitiveRoots h, mul_one, natDegree_X_sub_C, Nat.cast_id,
      Finset.sum_const, nsmul_eq_mul]
  intro z _
  exact X_sub_C_ne_zero z

Depends on / 依赖: Finset, Finset.sum_const, IsPrimitiveRoot, IsPrimitiveRoot.card_primitiveRoots, Nat.cast_id, X_sub_C_ne_zero, card_primitiveRoots, cast_id, cyclotomic, mul_one, natDegree_X_sub_C, natDegree_prod, nsmul_eq_mul, primitiveRoots, sum_const
-/
theorem natDegree_cyclotomic' {ζ : R} {n : Nat} (h : IsPrimitiveRoot ζ n) :
    (cyclotomic' n R).natDegree = Nat.totient n := by
  rw [cyclotomic']
  rw [natDegree_prod (primitiveRoots n R) fun z : R => X - C z]
  · simp only [IsPrimitiveRoot.card_primitiveRoots h, mul_one, natDegree_X_sub_C, Nat.cast_id,
      Finset.sum_const, nsmul_eq_mul]
  intro z _
  exact X_sub_C_ne_zero z

/--
theorem `degree_cyclotomic'` / 定理 `degree_cyclotomic'`

English:
theorem degree_cyclotomic'
  given: {ζ : R} {n : Nat} (h : IsPrimitiveRoot ζ n)
  proof: by
  simp only [degree_eq_natDegree (cyclotomic'_ne_zero n R), natDegree_cyclotomic' h]

中文:
定理 degree_cyclotomic'
  条件: {ζ : R} {n : 自然数} (h : 是PrimitiveRoot ζ n)
  证明: by
  simp only [degree_eq_natDegree (cyclotomic'_ne_zero n R), natDegree_cyclotomic' h]

Depends on / 依赖: _ne_zero, cyclotomic, degree_eq_natDegree, natDegree_cyclotomic
-/
theorem degree_cyclotomic' {ζ : R} {n : Nat} (h : IsPrimitiveRoot ζ n) :
    (cyclotomic' n R).degree = Nat.totient n := by
  simp only [degree_eq_natDegree (cyclotomic'_ne_zero n R), natDegree_cyclotomic' h]

/--
theorem `roots_of_cyclotomic` / 定理 `roots_of_cyclotomic`

English:
theorem roots_of_cyclotomic
  given: (n : Nat) (R : Type*) [CommRing R] [IsDomain R]
  proof: by
  rw [cyclotomic']; exact roots_prod_X_sub_C (primitiveRoots n R)

中文:
定理 roots_of_cyclotomic
  条件: (n : 自然数) (R : 类型) [交换环 R] [是整环 R]
  证明: by
  rw [cyclotomic']; exact roots_prod_X_sub_C (primitiveRoots n R)

Depends on / 依赖: cyclotomic, primitiveRoots, roots_prod_X_sub_C
-/
theorem roots_of_cyclotomic (n : Nat) (R : Type*) [CommRing R] [IsDomain R] :
    (cyclotomic' n R).roots = (primitiveRoots n R).val := by
  rw [cyclotomic']; exact roots_prod_X_sub_C (primitiveRoots n R)

/--
theorem `X_pow_sub_one_eq_prod` / 定理 `X_pow_sub_one_eq_prod`

English:
theorem X_pow_sub_one_eq_prod
  given: {ζ : R} {n : Nat} (hpos : 0 < n) (h : IsPrimitiveRoot ζ n)
  proof: by
  classical
  rw [nthRootsFinset]; rw [← Multiset.toFinset_eq (IsPrimitiveRoot.nthRoots_one_nodup h)]
  simp only [Finset.prod_mk]
  rw [nthRoots]
  have hmonic : (X ^ n - C (1 : R)).Monic := monic_X_pow_sub_C (1 : R) (ne_of_lt hpos).symm
  symm
  apply prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic
  rw [@natDegree_X_pow_sub_C R _ _ n 1]; rw [← nthRoots]
  exact IsPrimitiveRoot.card_nthRoots_one h

中文:
定理 X_pow_sub_one_eq_prod
  条件: {ζ : R} {n : 自然数} (hpos : 0 < n) (h : 是PrimitiveRoot ζ n)
  证明: by
  classical
  rw [nthRootsFinset]; rw [← Multiset.toFinset_eq (IsPrimitiveRoot.nthRoots_one_nodup h)]
  simp only [Finset.prod_mk]
  rw [nthRoots]
  have hmonic : (X ^ n - C (1 : R)).Monic := monic_X_pow_sub_C (1 : R) (ne_of_lt hpos).symm
  symm
  apply prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic
  rw [@natDegree_X_pow_sub_C R _ _ n 1]; rw [← nthRoots]
  exact IsPrimitiveRoot.card_nthRoots_one h

Depends on / 依赖: Finset, Finset.prod_mk, IsPrimitiveRoot, IsPrimitiveRoot.card_nthRoots_one, IsPrimitiveRoot.nthRoots_one_nodup, Multiset, Multiset.toFinset_eq, TopologicalSpace, card_nthRoots_one, classical, hmonic, monic_X_pow_sub_C, natDegree_X_pow_sub_C, ne_of_lt, nthRoots, nthRootsFinset, nthRoots_one_nodup, prod_mk, prod_multiset_X_sub_C_of_monic_of_roots_card_eq, toFinset_eq
-/
theorem X_pow_sub_one_eq_prod {ζ : R} {n : Nat} (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) :
    X ^ n - 1 = ∏ ζ in nthRootsFinset n (1 : R), (X - C ζ) := by
  classical
  rw [nthRootsFinset]; rw [← Multiset.toFinset_eq (IsPrimitiveRoot.nthRoots_one_nodup h)]
  simp only [Finset.prod_mk]
  rw [nthRoots]
  have hmonic : (X ^ n - C (1 : R)).Monic := monic_X_pow_sub_C (1 : R) (ne_of_lt hpos).symm
  symm
  apply prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic
  rw [@natDegree_X_pow_sub_C R _ _ n 1]; rw [← nthRoots]
  exact IsPrimitiveRoot.card_nthRoots_one h

end IsDomain

section Field

variable {K : Type*} [Field K]

/--
theorem `cyclotomic'_splits` / 定理 `cyclotomic'_splits`

English:
theorem cyclotomic'_splits
  given: (n : Nat)
  statement: Splits (cyclotomic' n K)
  proof: by
  apply Splits.prod
  intro z _
  simp only [Splits.X_sub_C]

中文:
定理 cyclotomic'_splits
  条件: (n : 自然数)
  结论: Splits (cyclotomic' n K)
  证明: by
  apply Splits.prod
  intro z _
  simp only [Splits.X_sub_C]

Depends on / 依赖: NonarchimedeanRing
-/
theorem cyclotomic'_splits (n : Nat) : Splits (cyclotomic' n K) := by
  apply Splits.prod
  intro z _
  simp only [Splits.X_sub_C]

/--
theorem `X_pow_sub_one_splits` / 定理 `X_pow_sub_one_splits`

English:
theorem X_pow_sub_one_splits
  given: {ζ : K} {n : Nat} (h : IsPrimitiveRoot ζ n)
  proof: by
  rw [splits_iff_card_roots]; rw [← nthRoots]; rw [IsPrimitiveRoot.card_nthRoots_one h]; rw [natDegree_X_pow_sub_C]

中文:
定理 X_pow_sub_one_splits
  条件: {ζ : K} {n : 自然数} (h : 是PrimitiveRoot ζ n)
  证明: by
  rw [splits_iff_card_roots]; rw [← nthRoots]; rw [IsPrimitiveRoot.card_nthRoots_one h]; rw [natDegree_X_pow_sub_C]

Depends on / 依赖: IsPrimitiveRoot, IsPrimitiveRoot.card_nthRoots_one, UniformSpace, card_nthRoots_one, natDegree_X_pow_sub_C, nthRoots, splits_iff_card_roots
-/
theorem X_pow_sub_one_splits {ζ : K} {n : Nat} (h : IsPrimitiveRoot ζ n) :
    Splits (X ^ n - C (1 : K)) := by
  rw [splits_iff_card_roots]; rw [← nthRoots]; rw [IsPrimitiveRoot.card_nthRoots_one h]; rw [natDegree_X_pow_sub_C]

/--
theorem `prod_cyclotomic'_eq_X_pow_sub_one` / 定理 `prod_cyclotomic'_eq_X_pow_sub_one`

English:
theorem prod_cyclotomic'_eq_X_pow_sub_one
  statement: {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : Nat}
  proof: by
  classical
  have hd : (n.divisors : Set Nat).PairwiseDisjoint fun k => primitiveRoots k K :=
    fun x _ y _ hne => IsPrimitiveRoot.disjoint hne
  simp only [X_pow_sub_one_eq_prod hpos h, cyclotomic', ← Finset.prod_biUnion hd,
    IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots]

中文:
定理 prod_cyclotomic'_eq_X_pow_sub_one
  结论: {K : 类型} [交换环 K] [是整环 K] {ζ : K} {n : 自然数}
  证明: by
  classical
  have hd : (n.divisors : Set Nat).PairwiseDisjoint fun k => primitiveRoots k K :=
    fun x _ y _ hne => IsPrimitiveRoot.disjoint hne
  simp only [X_pow_sub_one_eq_prod hpos h, cyclotomic', ← Finset.prod_biUnion hd,
    IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots]

Depends on / 依赖: Finset, Finset.prod_biUnion, IsPrimitiveRoot, IsPrimitiveRoot.disjoint, IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots, IsUniformAddGroup, PairwiseDisjoint, X_pow_sub_one_eq_prod, classical, cyclotomic, disjoint, divisors, n.divisors, nthRoots_one_eq_biUnion_primitiveRoots, primitiveRoots, prod_biUnion
-/
theorem prod_cyclotomic'_eq_X_pow_sub_one {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : Nat}
    (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) :
    ∏ i in Nat.divisors n, cyclotomic' i K = X ^ n - 1 := by
  classical
  have hd : (n.divisors : Set Nat).PairwiseDisjoint fun k => primitiveRoots k K :=
    fun x _ y _ hne => IsPrimitiveRoot.disjoint hne
  simp only [X_pow_sub_one_eq_prod hpos h, cyclotomic', ← Finset.prod_biUnion hd,
    IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots]

/--
theorem `cyclotomic'_eq_X_pow_sub_one_div` / 定理 `cyclotomic'_eq_X_pow_sub_one_div`

English:
theorem cyclotomic'_eq_X_pow_sub_one_div
  statement: {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : Nat}
  proof: by
  rw [← prod_cyclotomic'_eq_X_pow_sub_one hpos h]; rw [← Nat.cons_self_properDivisors hpos.ne']; rw [Finset.prod_cons]
  have prod_monic : (∏ i in Nat.properDivisors n, cyclotomic' i K).Monic := by
    apply monic_prod_of_monic
    intro i _
    exact cyclotomic'.monic i K
  rw [(div_modByMonic_unique (cyclotomic' n K) 0 prod_monic _).1]
  simp only [degree_zero, zero_add]
  refine ⟨by rw [mul_comm], ?_⟩
  rw [bot_lt_iff_ne_bot]
  intro h
  exact Monic.ne_zero prod_monic (degree_eq_bot.1 h)

中文:
定理 cyclotomic'_eq_X_pow_sub_one_div
  结论: {K : 类型} [交换环 K] [是整环 K] {ζ : K} {n : 自然数}
  证明: by
  rw [← prod_cyclotomic'_eq_X_pow_sub_one hpos h]; rw [← Nat.cons_self_properDivisors hpos.ne']; rw [Finset.prod_cons]
  have prod_monic : (∏ i in Nat.properDivisors n, cyclotomic' i K).Monic := by
    apply monic_prod_of_monic
    intro i _
    exact cyclotomic'.monic i K
  rw [(div_modByMonic_unique (cyclotomic' n K) 0 prod_monic _).1]
  simp only [degree_zero, zero_add]
  refine ⟨by rw [mul_comm], ?_⟩
  rw [bot_lt_iff_ne_bot]
  intro h
  exact Monic.ne_zero prod_monic (degree_eq_bot.1 h)

Depends on / 依赖: IsLinearTopology, i.isLinearTopology, isLinearTopology
-/
theorem cyclotomic'_eq_X_pow_sub_one_div {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : Nat}
    (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) :
    cyclotomic' n K = (X ^ n - 1) /ₘ ∏ i in Nat.properDivisors n, cyclotomic' i K := by
  rw [← prod_cyclotomic'_eq_X_pow_sub_one hpos h]; rw [← Nat.cons_self_properDivisors hpos.ne']; rw [Finset.prod_cons]
  have prod_monic : (∏ i in Nat.properDivisors n, cyclotomic' i K).Monic := by
    apply monic_prod_of_monic
    intro i _
    exact cyclotomic'.monic i K
  rw [(div_modByMonic_unique (cyclotomic' n K) 0 prod_monic _).1]
  simp only [degree_zero, zero_add]
  refine ⟨by rw [mul_comm], ?_⟩
  rw [bot_lt_iff_ne_bot]
  intro h
  exact Monic.ne_zero prod_monic (degree_eq_bot.1 h)

/--
theorem `int_coeff_of_cyclotomic'` / 定理 `int_coeff_of_cyclotomic'`

English:
theorem int_coeff_of_cyclotomic'
  statement: {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : Nat}
  proof: by
  refine lifts_and_degree_eq_and_monic ?_ (cyclotomic'.monic n K)
  induction n using Nat.strong_induction_on generalizing ζ with | _ k ihk
  rcases k.eq_zero_or_pos with (rfl | hpos)
  · use 1
    simp only [cyclotomic'_zero, coe_mapRingHom, Polynomial.map_one]
  let B : K[X] := ∏ i in Nat.properDivisors k, cyclotomic' i K
  have Bmo : B.Monic := by
    apply monic_prod_of_monic
    intro i _
    exact cyclotomic'.monic i K
  have Bint : B in lifts (Int.castRingHom K) := by
    refine Subsemiring.prod_mem (lifts (Int.castRingHom K)) ?_
    intro x hx
    have xsmall := (Nat.mem_properDivisors.1 hx).2
    obtain ⟨d, hd⟩ := (Nat.mem_properDivisors.1 hx).1
    rw [mul_comm] at hd
    exact ihk x xsmall (h.pow hpos hd)
  replace Bint := lifts_and_degree_eq_and_monic Bint Bmo
  obtain ⟨B₁, hB₁, _, hB₁mo⟩ := Bint
  let Q₁ : Int[X] := (X ^ k - 1) /ₘ B₁
  have huniq : 0 + B * cyclotomic' k K = X ^ k - 1 ∧ (0 : K[X]).degree < B.degree := by
    constructor
    · rw [zero_add, mul_comm, ← prod_cyclotomic'_eq_X_pow_sub_one hpos h, ←
        Nat.cons_self_properDivisors hpos.ne', Finset.prod_cons]
    · simpa only [degree_zero, bot_lt_iff_ne_bot, Ne, degree_eq_bot] using Bmo.ne_zero
  replace huniq := div_modByMonic_unique (cyclotomic' k K) (0 : K[X]) Bmo huniq
  simp only [lifts, RingHom.mem_rangeS]
  use Q₁
  rw [coe_mapRingHom]; rw [map_divByMonic (Int.castRingHom K) hB₁mo]; rw [hB₁]; rw [← huniq.1]
  simp

中文:
定理 int_coeff_of_cyclotomic'
  结论: {K : 类型} [交换环 K] [是整环 K] {ζ : K} {n : 自然数}
  证明: by
  refine lifts_and_degree_eq_and_monic ?_ (cyclotomic'.monic n K)
  induction n using Nat.strong_induction_on generalizing ζ with | _ k ihk
  rcases k.eq_zero_or_pos with (rfl | hpos)
  · use 1
    simp only [cyclotomic'_zero, coe_mapRingHom, Polynomial.map_one]
  let B : K[X] := ∏ i in Nat.properDivisors k, cyclotomic' i K
  have Bmo : B.Monic := by
    apply monic_prod_of_monic
    intro i _
    exact cyclotomic'.monic i K
  have Bint : B in lifts (Int.castRingHom K) := by
    refine Subsemiring.prod_mem (lifts (Int.castRingHom K)) ?_
    intro x hx
    have xsmall := (Nat.mem_properDivisors.1 hx).2
    obtain ⟨d, hd⟩ := (Nat.mem_properDivisors.1 hx).1
    rw [mul_comm] at hd
    exact ihk x xsmall (h.pow hpos hd)
  replace Bint := lifts_and_degree_eq_and_monic Bint Bmo
  obtain ⟨B₁, hB₁, _, hB₁mo⟩ := Bint
  let Q₁ : Int[X] := (X ^ k - 1) /ₘ B₁
  have huniq : 0 + B * cyclotomic' k K = X ^ k - 1 ∧ (0 : K[X]).degree < B.degree := by
    constructor
    · rw [zero_add, mul_comm, ← prod_cyclotomic'_eq_X_pow_sub_one hpos h, ←
        Nat.cons_self_properDivisors hpos.ne', Finset.prod_cons]
    · simpa only [degree_zero, bot_lt_iff_ne_bot, Ne, degree_eq_bot] using Bmo.ne_zero
  replace huniq := div_modByMonic_unique (cyclotomic' k K) (0 : K[X]) Bmo huniq
  simp only [lifts, RingHom.mem_rangeS]
  use Q₁
  rw [coe_mapRingHom]; rw [map_divByMonic (Int.castRingHom K) hB₁mo]; rw [hB₁]; rw [← huniq.1]
  simp

Depends on / 依赖: B.Monic, Int.castRin, Int.castRingHom, Nat.properDivisors, Nat.strong_induction_on, Polynomial, Polynomial.map_one, Subsemiring, Subsemiring.prod_mem, _zero, castRin, castRingHom, coe_mapRingHom, cyclotomic, eq_zero_or_pos, generalizing, k.eq_zero_or_pos, lifts_and_degree_eq_and_monic, map_one, monic_prod_of_monic
-/
theorem int_coeff_of_cyclotomic' {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : Nat}
    (h : IsPrimitiveRoot ζ n) : exists P : Int[X], map (Int.castRingHom K) P =
      cyclotomic' n K ∧ P.degree = (cyclotomic' n K).degree ∧ P.Monic := by
  refine lifts_and_degree_eq_and_monic ?_ (cyclotomic'.monic n K)
  induction n using Nat.strong_induction_on generalizing ζ with | _ k ihk
  rcases k.eq_zero_or_pos with (rfl | hpos)
  · use 1
    simp only [cyclotomic'_zero, coe_mapRingHom, Polynomial.map_one]
  let B : K[X] := ∏ i in Nat.properDivisors k, cyclotomic' i K
  have Bmo : B.Monic := by
    apply monic_prod_of_monic
    intro i _
    exact cyclotomic'.monic i K
  have Bint : B in lifts (Int.castRingHom K) := by
    refine Subsemiring.prod_mem (lifts (Int.castRingHom K)) ?_
    intro x hx
    have xsmall := (Nat.mem_properDivisors.1 hx).2
    obtain ⟨d, hd⟩ := (Nat.mem_properDivisors.1 hx).1
    rw [mul_comm] at hd
    exact ihk x xsmall (h.pow hpos hd)
  replace Bint := lifts_and_degree_eq_and_monic Bint Bmo
  obtain ⟨B₁, hB₁, _, hB₁mo⟩ := Bint
  let Q₁ : Int[X] := (X ^ k - 1) /ₘ B₁
  have huniq : 0 + B * cyclotomic' k K = X ^ k - 1 ∧ (0 : K[X]).degree < B.degree := by
    constructor
    · rw [zero_add, mul_comm, ← prod_cyclotomic'_eq_X_pow_sub_one hpos h, ←
        Nat.cons_self_properDivisors hpos.ne', Finset.prod_cons]
    · simpa only [degree_zero, bot_lt_iff_ne_bot, Ne, degree_eq_bot] using Bmo.ne_zero
  replace huniq := div_modByMonic_unique (cyclotomic' k K) (0 : K[X]) Bmo huniq
  simp only [lifts, RingHom.mem_rangeS]
  use Q₁
  rw [coe_mapRingHom]; rw [map_divByMonic (Int.castRingHom K) hB₁mo]; rw [hB₁]; rw [← huniq.1]
  simp

/--
theorem `unique_int_coeff_of_cycl` / 定理 `unique_int_coeff_of_cycl`

English:
theorem unique_int_coeff_of_cycl
  statement: {K : Type*} [CommRing K] [IsDomain K] [CharZero K] {ζ : K}
  proof: by
  obtain ⟨P, hP⟩ := int_coeff_of_cyclotomic' h
  refine ⟨P, hP.1, fun Q hQ => ?_⟩
  apply map_injective (Int.castRingHom K) Int.cast_injective
  rw [hP.1]; rw [hQ]

中文:
定理 unique_int_coeff_of_cycl
  结论: {K : 类型} [交换环 K] [是整环 K] [特征零 K] {ζ : K}
  证明: by
  obtain ⟨P, hP⟩ := int_coeff_of_cyclotomic' h
  refine ⟨P, hP.1, fun Q hQ => ?_⟩
  apply map_injective (Int.castRingHom K) Int.cast_injective
  rw [hP.1]; rw [hQ]

Depends on / 依赖: Int.castRingHom, Int.cast_injective, castRingHom, cast_injective, int_coeff_of_cyclotomic, map_injective
-/
theorem unique_int_coeff_of_cycl {K : Type*} [CommRing K] [IsDomain K] [CharZero K] {ζ : K}
    {n : Nat+} (h : IsPrimitiveRoot ζ n) :
    exists! P : Int[X], map (Int.castRingHom K) P = cyclotomic' n K := by
  obtain ⟨P, hP⟩ := int_coeff_of_cyclotomic' h
  refine ⟨P, hP.1, fun Q hQ => ?_⟩
  apply map_injective (Int.castRingHom K) Int.cast_injective
  rw [hP.1]; rw [hQ]

end Field

end Cyclotomic'

section Cyclotomic

/--
Definition of `cyclotomic` / `cyclotomic` 的定义

English:
definition cyclotomic
  signature: (n : Nat) (R : Type*) [Ring R]
  body: if h : n = 0 then 1
  else map (Int.castRingHom R) (int_coeff_of_cyclotomic' (Complex.isPrimitiveRoot_exp n h)).choose

中文:
定义 cyclotomic
  签名: (n : 自然数) (R : 类型) [环 R]
  定义体: if h : n = 0 then 1
  else map (Int.castRingHom R) (int_coeff_of_cyclotomic' (Complex.isPrimitiveRoot_exp n h)).choose

Depends on / 依赖: Complex.isPrimitiveRoot_exp, Int.castRingHom, castRingHom, int_coeff_of_cyclotomic, isPrimitiveRoot_exp
-/
def cyclotomic (n : Nat) (R : Type*) [Ring R] : R[X] :=
  if h : n = 0 then 1
  else map (Int.castRingHom R) (int_coeff_of_cyclotomic' (Complex.isPrimitiveRoot_exp n h)).choose

/--
theorem `int_cyclotomic_rw` / 定理 `int_cyclotomic_rw`

English:
theorem int_cyclotomic_rw
  given: {n : Nat} (h : n != 0)
  proof: by
  simp only [cyclotomic, h, dif_neg, not_false_iff]
  ext i
  simp only [coeff_map, Int.cast_id, eq_intCast]

中文:
定理 int_cyclotomic_rw
  条件: {n : 自然数} (h : n != 0)
  证明: by
  simp only [cyclotomic, h, dif_neg, not_false_iff]
  ext i
  simp only [coeff_map, Int.cast_id, eq_intCast]

Depends on / 依赖: Int.cast_id, cast_id, coeff_map, cyclotomic, dif_neg, eq_intCast, not_false_iff
-/
theorem int_cyclotomic_rw {n : Nat} (h : n != 0) :
    cyclotomic n Int = (int_coeff_of_cyclotomic' (Complex.isPrimitiveRoot_exp n h)).choose := by
  simp only [cyclotomic, h, dif_neg, not_false_iff]
  ext i
  simp only [coeff_map, Int.cast_id, eq_intCast]

/--
theorem `map_cyclotomic_int` / 定理 `map_cyclotomic_int`

English:
theorem map_cyclotomic_int
  given: (n : Nat) (R : Type*) [Ring R]
  proof: by
  by_cases hzero : n = 0
  · simp only [hzero, cyclotomic, dif_pos, Polynomial.map_one]
  simp [cyclotomic, hzero]

中文:
定理 map_cyclotomic_int
  条件: (n : 自然数) (R : 类型) [环 R]
  证明: by
  by_cases hzero : n = 0
  · simp only [hzero, cyclotomic, dif_pos, Polynomial.map_one]
  simp [cyclotomic, hzero]

Depends on / 依赖: Polynomial, Polynomial.map_one, cyclotomic, dif_pos, map_one
-/
theorem map_cyclotomic_int (n : Nat) (R : Type*) [Ring R] :
    map (Int.castRingHom R) (cyclotomic n Int) = cyclotomic n R := by
  by_cases hzero : n = 0
  · simp only [hzero, cyclotomic, dif_pos, Polynomial.map_one]
  simp [cyclotomic, hzero]

/--
theorem `int_cyclotomic_spec` / 定理 `int_cyclotomic_spec`

English:
theorem int_cyclotomic_spec
  given: (n : Nat)
  proof: by
  by_cases hzero : n = 0
  · simp only [hzero, cyclotomic, degree_one, monic_one, cyclotomic'_zero, dif_pos,
      Polynomial.map_one, and_self_iff]
  rw [int_cyclotomic_rw hzero]
  exact (int_coeff_of_cyclotomic' (Complex.isPrimitiveRoot_exp n hzero)).choose_spec

中文:
定理 int_cyclotomic_spec
  条件: (n : 自然数)
  证明: by
  by_cases hzero : n = 0
  · simp only [hzero, cyclotomic, degree_one, monic_one, cyclotomic'_zero, dif_pos,
      Polynomial.map_one, and_self_iff]
  rw [int_cyclotomic_rw hzero]
  exact (int_coeff_of_cyclotomic' (Complex.isPrimitiveRoot_exp n hzero)).choose_spec

Depends on / 依赖: Complex.isPrimitiveRoot_exp, Polynomial, Polynomial.map_one, _zero, and_self_iff, choose_spec, cyclotomic, degree_one, dif_pos, int_coeff_of_cyclotomic, int_cyclotomic_rw, isPrimitiveRoot_exp, map_one, monic_one
-/
theorem int_cyclotomic_spec (n : Nat) :
    map (Int.castRingHom Complex) (cyclotomic n Int) = cyclotomic' n Complex ∧
      (cyclotomic n Int).degree = (cyclotomic' n Complex).degree ∧ (cyclotomic n Int).Monic := by
  by_cases hzero : n = 0
  · simp only [hzero, cyclotomic, degree_one, monic_one, cyclotomic'_zero, dif_pos,
      Polynomial.map_one, and_self_iff]
  rw [int_cyclotomic_rw hzero]
  exact (int_coeff_of_cyclotomic' (Complex.isPrimitiveRoot_exp n hzero)).choose_spec

/--
theorem `int_cyclotomic_unique` / 定理 `int_cyclotomic_unique`

English:
theorem int_cyclotomic_unique
  given: {n : Nat} {P : Int[X]} (h : map (Int.castRingHom Complex) P = cyclotomic' n Complex)
  proof: by
  apply map_injective (Int.castRingHom Complex) Int.cast_injective
  rw [h]; rw [(int_cyclotomic_spec n).1]

中文:
定理 int_cyclotomic_unique
  条件: {n : 自然数} {P : 整数[X]} (h : map (整数.castRingHom 复形) P = cyclotomic' n 复形)
  证明: by
  apply map_injective (Int.castRingHom Complex) Int.cast_injective
  rw [h]; rw [(int_cyclotomic_spec n).1]

Depends on / 依赖: Int.castRingHom, Int.cast_injective, castRingHom, cast_injective, int_cyclotomic_spec, map_injective
-/
theorem int_cyclotomic_unique {n : Nat} {P : Int[X]} (h : map (Int.castRingHom Complex) P = cyclotomic' n Complex) :
    P = cyclotomic n Int := by
  apply map_injective (Int.castRingHom Complex) Int.cast_injective
  rw [h]; rw [(int_cyclotomic_spec n).1]

/-- The definition of `cyclotomic n R` commutes with any ring homomorphism. -/
@[simp]
/--
theorem `map_cyclotomic` / 定理 `map_cyclotomic`

English:
theorem map_cyclotomic
  given: (n : Nat) {R S : Type*} [Ring R] [Ring S] (f : R ->+* S)
  proof: by
  rw [← map_cyclotomic_int n R]; rw [← map_cyclotomic_int n S]; rw [map_map]
  have : Subsingleton (Int ->+* S) := inferInstance
  congr!

中文:
定理 map_cyclotomic
  条件: (n : 自然数) {R S : 类型} [环 R] [环 S] (f : R ->+* S)
  证明: by
  rw [← map_cyclotomic_int n R]; rw [← map_cyclotomic_int n S]; rw [map_map]
  have : Subsingleton (Int ->+* S) := inferInstance
  congr!

Depends on / 依赖: Subsingleton, map_cyclotomic_int, map_map
-/
theorem map_cyclotomic (n : Nat) {R S : Type*} [Ring R] [Ring S] (f : R ->+* S) :
    map f (cyclotomic n R) = cyclotomic n S := by
  rw [← map_cyclotomic_int n R]; rw [← map_cyclotomic_int n S]; rw [map_map]
  have : Subsingleton (Int ->+* S) := inferInstance
  congr!

/--
theorem `cyclotomic.eval_apply` / 定理 `cyclotomic.eval_apply`

English:
theorem cyclotomic.eval_apply
  given: {R S : Type*} (q : R) (n : Nat) [Ring R] [Ring S] (f : R ->+* S)
  proof: by
  rw [← map_cyclotomic n f]; rw [eval_map]; rw [eval₂_at_apply]

中文:
定理 cyclotomic.eval_apply
  条件: {R S : 类型} (q : R) (n : 自然数) [环 R] [环 S] (f : R ->+* S)
  证明: by
  rw [← map_cyclotomic n f]; rw [eval_map]; rw [eval₂_at_apply]

Depends on / 依赖: eval_map, map_cyclotomic
-/
theorem cyclotomic.eval_apply {R S : Type*} (q : R) (n : Nat) [Ring R] [Ring S] (f : R ->+* S) :
    eval (f q) (cyclotomic n S) = f (eval q (cyclotomic n R)) := by
  rw [← map_cyclotomic n f]; rw [eval_map]; rw [eval₂_at_apply]

/--
theorem `cyclotomic.eval_apply_ofReal` / 定理 `cyclotomic.eval_apply_ofReal`

English:
theorem cyclotomic.eval_apply_ofReal
  given: (q : Real) (n : Nat)
  proof: cyclotomic.eval_apply q n (algebraMap Real Complex)

中文:
定理 cyclotomic.eval_apply_of实数
  条件: (q : 实数) (n : 自然数)
  证明: cyclotomic.eval_apply q n (algebraMap Real Complex)
-/
@[simp] theorem cyclotomic.eval_apply_ofReal (q : Real) (n : Nat) :
    eval (q : Complex) (cyclotomic n Complex) = (eval q (cyclotomic n Real)) :=
  cyclotomic.eval_apply q n (algebraMap Real Complex)

/-- The zeroth cyclotomic polynomial is `1`. -/
@[simp]
/--
theorem `cyclotomic_zero` / 定理 `cyclotomic_zero`

English:
theorem cyclotomic_zero
  given: (R : Type*) [Ring R]
  statement: cyclotomic 0 R = 1
  proof: by
  simp only [cyclotomic, dif_pos]

中文:
定理 cyclotomic_zero
  条件: (R : 类型) [环 R]
  结论: cyclotomic 0 R = 1
  证明: by
  simp only [cyclotomic, dif_pos]

Depends on / 依赖: cyclotomic, dif_pos
-/
theorem cyclotomic_zero (R : Type*) [Ring R] : cyclotomic 0 R = 1 := by
  simp only [cyclotomic, dif_pos]

/-- The first cyclotomic polynomial is `X - 1`. -/
@[simp]
/--
theorem `cyclotomic_one` / 定理 `cyclotomic_one`

English:
theorem cyclotomic_one
  given: (R : Type*) [Ring R]
  statement: cyclotomic 1 R = X - 1
  proof: by
  have hspec : map (Int.castRingHom Complex) (X - 1) = cyclotomic' 1 Complex := by
    simp only [cyclotomic'_one, map_X, Polynomial.map_one, Polynomial.map_sub]
  symm
  rw [← map_cyclotomic_int]; rw [← int_cyclotomic_unique hspec]
  simp only [map_X, Polynomial.map_one, Polynomial.map_sub]

中文:
定理 cyclotomic_one
  条件: (R : 类型) [环 R]
  结论: cyclotomic 1 R = X - 1
  证明: by
  have hspec : map (Int.castRingHom Complex) (X - 1) = cyclotomic' 1 Complex := by
    simp only [cyclotomic'_one, map_X, Polynomial.map_one, Polynomial.map_sub]
  symm
  rw [← map_cyclotomic_int]; rw [← int_cyclotomic_unique hspec]
  simp only [map_X, Polynomial.map_one, Polynomial.map_sub]

Depends on / 依赖: Int.castRingHom, Polynomial, Polynomial.map_one, Polynomial.map_sub, _one, castRingHom, cyclotomic, int_cyclotomic_unique, map_X, map_cyclotomic_int, map_one, map_sub
-/
theorem cyclotomic_one (R : Type*) [Ring R] : cyclotomic 1 R = X - 1 := by
  have hspec : map (Int.castRingHom Complex) (X - 1) = cyclotomic' 1 Complex := by
    simp only [cyclotomic'_one, map_X, Polynomial.map_one, Polynomial.map_sub]
  symm
  rw [← map_cyclotomic_int]; rw [← int_cyclotomic_unique hspec]
  simp only [map_X, Polynomial.map_one, Polynomial.map_sub]

/--
theorem `cyclotomic.monic` / 定理 `cyclotomic.monic`

English:
theorem cyclotomic.monic
  given: (n : Nat) (R : Type*) [Ring R]
  statement: (cyclotomic n R).Monic
  proof: by
  rw [← map_cyclotomic_int]
  exact (int_cyclotomic_spec n).2.2.map _

中文:
定理 cyclotomic.monic
  条件: (n : 自然数) (R : 类型) [环 R]
  结论: (cyclotomic n R).Monic
  证明: by
  rw [← map_cyclotomic_int]
  exact (int_cyclotomic_spec n).2.2.map _

Depends on / 依赖: int_cyclotomic_spec, map_cyclotomic_int
-/
theorem cyclotomic.monic (n : Nat) (R : Type*) [Ring R] : (cyclotomic n R).Monic := by
  rw [← map_cyclotomic_int]
  exact (int_cyclotomic_spec n).2.2.map _

/--
theorem `cyclotomic.isPrimitive` / 定理 `cyclotomic.isPrimitive`

English:
theorem cyclotomic.isPrimitive
  given: (n : Nat) (R : Type*) [CommRing R]
  statement: (cyclotomic n R).IsPrimitive
  proof: (cyclotomic.monic n R).isPrimitive

中文:
定理 cyclotomic.isPrimitive
  条件: (n : 自然数) (R : 类型) [交换环 R]
  结论: (cyclotomic n R).是Primitive
  证明: (cyclotomic.monic n R).isPrimitive

Depends on / 依赖: cyclotomic, cyclotomic.monic, isPrimitive
-/
theorem cyclotomic.isPrimitive (n : Nat) (R : Type*) [CommRing R] : (cyclotomic n R).IsPrimitive :=
  (cyclotomic.monic n R).isPrimitive

/--
theorem `cyclotomic_ne_zero` / 定理 `cyclotomic_ne_zero`

English:
theorem cyclotomic_ne_zero
  given: (n : Nat) (R : Type*) [Ring R] [Nontrivial R]
  statement: cyclotomic n R != 0
  proof: (cyclotomic.monic n R).ne_zero

中文:
定理 cyclotomic_ne_zero
  条件: (n : 自然数) (R : 类型) [环 R] [非平凡 R]
  结论: cyclotomic n R != 0
  证明: (cyclotomic.monic n R).ne_zero

Depends on / 依赖: cyclotomic, cyclotomic.monic, ne_zero
-/
theorem cyclotomic_ne_zero (n : Nat) (R : Type*) [Ring R] [Nontrivial R] : cyclotomic n R != 0 :=
  (cyclotomic.monic n R).ne_zero

/--
theorem `degree_cyclotomic` / 定理 `degree_cyclotomic`

English:
theorem degree_cyclotomic
  given: (n : Nat) (R : Type*) [Ring R] [Nontrivial R]
  proof: by
  rw [← map_cyclotomic_int]
  rw [degree_map_eq_of_leadingCoeff_ne_zero (Int.castRingHom R) _]
  · rcases n with - | k
    · simp only [cyclotomic, degree_one, dif_pos, Nat.totient_zero, CharP.cast_eq_zero]
    rw [← degree_cyclotomic' (Complex.isPrimitiveRoot_exp k.succ (Nat.succ_ne_zero k))]
    exact (int_cyclotomic_spec k.succ).2.1
  simp only [(int_cyclotomic_spec n).right.right, eq_intCast, Monic.leadingCoeff, Int.cast_one,
    Ne, not_false_iff, one_ne_zero]

中文:
定理 degree_cyclotomic
  条件: (n : 自然数) (R : 类型) [环 R] [非平凡 R]
  证明: by
  rw [← map_cyclotomic_int]
  rw [degree_map_eq_of_leadingCoeff_ne_zero (Int.castRingHom R) _]
  · rcases n with - | k
    · simp only [cyclotomic, degree_one, dif_pos, Nat.totient_zero, CharP.cast_eq_zero]
    rw [← degree_cyclotomic' (Complex.isPrimitiveRoot_exp k.succ (Nat.succ_ne_zero k))]
    exact (int_cyclotomic_spec k.succ).2.1
  simp only [(int_cyclotomic_spec n).right.right, eq_intCast, Monic.leadingCoeff, Int.cast_one,
    Ne, not_false_iff, one_ne_zero]

Depends on / 依赖: CharP.cast_eq_zero, Complex.isPrimitiveRoot_exp, Int.castRingHom, Int.cast_one, Monic.leadingCoeff, Nat.succ_ne_zero, Nat.totient_zero, castRingHom, cast_eq_zero, cast_one, cyclotomic, degree_cyclotomic, degree_map_eq_of_leadingCoeff_ne_zero, degree_one, dif_pos, eq_intCast, int_cyclotomic_spec, isPrimitiveRoot_exp, k.succ, leadingCoeff
-/
theorem degree_cyclotomic (n : Nat) (R : Type*) [Ring R] [Nontrivial R] :
    (cyclotomic n R).degree = Nat.totient n := by
  rw [← map_cyclotomic_int]
  rw [degree_map_eq_of_leadingCoeff_ne_zero (Int.castRingHom R) _]
  · rcases n with - | k
    · simp only [cyclotomic, degree_one, dif_pos, Nat.totient_zero, CharP.cast_eq_zero]
    rw [← degree_cyclotomic' (Complex.isPrimitiveRoot_exp k.succ (Nat.succ_ne_zero k))]
    exact (int_cyclotomic_spec k.succ).2.1
  simp only [(int_cyclotomic_spec n).right.right, eq_intCast, Monic.leadingCoeff, Int.cast_one,
    Ne, not_false_iff, one_ne_zero]

/--
theorem `natDegree_cyclotomic` / 定理 `natDegree_cyclotomic`

English:
theorem natDegree_cyclotomic
  given: (n : Nat) (R : Type*) [Ring R] [Nontrivial R]
  proof: by
  rw [natDegree]; rw [degree_cyclotomic]; norm_cast

中文:
定理 natDegree_cyclotomic
  条件: (n : 自然数) (R : 类型) [环 R] [非平凡 R]
  证明: by
  rw [natDegree]; rw [degree_cyclotomic]; norm_cast

Depends on / 依赖: degree_cyclotomic, natDegree
-/
theorem natDegree_cyclotomic (n : Nat) (R : Type*) [Ring R] [Nontrivial R] :
    (cyclotomic n R).natDegree = Nat.totient n := by
  rw [natDegree]; rw [degree_cyclotomic]; norm_cast

/--
lemma `natDegree_cyclotomic_le` / 引理 `natDegree_cyclotomic_le`

English:
lemma natDegree_cyclotomic_le
  given: {R : Type*} [Ring R] {n : Nat}
  proof: by
  nontriviality R
  rw [natDegree_cyclotomic]

中文:
引理 natDegree_cyclotomic_le
  条件: {R : 类型} [环 R] {n : 自然数}
  证明: by
  nontriviality R
  rw [natDegree_cyclotomic]

Depends on / 依赖: natDegree_cyclotomic, nontriviality
-/
lemma natDegree_cyclotomic_le {R : Type*} [Ring R] {n : Nat} :
    natDegree (cyclotomic n R) <= n.totient := by
  nontriviality R
  rw [natDegree_cyclotomic]

/--
theorem `degree_cyclotomic_pos` / 定理 `degree_cyclotomic_pos`

English:
theorem degree_cyclotomic_pos
  given: (n : Nat) (R : Type*) (hpos : 0 < n) [Ring R] [Nontrivial R]
  proof: by
  rwa [degree_cyclotomic n R, Nat.cast_pos, Nat.totient_pos]

中文:
定理 degree_cyclotomic_pos
  条件: (n : 自然数) (R : 类型) (hpos : 0 < n) [环 R] [非平凡 R]
  证明: by
  rwa [degree_cyclotomic n R, Nat.cast_pos, Nat.totient_pos]

Depends on / 依赖: Nat.cast_pos, Nat.totient_pos, cast_pos, degree_cyclotomic, totient_pos
-/
theorem degree_cyclotomic_pos (n : Nat) (R : Type*) (hpos : 0 < n) [Ring R] [Nontrivial R] :
    0 < (cyclotomic n R).degree := by
  rwa [degree_cyclotomic n R, Nat.cast_pos, Nat.totient_pos]

open Finset

/--
theorem `prod_cyclotomic_eq_X_pow_sub_one` / 定理 `prod_cyclotomic_eq_X_pow_sub_one`

English:
theorem prod_cyclotomic_eq_X_pow_sub_one
  given: {n : Nat} (hpos : 0 < n) (R : Type*) [CommRing R]
  proof: by
  have integer : ∏ i in Nat.divisors n, cyclotomic i Int = X ^ n - 1 := by
    apply map_injective (Int.castRingHom Complex) Int.cast_injective
    simp only [Polynomial.map_prod, int_cyclotomic_spec, Polynomial.map_pow, map_X,
      Polynomial.map_one, Polynomial.map_sub]
    exact prod_cyclotomic'_eq_X_pow_sub_one hpos (Complex.isPrimitiveRoot_exp n hpos.ne')
  simpa only [Polynomial.map_prod, map_cyclotomic_int, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_pow, Polynomial.map_X] using congr_arg (map (Int.castRingHom R)) integer

中文:
定理 prod_cyclotomic_eq_X_pow_sub_one
  条件: {n : 自然数} (hpos : 0 < n) (R : 类型) [交换环 R]
  证明: by
  have integer : ∏ i in Nat.divisors n, cyclotomic i Int = X ^ n - 1 := by
    apply map_injective (Int.castRingHom Complex) Int.cast_injective
    simp only [Polynomial.map_prod, int_cyclotomic_spec, Polynomial.map_pow, map_X,
      Polynomial.map_one, Polynomial.map_sub]
    exact prod_cyclotomic'_eq_X_pow_sub_one hpos (Complex.isPrimitiveRoot_exp n hpos.ne')
  simpa only [Polynomial.map_prod, map_cyclotomic_int, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_pow, Polynomial.map_X] using congr_arg (map (Int.castRingHom R)) integer

Depends on / 依赖: Complex.isPrimitiveRoot_exp, Int.castRingHom, Int.cast_injective, Nat.divisors, Polynomial, Polynomial.map_X, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_prod, Polynomial.map_sub, _eq_X_pow_sub_one, castRingHom, cast_injective, congr_arg, cyclotomic, divisors, hpos.ne, int_cyclotomic_spec, integer, isPrimitiveRoot_exp
-/
theorem prod_cyclotomic_eq_X_pow_sub_one {n : Nat} (hpos : 0 < n) (R : Type*) [CommRing R] :
    ∏ i in Nat.divisors n, cyclotomic i R = X ^ n - 1 := by
  have integer : ∏ i in Nat.divisors n, cyclotomic i Int = X ^ n - 1 := by
    apply map_injective (Int.castRingHom Complex) Int.cast_injective
    simp only [Polynomial.map_prod, int_cyclotomic_spec, Polynomial.map_pow, map_X,
      Polynomial.map_one, Polynomial.map_sub]
    exact prod_cyclotomic'_eq_X_pow_sub_one hpos (Complex.isPrimitiveRoot_exp n hpos.ne')
  simpa only [Polynomial.map_prod, map_cyclotomic_int, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_pow, Polynomial.map_X] using congr_arg (map (Int.castRingHom R)) integer

/--
theorem `cyclotomic.dvd_X_pow_sub_one` / 定理 `cyclotomic.dvd_X_pow_sub_one`

English:
theorem cyclotomic.dvd_X_pow_sub_one
  given: (n : Nat) (R : Type*) [Ring R]
  proof: by
  suffices cyclotomic n Int ∣ X ^ n - 1 by
    simpa only [map_cyclotomic_int, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow,
      Polynomial.map_X] using Polynomial.map_dvd (Int.castRingHom R) this
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  rw [← prod_cyclotomic_eq_X_pow_sub_one hn]
  exact Finset.dvd_prod_of_mem _ (n.mem_divisors_self hn.ne')

中文:
定理 cyclotomic.dvd_X_pow_sub_one
  条件: (n : 自然数) (R : 类型) [环 R]
  证明: by
  suffices cyclotomic n Int ∣ X ^ n - 1 by
    simpa only [map_cyclotomic_int, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow,
      Polynomial.map_X] using Polynomial.map_dvd (Int.castRingHom R) this
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  rw [← prod_cyclotomic_eq_X_pow_sub_one hn]
  exact Finset.dvd_prod_of_mem _ (n.mem_divisors_self hn.ne')

Depends on / 依赖: Finset, Finset.dvd_prod_of_mem, Int.castRingHom, Polynomial, Polynomial.map_X, Polynomial.map_dvd, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_sub, castRingHom, cyclotomic, dvd_prod_of_mem, eq_zero_or_pos, hn.ne, map_X, map_cyclotomic_int, map_dvd, map_one, map_pow, map_sub
-/
theorem cyclotomic.dvd_X_pow_sub_one (n : Nat) (R : Type*) [Ring R] :
    cyclotomic n R ∣ X ^ n - 1 := by
  suffices cyclotomic n Int ∣ X ^ n - 1 by
    simpa only [map_cyclotomic_int, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow,
      Polynomial.map_X] using Polynomial.map_dvd (Int.castRingHom R) this
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  rw [← prod_cyclotomic_eq_X_pow_sub_one hn]
  exact Finset.dvd_prod_of_mem _ (n.mem_divisors_self hn.ne')

/--
theorem `prod_cyclotomic_eq_geom_sum` / 定理 `prod_cyclotomic_eq_geom_sum`

English:
theorem prod_cyclotomic_eq_geom_sum
  given: {n : Nat} (h : 0 < n) (R) [CommRing R]
  proof: by
  suffices (∏ i in n.divisors.erase 1, cyclotomic i Int) = ∑ i in Finset.range n, X ^ i by
    simpa only [Polynomial.map_prod, map_cyclotomic_int, Polynomial.map_sum, Polynomial.map_pow,
      Polynomial.map_X] using congr_arg (map (Int.castRingHom R)) this
  rw [← mul_left_inj' (cyclotomic_ne_zero 1 Int)]; rw [prod_erase_mul _ _ (Nat.one_mem_divisors.2 h.ne')]; rw [cyclotomic_one]; rw [geom_sum_mul]; rw [prod_cyclotomic_eq_X_pow_sub_one h]

中文:
定理 prod_cyclotomic_eq_geom_sum
  条件: {n : 自然数} (h : 0 < n) (R) [交换环 R]
  证明: by
  suffices (∏ i in n.divisors.erase 1, cyclotomic i Int) = ∑ i in Finset.range n, X ^ i by
    simpa only [Polynomial.map_prod, map_cyclotomic_int, Polynomial.map_sum, Polynomial.map_pow,
      Polynomial.map_X] using congr_arg (map (Int.castRingHom R)) this
  rw [← mul_left_inj' (cyclotomic_ne_zero 1 Int)]; rw [prod_erase_mul _ _ (Nat.one_mem_divisors.2 h.ne')]; rw [cyclotomic_one]; rw [geom_sum_mul]; rw [prod_cyclotomic_eq_X_pow_sub_one h]

Depends on / 依赖: Finset, Finset.range, Int.castRingHom, Nat.one_mem_divisors, Polynomial, Polynomial.map_X, Polynomial.map_pow, Polynomial.map_prod, Polynomial.map_sum, castRingHom, congr_arg, cyclotomic, cyclotomic_ne_zero, cyclotomic_one, divisors, geom_sum_mul, h.ne, map_X, map_cyclotomic_int, map_pow
-/
theorem prod_cyclotomic_eq_geom_sum {n : Nat} (h : 0 < n) (R) [CommRing R] :
    ∏ i in n.divisors.erase 1, cyclotomic i R = ∑ i in Finset.range n, X ^ i := by
  suffices (∏ i in n.divisors.erase 1, cyclotomic i Int) = ∑ i in Finset.range n, X ^ i by
    simpa only [Polynomial.map_prod, map_cyclotomic_int, Polynomial.map_sum, Polynomial.map_pow,
      Polynomial.map_X] using congr_arg (map (Int.castRingHom R)) this
  rw [← mul_left_inj' (cyclotomic_ne_zero 1 Int)]; rw [prod_erase_mul _ _ (Nat.one_mem_divisors.2 h.ne')]; rw [cyclotomic_one]; rw [geom_sum_mul]; rw [prod_cyclotomic_eq_X_pow_sub_one h]

/--
theorem `cyclotomic_prime` / 定理 `cyclotomic_prime`

English:
theorem cyclotomic_prime
  given: (R : Type*) [Ring R] (p : Nat) [hp : Fact p.Prime]
  proof: by
  suffices cyclotomic p Int = ∑ i in range p, X ^ i by
    simpa only [map_cyclotomic_int, Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_X] using
      congr_arg (map (Int.castRingHom R)) this
  rw [← prod_cyclotomic_eq_geom_sum hp.out.pos]; rw [hp.out.divisors]; rw [erase_insert (mem_singleton.not.2 hp.out.ne_one.symm)]; rw [prod_singleton]

中文:
定理 cyclotomic_prime
  条件: (R : 类型) [环 R] (p : 自然数) [hp : Fact p.素]
  证明: by
  suffices cyclotomic p Int = ∑ i in range p, X ^ i by
    simpa only [map_cyclotomic_int, Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_X] using
      congr_arg (map (Int.castRingHom R)) this
  rw [← prod_cyclotomic_eq_geom_sum hp.out.pos]; rw [hp.out.divisors]; rw [erase_insert (mem_singleton.not.2 hp.out.ne_one.symm)]; rw [prod_singleton]

Depends on / 依赖: Int.castRingHom, NonarchimedeanRing, NonarchimedeanRing.to_nonarchimedeanAddGroup, Polynomial, Polynomial.map_X, Polynomial.map_pow, Polynomial.map_sum, castRingHom, congr_arg, cyclotomic, divisors, erase_insert, hp.out.divisors, hp.out.ne_one.symm, hp.out.pos, map_X, map_cyclotomic_int, map_pow, map_sum, mem_singleton
-/
theorem cyclotomic_prime (R : Type*) [Ring R] (p : Nat) [hp : Fact p.Prime] :
    cyclotomic p R = ∑ i in Finset.range p, X ^ i := by
  suffices cyclotomic p Int = ∑ i in range p, X ^ i by
    simpa only [map_cyclotomic_int, Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_X] using
      congr_arg (map (Int.castRingHom R)) this
  rw [← prod_cyclotomic_eq_geom_sum hp.out.pos]; rw [hp.out.divisors]; rw [erase_insert (mem_singleton.not.2 hp.out.ne_one.symm)]; rw [prod_singleton]

/--
theorem `cyclotomic_prime_mul_X_sub_one` / 定理 `cyclotomic_prime_mul_X_sub_one`

English:
theorem cyclotomic_prime_mul_X_sub_one
  given: (R : Type*) [Ring R] (p : Nat) [hn : Fact (Nat.Prime p)]
  proof: by rw [cyclotomic_prime, geom_sum_mul]

@[simp]

中文:
定理 cyclotomic_prime_mul_X_sub_one
  条件: (R : 类型) [环 R] (p : 自然数) [hn : Fact (自然数.素 p)]
  证明: by rw [cyclotomic_prime, geom_sum_mul]

@[simp]

Depends on / 依赖: cyclotomic_prime, geom_sum_mul
-/
theorem cyclotomic_prime_mul_X_sub_one (R : Type*) [Ring R] (p : Nat) [hn : Fact (Nat.Prime p)] :
    cyclotomic p R * (X - 1) = X ^ p - 1 := by rw [cyclotomic_prime, geom_sum_mul]

@[simp]
/--
theorem `cyclotomic_two` / 定理 `cyclotomic_two`

English:
theorem cyclotomic_two
  given: (R : Type*) [Ring R]
  statement: cyclotomic 2 R = X + 1
  proof: by simp [cyclotomic_prime]

@[simp]

中文:
定理 cyclotomic_two
  条件: (R : 类型) [环 R]
  结论: cyclotomic 2 R = X + 1
  证明: by simp [cyclotomic_prime]

@[simp]

Depends on / 依赖: cyclotomic_prime
-/
theorem cyclotomic_two (R : Type*) [Ring R] : cyclotomic 2 R = X + 1 := by simp [cyclotomic_prime]

@[simp]
/--
theorem `cyclotomic_three` / 定理 `cyclotomic_three`

English:
theorem cyclotomic_three
  given: (R : Type*) [Ring R]
  statement: cyclotomic 3 R = X ^ 2 + X + 1
  proof: by
  simp [cyclotomic_prime, sum_range_succ']

中文:
定理 cyclotomic_three
  条件: (R : 类型) [环 R]
  结论: cyclotomic 3 R = X ^ 2 + X + 1
  证明: by
  simp [cyclotomic_prime, sum_range_succ']

Depends on / 依赖: cyclotomic_prime, sum_range_succ
-/
theorem cyclotomic_three (R : Type*) [Ring R] : cyclotomic 3 R = X ^ 2 + X + 1 := by
  simp [cyclotomic_prime, sum_range_succ']

/--
theorem `cyclotomic_dvd_geom_sum_of_dvd` / 定理 `cyclotomic_dvd_geom_sum_of_dvd`

English:
theorem cyclotomic_dvd_geom_sum_of_dvd
  given: (R) [Ring R] {d n : Nat} (hdn : d ∣ n) (hd : d != 1)
  proof: by
  suffices cyclotomic d Int ∣ ∑ i in Finset.range n, X ^ i by
    simpa only [map_cyclotomic_int, Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_X] using
      map_dvd (Int.castRingHom R) this
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  rw [← prod_cyclotomic_eq_geom_sum hn]
  apply Finset.dvd_prod_of_mem
  simp [hd, hdn, hn.ne']

中文:
定理 cyclotomic_dvd_geom_sum_of_dvd
  条件: (R) [环 R] {d n : 自然数} (hdn : d ∣ n) (hd : d != 1)
  证明: by
  suffices cyclotomic d Int ∣ ∑ i in Finset.range n, X ^ i by
    simpa only [map_cyclotomic_int, Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_X] using
      map_dvd (Int.castRingHom R) this
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  rw [← prod_cyclotomic_eq_geom_sum hn]
  apply Finset.dvd_prod_of_mem
  simp [hd, hdn, hn.ne']

Depends on / 依赖: Finset, Finset.dvd_prod_of_mem, Finset.range, Int.castRingHom, Polynomial, Polynomial.map_X, Polynomial.map_pow, Polynomial.map_sum, castRingHom, cyclotomic, dvd_prod_of_mem, eq_zero_or_pos, hn.ne, map_X, map_cyclotomic_int, map_dvd, map_pow, map_sum, n.eq_zero_or_pos, prod_cyclotomic_eq_geom_sum
-/
theorem cyclotomic_dvd_geom_sum_of_dvd (R) [Ring R] {d n : Nat} (hdn : d ∣ n) (hd : d != 1) :
    cyclotomic d R ∣ ∑ i in Finset.range n, X ^ i := by
  suffices cyclotomic d Int ∣ ∑ i in Finset.range n, X ^ i by
    simpa only [map_cyclotomic_int, Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_X] using
      map_dvd (Int.castRingHom R) this
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  rw [← prod_cyclotomic_eq_geom_sum hn]
  apply Finset.dvd_prod_of_mem
  simp [hd, hdn, hn.ne']

/--
theorem `X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd` / 定理 `X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd`

English:
theorem X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd
  statement: (R) [CommRing R] {d n : Nat}
  proof: by
  have h0d : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by positivity)
  rw [← prod_cyclotomic_eq_X_pow_sub_one h0d]; rw [← prod_cyclotomic_eq_X_pow_sub_one (by positivity)]; rw [mul_comm]; rw [Finset.prod_sdiff (by gcongr)]

中文:
定理 X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd
  结论: (R) [交换环 R] {d n : 自然数}
  证明: by
  have h0d : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by positivity)
  rw [← prod_cyclotomic_eq_X_pow_sub_one h0d]; rw [← prod_cyclotomic_eq_X_pow_sub_one (by positivity)]; rw [mul_comm]; rw [Finset.prod_sdiff (by gcongr)]

Depends on / 依赖: Finset, Finset.prod_sdiff, Nat.pos_of_dvd_of_pos, mul_comm, pos_of_dvd_of_pos, prod_cyclotomic_eq_X_pow_sub_one, prod_sdiff
-/
theorem X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd (R) [CommRing R] {d n : Nat}
    (hdvd : d ∣ n) (hn : n != 0) :
    ((X ^ d - 1) * ∏ x in n.divisors \ d.divisors, cyclotomic x R) = X ^ n - 1 := by
  have h0d : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by positivity)
  rw [← prod_cyclotomic_eq_X_pow_sub_one h0d]; rw [← prod_cyclotomic_eq_X_pow_sub_one (by positivity)]; rw [mul_comm]; rw [Finset.prod_sdiff (by gcongr)]

/--
theorem `X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd` / 定理 `X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd`

English:
theorem X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd
  statement: (R) [CommRing R] {d n : Nat}
  proof: by
  rw [Nat.mem_properDivisors] at h
  use ∏ x in n.properDivisors \ d.divisors, cyclotomic x R
  rw [← X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd R h.1 h.2.ne_bot]; rw [← Nat.insert_self_properDivisors]; rw [Finset.insert_sdiff_of_notMem]; rw [Finset.prod_insert]; rw [mul_assoc]
  · exact Finset.notMem_sdiff_of_notMem_left Nat.self_notMem_properDivisors
· exact fun hk => h.2.not_ge Nat.divisor_le hk
  · exact h.2.ne_bot

中文:
定理 X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd
  结论: (R) [交换环 R] {d n : 自然数}
  证明: by
  rw [Nat.mem_properDivisors] at h
  use ∏ x in n.properDivisors \ d.divisors, cyclotomic x R
  rw [← X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd R h.1 h.2.ne_bot]; rw [← Nat.insert_self_properDivisors]; rw [Finset.insert_sdiff_of_notMem]; rw [Finset.prod_insert]; rw [mul_assoc]
  · exact Finset.notMem_sdiff_of_notMem_left Nat.self_notMem_properDivisors
· exact fun hk => h.2.not_ge Nat.divisor_le hk
  · exact h.2.ne_bot

Depends on / 依赖: Finset, Finset.insert_sdiff_of_notMem, Finset.notMem_sdiff_of_notMem_left, Finset.prod_insert, Nat.divisor_le, Nat.insert_self_properDivisors, Nat.mem_properDivisors, Nat.self_notMem_properDivisors, X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd, cyclotomic, d.divisors, divisor_le, divisors, insert_sdiff_of_notMem, insert_self_properDivisors, mem_properDivisors, mul_assoc, n.properDivisors, ne_bot, notMem_sdiff_of_notMem_left
-/
theorem X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd (R) [CommRing R] {d n : Nat}
    (h : d in n.properDivisors) : (X ^ d - 1) * cyclotomic n R ∣ X ^ n - 1 := by
  rw [Nat.mem_properDivisors] at h
  use ∏ x in n.properDivisors \ d.divisors, cyclotomic x R
  rw [← X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd R h.1 h.2.ne_bot]; rw [← Nat.insert_self_properDivisors]; rw [Finset.insert_sdiff_of_notMem]; rw [Finset.prod_insert]; rw [mul_assoc]
  · exact Finset.notMem_sdiff_of_notMem_left Nat.self_notMem_properDivisors
· exact fun hk => h.2.not_ge Nat.divisor_le hk
  · exact h.2.ne_bot

section ArithmeticFunction

open ArithmeticFunction

-- access notation `μ`
open scoped ArithmeticFunction.Moebius

/--
theorem `cyclotomic_eq_prod_X_pow_sub_one_pow_moebius` / 定理 `cyclotomic_eq_prod_X_pow_sub_one_pow_moebius`

English:
theorem cyclotomic_eq_prod_X_pow_sub_one_pow_moebius
  statement: {n : Nat} (R : Type*) [CommRing R]
  proof: by
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · simp
  have h : forall n : Nat, 0 < n -> (∏ i in Nat.divisors n, algebraMap _ (RatFunc R) (cyclotomic i R)) =
      algebraMap _ _ (X ^ n - 1 : R[X]) := by
    intro n hn
    rw [← prod_cyclotomic_eq_X_pow_sub_one hn R]; rw [map_prod]
  rw [(prod_eq_iff_prod_pow_moebius_eq_of_nonzero (fun n hn => _) fun n hn => _).1 h n hpos] <;>
    simp_rw [Ne, IsFractionRing.to_map_eq_zero_iff]
  · simp [cyclotomic_ne_zero]
  · intro n hn
    apply Monic.ne_zero
    apply monic_X_pow_sub_C _ (ne_of_gt hn)

中文:
定理 cyclotomic_eq_prod_X_pow_sub_one_pow_moebius
  结论: {n : 自然数} (R : 类型) [交换环 R]
  证明: by
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · simp
  have h : forall n : Nat, 0 < n -> (∏ i in Nat.divisors n, algebraMap _ (RatFunc R) (cyclotomic i R)) =
      algebraMap _ _ (X ^ n - 1 : R[X]) := by
    intro n hn
    rw [← prod_cyclotomic_eq_X_pow_sub_one hn R]; rw [map_prod]
  rw [(prod_eq_iff_prod_pow_moebius_eq_of_nonzero (fun n hn => _) fun n hn => _).1 h n hpos] <;>
    simp_rw [Ne, IsFractionRing.to_map_eq_zero_iff]
  · simp [cyclotomic_ne_zero]
  · intro n hn
    apply Monic.ne_zero
    apply monic_X_pow_sub_C _ (ne_of_gt hn)

Depends on / 依赖: IsFractionRing, IsFractionRing.to_map_eq_zero_iff, Monic.ne_zero, Nat.divisors, RatFunc, algebraMap, cyclotomic, cyclotomic_ne_zero, divisors, eq_zero_or_pos, map_prod, monic_X_pow_sub_C, n.eq_zero_or_pos, ne_zero, prod_cyclotomic_eq_X_pow_sub_one, prod_eq_iff_prod_pow_moebius_eq_of_nonzero, simp_rw, to_map_eq_zero_iff
-/
theorem cyclotomic_eq_prod_X_pow_sub_one_pow_moebius {n : Nat} (R : Type*) [CommRing R]
    [IsDomain R] : algebraMap _ (RatFunc R) (cyclotomic n R) =
      ∏ i in n.divisorsAntidiagonal, algebraMap R[X] _ (X ^ i.snd - 1) ^ μ i.fst := by
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · simp
  have h : forall n : Nat, 0 < n -> (∏ i in Nat.divisors n, algebraMap _ (RatFunc R) (cyclotomic i R)) =
      algebraMap _ _ (X ^ n - 1 : R[X]) := by
    intro n hn
    rw [← prod_cyclotomic_eq_X_pow_sub_one hn R]; rw [map_prod]
  rw [(prod_eq_iff_prod_pow_moebius_eq_of_nonzero (fun n hn => _) fun n hn => _).1 h n hpos] <;>
    simp_rw [Ne, IsFractionRing.to_map_eq_zero_iff]
  · simp [cyclotomic_ne_zero]
  · intro n hn
    apply Monic.ne_zero
    apply monic_X_pow_sub_C _ (ne_of_gt hn)

end ArithmeticFunction

/--
theorem `cyclotomic_eq_X_pow_sub_one_div` / 定理 `cyclotomic_eq_X_pow_sub_one_div`

English:
theorem cyclotomic_eq_X_pow_sub_one_div
  given: {R : Type*} [CommRing R] {n : Nat} (hpos : 0 < n)
  proof: by
  nontriviality R
  rw [← prod_cyclotomic_eq_X_pow_sub_one hpos]; rw [← Nat.cons_self_properDivisors hpos.ne']; rw [Finset.prod_cons]
  have prod_monic : (∏ i in Nat.properDivisors n, cyclotomic i R).Monic := by
    apply monic_prod_of_monic
    intro i _
    exact cyclotomic.monic i R
  rw [(div_modByMonic_unique (cyclotomic n R) 0 prod_monic _).1]
  simp only [degree_zero, zero_add]
  constructor
  · rw [mul_comm]
  rw [bot_lt_iff_ne_bot]
  intro h
  exact Monic.ne_zero prod_monic (degree_eq_bot.1 h)

中文:
定理 cyclotomic_eq_X_pow_sub_one_div
  条件: {R : 类型} [交换环 R] {n : 自然数} (hpos : 0 < n)
  证明: by
  nontriviality R
  rw [← prod_cyclotomic_eq_X_pow_sub_one hpos]; rw [← Nat.cons_self_properDivisors hpos.ne']; rw [Finset.prod_cons]
  have prod_monic : (∏ i in Nat.properDivisors n, cyclotomic i R).Monic := by
    apply monic_prod_of_monic
    intro i _
    exact cyclotomic.monic i R
  rw [(div_modByMonic_unique (cyclotomic n R) 0 prod_monic _).1]
  simp only [degree_zero, zero_add]
  constructor
  · rw [mul_comm]
  rw [bot_lt_iff_ne_bot]
  intro h
  exact Monic.ne_zero prod_monic (degree_eq_bot.1 h)

Depends on / 依赖: Finset, Finset.prod_cons, Monic.ne_zero, Nat.cons_self_properDivisors, Nat.properDivisors, bot_lt_iff_ne_bot, cons_self_properDivisors, cyclotomic, cyclotomic.monic, degree_eq_bot, degree_zero, div_modByMonic_unique, hpos.ne, monic_prod_of_monic, mul_comm, ne_zero, nontriviality, prod_cons, prod_cyclotomic_eq_X_pow_sub_one, prod_monic
-/
theorem cyclotomic_eq_X_pow_sub_one_div {R : Type*} [CommRing R] {n : Nat} (hpos : 0 < n) :
    cyclotomic n R = (X ^ n - 1) /ₘ ∏ i in Nat.properDivisors n, cyclotomic i R := by
  nontriviality R
  rw [← prod_cyclotomic_eq_X_pow_sub_one hpos]; rw [← Nat.cons_self_properDivisors hpos.ne']; rw [Finset.prod_cons]
  have prod_monic : (∏ i in Nat.properDivisors n, cyclotomic i R).Monic := by
    apply monic_prod_of_monic
    intro i _
    exact cyclotomic.monic i R
  rw [(div_modByMonic_unique (cyclotomic n R) 0 prod_monic _).1]
  simp only [degree_zero, zero_add]
  constructor
  · rw [mul_comm]
  rw [bot_lt_iff_ne_bot]
  intro h
  exact Monic.ne_zero prod_monic (degree_eq_bot.1 h)

/--
theorem `X_pow_sub_one_dvd_prod_cyclotomic` / 定理 `X_pow_sub_one_dvd_prod_cyclotomic`

English:
theorem X_pow_sub_one_dvd_prod_cyclotomic
  statement: (R : Type*) [CommRing R] {n m : Nat} (hpos : 0 < n)
  proof: by
  replace hm := Nat.mem_properDivisors.2
    ⟨hm, lt_of_le_of_ne (Nat.divisor_le (Nat.mem_divisors.2 ⟨hm, hpos.ne'⟩)) hdiff⟩
  rw [← Finset.sdiff_union_of_subset (Nat.divisors_subset_properDivisors (ne_of_lt hpos).symm
    (Nat.mem_properDivisors.1 hm).1 (ne_of_lt (Nat.mem_properDivisors.1 hm).2))]; rw [Finset.prod_union Finset.sdiff_disjoint]; rw [prod_cyclotomic_eq_X_pow_sub_one (Nat.pos_of_mem_properDivisors hm)]
  exact ⟨∏ x in n.properDivisors \ m.divisors, cyclotomic x R, by rw [mul_comm]⟩

中文:
定理 X_pow_sub_one_dvd_prod_cyclotomic
  结论: (R : 类型) [交换环 R] {n m : 自然数} (hpos : 0 < n)
  证明: by
  replace hm := Nat.mem_properDivisors.2
    ⟨hm, lt_of_le_of_ne (Nat.divisor_le (Nat.mem_divisors.2 ⟨hm, hpos.ne'⟩)) hdiff⟩
  rw [← Finset.sdiff_union_of_subset (Nat.divisors_subset_properDivisors (ne_of_lt hpos).symm
    (Nat.mem_properDivisors.1 hm).1 (ne_of_lt (Nat.mem_properDivisors.1 hm).2))]; rw [Finset.prod_union Finset.sdiff_disjoint]; rw [prod_cyclotomic_eq_X_pow_sub_one (Nat.pos_of_mem_properDivisors hm)]
  exact ⟨∏ x in n.properDivisors \ m.divisors, cyclotomic x R, by rw [mul_comm]⟩

Depends on / 依赖: Finset, Finset.prod_union, Finset.sdiff_disjoint, Finset.sdiff_union_of_subset, Nat.divisor_le, Nat.divisors_subset_properDivisors, Nat.mem_divisors, Nat.mem_properDivisors, Nat.pos_of_mem_properDivisors, NonarchimedeanAddGroup, NonarchimedeanAddGroup.is_nonarchimedean, cyclotomic, divisor_le, divisors, divisors_subset_properDivisors, hpos.ne, is_nonarchimedean, lt_of_le_of_ne, m.divisors, mem_divisors
-/
theorem X_pow_sub_one_dvd_prod_cyclotomic (R : Type*) [CommRing R] {n m : Nat} (hpos : 0 < n)
    (hm : m ∣ n) (hdiff : m != n) : X ^ m - 1 ∣ ∏ i in Nat.properDivisors n, cyclotomic i R := by
  replace hm := Nat.mem_properDivisors.2
    ⟨hm, lt_of_le_of_ne (Nat.divisor_le (Nat.mem_divisors.2 ⟨hm, hpos.ne'⟩)) hdiff⟩
  rw [← Finset.sdiff_union_of_subset (Nat.divisors_subset_properDivisors (ne_of_lt hpos).symm
    (Nat.mem_properDivisors.1 hm).1 (ne_of_lt (Nat.mem_properDivisors.1 hm).2))]; rw [Finset.prod_union Finset.sdiff_disjoint]; rw [prod_cyclotomic_eq_X_pow_sub_one (Nat.pos_of_mem_properDivisors hm)]
  exact ⟨∏ x in n.properDivisors \ m.divisors, cyclotomic x R, by rw [mul_comm]⟩

/--
theorem `cyclotomic_eq_prod_X_sub_primitiveRoots` / 定理 `cyclotomic_eq_prod_X_sub_primitiveRoots`

English:
theorem cyclotomic_eq_prod_X_sub_primitiveRoots
  statement: {K : Type*} [CommRing K] [IsDomain K] {ζ : K}
  proof: by
  rw [← cyclotomic']
  induction n using Nat.strong_induction_on generalizing ζ with | _ k hk
  obtain hzero | hpos := k.eq_zero_or_pos
  · simp only [hzero, cyclotomic'_zero, cyclotomic_zero]
  have h : forall i in k.properDivisors, cyclotomic i K = cyclotomic' i K := by
    intro i hi
    obtain ⟨d, hd⟩ := (Nat.mem_properDivisors.1 hi).1
    rw [mul_comm] at hd
    exact hk i (Nat.mem_properDivisors.1 hi).2 (IsPrimitiveRoot.pow hpos hz hd)
  rw [@cyclotomic_eq_X_pow_sub_one_div _ _ _ hpos]; rw [cyclotomic'_eq_X_pow_sub_one_div hpos hz]; rw [Finset.prod_congr (refl k.properDivisors) h]

中文:
定理 cyclotomic_eq_prod_X_sub_primitiveRoots
  结论: {K : 类型} [交换环 K] [是整环 K] {ζ : K}
  证明: by
  rw [← cyclotomic']
  induction n using Nat.strong_induction_on generalizing ζ with | _ k hk
  obtain hzero | hpos := k.eq_zero_or_pos
  · simp only [hzero, cyclotomic'_zero, cyclotomic_zero]
  have h : forall i in k.properDivisors, cyclotomic i K = cyclotomic' i K := by
    intro i hi
    obtain ⟨d, hd⟩ := (Nat.mem_properDivisors.1 hi).1
    rw [mul_comm] at hd
    exact hk i (Nat.mem_properDivisors.1 hi).2 (IsPrimitiveRoot.pow hpos hz hd)
  rw [@cyclotomic_eq_X_pow_sub_one_div _ _ _ hpos]; rw [cyclotomic'_eq_X_pow_sub_one_div hpos hz]; rw [Finset.prod_congr (refl k.properDivisors) h]

Depends on / 依赖: IsPrimitiveRoot, IsPrimitiveRoot.pow, Nat.mem_properDivisors, Nat.strong_induction_on, _eq_X_pow_su, _zero, cyclotomic, cyclotomic_eq_X_pow_sub_one_div, cyclotomic_zero, eq_zero_or_pos, generalizing, k.eq_zero_or_pos, k.properDivisors, mem_properDivisors, mul_comm, properDivisors, strong_induction_on
-/
theorem cyclotomic_eq_prod_X_sub_primitiveRoots {K : Type*} [CommRing K] [IsDomain K] {ζ : K}
    {n : Nat} (hz : IsPrimitiveRoot ζ n) : cyclotomic n K = ∏ μ in primitiveRoots n K, (X - C μ) := by
  rw [← cyclotomic']
  induction n using Nat.strong_induction_on generalizing ζ with | _ k hk
  obtain hzero | hpos := k.eq_zero_or_pos
  · simp only [hzero, cyclotomic'_zero, cyclotomic_zero]
  have h : forall i in k.properDivisors, cyclotomic i K = cyclotomic' i K := by
    intro i hi
    obtain ⟨d, hd⟩ := (Nat.mem_properDivisors.1 hi).1
    rw [mul_comm] at hd
    exact hk i (Nat.mem_properDivisors.1 hi).2 (IsPrimitiveRoot.pow hpos hz hd)
  rw [@cyclotomic_eq_X_pow_sub_one_div _ _ _ hpos]; rw [cyclotomic'_eq_X_pow_sub_one_div hpos hz]; rw [Finset.prod_congr (refl k.properDivisors) h]

/--
theorem `eq_cyclotomic_iff` / 定理 `eq_cyclotomic_iff`

English:
theorem eq_cyclotomic_iff
  given: {R : Type*} [CommRing R] {n : Nat} (hpos : 0 < n) (P : R[X])
  proof: by
  nontriviality R
  refine ⟨fun hcycl => ?_, fun hP => ?_⟩
  · rw [hcycl, ← prod_cyclotomic_eq_X_pow_sub_one hpos R, ← Nat.cons_self_properDivisors hpos.ne',
      Finset.prod_cons]
  · have prod_monic : (∏ i in Nat.properDivisors n, cyclotomic i R).Monic := by
      apply monic_prod_of_monic
      intro i _
      exact cyclotomic.monic i R
    rw [@cyclotomic_eq_X_pow_sub_one_div R _ _ hpos]; rw [(div_modByMonic_unique P 0 prod_monic _).1]
    refine ⟨by rwa [zero_add, mul_comm], ?_⟩
    rw [degree_zero]; rw [bot_lt_iff_ne_bot]
    intro h
    exact Monic.ne_zero prod_monic (degree_eq_bot.1 h)

中文:
定理 eq_cyclotomic_iff
  条件: {R : 类型} [交换环 R] {n : 自然数} (hpos : 0 < n) (P : R[X])
  证明: by
  nontriviality R
  refine ⟨fun hcycl => ?_, fun hP => ?_⟩
  · rw [hcycl, ← prod_cyclotomic_eq_X_pow_sub_one hpos R, ← Nat.cons_self_properDivisors hpos.ne',
      Finset.prod_cons]
  · have prod_monic : (∏ i in Nat.properDivisors n, cyclotomic i R).Monic := by
      apply monic_prod_of_monic
      intro i _
      exact cyclotomic.monic i R
    rw [@cyclotomic_eq_X_pow_sub_one_div R _ _ hpos]; rw [(div_modByMonic_unique P 0 prod_monic _).1]
    refine ⟨by rwa [zero_add, mul_comm], ?_⟩
    rw [degree_zero]; rw [bot_lt_iff_ne_bot]
    intro h
    exact Monic.ne_zero prod_monic (degree_eq_bot.1 h)

Depends on / 依赖: Finset, Finset.prod_cons, Nat.cons_self_properDivisors, Nat.properDivisors, TotallySeparatedSpace, bot_lt_iff_ne_bot, cons_self_properDivisors, cyclotomic, cyclotomic.monic, cyclotomic_eq_X_pow_sub_one_div, degree_zero, div_modByMonic_unique, hpos.ne, instTotallySeparated, monic_prod_of_monic, mul_comm, nontriviality, prod_cons, prod_cyclotomic_eq_X_pow_sub_one, prod_monic
-/
theorem eq_cyclotomic_iff {R : Type*} [CommRing R] {n : Nat} (hpos : 0 < n) (P : R[X]) :
    P = cyclotomic n R ↔
    (P * ∏ i in Nat.properDivisors n, Polynomial.cyclotomic i R) = X ^ n - 1 := by
  nontriviality R
  refine ⟨fun hcycl => ?_, fun hP => ?_⟩
  · rw [hcycl, ← prod_cyclotomic_eq_X_pow_sub_one hpos R, ← Nat.cons_self_properDivisors hpos.ne',
      Finset.prod_cons]
  · have prod_monic : (∏ i in Nat.properDivisors n, cyclotomic i R).Monic := by
      apply monic_prod_of_monic
      intro i _
      exact cyclotomic.monic i R
    rw [@cyclotomic_eq_X_pow_sub_one_div R _ _ hpos]; rw [(div_modByMonic_unique P 0 prod_monic _).1]
    refine ⟨by rwa [zero_add, mul_comm], ?_⟩
    rw [degree_zero]; rw [bot_lt_iff_ne_bot]
    intro h
    exact Monic.ne_zero prod_monic (degree_eq_bot.1 h)

/--
theorem `cyclotomic_prime_pow_eq_geom_sum` / 定理 `cyclotomic_prime_pow_eq_geom_sum`

English:
theorem cyclotomic_prime_pow_eq_geom_sum
  given: {R : Type*} [CommRing R] {p n : Nat} (hp : p.Prime)
  proof: by
  have : forall m, (cyclotomic (p ^ (m + 1)) R = ∑ i in Finset.range p, (X ^ p ^ m) ^ i) ↔
      ((∑ i in Finset.range p, (X ^ p ^ m) ^ i) *
        ∏ x in Finset.range (m + 1), cyclotomic (p ^ x) R) = X ^ p ^ (m + 1) - 1 := by
    intro m
    have := eq_cyclotomic_iff (R := R) (P := ∑ i in range p, (X ^ p ^ m) ^ i)
      (pow_pos hp.pos (m + 1))
    rw [eq_comm] at this
    rw [this]; rw [Nat.prod_properDivisors_prime_pow hp]
  induction n with
  | zero => have := Fact.mk hp; simp [cyclotomic_prime]
  | succ n_n n_ih =>
    rw [← (eq_cyclotomic_iff (pow_pos hp.pos (n_n + 1 + 1)) _).mpr ?_]
    rw [Nat.prod_properDivisors_prime_pow hp]; rw [Finset.prod_range_succ]; rw [n_ih]
    rw [this] at n_ih
    rw [mul_comm _ (∑ i in _]; rw [_)]; rw [n_ih]; rw [geom_sum_mul]; rw [sub_left_inj]; rw [← pow_mul]
    simp only [pow_add, pow_one]

中文:
定理 cyclotomic_prime_pow_eq_geom_sum
  条件: {R : 类型} [交换环 R] {p n : 自然数} (hp : p.素)
  证明: by
  have : forall m, (cyclotomic (p ^ (m + 1)) R = ∑ i in Finset.range p, (X ^ p ^ m) ^ i) ↔
      ((∑ i in Finset.range p, (X ^ p ^ m) ^ i) *
        ∏ x in Finset.range (m + 1), cyclotomic (p ^ x) R) = X ^ p ^ (m + 1) - 1 := by
    intro m
    have := eq_cyclotomic_iff (R := R) (P := ∑ i in range p, (X ^ p ^ m) ^ i)
      (pow_pos hp.pos (m + 1))
    rw [eq_comm] at this
    rw [this]; rw [Nat.prod_properDivisors_prime_pow hp]
  induction n with
  | zero => have := Fact.mk hp; simp [cyclotomic_prime]
  | succ n_n n_ih =>
    rw [← (eq_cyclotomic_iff (pow_pos hp.pos (n_n + 1 + 1)) _).mpr ?_]
    rw [Nat.prod_properDivisors_prime_pow hp]; rw [Finset.prod_range_succ]; rw [n_ih]
    rw [this] at n_ih
    rw [mul_comm _ (∑ i in _]; rw [_)]; rw [n_ih]; rw [geom_sum_mul]; rw [sub_left_inj]; rw [← pow_mul]
    simp only [pow_add, pow_one]

Depends on / 依赖: Fact.mk, Finset, Finset.range, Nat.prod_properDivisors_prime_pow, cyclotomic, cyclotomic_prime, eq_comm, eq_cycl, eq_cyclotomic_iff, hp.pos, n_ih, pow_pos, prod_properDivisors_prime_pow
-/
theorem cyclotomic_prime_pow_eq_geom_sum {R : Type*} [CommRing R] {p n : Nat} (hp : p.Prime) :
    cyclotomic (p ^ (n + 1)) R = ∑ i in Finset.range p, (X ^ p ^ n) ^ i := by
  have : forall m, (cyclotomic (p ^ (m + 1)) R = ∑ i in Finset.range p, (X ^ p ^ m) ^ i) ↔
      ((∑ i in Finset.range p, (X ^ p ^ m) ^ i) *
        ∏ x in Finset.range (m + 1), cyclotomic (p ^ x) R) = X ^ p ^ (m + 1) - 1 := by
    intro m
    have := eq_cyclotomic_iff (R := R) (P := ∑ i in range p, (X ^ p ^ m) ^ i)
      (pow_pos hp.pos (m + 1))
    rw [eq_comm] at this
    rw [this]; rw [Nat.prod_properDivisors_prime_pow hp]
  induction n with
  | zero => have := Fact.mk hp; simp [cyclotomic_prime]
  | succ n_n n_ih =>
    rw [← (eq_cyclotomic_iff (pow_pos hp.pos (n_n + 1 + 1)) _).mpr ?_]
    rw [Nat.prod_properDivisors_prime_pow hp]; rw [Finset.prod_range_succ]; rw [n_ih]
    rw [this] at n_ih
    rw [mul_comm _ (∑ i in _]; rw [_)]; rw [n_ih]; rw [geom_sum_mul]; rw [sub_left_inj]; rw [← pow_mul]
    simp only [pow_add, pow_one]

/--
theorem `cyclotomic_prime_pow_mul_X_pow_sub_one` / 定理 `cyclotomic_prime_pow_mul_X_pow_sub_one`

English:
theorem cyclotomic_prime_pow_mul_X_pow_sub_one
  statement: (R : Type*) [CommRing R] (p k : Nat)
  proof: by
  rw [cyclotomic_prime_pow_eq_geom_sum hn.out]; rw [geom_sum_mul]; rw [← pow_mul]; rw [pow_succ]; rw [mul_comm]

中文:
定理 cyclotomic_prime_pow_mul_X_pow_sub_one
  结论: (R : 类型) [交换环 R] (p k : 自然数)
  证明: by
  rw [cyclotomic_prime_pow_eq_geom_sum hn.out]; rw [geom_sum_mul]; rw [← pow_mul]; rw [pow_succ]; rw [mul_comm]

Depends on / 依赖: cyclotomic_prime_pow_eq_geom_sum, geom_sum_mul, hn.out, mul_comm, pow_mul, pow_succ
-/
theorem cyclotomic_prime_pow_mul_X_pow_sub_one (R : Type*) [CommRing R] (p k : Nat)
    [hn : Fact (Nat.Prime p)] :
    cyclotomic (p ^ (k + 1)) R * (X ^ p ^ k - 1) = X ^ p ^ (k + 1) - 1 := by
  rw [cyclotomic_prime_pow_eq_geom_sum hn.out]; rw [geom_sum_mul]; rw [← pow_mul]; rw [pow_succ]; rw [mul_comm]

/--
theorem `cyclotomic_coeff_zero` / 定理 `cyclotomic_coeff_zero`

English:
theorem cyclotomic_coeff_zero
  given: (R : Type*) [CommRing R] {n : Nat} (hn : 1 < n)
  proof: by
  induction n using Nat.strong_induction_on with | _ n hi
  have hprod : (∏ i in Nat.properDivisors n, (Polynomial.cyclotomic i R).coeff 0) = -1 := by
    rw [← Finset.insert_erase (Nat.one_mem_properDivisors_iff_one_lt.2
      (lt_of_lt_of_le one_lt_two hn))]; rw [Finset.prod_insert (Finset.notMem_erase 1 _)]; rw [cyclotomic_one R]
    have hleq : forall j in n.properDivisors.erase 1, 2 <= j := by
      intro j hj
      apply Nat.succ_le_of_lt
      exact (Ne.le_iff_lt (Finset.mem_erase.1 hj).1.symm).mp
        (Nat.succ_le_of_lt (Nat.pos_of_mem_properDivisors (Finset.mem_erase.1 hj).2))
    have hcongr : forall j in n.properDivisors.erase 1, (cyclotomic j R).coeff 0 = 1 := by
      intro j hj
      exact hi j (Nat.mem_properDivisors.1 (Finset.mem_erase.1 hj).2).2 (hleq j hj)
    have hrw : (∏ x in n.properDivisors.erase 1, (cyclotomic x R).coeff 0) = 1 := by
      rw [Finset.prod_congr (refl (n.properDivisors.erase 1)) hcongr]
      simp only [Finset.prod_const_one]
    simp only [hrw, mul_one, zero_sub, coeff_one_zero, coeff_X_zero, coeff_sub]
  have heq : (X ^ n - 1 : R[X]).coeff 0 = -(cyclotomic n R).coeff 0 := by
    rw [← prod_cyclotomic_eq_X_pow_sub_one (zero_le_one.trans_lt hn)]; rw [←
      Nat.cons_self_properDivisors hn.ne_bot]; rw [Finset.prod_cons]; rw [mul_coeff_zero]; rw [coeff_zero_prod]; rw [hprod]; rw [mul_neg]; rw [mul_one]
  have hzero : (X ^ n - 1 : R[X]).coeff 0 = (-1 : R) := by
    rw [coeff_zero_eq_eval_zero _]
    simp only [zero_pow (by positivity : n != 0), eval_X, eval_one, zero_sub, eval_pow, eval_sub]
  rw [hzero] at heq
  exact neg_inj.mp (Eq.symm heq)

中文:
定理 cyclotomic_coeff_zero
  条件: (R : 类型) [交换环 R] {n : 自然数} (hn : 1 < n)
  证明: by
  induction n using Nat.strong_induction_on with | _ n hi
  have hprod : (∏ i in Nat.properDivisors n, (Polynomial.cyclotomic i R).coeff 0) = -1 := by
    rw [← Finset.insert_erase (Nat.one_mem_properDivisors_iff_one_lt.2
      (lt_of_lt_of_le one_lt_two hn))]; rw [Finset.prod_insert (Finset.notMem_erase 1 _)]; rw [cyclotomic_one R]
    have hleq : forall j in n.properDivisors.erase 1, 2 <= j := by
      intro j hj
      apply Nat.succ_le_of_lt
      exact (Ne.le_iff_lt (Finset.mem_erase.1 hj).1.symm).mp
        (Nat.succ_le_of_lt (Nat.pos_of_mem_properDivisors (Finset.mem_erase.1 hj).2))
    have hcongr : forall j in n.properDivisors.erase 1, (cyclotomic j R).coeff 0 = 1 := by
      intro j hj
      exact hi j (Nat.mem_properDivisors.1 (Finset.mem_erase.1 hj).2).2 (hleq j hj)
    have hrw : (∏ x in n.properDivisors.erase 1, (cyclotomic x R).coeff 0) = 1 := by
      rw [Finset.prod_congr (refl (n.properDivisors.erase 1)) hcongr]
      simp only [Finset.prod_const_one]
    simp only [hrw, mul_one, zero_sub, coeff_one_zero, coeff_X_zero, coeff_sub]
  have heq : (X ^ n - 1 : R[X]).coeff 0 = -(cyclotomic n R).coeff 0 := by
    rw [← prod_cyclotomic_eq_X_pow_sub_one (zero_le_one.trans_lt hn)]; rw [←
      Nat.cons_self_properDivisors hn.ne_bot]; rw [Finset.prod_cons]; rw [mul_coeff_zero]; rw [coeff_zero_prod]; rw [hprod]; rw [mul_neg]; rw [mul_one]
  have hzero : (X ^ n - 1 : R[X]).coeff 0 = (-1 : R) := by
    rw [coeff_zero_eq_eval_zero _]
    simp only [zero_pow (by positivity : n != 0), eval_X, eval_one, zero_sub, eval_pow, eval_sub]
  rw [hzero] at heq
  exact neg_inj.mp (Eq.symm heq)

Depends on / 依赖: Finset, Finset.insert_erase, Finset.mem_erase, Finset.notMem_erase, Finset.prod_insert, Nat.one_mem_properDivisors_iff_one_lt, Nat.properDivisors, Nat.strong_induction_on, Nat.succ_le_of_lt, Ne.le_iff_lt, Polynomial, Polynomial.cyclotomic, cyclotomic, cyclotomic_one, insert_erase, le_iff_lt, lt_of_lt_of_le, mem_erase, n.properDivisors.erase, notMem_erase
-/
theorem cyclotomic_coeff_zero (R : Type*) [CommRing R] {n : Nat} (hn : 1 < n) :
    (cyclotomic n R).coeff 0 = 1 := by
  induction n using Nat.strong_induction_on with | _ n hi
  have hprod : (∏ i in Nat.properDivisors n, (Polynomial.cyclotomic i R).coeff 0) = -1 := by
    rw [← Finset.insert_erase (Nat.one_mem_properDivisors_iff_one_lt.2
      (lt_of_lt_of_le one_lt_two hn))]; rw [Finset.prod_insert (Finset.notMem_erase 1 _)]; rw [cyclotomic_one R]
    have hleq : forall j in n.properDivisors.erase 1, 2 <= j := by
      intro j hj
      apply Nat.succ_le_of_lt
      exact (Ne.le_iff_lt (Finset.mem_erase.1 hj).1.symm).mp
        (Nat.succ_le_of_lt (Nat.pos_of_mem_properDivisors (Finset.mem_erase.1 hj).2))
    have hcongr : forall j in n.properDivisors.erase 1, (cyclotomic j R).coeff 0 = 1 := by
      intro j hj
      exact hi j (Nat.mem_properDivisors.1 (Finset.mem_erase.1 hj).2).2 (hleq j hj)
    have hrw : (∏ x in n.properDivisors.erase 1, (cyclotomic x R).coeff 0) = 1 := by
      rw [Finset.prod_congr (refl (n.properDivisors.erase 1)) hcongr]
      simp only [Finset.prod_const_one]
    simp only [hrw, mul_one, zero_sub, coeff_one_zero, coeff_X_zero, coeff_sub]
  have heq : (X ^ n - 1 : R[X]).coeff 0 = -(cyclotomic n R).coeff 0 := by
    rw [← prod_cyclotomic_eq_X_pow_sub_one (zero_le_one.trans_lt hn)]; rw [←
      Nat.cons_self_properDivisors hn.ne_bot]; rw [Finset.prod_cons]; rw [mul_coeff_zero]; rw [coeff_zero_prod]; rw [hprod]; rw [mul_neg]; rw [mul_one]
  have hzero : (X ^ n - 1 : R[X]).coeff 0 = (-1 : R) := by
    rw [coeff_zero_eq_eval_zero _]
    simp only [zero_pow (by positivity : n != 0), eval_X, eval_one, zero_sub, eval_pow, eval_sub]
  rw [hzero] at heq
  exact neg_inj.mp (Eq.symm heq)

/--
theorem `coprime_of_root_cyclotomic` / 定理 `coprime_of_root_cyclotomic`

English:
theorem coprime_of_root_cyclotomic
  statement: {n : Nat} (hpos : 0 < n) {p : Nat} [hprime : Fact p.Prime] {a : Nat}
  proof: by
  apply Nat.Coprime.symm
  rw [hprime.1.coprime_iff_not_dvd]
  intro h
  replace h := (ZMod.natCast_eq_zero_iff a p).2 h
  rw [IsRoot.def]; rw [eq_natCast]; rw [h]; rw [← coeff_zero_eq_eval_zero] at hroot
  by_cases hone : n = 1
  · simp only [hone, cyclotomic_one, zero_sub, coeff_one_zero, coeff_X_zero, neg_eq_zero,
      one_ne_zero, coeff_sub] at hroot
  rw [cyclotomic_coeff_zero (ZMod p) (Nat.succ_le_of_lt
    (lt_of_le_of_ne (Nat.succ_le_of_lt hpos) (Ne.symm hone)))] at hroot
  exact one_ne_zero hroot

中文:
定理 coprime_of_root_cyclotomic
  结论: {n : 自然数} (hpos : 0 < n) {p : 自然数} [hprime : Fact p.素] {a : 自然数}
  证明: by
  apply Nat.Coprime.symm
  rw [hprime.1.coprime_iff_not_dvd]
  intro h
  replace h := (ZMod.natCast_eq_zero_iff a p).2 h
  rw [IsRoot.def]; rw [eq_natCast]; rw [h]; rw [← coeff_zero_eq_eval_zero] at hroot
  by_cases hone : n = 1
  · simp only [hone, cyclotomic_one, zero_sub, coeff_one_zero, coeff_X_zero, neg_eq_zero,
      one_ne_zero, coeff_sub] at hroot
  rw [cyclotomic_coeff_zero (ZMod p) (Nat.succ_le_of_lt
    (lt_of_le_of_ne (Nat.succ_le_of_lt hpos) (Ne.symm hone)))] at hroot
  exact one_ne_zero hroot

Depends on / 依赖: Coprime, IsRoot, IsRoot.def, Nat.Coprime.symm, Nat.succ_le_of_lt, Ne.symm, ZMod.natCast_eq_zero_iff, coeff_X_zero, coeff_one_zero, coeff_sub, coeff_zero_eq_eval_zero, coprime_iff_not_dvd, cyclotomic_coeff_zero, cyclotomic_one, eq_natCast, hprime, lt_of_le_of_ne, natCast_eq_zero_iff, neg_eq_zero, one_ne_zero
-/
theorem coprime_of_root_cyclotomic {n : Nat} (hpos : 0 < n) {p : Nat} [hprime : Fact p.Prime] {a : Nat}
    (hroot : IsRoot (cyclotomic n (ZMod p)) (Nat.castRingHom (ZMod p) a)) : a.Coprime p := by
  apply Nat.Coprime.symm
  rw [hprime.1.coprime_iff_not_dvd]
  intro h
  replace h := (ZMod.natCast_eq_zero_iff a p).2 h
  rw [IsRoot.def]; rw [eq_natCast]; rw [h]; rw [← coeff_zero_eq_eval_zero] at hroot
  by_cases hone : n = 1
  · simp only [hone, cyclotomic_one, zero_sub, coeff_one_zero, coeff_X_zero, neg_eq_zero,
      one_ne_zero, coeff_sub] at hroot
  rw [cyclotomic_coeff_zero (ZMod p) (Nat.succ_le_of_lt
    (lt_of_le_of_ne (Nat.succ_le_of_lt hpos) (Ne.symm hone)))] at hroot
  exact one_ne_zero hroot

end Cyclotomic

section Order

/--
theorem `orderOf_root_cyclotomic_dvd` / 定理 `orderOf_root_cyclotomic_dvd`

English:
theorem orderOf_root_cyclotomic_dvd
  statement: {n : Nat} (hpos : 0 < n) {p : Nat} [Fact p.Prime] {a : Nat}
  proof: by
  apply orderOf_dvd_of_pow_eq_one
  suffices hpow : eval (Nat.castRingHom (ZMod p) a) (X ^ n - 1 : (ZMod p)[X]) = 0 by
    simp only [eval_X, eval_one, eval_pow, eval_sub, eq_natCast] at hpow
    apply Units.val_eq_one.1
    simp only [sub_eq_zero.mp hpow, ZMod.coe_unitOfCoprime, Units.val_pow_eq_pow_val]
  rw [IsRoot.def] at hroot
  rw [← prod_cyclotomic_eq_X_pow_sub_one hpos (ZMod p)]; rw [← Nat.cons_self_properDivisors hpos.ne']; rw [Finset.prod_cons]; rw [eval_mul]; rw [hroot]; rw [zero_mul]

中文:
定理 orderOf_root_cyclotomic_dvd
  结论: {n : 自然数} (hpos : 0 < n) {p : 自然数} [Fact p.素] {a : 自然数}
  证明: by
  apply orderOf_dvd_of_pow_eq_one
  suffices hpow : eval (Nat.castRingHom (ZMod p) a) (X ^ n - 1 : (ZMod p)[X]) = 0 by
    simp only [eval_X, eval_one, eval_pow, eval_sub, eq_natCast] at hpow
    apply Units.val_eq_one.1
    simp only [sub_eq_zero.mp hpow, ZMod.coe_unitOfCoprime, Units.val_pow_eq_pow_val]
  rw [IsRoot.def] at hroot
  rw [← prod_cyclotomic_eq_X_pow_sub_one hpos (ZMod p)]; rw [← Nat.cons_self_properDivisors hpos.ne']; rw [Finset.prod_cons]; rw [eval_mul]; rw [hroot]; rw [zero_mul]

Depends on / 依赖: Finset, Finset.prod_cons, IsRoot, IsRoot.def, Nat.castRingHom, Nat.cons_self_properDivisors, Units.val_eq_one, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, castRingHom, coe_unitOfCoprime, cons_self_properDivisors, eq_natCast, eval_X, eval_mul, eval_one, eval_pow, eval_sub, hpos.ne, orderOf_dvd_of_pow_eq_one
-/
theorem orderOf_root_cyclotomic_dvd {n : Nat} (hpos : 0 < n) {p : Nat} [Fact p.Prime] {a : Nat}
    (hroot : IsRoot (cyclotomic n (ZMod p)) (Nat.castRingHom (ZMod p) a)) :
    orderOf (ZMod.unitOfCoprime a (coprime_of_root_cyclotomic hpos hroot)) ∣ n := by
  apply orderOf_dvd_of_pow_eq_one
  suffices hpow : eval (Nat.castRingHom (ZMod p) a) (X ^ n - 1 : (ZMod p)[X]) = 0 by
    simp only [eval_X, eval_one, eval_pow, eval_sub, eq_natCast] at hpow
    apply Units.val_eq_one.1
    simp only [sub_eq_zero.mp hpow, ZMod.coe_unitOfCoprime, Units.val_pow_eq_pow_val]
  rw [IsRoot.def] at hroot
  rw [← prod_cyclotomic_eq_X_pow_sub_one hpos (ZMod p)]; rw [← Nat.cons_self_properDivisors hpos.ne']; rw [Finset.prod_cons]; rw [eval_mul]; rw [hroot]; rw [zero_mul]

end Order

section miscellaneous

open Finset

variable {R : Type*} [CommRing R] {ζ : R} {n : Nat} (x y : R)

/--
lemma `dvd_C_mul_X_sub_one_pow_add_one` / 引理 `dvd_C_mul_X_sub_one_pow_add_one`

English:
lemma dvd_C_mul_X_sub_one_pow_add_one
  statement: {p : Nat} (hpri : p.Prime)
  proof: by
  have := hpri.dvd_add_pow_sub_pow_of_dvd (C a * X) (-1) (r := C r) ?_ ?_
  · rwa [← sub_eq_add_neg, (hpri.odd_of_ne_two hp).neg_pow, one_pow, sub_neg_eq_add] at this
  · simp only [mul_pow, ← map_pow, dvd_mul_right, (_root_.map_dvd C h₁).trans]
  simp only [map_mul, map_natCast, ← mul_assoc, dvd_mul_right, (_root_.map_dvd C h₂).trans]

中文:
引理 dvd_C_mul_X_sub_one_pow_add_one
  结论: {p : 自然数} (hpri : p.素)
  证明: by
  have := hpri.dvd_add_pow_sub_pow_of_dvd (C a * X) (-1) (r := C r) ?_ ?_
  · rwa [← sub_eq_add_neg, (hpri.odd_of_ne_two hp).neg_pow, one_pow, sub_neg_eq_add] at this
  · simp only [mul_pow, ← map_pow, dvd_mul_right, (_root_.map_dvd C h₁).trans]
  simp only [map_mul, map_natCast, ← mul_assoc, dvd_mul_right, (_root_.map_dvd C h₂).trans]

Depends on / 依赖: _root_, _root_.map_dvd, dvd_add_pow_sub_pow_of_dvd, dvd_mul_right, hpri.dvd_add_pow_sub_pow_of_dvd, hpri.odd_of_ne_two, map_dvd, map_mul, map_natCast, map_pow, mul_assoc, mul_pow, neg_pow, odd_of_ne_two, one_pow, sub_eq_add_neg, sub_neg_eq_add
-/
lemma dvd_C_mul_X_sub_one_pow_add_one {p : Nat} (hpri : p.Prime)
    (hp : p != 2) (a r : R) (h₁ : r ∣ a ^ p) (h₂ : r ∣ p * a) : C r ∣ (C a * X - 1) ^ p + 1 := by
  have := hpri.dvd_add_pow_sub_pow_of_dvd (C a * X) (-1) (r := C r) ?_ ?_
  · rwa [← sub_eq_add_neg, (hpri.odd_of_ne_two hp).neg_pow, one_pow, sub_neg_eq_add] at this
  · simp only [mul_pow, ← map_pow, dvd_mul_right, (_root_.map_dvd C h₁).trans]
  simp only [map_mul, map_natCast, ← mul_assoc, dvd_mul_right, (_root_.map_dvd C h₂).trans]

/--
theorem `_root_.IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul_field` / 定理 `_root_.IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul_field`

English:
theorem _root_.IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul_field
  statement: {K : Type*}
  proof: by
  by_cases hy : y = 0
  · simp only [hy, zero_pow (Nat.ne_zero_of_lt hpos), sub_zero, mul_zero, prod_const]
    congr
    rw [h.card_nthRootsFinset]
  convert!
congr_arg (eval (x / y) · * y ^ card (nthRootsFinset n (1 : K)))
      X_pow_sub_one_eq_prod hpos h using 1
  · simp [sub_mul, div_pow, hy, h.card_nthRootsFinset]
  · simp [eval_prod, prod_mul_pow_card, sub_mul, hy]

中文:
定理 _root_.是PrimitiveRoot.pow_sub_pow_eq_prod_sub_mul_field
  结论: {K : 类型}
  证明: by
  by_cases hy : y = 0
  · simp only [hy, zero_pow (Nat.ne_zero_of_lt hpos), sub_zero, mul_zero, prod_const]
    congr
    rw [h.card_nthRootsFinset]
  convert!
congr_arg (eval (x / y) · * y ^ card (nthRootsFinset n (1 : K)))
      X_pow_sub_one_eq_prod hpos h using 1
  · simp [sub_mul, div_pow, hy, h.card_nthRootsFinset]
  · simp [eval_prod, prod_mul_pow_card, sub_mul, hy]
-/
private theorem _root_.IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul_field {K : Type*}
    [Field K] {ζ : K} (x y : K) (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) :
    x ^ n - y ^ n = ∏ ζ in nthRootsFinset n (1 : K), (x - ζ * y) := by
  by_cases hy : y = 0
  · simp only [hy, zero_pow (Nat.ne_zero_of_lt hpos), sub_zero, mul_zero, prod_const]
    congr
    rw [h.card_nthRootsFinset]
  convert!
congr_arg (eval (x / y) · * y ^ card (nthRootsFinset n (1 : K)))
      X_pow_sub_one_eq_prod hpos h using 1
  · simp [sub_mul, div_pow, hy, h.card_nthRootsFinset]
  · simp [eval_prod, prod_mul_pow_card, sub_mul, hy]

variable [IsDomain R]

/--
theorem `_root_.IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul` / 定理 `_root_.IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul`

English:
theorem _root_.IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul
  statement: (hpos : 0 < n)
  proof: by
  let K := FractionRing R
  apply FaithfulSMul.algebraMap_injective R K
  rw [map_sub]; rw [map_pow]; rw [map_pow]; rw [map_prod]
  simp_rw [map_sub, map_mul]
  have h' : IsPrimitiveRoot (algebraMap R K ζ) n :=
h.map_of_injective FaithfulSMul.algebraMap_injective R K
  rw [h'.pow_sub_pow_eq_prod_sub_mul_field _ _ hpos]
  refine (prod_nbij (algebraMap R K) (fun a ha => map_mem_nthRootsFinset_one ha _)
    (fun a _ b _ H => FaithfulSMul.algebraMap_injective R K H) (fun a ha => ?_) (fun _ _ => rfl)).symm
  have := Set.surj_on_of_inj_on_of_ncard_le (s := nthRootsFinset n (1 : R))
    (t := nthRootsFinset n (1 : K)) _ (fun _ hr => map_mem_nthRootsFinset_one hr _)
    (fun a _ b _ H => FaithfulSMul.algebraMap_injective R K H)
    (by simp [h.card_nthRootsFinset, h'.card_nthRootsFinset])
  obtain ⟨x, hx, hx1⟩ := this _ ha
  exact ⟨x, hx, hx1.symm⟩

中文:
定理 _root_.是PrimitiveRoot.pow_sub_pow_eq_prod_sub_mul
  结论: (hpos : 0 < n)
  证明: by
  let K := FractionRing R
  apply FaithfulSMul.algebraMap_injective R K
  rw [map_sub]; rw [map_pow]; rw [map_pow]; rw [map_prod]
  simp_rw [map_sub, map_mul]
  have h' : IsPrimitiveRoot (algebraMap R K ζ) n :=
h.map_of_injective FaithfulSMul.algebraMap_injective R K
  rw [h'.pow_sub_pow_eq_prod_sub_mul_field _ _ hpos]
  refine (prod_nbij (algebraMap R K) (fun a ha => map_mem_nthRootsFinset_one ha _)
    (fun a _ b _ H => FaithfulSMul.algebraMap_injective R K H) (fun a ha => ?_) (fun _ _ => rfl)).symm
  have := Set.surj_on_of_inj_on_of_ncard_le (s := nthRootsFinset n (1 : R))
    (t := nthRootsFinset n (1 : K)) _ (fun _ hr => map_mem_nthRootsFinset_one hr _)
    (fun a _ b _ H => FaithfulSMul.algebraMap_injective R K H)
    (by simp [h.card_nthRootsFinset, h'.card_nthRootsFinset])
  obtain ⟨x, hx, hx1⟩ := this _ ha
  exact ⟨x, hx, hx1.symm⟩

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, FractionRing, IsPrimitiveRoot, algebraMap, algebraMap_injective, h.map_of_injective, map_mem_nthRootsFinset_one, map_mul, map_of_injective, map_pow, map_prod, map_sub, pow_sub_pow_eq_prod_sub_mul_field, prod_nbij, simp_rw
-/
theorem _root_.IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul (hpos : 0 < n)
    (h : IsPrimitiveRoot ζ n) : x ^ n - y ^ n = ∏ ζ in nthRootsFinset n (1 : R), (x - ζ * y) := by
  let K := FractionRing R
  apply FaithfulSMul.algebraMap_injective R K
  rw [map_sub]; rw [map_pow]; rw [map_pow]; rw [map_prod]
  simp_rw [map_sub, map_mul]
  have h' : IsPrimitiveRoot (algebraMap R K ζ) n :=
h.map_of_injective FaithfulSMul.algebraMap_injective R K
  rw [h'.pow_sub_pow_eq_prod_sub_mul_field _ _ hpos]
  refine (prod_nbij (algebraMap R K) (fun a ha => map_mem_nthRootsFinset_one ha _)
    (fun a _ b _ H => FaithfulSMul.algebraMap_injective R K H) (fun a ha => ?_) (fun _ _ => rfl)).symm
  have := Set.surj_on_of_inj_on_of_ncard_le (s := nthRootsFinset n (1 : R))
    (t := nthRootsFinset n (1 : K)) _ (fun _ hr => map_mem_nthRootsFinset_one hr _)
    (fun a _ b _ H => FaithfulSMul.algebraMap_injective R K H)
    (by simp [h.card_nthRootsFinset, h'.card_nthRootsFinset])
  obtain ⟨x, hx, hx1⟩ := this _ ha
  exact ⟨x, hx, hx1.symm⟩

/--
theorem `_root_.IsPrimitiveRoot.pow_add_pow_eq_prod_add_mul` / 定理 `_root_.IsPrimitiveRoot.pow_add_pow_eq_prod_add_mul`

English:
theorem _root_.IsPrimitiveRoot.pow_add_pow_eq_prod_add_mul
  statement: (hodd : Odd n)
  proof: by
  simpa [hodd.neg_pow] using h.pow_sub_pow_eq_prod_sub_mul x (-y) hodd.pos

中文:
定理 _root_.是PrimitiveRoot.pow_add_pow_eq_prod_add_mul
  结论: (hodd : Odd n)
  证明: by
  simpa [hodd.neg_pow] using h.pow_sub_pow_eq_prod_sub_mul x (-y) hodd.pos

Depends on / 依赖: h.pow_sub_pow_eq_prod_sub_mul, hodd.neg_pow, hodd.pos, neg_pow, pow_sub_pow_eq_prod_sub_mul
-/
theorem _root_.IsPrimitiveRoot.pow_add_pow_eq_prod_add_mul (hodd : Odd n)
    (h : IsPrimitiveRoot ζ n) : x ^ n + y ^ n = ∏ ζ in nthRootsFinset n (1 : R), (x + ζ * y) := by
  simpa [hodd.neg_pow] using h.pow_sub_pow_eq_prod_sub_mul x (-y) hodd.pos

/--
theorem `separable_cyclotomic` / 定理 `separable_cyclotomic`

English:
theorem separable_cyclotomic
  given: (n : Nat) (K : Type*) [Field K] [NeZero (n : K)]
  proof: .of_dvd (separable_X_pow_sub_C 1 NeZero.out one_ne_zero) (cyclotomic.dvd_X_pow_sub_one n K)

中文:
定理 separable_cyclotomic
  条件: (n : 自然数) (K : 类型) [域 K] [NeZero (n : K)]
  证明: .of_dvd (separable_X_pow_sub_C 1 NeZero.out one_ne_zero) (cyclotomic.dvd_X_pow_sub_one n K)

Depends on / 依赖: NeZero, NeZero.out, cyclotomic, cyclotomic.dvd_X_pow_sub_one, dvd_X_pow_sub_one, of_dvd, one_ne_zero, separable_X_pow_sub_C
-/
theorem separable_cyclotomic (n : Nat) (K : Type*) [Field K] [NeZero (n : K)] :
    (cyclotomic n K).Separable :=
  .of_dvd (separable_X_pow_sub_C 1 NeZero.out one_ne_zero) (cyclotomic.dvd_X_pow_sub_one n K)

/--
theorem `squarefree_cyclotomic` / 定理 `squarefree_cyclotomic`

English:
theorem squarefree_cyclotomic
  given: (n : Nat) (K : Type*) [Field K] [NeZero (n : K)]
  proof: (separable_cyclotomic n K).squarefree

中文:
定理 squarefree_cyclotomic
  条件: (n : 自然数) (K : 类型) [域 K] [NeZero (n : K)]
  证明: (separable_cyclotomic n K).squarefree

Depends on / 依赖: separable_cyclotomic, squarefree
-/
theorem squarefree_cyclotomic (n : Nat) (K : Type*) [Field K] [NeZero (n : K)] :
    Squarefree (cyclotomic n K) :=
  (separable_cyclotomic n K).squarefree

end miscellaneous

end Polynomial
