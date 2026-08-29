/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Cyclotomic polynomials and `expand`.

We gather results relating cyclotomic polynomials and `expand`.

## Main results

* `Polynomial.cyclotomic_expand_eq_cyclotomic_mul` : If `p` is a prime such that `¬ p ∣ n`, then
  `expand R p (cyclotomic n R) = (cyclotomic (n * p) R) * (cyclotomic n R)`.
* `Polynomial.cyclotomic_expand_eq_cyclotomic` : If `p` is a prime such that `p ∣ n`, then
  `expand R p (cyclotomic n R) = cyclotomic (p * n) R`.
* `Polynomial.cyclotomic_mul_prime_eq_pow_of_not_dvd` : If `R` is of characteristic `p` and
  `¬p ∣ n`, then `cyclotomic (n * p) R = (cyclotomic n R) ^ (p - 1)`.
* `Polynomial.cyclotomic_mul_prime_dvd_eq_pow` : If `R` is of characteristic `p` and `p ∣ n`, then
  `cyclotomic (n * p) R = (cyclotomic n R) ^ p`.
* `Polynomial.cyclotomic_mul_prime_pow_eq` : If `R` is of characteristic `p` and `¬p ∣ m`, then
  `cyclotomic (p ^ k * m) R = (cyclotomic m R) ^ (p ^ k - p ^ (k - 1))`.
-/

public section


namespace Polynomial

/-- If `p` is a prime such that `¬ p ∣ n`, then
`expand R p (cyclotomic n R) = (cyclotomic (n * p) R) * (cyclotomic n R)`. -/
@[simp]
/--
theorem `cyclotomic_expand_eq_cyclotomic_mul` / 定理 `cyclotomic_expand_eq_cyclotomic_mul`

English:
theorem cyclotomic_expand_eq_cyclotomic_mul
  statement: {p n : Nat} (hp : Nat.Prime p) (hdiv : ¬p ∣ n)
  proof: by
  rcases Nat.eq_zero_or_pos n with (rfl | hnpos)
  · simp
  have := NeZero.of_pos hnpos
  suffices expand Int p (cyclotomic n Int) = cyclotomic (n * p) Int * cyclotomic n Int by
    rw [← map_cyclotomic_int]; rw [← map_expand]; rw [this]; rw [Polynomial.map_mul]; rw [map_cyclotomic_int]; rw [map_

中文:
定理 cyclotomic_expand_eq_cyclotomic_mul
  结论: {p n : 自然数} (hp : 自然数.Prime p) (hdiv : ¬p ∣ n)
  证明: by
  rcases Nat.eq_zero_or_pos n with (rfl | hnpos)
  · simp
  have := NeZero.of_pos hnpos
  suffices expand Int p (cyclotomic n Int) = cyclotomic (n * p) Int * cyclotomic n Int by
    rw [← map_cyclotomic_int]; rw [← map_expand]; rw [this]; rw [Polynomial.map_mul]; rw [map_cyclotomic_int]; rw [map_

Depends on / 依赖: IsPrimitive, IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast, Nat.eq_zero_or_pos, NeZero, NeZero.of_pos, Polynomial, Polynomial.map_mul, cyclotomic, cyclotomic.monic, dvd_iff_map_cast_dvd_map_cast, eq_of_monic_of_dvd_of_natDegree_le, eq_zero_or_pos, expand, hp.pos, map_cyclotomic, map_cyclotomic_int, map_expand, map_mul, of_pos
-/
theorem cyclotomic_expand_eq_cyclotomic_mul {p n : Nat} (hp : Nat.Prime p) (hdiv : ¬p ∣ n)
    (R : Type*) [CommRing R] :
    expand R p (cyclotomic n R) = cyclotomic (n * p) R * cyclotomic n R := by
  rcases Nat.eq_zero_or_pos n with (rfl | hnpos)
  · simp
  have := NeZero.of_pos hnpos
  suffices expand Int p (cyclotomic n Int) = cyclotomic (n * p) Int * cyclotomic n Int by
    rw [← map_cyclotomic_int]; rw [← map_expand]; rw [this]; rw [Polynomial.map_mul]; rw [map_cyclotomic_int]; rw [map_cyclotomic]
  refine eq_of_monic_of_dvd_of_natDegree_le ((cyclotomic.monic _ Int).mul (cyclotomic.monic _ Int))
    ((cyclotomic.monic n Int).expand hp.pos) ?_ ?_
  · refine (IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _
      ((cyclotomic.isPrimitive (n * p) Int).mul (cyclotomic.isPrimitive n Int))).2 ?_
    rw [Polynomial.map_mul]; rw [map_cyclotomic_int]; rw [map_cyclotomic_int]; rw [map_expand]; rw [map_cyclotomic_int]
    refine IsCoprime.mul_dvd (cyclotomic.isCoprime_rat fun h => ?_) ?_ ?_
    · replace h : n * p = n * 1 := by simp [h]
      exact Nat.Prime.ne_one hp (mul_left_cancel₀ hnpos.ne' h)
    · have hpos : 0 < n * p := mul_pos hnpos hp.pos
      have hprim := Complex.isPrimitiveRoot_exp _ hpos.ne'
      rw [cyclotomic_eq_minpoly_rat hprim hpos]
      refine minpoly.dvd Rat _ ?_
      rw [← eval_map_algebraMap]; rw [map_expand]; rw [map_cyclotomic]; rw [expand_eval]; rw [← IsRoot.def]; rw [@isRoot_cyclotomic_iff]
      convert! IsPrimitiveRoot.pow_of_dvd hprim hp.ne_zero (dvd_mul_left p n)
      rw [Nat.mul_div_cancel _ (Nat.Prime.pos hp)]
    · have hprim := Complex.isPrimitiveRoot_exp _ hnpos.ne.symm
      rw [cyclotomic_eq_minpoly_rat hprim hnpos]
      refine minpoly.dvd Rat _ ?_
      rw [← eval_map_algebraMap]; rw [map_expand]; rw [expand_eval]; rw [← IsRoot.def]; rw [←
        cyclotomic_eq_minpoly_rat hprim hnpos]; rw [map_cyclotomic]; rw [@isRoot_cyclotomic_iff]
      exact IsPrimitiveRoot.pow_of_prime hprim hp hdiv
  · rw [natDegree_expand, natDegree_cyclotomic,
      natDegree_mul (cyclotomic_ne_zero _ Int) (cyclotomic_ne_zero _ Int), natDegree_cyclotomic,
      natDegree_cyclotomic, mul_comm n,
      Nat.totient_mul ((Nat.Prime.coprime_iff_not_dvd hp).2 hdiv), Nat.totient_prime hp,
      mul_comm (p - 1), ← Nat.mul_succ, Nat.sub_one, Nat.succ_pred_eq_of_pos hp.pos]

@[simp]
/--
lemma `cyclotomic_six` / 引理 `cyclotomic_six`

English:
lemma cyclotomic_six
  given: (R : Type*) [Ring R]
  statement: cyclotomic 6 R = X ^ 2 - X + 1
  proof: by
  suffices cyclotomic 6 Int = X ^ 2 - X + 1 by
    rw [← map_cyclotomic_int]; rw [this]
    simp
  apply mul_right_cancel₀ (cyclotomic_ne_zero 2 Int)
  rw [show 6 = 2 * 3 by rfl]; rw [← cyclotomic_expand_eq_cyclotomic_mul Nat.prime_three (by norm_num1)]
  simp; ring

中文:
引理 cyclotomic_six
  条件: (R : 类型) [Ring R]
  结论: cyclotomic 6 R = X ^ 2 - X + 1
  证明: by
  suffices cyclotomic 6 Int = X ^ 2 - X + 1 by
    rw [← map_cyclotomic_int]; rw [this]
    simp
  apply mul_right_cancel₀ (cyclotomic_ne_zero 2 Int)
  rw [show 6 = 2 * 3 by rfl]; rw [← cyclotomic_expand_eq_cyclotomic_mul Nat.prime_three (by norm_num1)]
  simp; ring

Depends on / 依赖: Nat.prime_three, cyclotomic, cyclotomic_expand_eq_cyclotomic_mul, cyclotomic_ne_zero, map_cyclotomic_int, norm_num1, prime_three
-/
lemma cyclotomic_six (R : Type*) [Ring R] : cyclotomic 6 R = X ^ 2 - X + 1 := by
  suffices cyclotomic 6 Int = X ^ 2 - X + 1 by
    rw [← map_cyclotomic_int]; rw [this]
    simp
  apply mul_right_cancel₀ (cyclotomic_ne_zero 2 Int)
  rw [show 6 = 2 * 3 by rfl]; rw [← cyclotomic_expand_eq_cyclotomic_mul Nat.prime_three (by norm_num1)]
  simp; ring

/-- If `p` is a prime such that `p ∣ n`, then
`expand R p (cyclotomic n R) = cyclotomic (p * n) R`. -/
@[simp]
/--
theorem `cyclotomic_expand_eq_cyclotomic` / 定理 `cyclotomic_expand_eq_cyclotomic`

English:
theorem cyclotomic_expand_eq_cyclotomic
  statement: {p n : Nat} (hp : Nat.Prime p) (hdiv : p ∣ n) (R : Type*)
  proof: by
  rcases n.eq_zero_or_pos with (rfl | hzero)
  · simp
  have := NeZero.of_pos hzero
  suffices expand Int p (cyclotomic n Int) = cyclotomic (n * p) Int by
    rw [← map_cyclotomic_int]; rw [← map_expand]; rw [this]; rw [map_cyclotomic_int]
  refine eq_of_monic_of_dvd_of_natDegree_le (cyclotomic.m

中文:
定理 cyclotomic_expand_eq_cyclotomic
  结论: {p n : 自然数} (hp : 自然数.Prime p) (hdiv : p ∣ n) (R : 类型)
  证明: by
  rcases n.eq_zero_or_pos with (rfl | hzero)
  · simp
  have := NeZero.of_pos hzero
  suffices expand Int p (cyclotomic n Int) = cyclotomic (n * p) Int by
    rw [← map_cyclotomic_int]; rw [← map_expand]; rw [this]; rw [map_cyclotomic_int]
  refine eq_of_monic_of_dvd_of_natDegree_le (cyclotomic.m

Depends on / 依赖: Complex.isPrimitiveRoot_exp, Nat.mul_pos, NeZero, NeZero.of_pos, cyclotomic, cyclotomic.monic, cyclotomic_eq_minpoly, eq_of_monic_of_dvd_of_natDegree_le, eq_zero_or_pos, expand, hp.pos, hpos.ne.symm, isPrimitiveRoot_exp, map_cyclotomic_int, map_expand, minpoly, minpoly.isInt, mul_pos, n.eq_zero_or_pos, of_pos
-/
theorem cyclotomic_expand_eq_cyclotomic {p n : Nat} (hp : Nat.Prime p) (hdiv : p ∣ n) (R : Type*)
    [CommRing R] : expand R p (cyclotomic n R) = cyclotomic (n * p) R := by
  rcases n.eq_zero_or_pos with (rfl | hzero)
  · simp
  have := NeZero.of_pos hzero
  suffices expand Int p (cyclotomic n Int) = cyclotomic (n * p) Int by
    rw [← map_cyclotomic_int]; rw [← map_expand]; rw [this]; rw [map_cyclotomic_int]
  refine eq_of_monic_of_dvd_of_natDegree_le (cyclotomic.monic _ Int)
    ((cyclotomic.monic n Int).expand hp.pos) ?_ ?_
  · have hpos := Nat.mul_pos hzero hp.pos
    have hprim := Complex.isPrimitiveRoot_exp _ hpos.ne.symm
    rw [cyclotomic_eq_minpoly hprim hpos]
    refine minpoly.isIntegrallyClosed_dvd (hprim.isIntegral hpos) ?_
    rw [← eval_map_algebraMap]; rw [map_expand]; rw [map_cyclotomic]; rw [expand_eval]; rw [← IsRoot.def]; rw [@isRoot_cyclotomic_iff]
    convert! IsPrimitiveRoot.pow_of_dvd hprim hp.ne_zero (dvd_mul_left p n)
    rw [Nat.mul_div_cancel _ hp.pos]
  · rw [natDegree_expand, natDegree_cyclotomic, natDegree_cyclotomic, mul_comm n,
      Nat.totient_mul_of_prime_of_dvd hp hdiv, mul_comm]

/--
theorem `cyclotomic_irreducible_pow_of_irreducible_pow` / 定理 `cyclotomic_irreducible_pow_of_irreducible_pow`

English:
theorem cyclotomic_irreducible_pow_of_irreducible_pow
  statement: {p : Nat} (hp : Nat.Prime p) {R} [CommRing R]
  proof: by
  rcases m.eq_zero_or_pos with (rfl | hm)
  · simpa using irreducible_X_sub_C (1 : R)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction k with
  | zero => simpa using h
  | succ k hk =>
    have : m + k != 0 := (add_pos_of_pos_of_nonneg hm k.zero_le).ne'
    rw [Nat.add_succ]; rw [pow_

中文:
定理 cyclotomic_irreducible_pow_of_irreducible_pow
  结论: {p : 自然数} (hp : 自然数.Prime p) {R} [CommRing R]
  证明: by
  rcases m.eq_zero_or_pos with (rfl | hm)
  · simpa using irreducible_X_sub_C (1 : R)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction k with
  | zero => simpa using h
  | succ k hk =>
    have : m + k != 0 := (add_pos_of_pos_of_nonneg hm k.zero_le).ne'
    rw [Nat.add_succ]; rw [pow_

Depends on / 依赖: Nat.add_succ, Nat.exists_eq_add_of_le, add_pos_of_pos_of_nonneg, add_succ, cyclotomic_expand_eq_cyclotomic, dvd_pow_self, eq_zero_or_pos, exists_eq_add_of_le, hp.ne_zero, irreducible_X_sub_C, k.zero_le, m.eq_zero_or_pos, ne_zero, of_irreducible_expand, pow_succ, zero_le
-/
theorem cyclotomic_irreducible_pow_of_irreducible_pow {p : Nat} (hp : Nat.Prime p) {R} [CommRing R]
    [IsDomain R] {n m : Nat} (hmn : m <= n) (h : Irreducible (cyclotomic (p ^ n) R)) :
    Irreducible (cyclotomic (p ^ m) R) := by
  rcases m.eq_zero_or_pos with (rfl | hm)
  · simpa using irreducible_X_sub_C (1 : R)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction k with
  | zero => simpa using h
  | succ k hk =>
    have : m + k != 0 := (add_pos_of_pos_of_nonneg hm k.zero_le).ne'
    rw [Nat.add_succ]; rw [pow_succ]; rw [← cyclotomic_expand_eq_cyclotomic hp <| dvd_pow_self p this] at h
    exact hk (by lia) (of_irreducible_expand hp.ne_zero h)

/--
theorem `cyclotomic_irreducible_of_irreducible_pow` / 定理 `cyclotomic_irreducible_of_irreducible_pow`

English:
theorem cyclotomic_irreducible_of_irreducible_pow
  statement: {p : Nat} (hp : Nat.Prime p) {R} [CommRing R]
  proof: pow_one p ▸ cyclotomic_irreducible_pow_of_irreducible_pow hp hn.bot_lt h

中文:
定理 cyclotomic_irreducible_of_irreducible_pow
  结论: {p : 自然数} (hp : 自然数.Prime p) {R} [CommRing R]
  证明: pow_one p ▸ cyclotomic_irreducible_pow_of_irreducible_pow hp hn.bot_lt h

Depends on / 依赖: bot_lt, cyclotomic_irreducible_pow_of_irreducible_pow, hn.bot_lt, pow_one
-/
theorem cyclotomic_irreducible_of_irreducible_pow {p : Nat} (hp : Nat.Prime p) {R} [CommRing R]
    [IsDomain R] {n : Nat} (hn : n != 0) (h : Irreducible (cyclotomic (p ^ n) R)) :
    Irreducible (cyclotomic p R) :=
  pow_one p ▸ cyclotomic_irreducible_pow_of_irreducible_pow hp hn.bot_lt h

section CharP

/--
theorem `cyclotomic_mul_prime_eq_pow_of_not_dvd` / 定理 `cyclotomic_mul_prime_eq_pow_of_not_dvd`

English:
theorem cyclotomic_mul_prime_eq_pow_of_not_dvd
  statement: (R : Type*) {p n : Nat} [hp : Fact (Nat.Prime p)]
  proof: by
  let : Algebra (ZMod p) R := ZMod.algebra _ _
  suffices cyclotomic (n * p) (ZMod p) = cyclotomic n (ZMod p) ^ (p - 1) by
    rw [← map_cyclotomic _ (algebraMap (ZMod p) R)]; rw [← map_cyclotomic _ (algebraMap (ZMod p) R)]; rw [this]; rw [Polynomial.map_pow]
  apply mul_right_injective₀ (cycloto

中文:
定理 cyclotomic_mul_prime_eq_pow_of_not_dvd
  结论: (R : 类型) {p n : 自然数} [hp : Fact (自然数.Prime p)]
  证明: by
  let : Algebra (ZMod p) R := ZMod.algebra _ _
  suffices cyclotomic (n * p) (ZMod p) = cyclotomic n (ZMod p) ^ (p - 1) by
    rw [← map_cyclotomic _ (algebraMap (ZMod p) R)]; rw [← map_cyclotomic _ (algebraMap (ZMod p) R)]; rw [this]; rw [Polynomial.map_pow]
  apply mul_right_injective₀ (cycloto

Depends on / 依赖: Algebra, Polynomial, Polynomial.map_pow, ZMod.algebra, ZMod.expand_card, algebra, algebraMap, conv_rhs, cyclotomic, cyclotomic_expa, cyclotomic_ne_zero, expand_card, hp.out.one_lt.le, map_cyclotomic, map_cyclotomic_int, map_expand, map_pow, mul_comm, one_lt, pow_succ
-/
theorem cyclotomic_mul_prime_eq_pow_of_not_dvd (R : Type*) {p n : Nat} [hp : Fact (Nat.Prime p)]
    [Ring R] [CharP R p] (hn : ¬p ∣ n) : cyclotomic (n * p) R = cyclotomic n R ^ (p - 1) := by
  let : Algebra (ZMod p) R := ZMod.algebra _ _
  suffices cyclotomic (n * p) (ZMod p) = cyclotomic n (ZMod p) ^ (p - 1) by
    rw [← map_cyclotomic _ (algebraMap (ZMod p) R)]; rw [← map_cyclotomic _ (algebraMap (ZMod p) R)]; rw [this]; rw [Polynomial.map_pow]
  apply mul_right_injective₀ (cyclotomic_ne_zero n <| ZMod p); dsimp
  rw [← pow_succ']; rw [tsub_add_cancel_of_le hp.out.one_lt.le]; rw [mul_comm]; rw [← ZMod.expand_card]
  conv_rhs => rw [← map_cyclotomic_int]
  rw [← map_expand]; rw [cyclotomic_expand_eq_cyclotomic_mul hp.out hn]; rw [Polynomial.map_mul]; rw [map_cyclotomic]; rw [map_cyclotomic]

/--
theorem `cyclotomic_mul_prime_dvd_eq_pow` / 定理 `cyclotomic_mul_prime_dvd_eq_pow`

English:
theorem cyclotomic_mul_prime_dvd_eq_pow
  statement: (R : Type*) {p n : Nat} [hp : Fact (Nat.Prime p)] [Ring R]
  proof: by
  let : Algebra (ZMod p) R := ZMod.algebra _ _
  suffices cyclotomic (n * p) (ZMod p) = cyclotomic n (ZMod p) ^ p by
    rw [← map_cyclotomic _ (algebraMap (ZMod p) R)]; rw [← map_cyclotomic _ (algebraMap (ZMod p) R)]; rw [this]; rw [Polynomial.map_pow]
  rw [← ZMod.expand_card]; rw [← map_cyclot

中文:
定理 cyclotomic_mul_prime_dvd_eq_pow
  结论: (R : 类型) {p n : 自然数} [hp : Fact (自然数.Prime p)] [Ring R]
  证明: by
  let : Algebra (ZMod p) R := ZMod.algebra _ _
  suffices cyclotomic (n * p) (ZMod p) = cyclotomic n (ZMod p) ^ p by
    rw [← map_cyclotomic _ (algebraMap (ZMod p) R)]; rw [← map_cyclotomic _ (algebraMap (ZMod p) R)]; rw [this]; rw [Polynomial.map_pow]
  rw [← ZMod.expand_card]; rw [← map_cyclot

Depends on / 依赖: Algebra, Polynomial, Polynomial.map_pow, ZMod.algebra, ZMod.expand_card, algebra, algebraMap, cyclotomic, cyclotomic_expand_eq_cyclotomic, expand_card, hp.out, map_cyclotomic, map_cyclotomic_int, map_expand, map_pow
-/
theorem cyclotomic_mul_prime_dvd_eq_pow (R : Type*) {p n : Nat} [hp : Fact (Nat.Prime p)] [Ring R]
    [CharP R p] (hn : p ∣ n) : cyclotomic (n * p) R = cyclotomic n R ^ p := by
  let : Algebra (ZMod p) R := ZMod.algebra _ _
  suffices cyclotomic (n * p) (ZMod p) = cyclotomic n (ZMod p) ^ p by
    rw [← map_cyclotomic _ (algebraMap (ZMod p) R)]; rw [← map_cyclotomic _ (algebraMap (ZMod p) R)]; rw [this]; rw [Polynomial.map_pow]
  rw [← ZMod.expand_card]; rw [← map_cyclotomic_int n]; rw [← map_expand]; rw [cyclotomic_expand_eq_cyclotomic hp.out hn]; rw [map_cyclotomic]

/--
theorem `cyclotomic_mul_prime_pow_eq` / 定理 `cyclotomic_mul_prime_pow_eq`

English:
theorem cyclotomic_mul_prime_pow_eq
  statement: (R : Type*) {p m : Nat} [Fact (Nat.Prime p)] [Ring R] [CharP R p]
  proof: ⟨p ^ a * m, by rw [← mul_assoc, pow_succ']⟩
    rw [pow_succ']; rw [mul_assoc]; rw [mul_comm]; rw [cyclotomic_mul_prime_dvd_eq_pow R hdiv]; rw [cyclotomic_mul_prime_pow_eq _ _ a.succ_pos]; rw [← pow_mul]
    · simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      rw [Nat.mul_sub_right_distrib]; r

中文:
定理 cyclotomic_mul_prime_pow_eq
  结论: (R : 类型) {p m : 自然数} [Fact (自然数.Prime p)] [Ring R] [CharP R p]
  证明: ⟨p ^ a * m, by rw [← mul_assoc, pow_succ']⟩
    rw [pow_succ']; rw [mul_assoc]; rw [mul_comm]; rw [cyclotomic_mul_prime_dvd_eq_pow R hdiv]; rw [cyclotomic_mul_prime_pow_eq _ _ a.succ_pos]; rw [← pow_mul]
    · simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      rw [Nat.mul_sub_right_distrib]; r

Depends on / 依赖: mul_assoc, pow_succ
-/
theorem cyclotomic_mul_prime_pow_eq (R : Type*) {p m : Nat} [Fact (Nat.Prime p)] [Ring R] [CharP R p]
    (hm : ¬p ∣ m) : forall {k}, 0 < k -> cyclotomic (p ^ k * m) R = cyclotomic m R ^ (p ^ k - p ^ (k - 1))
  | 1, _ => by
    rw [pow_one]; rw [Nat.sub_self]; rw [pow_zero]; rw [mul_comm]; rw [cyclotomic_mul_prime_eq_pow_of_not_dvd R hm]
  | a + 2, _ => by
    have hdiv : p ∣ p ^ a.succ * m := ⟨p ^ a * m, by rw [← mul_assoc, pow_succ']⟩
    rw [pow_succ']; rw [mul_assoc]; rw [mul_comm]; rw [cyclotomic_mul_prime_dvd_eq_pow R hdiv]; rw [cyclotomic_mul_prime_pow_eq _ _ a.succ_pos]; rw [← pow_mul]
    · simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      rw [Nat.mul_sub_right_distrib]; rw [mul_comm]; rw [pow_succ]
    · assumption

/--
theorem `isRoot_cyclotomic_prime_pow_mul_iff_of_charP` / 定理 `isRoot_cyclotomic_prime_pow_mul_iff_of_charP`

English:
theorem isRoot_cyclotomic_prime_pow_mul_iff_of_charP
  statement: {m k p : Nat} {R : Type*} [CommRing R]
  proof: by
  rcases k.eq_zero_or_pos with (rfl | hk)
  · rw [pow_zero, one_mul, isRoot_cyclotomic_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [IsRoot.def, cyclotomic_mul_prime_pow_eq R (NeZero.not_char_dvd R p m) hk, eval_pow]
      at h
    replace h := eq_zero_of_pow_eq_zero h
    rwa [← IsRoot.def, i

中文:
定理 isRoot_cyclotomic_prime_pow_mul_iff_of_charP
  结论: {m k p : 自然数} {R : 类型} [CommRing R]
  证明: by
  rcases k.eq_zero_or_pos with (rfl | hk)
  · rw [pow_zero, one_mul, isRoot_cyclotomic_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [IsRoot.def, cyclotomic_mul_prime_pow_eq R (NeZero.not_char_dvd R p m) hk, eval_pow]
      at h
    replace h := eq_zero_of_pow_eq_zero h
    rwa [← IsRoot.def, i

Depends on / 依赖: IsRoot, IsRoot.def, Nat.sub_ne_zero_of_l, NeZero, NeZero.not_char_dvd, cyclotomic_mul_prime_pow_eq, eq_zero_of_pow_eq_zero, eq_zero_or_pos, eval_pow, isRoot_cyclotomic_iff, k.eq_zero_or_pos, not_char_dvd, one_mul, pow_zero, replace, sub_ne_zero_of_l, zero_pow
-/
theorem isRoot_cyclotomic_prime_pow_mul_iff_of_charP {m k p : Nat} {R : Type*} [CommRing R]
    [IsDomain R] [hp : Fact (Nat.Prime p)] [hchar : CharP R p] {μ : R} [NeZero (m : R)] :
    (Polynomial.cyclotomic (p ^ k * m) R).IsRoot μ ↔ IsPrimitiveRoot μ m := by
  rcases k.eq_zero_or_pos with (rfl | hk)
  · rw [pow_zero, one_mul, isRoot_cyclotomic_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [IsRoot.def, cyclotomic_mul_prime_pow_eq R (NeZero.not_char_dvd R p m) hk, eval_pow]
      at h
    replace h := eq_zero_of_pow_eq_zero h
    rwa [← IsRoot.def, isRoot_cyclotomic_iff] at h
  · rw [← isRoot_cyclotomic_iff, IsRoot.def] at h
    rw [cyclotomic_mul_prime_pow_eq R (NeZero.not_char_dvd R p m) hk]; rw [IsRoot.def]; rw [eval_pow]; rw [h]; rw [zero_pow]
exact Nat.sub_ne_zero_of_lt pow_right_strictMono₀ hp.out.one_lt Nat.pred_lt hk.ne'

end CharP

end Polynomial
