/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
module

public import Mathlib.Algebra.ContinuedFractions.Determinant
public import Mathlib.Algebra.ContinuedFractions.Computation.CorrectnessTerminating
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Tactic.Monotonicity
public import Mathlib.Tactic.GCongr

/-!
# Approximations for Continued Fraction Computations (`GenContFract.of`)

## Summary

This file contains useful approximations for the values involved in the continued fractions
computation `GenContFract.of`. In particular, we show that the generalized continued fraction given
by `GenContFract.of` in fact is a (regular) continued fraction.

Moreover, we derive some upper bounds for the error term when computing a continued fraction up a
given position, i.e. bounds for the term
`|v - (GenContFract.of v).convs n|`. The derived bounds will show us that the error term indeed gets
smaller. As a corollary, we will be able to show that `(GenContFract.of v).convs` converges to `v`
in `Algebra.ContinuedFractions.Computation.ApproximationCorollaries`.

## Main Theorems

- `GenContFract.of_partNum_eq_one`: shows that all partial numerators `aᵢ` are
  equal to one.
- `GenContFract.exists_int_eq_of_partDen`: shows that all partial denominators
  `bᵢ` correspond to an integer.
- `GenContFract.of_one_le_get?_partDen`: shows that `1 ≤ bᵢ`.
- `ContFract.of` returns the regular continued fraction of a value.
- `GenContFract.succ_nth_fib_le_of_nthDen`: shows that the `n`th denominator
  `Bₙ` is greater than or equal to the `n + 1`th fibonacci number `Nat.fib (n + 1)`.
- `GenContFract.le_of_succ_get?_den`: shows that `bₙ * Bₙ ≤ Bₙ₊₁`, where `bₙ` is
  the `n`th partial denominator of the continued fraction.
- `GenContFract.abs_sub_convs_le`: shows that
  `|v - Aₙ / Bₙ| ≤ 1 / (Bₙ * Bₙ₊₁)`, where `Aₙ` is the `n`th partial numerator.

## References

- [*Hardy, GH and Wright, EM and Heath-Brown, Roger and Silverman, Joseph*][hardy2008introduction]

-/

@[expose] public section

open GenContFract

open GenContFract (of)

open Int

variable {K : Type*} {v : K} {n : Nat} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

namespace GenContFract

namespace IntFractPair

/-!
We begin with some lemmas about the stream of `IntFractPair`s, which presumably are not
of great interest for the end user.
-/


/--
theorem `nth_stream_fr_nonneg_lt_one` / 定理 `nth_stream_fr_nonneg_lt_one`

English:
theorem nth_stream_fr_nonneg_lt_one
  statement: {ifp_n : IntFractPair K}
  proof: by
  cases n with
  | zero =>
    obtain rfl : IntFractPair.of v = ifp_n := by injection nth_stream_eq
    exact ⟨fract_nonneg _, fract_lt_one _⟩
  | succ =>
    rcases succ_nth_stream_eq_some_iff.1 nth_stream_eq with ⟨_, _, _, rfl⟩
    exact ⟨fract_nonneg _, fract_lt_one _⟩

中文:
定理 nth_stream_fr_nonneg_lt_one
  结论: {ifp_n : 整数FractPair K}
  证明: by
  cases n with
  | zero =>
    obtain rfl : IntFractPair.of v = ifp_n := by injection nth_stream_eq
    exact ⟨fract_nonneg _, fract_lt_one _⟩
  | succ =>
    rcases succ_nth_stream_eq_some_iff.1 nth_stream_eq with ⟨_, _, _, rfl⟩
    exact ⟨fract_nonneg _, fract_lt_one _⟩

Depends on / 依赖: IntFractPair, IntFractPair.of, fract_lt_one, fract_nonneg, ifp_n, injection, nth_stream_eq, succ_nth_stream_eq_some_iff
-/
theorem nth_stream_fr_nonneg_lt_one {ifp_n : IntFractPair K}
    (nth_stream_eq : IntFractPair.stream v n = some ifp_n) : 0 <= ifp_n.fr ∧ ifp_n.fr < 1 := by
  cases n with
  | zero =>
    obtain rfl : IntFractPair.of v = ifp_n := by injection nth_stream_eq
    exact ⟨fract_nonneg _, fract_lt_one _⟩
  | succ =>
    rcases succ_nth_stream_eq_some_iff.1 nth_stream_eq with ⟨_, _, _, rfl⟩
    exact ⟨fract_nonneg _, fract_lt_one _⟩

/--
theorem `nth_stream_fr_nonneg` / 定理 `nth_stream_fr_nonneg`

English:
theorem nth_stream_fr_nonneg
  statement: {ifp_n : IntFractPair K}
  proof: (nth_stream_fr_nonneg_lt_one nth_stream_eq).left

中文:
定理 nth_stream_fr_nonneg
  结论: {ifp_n : 整数FractPair K}
  证明: (nth_stream_fr_nonneg_lt_one nth_stream_eq).left

Depends on / 依赖: nth_stream_eq, nth_stream_fr_nonneg_lt_one
-/
theorem nth_stream_fr_nonneg {ifp_n : IntFractPair K}
    (nth_stream_eq : IntFractPair.stream v n = some ifp_n) : 0 <= ifp_n.fr :=
  (nth_stream_fr_nonneg_lt_one nth_stream_eq).left

/--
theorem `nth_stream_fr_lt_one` / 定理 `nth_stream_fr_lt_one`

English:
theorem nth_stream_fr_lt_one
  statement: {ifp_n : IntFractPair K}
  proof: (nth_stream_fr_nonneg_lt_one nth_stream_eq).right

中文:
定理 nth_stream_fr_lt_one
  结论: {ifp_n : 整数FractPair K}
  证明: (nth_stream_fr_nonneg_lt_one nth_stream_eq).right

Depends on / 依赖: nth_stream_eq, nth_stream_fr_nonneg_lt_one
-/
theorem nth_stream_fr_lt_one {ifp_n : IntFractPair K}
    (nth_stream_eq : IntFractPair.stream v n = some ifp_n) : ifp_n.fr < 1 :=
  (nth_stream_fr_nonneg_lt_one nth_stream_eq).right

/--
theorem `one_le_succ_nth_stream_b` / 定理 `one_le_succ_nth_stream_b`

English:
theorem one_le_succ_nth_stream_b
  statement: {ifp_succ_n : IntFractPair K}
  proof: by
  obtain ⟨ifp_n, nth_stream_eq, stream_nth_fr_ne_zero, ⟨-⟩⟩ :
      exists ifp_n, IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr != 0
        ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n :=
    succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
  rw [IntFractPair.of]; rw [le_floor]; rw [cast_one]; rw

中文:
定理 one_le_succ_nth_stream_b
  结论: {ifp_succ_n : 整数FractPair K}
  证明: by
  obtain ⟨ifp_n, nth_stream_eq, stream_nth_fr_ne_zero, ⟨-⟩⟩ :
      exists ifp_n, IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr != 0
        ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n :=
    succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
  rw [IntFractPair.of]; rw [le_floor]; rw [cast_one]; rw

Depends on / 依赖: IntFractPair, IntFractPair.of, IntFractPair.stream, cast_one, ifp_n, ifp_n.fr, ifp_succ_n, le_floor, lt_of_ne, nth_stream_eq, nth_stream_fr_lt_one, nth_stream_fr_nonneg, stream, stream_nth_fr_ne_zero, succ_nth_stream_eq, succ_nth_stream_eq_some_iff
-/
theorem one_le_succ_nth_stream_b {ifp_succ_n : IntFractPair K}
    (succ_nth_stream_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n) : 1 <= ifp_succ_n.b := by
  obtain ⟨ifp_n, nth_stream_eq, stream_nth_fr_ne_zero, ⟨-⟩⟩ :
      exists ifp_n, IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr != 0
        ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n :=
    succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
  rw [IntFractPair.of]; rw [le_floor]; rw [cast_one]; rw [one_le_inv₀
    ((nth_stream_fr_nonneg nth_stream_eq).lt_of_ne' stream_nth_fr_ne_zero)]
  exact (nth_stream_fr_lt_one nth_stream_eq).le

omit [IsStrictOrderedRing K] in
/--
theorem `succ_nth_stream_b_le_nth_stream_fr_inv` / 定理 `succ_nth_stream_b_le_nth_stream_fr_inv`

English:
theorem succ_nth_stream_b_le_nth_stream_fr_inv
  statement: {ifp_n ifp_succ_n : IntFractPair K}
  proof: by
  suffices (⌊ifp_n.fr⁻¹⌋ : K) <= ifp_n.fr⁻¹ by
    obtain ⟨_, ifp_n_fr⟩ := ifp_n
    have : ifp_n_fr != 0 := by
      intro h
      simp [h, IntFractPair.stream, nth_stream_eq] at succ_nth_stream_eq
    have : IntFractPair.of ifp_n_fr⁻¹ = ifp_succ_n := by
      simpa [this, IntFractPair.stream, n

中文:
定理 succ_nth_stream_b_le_nth_stream_fr_inv
  结论: {ifp_n ifp_succ_n : 整数FractPair K}
  证明: by
  suffices (⌊ifp_n.fr⁻¹⌋ : K) <= ifp_n.fr⁻¹ by
    obtain ⟨_, ifp_n_fr⟩ := ifp_n
    have : ifp_n_fr != 0 := by
      intro h
      simp [h, IntFractPair.stream, nth_stream_eq] at succ_nth_stream_eq
    have : IntFractPair.of ifp_n_fr⁻¹ = ifp_succ_n := by
      simpa [this, IntFractPair.stream, n

Depends on / 依赖: IntFractPair, IntFractPair.of, IntFractPair.stream, Option.coe_def, coe_def, floor_le, ifp_n, ifp_n.fr, ifp_n_fr, ifp_succ_n, nth_stream_eq, stream, succ_nth_stream_eq
-/
theorem succ_nth_stream_b_le_nth_stream_fr_inv {ifp_n ifp_succ_n : IntFractPair K}
    (nth_stream_eq : IntFractPair.stream v n = some ifp_n)
    (succ_nth_stream_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n) :
    (ifp_succ_n.b : K) <= ifp_n.fr⁻¹ := by
  suffices (⌊ifp_n.fr⁻¹⌋ : K) <= ifp_n.fr⁻¹ by
    obtain ⟨_, ifp_n_fr⟩ := ifp_n
    have : ifp_n_fr != 0 := by
      intro h
      simp [h, IntFractPair.stream, nth_stream_eq] at succ_nth_stream_eq
    have : IntFractPair.of ifp_n_fr⁻¹ = ifp_succ_n := by
      simpa [this, IntFractPair.stream, nth_stream_eq, Option.coe_def] using succ_nth_stream_eq
    rwa [← this]
  exact floor_le ifp_n.fr⁻¹

end IntFractPair

/-!
Next we translate above results about the stream of `IntFractPair`s to the computed continued
fraction `GenContFract.of`.
-/


/--
theorem `of_one_le_get?_partDen` / 定理 `of_one_le_get?_partDen`

English:
theorem of_one_le_get?_partDen
  statement: {b : K}
  proof: by
  obtain ⟨gp_n, nth_s_eq, ⟨-⟩⟩ : exists gp_n, (of v).s.get? n = some gp_n ∧ gp_n.b = b :=
    exists_s_b_of_partDen nth_partDen_eq
  obtain ⟨ifp_n, succ_nth_stream_eq, ifp_n_b_eq_gp_n_b⟩ :
      exists ifp, IntFractPair.stream v (n + 1) = some ifp ∧ (ifp.b : K) = gp_n.b :=
    IntFractPair.exists

中文:
定理 of_one_le_get?_partDen
  结论: {b : K}
  证明: by
  obtain ⟨gp_n, nth_s_eq, ⟨-⟩⟩ : exists gp_n, (of v).s.get? n = some gp_n ∧ gp_n.b = b :=
    exists_s_b_of_partDen nth_partDen_eq
  obtain ⟨ifp_n, succ_nth_stream_eq, ifp_n_b_eq_gp_n_b⟩ :
      exists ifp, IntFractPair.stream v (n + 1) = some ifp ∧ (ifp.b : K) = gp_n.b :=
    IntFractPair.exists

Depends on / 依赖: IntFractPair, IntFractPair.exists_succ_get, IntFractPair.one_le_succ_nth_stream_b, IntFractPair.stream, _eq_some, _stream_of_gcf_of_get, exists_s_b_of_partDen, exists_succ_get, gp_n, gp_n.b, ifp.b, ifp_n, ifp_n_b_eq_gp_n_b, mod_cast, nth_partDen_eq, nth_s_eq, one_le_succ_nth_stream_b, s.get, stream, succ_nth_stream_eq
-/
theorem of_one_le_get?_partDen {b : K}
    (nth_partDen_eq : (of v).partDens.get? n = some b) : 1 <= b := by
  obtain ⟨gp_n, nth_s_eq, ⟨-⟩⟩ : exists gp_n, (of v).s.get? n = some gp_n ∧ gp_n.b = b :=
    exists_s_b_of_partDen nth_partDen_eq
  obtain ⟨ifp_n, succ_nth_stream_eq, ifp_n_b_eq_gp_n_b⟩ :
      exists ifp, IntFractPair.stream v (n + 1) = some ifp ∧ (ifp.b : K) = gp_n.b :=
    IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some nth_s_eq
  rw [← ifp_n_b_eq_gp_n_b]
  exact mod_cast IntFractPair.one_le_succ_nth_stream_b succ_nth_stream_eq

omit [IsStrictOrderedRing K] in
/--
theorem `of_partNum_eq_one_and_exists_int_partDen_eq` / 定理 `of_partNum_eq_one_and_exists_int_partDen_eq`

English:
theorem of_partNum_eq_one_and_exists_int_partDen_eq
  statement: {gp : GenContFract.Pair K}
  proof: by
  obtain ⟨ifp, stream_succ_nth_eq, -⟩ : exists ifp, IntFractPair.stream v (n + 1) = some ifp ∧ _ :=
    IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some nth_s_eq
  have : gp = ⟨1, ifp.b⟩ := by
    have : (of v).s.get? n = some ⟨1, ifp.b⟩ :=
      get?_of_eq_some_of_succ_get?_intFractPa

中文:
定理 of_partNum_eq_one_and_exists_int_partDen_eq
  结论: {gp : GenContFract.Pair K}
  证明: by
  obtain ⟨ifp, stream_succ_nth_eq, -⟩ : exists ifp, IntFractPair.stream v (n + 1) = some ifp ∧ _ :=
    IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some nth_s_eq
  have : gp = ⟨1, ifp.b⟩ := by
    have : (of v).s.get? n = some ⟨1, ifp.b⟩ :=
      get?_of_eq_some_of_succ_get?_intFractPa

Depends on / 依赖: IntFractPair, IntFractPair.exists_succ_get, IntFractPair.stream, _eq_some, _intFractPair_stream, _of_eq_some_of_succ_get, _stream_of_gcf_of_get, exists_succ_get, ifp.b, injection, nth_s_eq, s.get, stream, stream_succ_nth_eq
-/
theorem of_partNum_eq_one_and_exists_int_partDen_eq {gp : GenContFract.Pair K}
    (nth_s_eq : (of v).s.get? n = some gp) : gp.a = 1 ∧ exists z : Int, gp.b = (z : K) := by
  obtain ⟨ifp, stream_succ_nth_eq, -⟩ : exists ifp, IntFractPair.stream v (n + 1) = some ifp ∧ _ :=
    IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some nth_s_eq
  have : gp = ⟨1, ifp.b⟩ := by
    have : (of v).s.get? n = some ⟨1, ifp.b⟩ :=
      get?_of_eq_some_of_succ_get?_intFractPair_stream stream_succ_nth_eq
    have : some gp = some ⟨1, ifp.b⟩ := by rwa [nth_s_eq] at this
    injection this
  simp [this]

omit [IsStrictOrderedRing K] in
/--
theorem `of_partNum_eq_one` / 定理 `of_partNum_eq_one`

English:
theorem of_partNum_eq_one
  given: {a : K} (nth_partNum_eq : (of v).partNums.get? n = some a)
  proof: by
  obtain ⟨gp, nth_s_eq, gp_a_eq_a_n⟩ : exists gp, (of v).s.get? n = some gp ∧ gp.a = a :=
    exists_s_a_of_partNum nth_partNum_eq
  have : gp.a = 1 := (of_partNum_eq_one_and_exists_int_partDen_eq nth_s_eq).left
  rwa [gp_a_eq_a_n] at this

omit [IsStrictOrderedRing K] in

中文:
定理 of_partNum_eq_one
  条件: {a : K} (nth_partNum_eq : (of v).partNums.get? n = some a)
  证明: by
  obtain ⟨gp, nth_s_eq, gp_a_eq_a_n⟩ : exists gp, (of v).s.get? n = some gp ∧ gp.a = a :=
    exists_s_a_of_partNum nth_partNum_eq
  have : gp.a = 1 := (of_partNum_eq_one_and_exists_int_partDen_eq nth_s_eq).left
  rwa [gp_a_eq_a_n] at this

omit [IsStrictOrderedRing K] in

Depends on / 依赖: exists_s_a_of_partNum, gp.a, gp_a_eq_a_n, nth_partNum_eq, nth_s_eq, of_partNum_eq_one_and_exists_int_partDen_eq, s.get
-/
theorem of_partNum_eq_one {a : K} (nth_partNum_eq : (of v).partNums.get? n = some a) :
    a = 1 := by
  obtain ⟨gp, nth_s_eq, gp_a_eq_a_n⟩ : exists gp, (of v).s.get? n = some gp ∧ gp.a = a :=
    exists_s_a_of_partNum nth_partNum_eq
  have : gp.a = 1 := (of_partNum_eq_one_and_exists_int_partDen_eq nth_s_eq).left
  rwa [gp_a_eq_a_n] at this

omit [IsStrictOrderedRing K] in
/--
theorem `exists_int_eq_of_partDen` / 定理 `exists_int_eq_of_partDen`

English:
theorem exists_int_eq_of_partDen
  statement: {b : K}
  proof: by
  obtain ⟨_, nth_s_eq, rfl⟩ : exists gp, (of v).s.get? n = some gp ∧ gp.b = b :=
    exists_s_b_of_partDen nth_partDen_eq
  exact (of_partNum_eq_one_and_exists_int_partDen_eq nth_s_eq).right

中文:
定理 exists_int_eq_of_partDen
  结论: {b : K}
  证明: by
  obtain ⟨_, nth_s_eq, rfl⟩ : exists gp, (of v).s.get? n = some gp ∧ gp.b = b :=
    exists_s_b_of_partDen nth_partDen_eq
  exact (of_partNum_eq_one_and_exists_int_partDen_eq nth_s_eq).right

Depends on / 依赖: exists_s_b_of_partDen, gp.b, nth_partDen_eq, nth_s_eq, of_partNum_eq_one_and_exists_int_partDen_eq, s.get
-/
theorem exists_int_eq_of_partDen {b : K}
    (nth_partDen_eq : (of v).partDens.get? n = some b) : exists z : Int, b = (z : K) := by
  obtain ⟨_, nth_s_eq, rfl⟩ : exists gp, (of v).s.get? n = some gp ∧ gp.b = b :=
    exists_s_b_of_partDen nth_partDen_eq
  exact (of_partNum_eq_one_and_exists_int_partDen_eq nth_s_eq).right

end GenContFract

variable (v)

omit [IsStrictOrderedRing K] in
/--
theorem `GenContFract.of_isSimpContFract` / 定理 `GenContFract.of_isSimpContFract`

English:
theorem GenContFract.of_isSimpContFract
  proof: fun _ _ nth_partNum_eq =>
  of_partNum_eq_one nth_partNum_eq

中文:
定理 GenContFract.of_isSimpContFract
  证明: fun _ _ nth_partNum_eq =>
  of_partNum_eq_one nth_partNum_eq

Depends on / 依赖: nth_partNum_eq
-/
theorem GenContFract.of_isSimpContFract :
    (of v).IsSimpContFract := fun _ _ nth_partNum_eq =>
  of_partNum_eq_one nth_partNum_eq

/--
Definition of `SimpContFract.of` / `SimpContFract.of` 的定义

English:
definition SimpContFract.of
  signature: : SimpContFract K
  body: ⟨GenContFract.of v, GenContFract.of_isSimpContFract v⟩

中文:
定义 SimpContFract.of
  签名: : SimpContFract K
  定义体: ⟨GenContFract.of v, GenContFract.of_isSimpContFract v⟩

Depends on / 依赖: GenContFract, GenContFract.of, GenContFract.of_isSimpContFract, of_isSimpContFract
-/
def SimpContFract.of : SimpContFract K :=
  ⟨GenContFract.of v, GenContFract.of_isSimpContFract v⟩

/--
theorem `SimpContFract.of_isContFract` / 定理 `SimpContFract.of_isContFract`

English:
theorem SimpContFract.of_isContFract
  proof: fun _ _ nth_partDen_eq =>
  lt_of_lt_of_le zero_lt_one (of_one_le_get?_partDen nth_partDen_eq)

中文:
定理 SimpContFract.of_isContFract
  证明: fun _ _ nth_partDen_eq =>
  lt_of_lt_of_le zero_lt_one (of_one_le_get?_partDen nth_partDen_eq)

Depends on / 依赖: nth_partDen_eq
-/
theorem SimpContFract.of_isContFract :
    (SimpContFract.of v).IsContFract := fun _ _ nth_partDen_eq =>
  lt_of_lt_of_le zero_lt_one (of_one_le_get?_partDen nth_partDen_eq)

/--
Definition of `ContFract.of` / `ContFract.of` 的定义

English:
definition ContFract.of
  signature: : ContFract K
  body: ⟨SimpContFract.of v, SimpContFract.of_isContFract v⟩

中文:
定义 ContFract.of
  签名: : ContFract K
  定义体: ⟨SimpContFract.of v, SimpContFract.of_isContFract v⟩

Depends on / 依赖: SimpContFract, SimpContFract.of, SimpContFract.of_isContFract, of_isContFract
-/
def ContFract.of : ContFract K :=
  ⟨SimpContFract.of v, SimpContFract.of_isContFract v⟩

variable {v}

namespace GenContFract

/-!
One of our next goals is to show that `bₙ * Bₙ ≤ Bₙ₊₁`. For this, we first show that the partial
denominators `Bₙ` are bounded from below by the fibonacci sequence `Nat.fib`. This then implies that
`0 ≤ Bₙ` and hence `Bₙ₊₂ = bₙ₊₁ * Bₙ₊₁ + Bₙ ≥ bₙ₊₁ * Bₙ₊₁ + 0 = bₙ₊₁ * Bₙ₊₁`.
-/


-- open `Nat` as we will make use of fibonacci numbers.
open Nat

/--
theorem `fib_le_of_contsAux_b` / 定理 `fib_le_of_contsAux_b`

English:
theorem fib_le_of_contsAux_b
  proof: Nat.strong_induction_on n
    (by
      intro n IH hyp
      rcases n with (_ | _ | n)
      · simp [contsAux] -- case n = 0
      · simp -- case n = 1
      · let g := of v -- case 2 ≤ n
        have : ¬n + 2 <= 1 := by lia
        have not_terminatedAt_n : ¬g.TerminatedAt n := Or.resolve_left hyp 

中文:
定理 fib_le_of_contsAux_b
  证明: Nat.strong_induction_on n
    (by
      intro n IH hyp
      rcases n with (_ | _ | n)
      · simp [contsAux] -- case n = 0
      · simp -- case n = 1
      · let g := of v -- case 2 ≤ n
        have : ¬n + 2 <= 1 := by lia
        have not_terminatedAt_n : ¬g.TerminatedAt n := Or.resolve_left hyp 

Depends on / 依赖: Nat.strong_induction_on, Option.ne_none_iff_exists, Or.resolve_left, TerminatedAt, contsAux, g.TerminatedAt, g.contsAux, g.s.get, ne_none_iff_exists, not_terminatedAt_n, pconts, pconts_eq, ppconts, ppconts_eq, resolve_left, s_ppred_nth_eq, strong_induction_on
-/
theorem fib_le_of_contsAux_b :
    n <= 1 ∨ ¬(of v).TerminatedAt (n - 2) -> (fib n : K) <= ((of v).contsAux n).b :=
  Nat.strong_induction_on n
    (by
      intro n IH hyp
      rcases n with (_ | _ | n)
      · simp [contsAux] -- case n = 0
      · simp -- case n = 1
      · let g := of v -- case 2 ≤ n
        have : ¬n + 2 <= 1 := by lia
        have not_terminatedAt_n : ¬g.TerminatedAt n := Or.resolve_left hyp this
        obtain ⟨gp, s_ppred_nth_eq⟩ : exists gp, g.s.get? n = some gp :=
          Option.ne_none_iff_exists'.mp not_terminatedAt_n
        set pconts := g.contsAux (n + 1) with pconts_eq
        set ppconts := g.contsAux n with ppconts_eq
        -- use the recurrence of `contsAux`
        simp only [Nat.add_assoc, Nat.reduceAdd]
        suffices (fib n : K) + fib (n + 1) <= gp.a * ppconts.b + gp.b * pconts.b by
          simpa [g, fib_add_two, add_comm, contsAux_recurrence s_ppred_nth_eq ppconts_eq pconts_eq]
        -- make use of the fact that `gp.a = 1`
        suffices (fib n : K) + fib (n + 1) <= ppconts.b + gp.b * pconts.b by
          simpa [of_partNum_eq_one <| partNum_eq_s_a s_ppred_nth_eq]
        have not_terminatedAt_pred_n : ¬g.TerminatedAt (n - 1) :=
          mt (terminated_stable <| Nat.sub_le n 1) not_terminatedAt_n
        have not_terminatedAt_ppred_n : ¬TerminatedAt g (n - 2) :=
          mt (terminated_stable <| Nat.sub_le n 2) not_terminatedAt_n
        -- use the IH to get the inequalities for `pconts` and `ppconts`
        have ppred_nth_fib_le_ppconts_B : (fib n : K) <= ppconts.b :=
          IH n (lt_trans (Nat.lt_add_one n) <| Nat.lt_add_one <| n + 1)
            (Or.inr not_terminatedAt_ppred_n)
        suffices (fib (n + 1) : K) <= gp.b * pconts.b by gcongr
        -- finally use the fact that `1 ≤ gp.b` to solve the goal
        suffices 1 * (fib (n + 1) : K) <= gp.b * pconts.b by rwa [one_mul] at this
        have one_le_gp_b : (1 : K) <= gp.b :=
          of_one_le_get?_partDen (partDen_eq_s_b s_ppred_nth_eq)
        gcongr
        grind)

/--
theorem `succ_nth_fib_le_of_nth_den` / 定理 `succ_nth_fib_le_of_nth_den`

English:
theorem succ_nth_fib_le_of_nth_den
  given: (hyp : n = 0 ∨ ¬(of v).TerminatedAt (n - 1))
  proof: by
  rw [den_eq_conts_b]; rw [nth_cont_eq_succ_nth_contAux]
  have : n + 1 <= 1 ∨ ¬(of v).TerminatedAt (n - 1) := by
    cases n with
| zero => exact Or.inl le_refl 1
    | succ n => exact Or.inr (Or.resolve_left hyp n.succ_ne_zero)
  exact fib_le_of_contsAux_b this

中文:
定理 succ_nth_fib_le_of_nth_den
  条件: (hyp : n = 0 ∨ ¬(of v).TerminatedAt (n - 1))
  证明: by
  rw [den_eq_conts_b]; rw [nth_cont_eq_succ_nth_contAux]
  have : n + 1 <= 1 ∨ ¬(of v).TerminatedAt (n - 1) := by
    cases n with
| zero => exact Or.inl le_refl 1
    | succ n => exact Or.inr (Or.resolve_left hyp n.succ_ne_zero)
  exact fib_le_of_contsAux_b this

Depends on / 依赖: Or.inl, Or.inr, Or.resolve_left, TerminatedAt, den_eq_conts_b, fib_le_of_contsAux_b, le_refl, n.succ_ne_zero, nth_cont_eq_succ_nth_contAux, resolve_left, succ_ne_zero
-/
theorem succ_nth_fib_le_of_nth_den (hyp : n = 0 ∨ ¬(of v).TerminatedAt (n - 1)) :
    (fib (n + 1) : K) <= (of v).dens n := by
  rw [den_eq_conts_b]; rw [nth_cont_eq_succ_nth_contAux]
  have : n + 1 <= 1 ∨ ¬(of v).TerminatedAt (n - 1) := by
    cases n with
| zero => exact Or.inl le_refl 1
    | succ n => exact Or.inr (Or.resolve_left hyp n.succ_ne_zero)
  exact fib_le_of_contsAux_b this



/--
theorem `zero_le_of_contsAux_b` / 定理 `zero_le_of_contsAux_b`

English:
theorem zero_le_of_contsAux_b
  statement: 0 <= ((of v).contsAux n).b
  proof: by
  let g := of v
  induction n with
  | zero => rfl
  | succ n IH =>
rcases Decidable.em g.TerminatedAt (n - 1) with terminated | not_terminated
    · -- terminating case
      rcases n with - | n
      · simp
      · have : g.contsAux (n + 2) = g.contsAux (n + 1) :=
          contsAux_stable_step

中文:
定理 zero_le_of_contsAux_b
  结论: 0 <= ((of v).contsAux n).b
  证明: by
  let g := of v
  induction n with
  | zero => rfl
  | succ n IH =>
rcases Decidable.em g.TerminatedAt (n - 1) with terminated | not_terminated
    · -- terminating case
      rcases n with - | n
      · simp
      · have : g.contsAux (n + 2) = g.contsAux (n + 1) :=
          contsAux_stable_step

Depends on / 依赖: Decidable, Decidable.em, Or.inr, TerminatedAt, contsAux, contsAux_stable_step_of_terminated, fib.zero_le, fib_le_of_contsAux_b, g.TerminatedAt, g.contsAux, mod_cast, not_terminated, terminated, terminating, zero_le
-/
theorem zero_le_of_contsAux_b : 0 <= ((of v).contsAux n).b := by
  let g := of v
  induction n with
  | zero => rfl
  | succ n IH =>
rcases Decidable.em g.TerminatedAt (n - 1) with terminated | not_terminated
    · -- terminating case
      rcases n with - | n
      · simp
      · have : g.contsAux (n + 2) = g.contsAux (n + 1) :=
          contsAux_stable_step_of_terminated terminated
        simp only [g, this, IH]
    · -- non-terminating case
      calc
        (0 : K) <= fib (n + 1) := mod_cast (n + 1).fib.zero_le
        _ <= ((of v).contsAux (n + 1)).b := fib_le_of_contsAux_b (Or.inr not_terminated)

/--
theorem `zero_le_of_den` / 定理 `zero_le_of_den`

English:
theorem zero_le_of_den
  statement: 0 <= (of v).dens n
  proof: by
  rw [den_eq_conts_b]; rw [nth_cont_eq_succ_nth_contAux]; exact zero_le_of_contsAux_b

中文:
定理 zero_le_of_den
  结论: 0 <= (of v).dens n
  证明: by
  rw [den_eq_conts_b]; rw [nth_cont_eq_succ_nth_contAux]; exact zero_le_of_contsAux_b

Depends on / 依赖: den_eq_conts_b, nth_cont_eq_succ_nth_contAux, zero_le_of_contsAux_b
-/
theorem zero_le_of_den : 0 <= (of v).dens n := by
  rw [den_eq_conts_b]; rw [nth_cont_eq_succ_nth_contAux]; exact zero_le_of_contsAux_b

/--
theorem `le_of_succ_succ_get?_contsAux_b` / 定理 `le_of_succ_succ_get?_contsAux_b`

English:
theorem le_of_succ_succ_get?_contsAux_b
  statement: {b : K}
  proof: by
  obtain ⟨gp_n, nth_s_eq, rfl⟩ : exists gp_n, (of v).s.get? n = some gp_n ∧ gp_n.b = b :=
    exists_s_b_of_partDen nth_partDen_eq
  simp [of_partNum_eq_one (partNum_eq_s_a nth_s_eq), zero_le_of_contsAux_b,
    GenContFract.contsAux_recurrence nth_s_eq rfl rfl]

中文:
定理 le_of_succ_succ_get?_contsAux_b
  结论: {b : K}
  证明: by
  obtain ⟨gp_n, nth_s_eq, rfl⟩ : exists gp_n, (of v).s.get? n = some gp_n ∧ gp_n.b = b :=
    exists_s_b_of_partDen nth_partDen_eq
  simp [of_partNum_eq_one (partNum_eq_s_a nth_s_eq), zero_le_of_contsAux_b,
    GenContFract.contsAux_recurrence nth_s_eq rfl rfl]

Depends on / 依赖: GenContFract, GenContFract.contsAux_recurrence, contsAux_recurrence, exists_s_b_of_partDen, gp_n, gp_n.b, nth_partDen_eq, nth_s_eq, of_partNum_eq_one, partNum_eq_s_a, s.get, zero_le_of_contsAux_b
-/
theorem le_of_succ_succ_get?_contsAux_b {b : K}
    (nth_partDen_eq : (of v).partDens.get? n = some b) :
    b * ((of v).contsAux <| n + 1).b <= ((of v).contsAux <| n + 2).b := by
  obtain ⟨gp_n, nth_s_eq, rfl⟩ : exists gp_n, (of v).s.get? n = some gp_n ∧ gp_n.b = b :=
    exists_s_b_of_partDen nth_partDen_eq
  simp [of_partNum_eq_one (partNum_eq_s_a nth_s_eq), zero_le_of_contsAux_b,
    GenContFract.contsAux_recurrence nth_s_eq rfl rfl]

/--
theorem `le_of_succ_get?_den` / 定理 `le_of_succ_get?_den`

English:
theorem le_of_succ_get?_den
  statement: {b : K}
  proof: by
  rw [den_eq_conts_b]; rw [nth_cont_eq_succ_nth_contAux]
  exact le_of_succ_succ_get?_contsAux_b nth_partDenom_eq

中文:
定理 le_of_succ_get?_den
  结论: {b : K}
  证明: by
  rw [den_eq_conts_b]; rw [nth_cont_eq_succ_nth_contAux]
  exact le_of_succ_succ_get?_contsAux_b nth_partDenom_eq

Depends on / 依赖: _contsAux_b, den_eq_conts_b, le_of_succ_succ_get, nth_cont_eq_succ_nth_contAux, nth_partDenom_eq
-/
theorem le_of_succ_get?_den {b : K}
    (nth_partDenom_eq : (of v).partDens.get? n = some b) :
    b * (of v).dens n <= (of v).dens (n + 1) := by
  rw [den_eq_conts_b]; rw [nth_cont_eq_succ_nth_contAux]
  exact le_of_succ_succ_get?_contsAux_b nth_partDenom_eq

/--
theorem `of_den_mono` / 定理 `of_den_mono`

English:
theorem of_den_mono
  statement: (of v).dens n <= (of v).dens (n + 1)
  proof: by
  let g := of v
rcases Decidable.em g.partDens.TerminatedAt n with terminated | not_terminated
  · have : g.TerminatedAt n :=
      terminatedAt_iff_partDen_none.2 (by rwa [Stream'.Seq.TerminatedAt] at terminated)
    have : g.dens (n + 1) = g.dens n :=
      dens_stable_of_terminated n.le_succ t

中文:
定理 of_den_mono
  结论: (of v).dens n <= (of v).dens (n + 1)
  证明: by
  let g := of v
rcases Decidable.em g.partDens.TerminatedAt n with terminated | not_terminated
  · have : g.TerminatedAt n :=
      terminatedAt_iff_partDen_none.2 (by rwa [Stream'.Seq.TerminatedAt] at terminated)
    have : g.dens (n + 1) = g.dens n :=
      dens_stable_of_terminated n.le_succ t

Depends on / 依赖: Decidable, Decidable.em, Option.ne_none_iff_exists, Seq.TerminatedAt, Stream, TerminatedAt, _partDen, dens_stable_of_terminated, g.TerminatedAt, g.dens, g.partDens.TerminatedAt, g.partDens.get, le_succ, n.le_succ, ne_none_iff_exists, not_terminated, nth_partDen_eq, of_one_le_get, partDens, terminated
-/
theorem of_den_mono : (of v).dens n <= (of v).dens (n + 1) := by
  let g := of v
rcases Decidable.em g.partDens.TerminatedAt n with terminated | not_terminated
  · have : g.TerminatedAt n :=
      terminatedAt_iff_partDen_none.2 (by rwa [Stream'.Seq.TerminatedAt] at terminated)
    have : g.dens (n + 1) = g.dens n :=
      dens_stable_of_terminated n.le_succ this
    rw [this]
  · obtain ⟨b, nth_partDen_eq⟩ : exists b, g.partDens.get? n = some b :=
      Option.ne_none_iff_exists'.mp not_terminated
    have : 1 <= b := of_one_le_get?_partDen nth_partDen_eq
    calc
      g.dens n <= b * g.dens n := by
        simpa using mul_le_mul_of_nonneg_right this zero_le_of_den
      _ <= g.dens (n + 1) := le_of_succ_get?_den nth_partDen_eq

section ErrorTerm

/-!
### Approximation of Error Term

Next we derive some approximations for the error term when computing a continued fraction up a given
position, i.e. bounds for the term `|v - (GenContFract.of v).convs n|`.
-/


/--
theorem `sub_convs_eq` / 定理 `sub_convs_eq`

English:
theorem sub_convs_eq
  statement: {ifp : IntFractPair K}
  proof: of v
    let B := (g.contsAux (n + 1)).b
    let pB := (g.contsAux n).b
    v - g.convs n = if ifp.fr = 0 then 0 else (-1) ^ n / (B * (ifp.fr⁻¹ * B + pB)) := by
  -- set up some shorthand notation
  let g := of v
  let conts := g.contsAux (n + 1)
  let pred_conts := g.contsAux n
  have g_finite_corr

中文:
定理 sub_convs_eq
  结论: {ifp : 整数FractPair K}
  证明: of v
    let B := (g.contsAux (n + 1)).b
    let pB := (g.contsAux n).b
    v - g.convs n = if ifp.fr = 0 then 0 else (-1) ^ n / (B * (ifp.fr⁻¹ * B + pB)) := by
  -- set up some shorthand notation
  let g := of v
  let conts := g.contsAux (n + 1)
  let pred_conts := g.contsAux n
  have g_finite_corr
-/
theorem sub_convs_eq {ifp : IntFractPair K}
    (stream_nth_eq : IntFractPair.stream v n = some ifp) :
    let g := of v
    let B := (g.contsAux (n + 1)).b
    let pB := (g.contsAux n).b
    v - g.convs n = if ifp.fr = 0 then 0 else (-1) ^ n / (B * (ifp.fr⁻¹ * B + pB)) := by
  -- set up some shorthand notation
  let g := of v
  let conts := g.contsAux (n + 1)
  let pred_conts := g.contsAux n
  have g_finite_correctness :
      v = GenContFract.compExactValue pred_conts conts ifp.fr :=
    compExactValue_correctness_of_stream_eq_some stream_nth_eq
  obtain (ifp_fr_eq_zero | ifp_fr_ne_zero) := eq_or_ne ifp.fr 0
  · suffices v - g.convs n = 0 by simpa [ifp_fr_eq_zero]
    replace g_finite_correctness : v = g.convs n := by
      simpa [GenContFract.compExactValue, ifp_fr_eq_zero] using! g_finite_correctness
    exact sub_eq_zero.2 g_finite_correctness
  · -- more shorthand notation
    let A := conts.a
    let B := conts.b
    let pA := pred_conts.a
    let pB := pred_conts.b
    -- first, let's simplify the goal as `ifp.fr ≠ 0`
    suffices v - A / B = (-1) ^ n / (B * (ifp.fr⁻¹ * B + pB)) by simpa [ifp_fr_ne_zero]
    -- now we can unfold `g.compExactValue` to derive the following equality for `v`
    replace g_finite_correctness : v = (pA + ifp.fr⁻¹ * A) / (pB + ifp.fr⁻¹ * B) := by
      simpa [GenContFract.compExactValue, ifp_fr_ne_zero, nextConts, nextNum, nextDen, add_comm]
        using! g_finite_correctness
    -- let's rewrite this equality for `v` in our goal
    suffices
      (pA + ifp.fr⁻¹ * A) / (pB + ifp.fr⁻¹ * B) - A / B = (-1) ^ n / (B * (ifp.fr⁻¹ * B + pB)) by
      rwa [g_finite_correctness]
    -- To continue, we need use the determinant equality. So let's derive the needed hypothesis.
    have n_eq_zero_or_not_terminatedAt_pred_n : n = 0 ∨ ¬g.TerminatedAt (n - 1) := by
      rcases n with - | n'
      · simp
      · have : IntFractPair.stream v (n' + 1) != none := by simp [stream_nth_eq]
        have : ¬g.TerminatedAt n' :=
          (not_congr of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none).2 this
        exact Or.inr this
    have determinant_eq : pA * B - pB * A = (-1) ^ n := by
      match hn : n with
      | 0 => subst n; simp [pA, pB, A, B, pred_conts, conts]
      | n' + 1 =>
        subst n
        simp only [succ_ne_zero, false_or] at n_eq_zero_or_not_terminatedAt_pred_n
        rw [add_tsub_cancel_right] at n_eq_zero_or_not_terminatedAt_pred_n
        exact (SimpContFract.of v).determinant n_eq_zero_or_not_terminatedAt_pred_n
    -- now all we got to do is to rewrite this equality in our goal and re-arrange terms;
    -- however, for this, we first have to derive quite a few tedious inequalities.
    have pB_ineq : (fib n : K) <= pB :=
      haveI : n <= 1 ∨ ¬g.TerminatedAt (n - 2) := by
        rcases n_eq_zero_or_not_terminatedAt_pred_n with n_eq_zero | not_terminatedAt_pred_n
        · simp [n_eq_zero]
· exact Or.inr mt (terminated_stable (n - 1).pred_le) not_terminatedAt_pred_n
      fib_le_of_contsAux_b this
    have B_ineq : (fib (n + 1) : K) <= B :=
      haveI : n + 1 <= 1 ∨ ¬g.TerminatedAt (n + 1 - 2) := by
        rcases n_eq_zero_or_not_terminatedAt_pred_n with n_eq_zero | not_terminatedAt_pred_n
        · simp [n_eq_zero]
        · exact Or.inr not_terminatedAt_pred_n
      fib_le_of_contsAux_b this
have zero_lt_B : 0 < B := B_ineq.trans_lt' cast_pos.2 fib_pos.2 n.succ_pos
    have : 0 <= pB := (Nat.cast_nonneg _).trans pB_ineq
    have : 0 < ifp.fr :=
ifp_fr_ne_zero.lt_of_le' IntFractPair.nth_stream_fr_nonneg stream_nth_eq
    have : pB + ifp.fr⁻¹ * B != 0 := by positivity
    grind

/--
theorem `abs_sub_convs_le` / 定理 `abs_sub_convs_le`

English:
theorem abs_sub_convs_le
  given: (not_terminatedAt_n : ¬(of v).TerminatedAt n)
  proof: by
  -- shorthand notation
  let g := of v
  let nextConts := g.contsAux (n + 2)
  set conts := contsAux g (n + 1) with conts_eq
  set pred_conts := contsAux g n with pred_conts_eq
  -- change the goal to something more readable
  change |v - convs g n| <= 1 / (conts.b * nextConts.b)
  obtain ⟨gp, s

中文:
定理 abs_sub_convs_le
  条件: (not_terminatedAt_n : ¬(of v).TerminatedAt n)
  证明: by
  -- shorthand notation
  let g := of v
  let nextConts := g.contsAux (n + 2)
  set conts := contsAux g (n + 1) with conts_eq
  set pred_conts := contsAux g n with pred_conts_eq
  -- change the goal to something more readable
  change |v - convs g n| <= 1 / (conts.b * nextConts.b)
  obtain ⟨gp, s
-/
theorem abs_sub_convs_le (not_terminatedAt_n : ¬(of v).TerminatedAt n) :
    |v - (of v).convs n| <= 1 / ((of v).dens n * ((of v).dens <| n + 1)) := by
  -- shorthand notation
  let g := of v
  let nextConts := g.contsAux (n + 2)
  set conts := contsAux g (n + 1) with conts_eq
  set pred_conts := contsAux g n with pred_conts_eq
  -- change the goal to something more readable
  change |v - convs g n| <= 1 / (conts.b * nextConts.b)
  obtain ⟨gp, s_nth_eq⟩ : exists gp, g.s.get? n = some gp :=
    Option.ne_none_iff_exists'.1 not_terminatedAt_n
  have gp_a_eq_one : gp.a = 1 := of_partNum_eq_one (partNum_eq_s_a s_nth_eq)
  -- unfold the recurrence relation for `nextConts.b`
  have nextConts_b_eq : nextConts.b = pred_conts.b + gp.b * conts.b := by
    simp [nextConts, contsAux_recurrence s_nth_eq pred_conts_eq conts_eq, gp_a_eq_one,
      pred_conts_eq.symm, conts_eq.symm, add_comm]
  let den := conts.b * (pred_conts.b + gp.b * conts.b)
  obtain ⟨ifp_succ_n, succ_nth_stream_eq, ifp_succ_n_b_eq_gp_b⟩ :
      exists ifp_succ_n, IntFractPair.stream v (n + 1) = some ifp_succ_n ∧ (ifp_succ_n.b : K) = gp.b :=
    IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some s_nth_eq
  obtain ⟨ifp_n, stream_nth_eq, stream_nth_fr_ne_zero, if_of_eq_ifp_succ_n⟩ :
    exists ifp_n, IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr != 0
      ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n :=
    IntFractPair.succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
  let den' := conts.b * (pred_conts.b + ifp_n.fr⁻¹ * conts.b)
  -- now we can use `sub_convs_eq` to simplify our goal
  suffices |(-1) ^ n / den'| <= 1 / den by grind [sub_convs_eq]
  -- derive some tedious inequalities that we need to rewrite our goal
  have nextConts_b_ineq : (fib (n + 2) : K) <= pred_conts.b + gp.b * conts.b := by
    have : (fib (n + 2) : K) <= nextConts.b :=
      fib_le_of_contsAux_b (Or.inr not_terminatedAt_n)
    rwa [nextConts_b_eq] at this
  have conts_b_ineq : (fib (n + 1) : K) <= conts.b :=
    haveI : ¬g.TerminatedAt (n - 1) := mt (terminated_stable n.pred_le) not_terminatedAt_n
fib_le_of_contsAux_b Or.inr this
  have zero_lt_conts_b : 0 < conts.b :=
conts_b_ineq.trans_lt' mod_cast fib_pos.2 n.succ_pos
  -- `den'` is positive, so we can remove `|⬝|` from our goal
  suffices 1 / den' <= 1 / den by
    have : |(-1) ^ n / den'| = 1 / den' := by
      suffices 1 / |den'| = 1 / den' by rwa [abs_div, abs_neg_one_pow n]
      have : 0 < den' := by
        have : 0 <= pred_conts.b :=
          haveI : (fib n : K) <= pred_conts.b :=
            haveI : ¬g.TerminatedAt (n - 2) :=
              mt (terminated_stable (n.sub_le 2)) not_terminatedAt_n
fib_le_of_contsAux_b Or.inr this
          le_trans (mod_cast (fib n).zero_le) this
        have : 0 < ifp_n.fr⁻¹ :=
          haveI zero_le_ifp_n_fract : 0 <= ifp_n.fr :=
            IntFractPair.nth_stream_fr_nonneg stream_nth_eq
          inv_pos.2 (lt_of_le_of_ne zero_le_ifp_n_fract stream_nth_fr_ne_zero.symm)
        positivity
      rw [abs_of_pos this]
    rwa [this]
  suffices 0 < den ∧ den <= den' from div_le_div_of_nonneg_left zero_le_one this.1 this.2
  constructor
  · have : 0 < pred_conts.b + gp.b * conts.b :=
nextConts_b_ineq.trans_lt' mod_cast fib_pos.2 succ_pos _
    solve_by_elim [mul_pos]
  · -- we can cancel multiplication by `conts.b` and addition with `pred_conts.b`
    suffices gp.b * conts.b <= ifp_n.fr⁻¹ * conts.b by
      simp only [den, den']; gcongr
    suffices (ifp_succ_n.b : K) * conts.b <= ifp_n.fr⁻¹ * conts.b by rwa [← ifp_succ_n_b_eq_gp_b]
    have : (ifp_succ_n.b : K) <= ifp_n.fr⁻¹ :=
      IntFractPair.succ_nth_stream_b_le_nth_stream_fr_inv stream_nth_eq succ_nth_stream_eq
    gcongr

/--
theorem `abs_sub_convergents_le'` / 定理 `abs_sub_convergents_le'`

English:
theorem abs_sub_convergents_le'
  statement: {b : K}
  proof: by
  have not_terminatedAt_n : ¬(of v).TerminatedAt n := by
    simp [terminatedAt_iff_partDen_none, nth_partDen_eq]
  refine (abs_sub_convs_le not_terminatedAt_n).trans ?_
  -- One can show that `0 < (GenContFract.of v).dens n` but it's easier
  -- to consider the case `(GenContFract.of v).dens n =

中文:
定理 abs_sub_convergents_le'
  结论: {b : K}
  证明: by
  have not_terminatedAt_n : ¬(of v).TerminatedAt n := by
    simp [terminatedAt_iff_partDen_none, nth_partDen_eq]
  refine (abs_sub_convs_le not_terminatedAt_n).trans ?_
  -- One can show that `0 < (GenContFract.of v).dens n` but it's easier
  -- to consider the case `(GenContFract.of v).dens n =

Depends on / 依赖: TerminatedAt, abs_sub_convs_le, not_terminatedAt_n, nth_partDen_eq, terminatedAt_iff_partDen_none
-/
theorem abs_sub_convergents_le' {b : K}
    (nth_partDen_eq : (of v).partDens.get? n = some b) :
    |v - (of v).convs n| <= 1 / (b * (of v).dens n * (of v).dens n) := by
  have not_terminatedAt_n : ¬(of v).TerminatedAt n := by
    simp [terminatedAt_iff_partDen_none, nth_partDen_eq]
  refine (abs_sub_convs_le not_terminatedAt_n).trans ?_
  -- One can show that `0 < (GenContFract.of v).dens n` but it's easier
  -- to consider the case `(GenContFract.of v).dens n = 0`.
  rcases (zero_le_of_den (K := K)).eq_or_lt' with
    ((hB : (GenContFract.of v).dens n = 0) | hB)
  · simp only [hB, mul_zero, zero_mul, div_zero, le_refl]
  · apply one_div_le_one_div_of_le
    · have : 0 < b := zero_lt_one.trans_le (of_one_le_get?_partDen nth_partDen_eq)
      apply_rules [mul_pos]
    · conv_rhs => rw [mul_comm]
      gcongr
      exact le_of_succ_get?_den nth_partDen_eq

end ErrorTerm

end GenContFract
