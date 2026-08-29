/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Order.Directed
public import Mathlib.Data.Rat.Floor

import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Order.Monoid.Units
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Int.LeastGreatest

/-!
# Archimedean groups and fields

This file proves several results connected to the notion of Archimedean groups. Being Archimedean
means that for all elements `x` and `y > 0` there exists a natural number `n` such that `x ≤ n • y`.

## Main definitions

* `Archimedean.floorRing` defines a floor function on an archimedean linearly ordered ring making it
  into a `floorRing`.

## Main statements

* `ℕ`, `ℤ`, and `ℚ` are archimedean.
-/

@[expose] public section

assert_not_exists Finset

open Int Set

variable {G M R K : Type*}

@[to_additive]
/--
lemma `MulArchimedean.comap` / 引理 `MulArchimedean.comap`

English:
lemma MulArchimedean.comap
  statement: [CommMonoid G] [LinearOrder G] [CommMonoid M] [PartialOrder M]
  proof: by
    refine (MulArchimedean.arch (f x) (by simpa using hf h)).imp ?_
    simp [← map_pow, hf.le_iff_le]

@[to_additive]

中文:
引理 MulArchimedean.comap
  结论: [CommMonoid G] [LinearOrder G] [CommMonoid M] [PartialOrder M]
  证明: by
    refine (MulArchimedean.arch (f x) (by simpa using hf h)).imp ?_
    simp [← map_pow, hf.le_iff_le]

@[to_additive]

Depends on / 依赖: MulArchimedean, MulArchimedean.arch, hf.le_iff_le, le_iff_le, map_pow
-/
lemma MulArchimedean.comap [CommMonoid G] [LinearOrder G] [CommMonoid M] [PartialOrder M]
    [MulArchimedean M] (f : G ->* M) (hf : StrictMono f) :
    MulArchimedean G where
  arch x _ h := by
    refine (MulArchimedean.arch (f x) (by simpa using hf h)).imp ?_
    simp [← map_pow, hf.le_iff_le]

@[to_additive]
/--
Instance `OrderDual.instMulArchimedean` / 实例 `OrderDual.instMulArchimedean`

English:
instance OrderDual.instMulArchimedean
  signature: [CommGroup G] [PartialOrder G] [IsOrderedMonoid G]
  body: ⟨fun x y hy =>
    have hy : (ofDual y) < 1 := hy
    let ⟨n, hn⟩ := MulArchimedean.arch (ofDual x)⁻¹ (one_lt_inv'.2 hy)
    ⟨n, by rwa [inv_pow, inv_le_inv_iff] at hn⟩⟩

中文:
实例 OrderDual.instMulArchimedean
  签名: [CommGroup G] [PartialOrder G] [IsOrderedMonoid G]
  定义体: ⟨fun x y hy =>
    have hy : (ofDual y) < 1 := hy
    let ⟨n, hn⟩ := MulArchimedean.arch (ofDual x)⁻¹ (one_lt_inv'.2 hy)
    ⟨n, by rwa [inv_pow, inv_le_inv_iff] at hn⟩⟩

Depends on / 依赖: MulArchimedean, MulArchimedean.arch, inv_le_inv_iff, inv_pow, ofDual, one_lt_inv
-/
instance OrderDual.instMulArchimedean [CommGroup G] [PartialOrder G] [IsOrderedMonoid G]
    [MulArchimedean G] :
    MulArchimedean Gᵒᵈ :=
  ⟨fun x y hy =>
    have hy : (ofDual y) < 1 := hy
    let ⟨n, hn⟩ := MulArchimedean.arch (ofDual x)⁻¹ (one_lt_inv'.2 hy)
    ⟨n, by rwa [inv_pow, inv_le_inv_iff] at hn⟩⟩

/--
Instance `Additive.instArchimedean` / 实例 `Additive.instArchimedean`

English:
instance Additive.instArchimedean
  signature: [CommGroup G] [PartialOrder G] [MulArchimedean G]
  body: ⟨fun x _ hy => MulArchimedean.arch x.toMul hy⟩

中文:
实例 Additive.instArchimedean
  签名: [CommGroup G] [PartialOrder G] [MulArchimedean G]
  定义体: ⟨fun x _ hy => MulArchimedean.arch x.toMul hy⟩

Depends on / 依赖: MulArchimedean, MulArchimedean.arch, x.toMul
-/
instance Additive.instArchimedean [CommGroup G] [PartialOrder G] [MulArchimedean G] :
    Archimedean (Additive G) :=
  ⟨fun x _ hy => MulArchimedean.arch x.toMul hy⟩

/--
Instance `Multiplicative.instMulArchimedean` / 实例 `Multiplicative.instMulArchimedean`

English:
instance Multiplicative.instMulArchimedean
  signature: [AddCommGroup G] [PartialOrder G] [Archimedean G]
  body: ⟨fun x _ hy => Archimedean.arch x.toAdd hy⟩

中文:
实例 Multiplicative.instMulArchimedean
  签名: [AddCommGroup G] [PartialOrder G] [Archimedean G]
  定义体: ⟨fun x _ hy => Archimedean.arch x.toAdd hy⟩

Depends on / 依赖: Archimedean, Archimedean.arch, x.toAdd
-/
instance Multiplicative.instMulArchimedean [AddCommGroup G] [PartialOrder G] [Archimedean G] :
    MulArchimedean (Multiplicative G) :=
  ⟨fun x _ hy => Archimedean.arch x.toAdd hy⟩

section IsOrderedMonoid

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [MulArchimedean G]

/-- An archimedean decidable linearly ordered `CommGroup` has a version of the floor: for
`a > 1`, any `g` in the group lies between some two consecutive powers of `a`. -/
@[to_additive /-- An archimedean decidable linearly ordered `AddCommGroup` has a version of the
floor: for `a > 0`, any `g` in the group lies between some two consecutive multiples of `a`. -/]
/--
theorem `existsUnique_zpow_near_of_one_lt` / 定理 `existsUnique_zpow_near_of_one_lt`

English:
theorem existsUnique_zpow_near_of_one_lt
  given: {a : G} (ha : 1 < a) (g : G)
  proof: by
  let s : Set Int := { n : Int | a ^ n <= g }
  obtain ⟨k, hk : g⁻¹ <= a ^ k⟩ := MulArchimedean.arch g⁻¹ ha
  have h_ne : s.Nonempty := ⟨-k, by simpa [s] using inv_le_inv' hk⟩
  obtain ⟨k, hk⟩ := MulArchimedean.arch g ha
  have h_bdd : forall n in s, n <= (k : Int) := by
    intro n hn
    apply 

中文:
定理 existsUnique_zpow_near_of_one_lt
  条件: {a : G} (ha : 1 < a) (g : G)
  证明: by
  let s : Set Int := { n : Int | a ^ n <= g }
  obtain ⟨k, hk : g⁻¹ <= a ^ k⟩ := MulArchimedean.arch g⁻¹ ha
  have h_ne : s.Nonempty := ⟨-k, by simpa [s] using inv_le_inv' hk⟩
  obtain ⟨k, hk⟩ := MulArchimedean.arch g ha
  have h_bdd : forall n in s, n <= (k : Int) := by
    intro n hn
    apply 

Depends on / 依赖: Int.exists_greatest_of_bdd, MulArchimedean, MulArchimedean.arch, Nonempty, contrapose, exists_greatest_of_bdd, h_bdd, h_ne, inv_le_inv, le_trans, lt_ad, s.Nonempty, zpow_le_zpow_iff_right, zpow_natCast
-/
theorem existsUnique_zpow_near_of_one_lt {a : G} (ha : 1 < a) (g : G) :
    exists! k : Int, a ^ k <= g ∧ g < a ^ (k + 1) := by
  let s : Set Int := { n : Int | a ^ n <= g }
  obtain ⟨k, hk : g⁻¹ <= a ^ k⟩ := MulArchimedean.arch g⁻¹ ha
  have h_ne : s.Nonempty := ⟨-k, by simpa [s] using inv_le_inv' hk⟩
  obtain ⟨k, hk⟩ := MulArchimedean.arch g ha
  have h_bdd : forall n in s, n <= (k : Int) := by
    intro n hn
    apply (zpow_le_zpow_iff_right ha).mp
    rw [← zpow_natCast] at hk
    exact le_trans hn hk
  obtain ⟨m, hm, hm'⟩ := Int.exists_greatest_of_bdd ⟨k, h_bdd⟩ h_ne
  have hm'' : g < a ^ (m + 1) := by
    contrapose! hm'
    exact ⟨m + 1, hm', lt_add_one _⟩
refine ⟨m, ⟨hm, hm''⟩, fun n hn => (hm' n hn.1).antisymm Int.le_of_lt_add_one ?_⟩
  rw [← zpow_lt_zpow_iff_right ha]
  exact lt_of_le_of_lt hm hn.2

@[to_additive]
/--
theorem `existsUnique_zpow_near_of_one_lt'` / 定理 `existsUnique_zpow_near_of_one_lt'`

English:
theorem existsUnique_zpow_near_of_one_lt'
  given: {a : G} (ha : 1 < a) (g : G)
  proof: by
  simpa only [one_le_div', zpow_add_one, div_lt_iff_lt_mul'] using
    existsUnique_zpow_near_of_one_lt ha g

@[to_additive]

中文:
定理 existsUnique_zpow_near_of_one_lt'
  条件: {a : G} (ha : 1 < a) (g : G)
  证明: by
  simpa only [one_le_div', zpow_add_one, div_lt_iff_lt_mul'] using
    existsUnique_zpow_near_of_one_lt ha g

@[to_additive]

Depends on / 依赖: div_lt_iff_lt_mul, existsUnique_zpow_near_of_one_lt, one_le_div, zpow_add_one
-/
theorem existsUnique_zpow_near_of_one_lt' {a : G} (ha : 1 < a) (g : G) :
    exists! k : Int, 1 <= g / a ^ k ∧ g / a ^ k < a := by
  simpa only [one_le_div', zpow_add_one, div_lt_iff_lt_mul'] using
    existsUnique_zpow_near_of_one_lt ha g

@[to_additive]
/--
theorem `existsUnique_div_zpow_mem_Ico` / 定理 `existsUnique_div_zpow_mem_Ico`

English:
theorem existsUnique_div_zpow_mem_Ico
  given: {a : G} (ha : 1 < a) (b c : G)
  proof: by
  simpa only [mem_Ico, le_div_iff_mul_le, one_mul, mul_comm c, div_lt_iff_lt_mul, mul_assoc] using
    existsUnique_zpow_near_of_one_lt' ha (b / c)

@[to_additive]

中文:
定理 existsUnique_div_zpow_mem_Ico
  条件: {a : G} (ha : 1 < a) (b c : G)
  证明: by
  simpa only [mem_Ico, le_div_iff_mul_le, one_mul, mul_comm c, div_lt_iff_lt_mul, mul_assoc] using
    existsUnique_zpow_near_of_one_lt' ha (b / c)

@[to_additive]

Depends on / 依赖: div_lt_iff_lt_mul, existsUnique_zpow_near_of_one_lt, le_div_iff_mul_le, mem_Ico, mul_assoc, mul_comm, one_mul
-/
theorem existsUnique_div_zpow_mem_Ico {a : G} (ha : 1 < a) (b c : G) :
    exists! m : Int, b / a ^ m in Set.Ico c (c * a) := by
  simpa only [mem_Ico, le_div_iff_mul_le, one_mul, mul_comm c, div_lt_iff_lt_mul, mul_assoc] using
    existsUnique_zpow_near_of_one_lt' ha (b / c)

@[to_additive]
/--
theorem `existsUnique_mul_zpow_mem_Ico` / 定理 `existsUnique_mul_zpow_mem_Ico`

English:
theorem existsUnique_mul_zpow_mem_Ico
  given: {a : G} (ha : 1 < a) (b c : G)
  proof: (Equiv.neg Int).bijective.existsUnique_iff.2 by
    simpa only [Equiv.neg_apply, mem_Ico, zpow_neg, ← div_eq_mul_inv, le_div_iff_mul_le, one_mul,
      mul_comm c, div_lt_iff_lt_mul, mul_assoc] using existsUnique_zpow_near_of_one_lt' ha (b / c)

@[to_additive]

中文:
定理 existsUnique_mul_zpow_mem_Ico
  条件: {a : G} (ha : 1 < a) (b c : G)
  证明: (Equiv.neg Int).bijective.existsUnique_iff.2 by
    simpa only [Equiv.neg_apply, mem_Ico, zpow_neg, ← div_eq_mul_inv, le_div_iff_mul_le, one_mul,
      mul_comm c, div_lt_iff_lt_mul, mul_assoc] using existsUnique_zpow_near_of_one_lt' ha (b / c)

@[to_additive]

Depends on / 依赖: Equiv.neg, Equiv.neg_apply, bijective, bijective.existsUnique_iff, div_eq_mul_inv, div_lt_iff_lt_mul, existsUnique_iff, existsUnique_zpow_near_of_one_lt, le_div_iff_mul_le, mem_Ico, mul_assoc, mul_comm, neg_apply, one_mul, zpow_neg
-/
theorem existsUnique_mul_zpow_mem_Ico {a : G} (ha : 1 < a) (b c : G) :
    exists! m : Int, b * a ^ m in Set.Ico c (c * a) :=
(Equiv.neg Int).bijective.existsUnique_iff.2 by
    simpa only [Equiv.neg_apply, mem_Ico, zpow_neg, ← div_eq_mul_inv, le_div_iff_mul_le, one_mul,
      mul_comm c, div_lt_iff_lt_mul, mul_assoc] using existsUnique_zpow_near_of_one_lt' ha (b / c)

@[to_additive]
/--
theorem `existsUnique_add_zpow_mem_Ioc` / 定理 `existsUnique_add_zpow_mem_Ioc`

English:
theorem existsUnique_add_zpow_mem_Ioc
  given: {a : G} (ha : 1 < a) (b c : G)
  proof: (Equiv.addRight (1 : Int)).bijective.existsUnique_iff.2 by
    simpa only [zpow_add_one, div_lt_iff_lt_mul', le_div_iff_mul_le', ← mul_assoc, and_comm,
      mem_Ioc, Equiv.coe_addRight, mul_le_mul_iff_right] using
      existsUnique_zpow_near_of_one_lt ha (c / b)

@[to_additive]

中文:
定理 existsUnique_add_zpow_mem_Ioc
  条件: {a : G} (ha : 1 < a) (b c : G)
  证明: (Equiv.addRight (1 : Int)).bijective.existsUnique_iff.2 by
    simpa only [zpow_add_one, div_lt_iff_lt_mul', le_div_iff_mul_le', ← mul_assoc, and_comm,
      mem_Ioc, Equiv.coe_addRight, mul_le_mul_iff_right] using
      existsUnique_zpow_near_of_one_lt ha (c / b)

@[to_additive]

Depends on / 依赖: Equiv.addRight, Equiv.coe_addRight, addRight, and_comm, bijective, bijective.existsUnique_iff, coe_addRight, div_lt_iff_lt_mul, existsUnique_iff, existsUnique_zpow_near_of_one_lt, le_div_iff_mul_le, mem_Ioc, mul_assoc, mul_le_mul_iff_right, zpow_add_one
-/
theorem existsUnique_add_zpow_mem_Ioc {a : G} (ha : 1 < a) (b c : G) :
    exists! m : Int, b * a ^ m in Set.Ioc c (c * a) :=
(Equiv.addRight (1 : Int)).bijective.existsUnique_iff.2 by
    simpa only [zpow_add_one, div_lt_iff_lt_mul', le_div_iff_mul_le', ← mul_assoc, and_comm,
      mem_Ioc, Equiv.coe_addRight, mul_le_mul_iff_right] using
      existsUnique_zpow_near_of_one_lt ha (c / b)

@[to_additive]
/--
theorem `existsUnique_sub_zpow_mem_Ioc` / 定理 `existsUnique_sub_zpow_mem_Ioc`

English:
theorem existsUnique_sub_zpow_mem_Ioc
  given: {a : G} (ha : 1 < a) (b c : G)
  proof: (Equiv.neg Int).bijective.existsUnique_iff.2 by
    simpa only [Equiv.neg_apply, zpow_neg, div_inv_eq_mul] using
      existsUnique_add_zpow_mem_Ioc ha b c

中文:
定理 existsUnique_sub_zpow_mem_Ioc
  条件: {a : G} (ha : 1 < a) (b c : G)
  证明: (Equiv.neg Int).bijective.existsUnique_iff.2 by
    simpa only [Equiv.neg_apply, zpow_neg, div_inv_eq_mul] using
      existsUnique_add_zpow_mem_Ioc ha b c

Depends on / 依赖: Equiv.neg, Equiv.neg_apply, bijective, bijective.existsUnique_iff, div_inv_eq_mul, existsUnique_add_zpow_mem_Ioc, existsUnique_iff, neg_apply, zpow_neg
-/
theorem existsUnique_sub_zpow_mem_Ioc {a : G} (ha : 1 < a) (b c : G) :
    exists! m : Int, b / a ^ m in Set.Ioc c (c * a) :=
(Equiv.neg Int).bijective.existsUnique_iff.2 by
    simpa only [Equiv.neg_apply, zpow_neg, div_inv_eq_mul] using
      existsUnique_add_zpow_mem_Ioc ha b c

end IsOrderedMonoid

section OrderedSemiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [Archimedean R]

instance (priority := 100) : IsDirectedOrder R :=
  ⟨fun x y =>
    let ⟨m, hm⟩ := exists_nat_ge x; let ⟨n, hn⟩ := exists_nat_ge y
    let ⟨k, hmk, hnk⟩ := exists_ge_ge m n
⟨k, hm.trans Nat.mono_cast hmk, hn.trans Nat.mono_cast hnk⟩⟩

end OrderedSemiring

section StrictOrderedSemiring
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R] {y : R}

/--
theorem `add_one_pow_unbounded_of_pos` / 定理 `add_one_pow_unbounded_of_pos`

English:
theorem add_one_pow_unbounded_of_pos
  given: (x : R) (hy : 0 < y)
  statement: exists n : Nat, x < (y + 1) ^ n
  proof: have : 0 <= 1 + y := add_nonneg zero_le_one hy.le
  (Archimedean.arch x hy).imp fun n h =>
    calc
      x <= n • y := h
      _ = n * y := nsmul_eq_mul _ _
      _ < 1 + n * y := lt_one_add _
      _ <= (1 + y) ^ n :=
        one_add_mul_le_pow_of_sq_nonneg (pow_nonneg hy.le _) (pow_nonneg this _)

中文:
定理 add_one_pow_unbounded_of_pos
  条件: (x : R) (hy : 0 < y)
  结论: 存在 n : 自然数, x < (y + 1) ^ n
  证明: have : 0 <= 1 + y := add_nonneg zero_le_one hy.le
  (Archimedean.arch x hy).imp fun n h =>
    calc
      x <= n • y := h
      _ = n * y := nsmul_eq_mul _ _
      _ < 1 + n * y := lt_one_add _
      _ <= (1 + y) ^ n :=
        one_add_mul_le_pow_of_sq_nonneg (pow_nonneg hy.le _) (pow_nonneg this _)

Depends on / 依赖: Archimedean, Archimedean.arch, add_comm, add_nonneg, hy.le, lt_one_add, nsmul_eq_mul, one_add_mul_le_pow_of_sq_nonneg, pow_nonneg, zero_le_one, zero_le_two
-/
theorem add_one_pow_unbounded_of_pos (x : R) (hy : 0 < y) : exists n : Nat, x < (y + 1) ^ n :=
  have : 0 <= 1 + y := add_nonneg zero_le_one hy.le
  (Archimedean.arch x hy).imp fun n h =>
    calc
      x <= n • y := h
      _ = n * y := nsmul_eq_mul _ _
      _ < 1 + n * y := lt_one_add _
      _ <= (1 + y) ^ n :=
        one_add_mul_le_pow_of_sq_nonneg (pow_nonneg hy.le _) (pow_nonneg this _)
          (add_nonneg zero_le_two hy.le) _
      _ = (y + 1) ^ n := by rw [add_comm]

/--
lemma `pow_unbounded_of_one_lt` / 引理 `pow_unbounded_of_one_lt`

English:
lemma pow_unbounded_of_one_lt
  given: [ExistsAddOfLE R] (x : R) (hy1 : 1 < y)
  statement: exists n : Nat, x < y ^ n
  proof: by
  obtain ⟨z, hz, rfl⟩ := exists_pos_add_of_lt' hy1
  rw [add_comm]
  exact add_one_pow_unbounded_of_pos _ hz

中文:
引理 pow_unbounded_of_one_lt
  条件: [ExistsAddOfLE R] (x : R) (hy1 : 1 < y)
  结论: 存在 n : 自然数, x < y ^ n
  证明: by
  obtain ⟨z, hz, rfl⟩ := exists_pos_add_of_lt' hy1
  rw [add_comm]
  exact add_one_pow_unbounded_of_pos _ hz

Depends on / 依赖: add_comm, add_one_pow_unbounded_of_pos, exists_pos_add_of_lt
-/
lemma pow_unbounded_of_one_lt [ExistsAddOfLE R] (x : R) (hy1 : 1 < y) : exists n : Nat, x < y ^ n := by
  obtain ⟨z, hz, rfl⟩ := exists_pos_add_of_lt' hy1
  rw [add_comm]
  exact add_one_pow_unbounded_of_pos _ hz

end StrictOrderedSemiring

section OrderedRing

variable [Ring R] [PartialOrder R] [IsOrderedRing R] [Archimedean R]

instance (priority := 100) : IsCodirectedOrder R where
  directed a b :=
    let ⟨m, hm⟩ := exists_int_le a; let ⟨n, hn⟩ := exists_int_le b
    ⟨(min m n : Int), le_trans (Int.cast_mono <| min_le_left _ _) hm,
      le_trans (Int.cast_mono <| min_le_right _ _) hn⟩

end OrderedRing

section StrictOrderedRing
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R]

/--
theorem `exists_floor` / 定理 `exists_floor`

English:
theorem exists_floor
  given: (x : R)
  statement: exists fl : Int, forall z : Int, z <= fl ↔ (z : R) <= x
  proof: by
  apply exists_floor'
  · obtain ⟨n, hn⟩ := exists_int_lt x
    exact ⟨n, hn.le⟩
  · obtain ⟨n, hn⟩ := exists_int_gt x
    exact ⟨n, hn.le⟩

中文:
定理 exists_floor
  条件: (x : R)
  结论: 存在 fl : 整数, 对任意 z : 整数, z <= fl ↔ (z : R) <= x
  证明: by
  apply exists_floor'
  · obtain ⟨n, hn⟩ := exists_int_lt x
    exact ⟨n, hn.le⟩
  · obtain ⟨n, hn⟩ := exists_int_gt x
    exact ⟨n, hn.le⟩

Depends on / 依赖: exists_floor, exists_int_gt, exists_int_lt, hn.le
-/
theorem exists_floor (x : R) : exists fl : Int, forall z : Int, z <= fl ↔ (z : R) <= x := by
  apply exists_floor'
  · obtain ⟨n, hn⟩ := exists_int_lt x
    exact ⟨n, hn.le⟩
  · obtain ⟨n, hn⟩ := exists_int_gt x
    exact ⟨n, hn.le⟩

end StrictOrderedRing

section LinearOrderedSemiring
variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] [Archimedean R] [ExistsAddOfLE R]
  {x y : R}

/--
theorem `exists_nat_pow_near` / 定理 `exists_nat_pow_near`

English:
theorem exists_nat_pow_near
  given: (hx : 1 <= x) (hy : 1 < y)
  statement: exists n : Nat, y ^ n <= x ∧ x < y ^ (n + 1)
  proof: by
  have h : exists n : Nat, x < y ^ n := pow_unbounded_of_one_lt _ hy
  exact
      let n := Nat.find h
      have hn : x < y ^ n := Nat.find_spec h
      have hnp : 0 < n :=
        pos_iff_ne_zero.2 fun hn0 => by rw [hn0, pow_zero] at hn; exact not_le_of_gt hn hx
      have hnsp : Nat.pred n + 1

中文:
定理 exists_nat_pow_near
  条件: (hx : 1 <= x) (hy : 1 < y)
  结论: 存在 n : 自然数, y ^ n <= x ∧ x < y ^ (n + 1)
  证明: by
  have h : exists n : Nat, x < y ^ n := pow_unbounded_of_one_lt _ hy
  exact
      let n := Nat.find h
      have hn : x < y ^ n := Nat.find_spec h
      have hnp : 0 < n :=
        pos_iff_ne_zero.2 fun hn0 => by rw [hn0, pow_zero] at hn; exact not_le_of_gt hn hx
      have hnsp : Nat.pred n + 1

Depends on / 依赖: Nat.find, Nat.find_min, Nat.find_spec, Nat.pred, Nat.pred_lt, Nat.succ_pred_eq_of_pos, find_min, find_spec, le_of_not_gt, ne_of_gt, not_le_of_gt, pos_iff_ne_zero, pow_unbounded_of_one_lt, pow_zero, pred_lt, succ_pred_eq_of_pos
-/
theorem exists_nat_pow_near (hx : 1 <= x) (hy : 1 < y) : exists n : Nat, y ^ n <= x ∧ x < y ^ (n + 1) := by
  have h : exists n : Nat, x < y ^ n := pow_unbounded_of_one_lt _ hy
  exact
      let n := Nat.find h
      have hn : x < y ^ n := Nat.find_spec h
      have hnp : 0 < n :=
        pos_iff_ne_zero.2 fun hn0 => by rw [hn0, pow_zero] at hn; exact not_le_of_gt hn hx
      have hnsp : Nat.pred n + 1 = n := Nat.succ_pred_eq_of_pos hnp
      have hltn : Nat.pred n < n := Nat.pred_lt (ne_of_gt hnp)
      ⟨Nat.pred n, le_of_not_gt (Nat.find_min h hltn), by rwa [hnsp]⟩

end LinearOrderedSemiring

section LinearOrderedSemifield
variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K] {x y ε : K}

/--
lemma `exists_nat_one_div_lt` / 引理 `exists_nat_one_div_lt`

English:
lemma exists_nat_one_div_lt
  given: (hε : 0 < ε)
  statement: exists n : Nat, 1 / (n + 1 : K) < ε
  proof: by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  use n
  rw [div_lt_iff₀]; rw [← div_lt_iff₀' hε]
  · apply hn.trans
    simp [zero_lt_one]
  · exact n.cast_add_one_pos

中文:
引理 exists_nat_one_div_lt
  条件: (hε : 0 < ε)
  结论: 存在 n : 自然数, 1 / (n + 1 : K) < ε
  证明: by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  use n
  rw [div_lt_iff₀]; rw [← div_lt_iff₀' hε]
  · apply hn.trans
    simp [zero_lt_one]
  · exact n.cast_add_one_pos

Depends on / 依赖: cast_add_one_pos, exists_nat_gt, hn.trans, n.cast_add_one_pos, zero_lt_one
-/
lemma exists_nat_one_div_lt (hε : 0 < ε) : exists n : Nat, 1 / (n + 1 : K) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  use n
  rw [div_lt_iff₀]; rw [← div_lt_iff₀' hε]
  · apply hn.trans
    simp [zero_lt_one]
  · exact n.cast_add_one_pos

variable [ExistsAddOfLE K]

/--
theorem `exists_mem_Ico_zpow` / 定理 `exists_mem_Ico_zpow`

English:
theorem exists_mem_Ico_zpow
  given: (hx : 0 < x) (hy : 1 < y)
  statement: exists n : Int, x in Ico (y ^ n) (y ^ (n + 1))
  proof: by
  have he : exists m : Int, y ^ m <= x := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt x⁻¹ hy
    use -N
    rw [zpow_neg y ↑N]; rw [zpow_natCast]
    exact ((inv_lt_comm₀ hx (lt_trans (inv_pos.2 hx) hN)).1 hN).le
  have hb : exists b : Int, forall m, y ^ m <= x -> m <= b := by
    obtain ⟨M,

中文:
定理 exists_mem_Ico_zpow
  条件: (hx : 0 < x) (hy : 1 < y)
  结论: 存在 n : 整数, x in Ico (y ^ n) (y ^ (n + 1))
  证明: by
  have he : exists m : Int, y ^ m <= x := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt x⁻¹ hy
    use -N
    rw [zpow_neg y ↑N]; rw [zpow_natCast]
    exact ((inv_lt_comm₀ hx (lt_trans (inv_pos.2 hx) hN)).1 hN).le
  have hb : exists b : Int, forall m, y ^ m <= x -> m <= b := by
    obtain ⟨M,

Depends on / 依赖: Int.exists_greatest_of_bdd, contrapose, exists_greatest_of_bdd, hM.le, hy.le, inv_pos, le_trans, lt_trans, pow_unbounded_of_one_lt, zpow_natCast, zpow_neg
-/
theorem exists_mem_Ico_zpow (hx : 0 < x) (hy : 1 < y) : exists n : Int, x in Ico (y ^ n) (y ^ (n + 1)) := by
  have he : exists m : Int, y ^ m <= x := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt x⁻¹ hy
    use -N
    rw [zpow_neg y ↑N]; rw [zpow_natCast]
    exact ((inv_lt_comm₀ hx (lt_trans (inv_pos.2 hx) hN)).1 hN).le
  have hb : exists b : Int, forall m, y ^ m <= x -> m <= b := by
    obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt x hy
    refine ⟨M, fun m hm => ?_⟩
    contrapose! hM
    rw [← zpow_natCast]
    exact le_trans (zpow_le_zpow_right₀ hy.le hM.le) hm
  obtain ⟨n, hn₁, hn₂⟩ := Int.exists_greatest_of_bdd hb he
  exact ⟨n, hn₁, lt_of_not_ge fun hge => (Int.lt_succ _).not_ge (hn₂ _ hge)⟩

/--
theorem `exists_mem_Ioc_zpow` / 定理 `exists_mem_Ioc_zpow`

English:
theorem exists_mem_Ioc_zpow
  given: (hx : 0 < x) (hy : 1 < y)
  statement: exists n : Int, x in Ioc (y ^ n) (y ^ (n + 1))
  proof: let ⟨m, hle, hlt⟩ := exists_mem_Ico_zpow (inv_pos.2 hx) hy
  have hyp : 0 < y := lt_trans zero_lt_one hy
  ⟨-(m + 1), by rwa [zpow_neg, inv_lt_comm₀ (zpow_pos hyp _) hx], by
    rwa [neg_add, neg_add_cancel_right, zpow_neg, le_inv_comm₀ hx (zpow_pos hyp _)]⟩

中文:
定理 exists_mem_Ioc_zpow
  条件: (hx : 0 < x) (hy : 1 < y)
  结论: 存在 n : 整数, x in Ioc (y ^ n) (y ^ (n + 1))
  证明: let ⟨m, hle, hlt⟩ := exists_mem_Ico_zpow (inv_pos.2 hx) hy
  have hyp : 0 < y := lt_trans zero_lt_one hy
  ⟨-(m + 1), by rwa [zpow_neg, inv_lt_comm₀ (zpow_pos hyp _) hx], by
    rwa [neg_add, neg_add_cancel_right, zpow_neg, le_inv_comm₀ hx (zpow_pos hyp _)]⟩

Depends on / 依赖: exists_mem_Ico_zpow, inv_pos, lt_trans, neg_add, neg_add_cancel_right, zero_lt_one, zpow_neg, zpow_pos
-/
theorem exists_mem_Ioc_zpow (hx : 0 < x) (hy : 1 < y) : exists n : Int, x in Ioc (y ^ n) (y ^ (n + 1)) :=
  let ⟨m, hle, hlt⟩ := exists_mem_Ico_zpow (inv_pos.2 hx) hy
  have hyp : 0 < y := lt_trans zero_lt_one hy
  ⟨-(m + 1), by rwa [zpow_neg, inv_lt_comm₀ (zpow_pos hyp _) hx], by
    rwa [neg_add, neg_add_cancel_right, zpow_neg, le_inv_comm₀ hx (zpow_pos hyp _)]⟩

/--
theorem `exists_pow_lt_of_lt_one` / 定理 `exists_pow_lt_of_lt_one`

English:
theorem exists_pow_lt_of_lt_one
  given: (hx : 0 < x) (hy : y < 1)
  statement: exists n : Nat, y ^ n < x
  proof: by
  by_cases! y_pos : y <= 0
  · use 1
    simp only [pow_one]
    exact y_pos.trans_lt hx
  rcases pow_unbounded_of_one_lt x⁻¹ ((one_lt_inv₀ y_pos).2 hy) with ⟨q, hq⟩
  exact ⟨q, by rwa [inv_pow, inv_lt_inv₀ hx (pow_pos y_pos _)] at hq⟩

中文:
定理 exists_pow_lt_of_lt_one
  条件: (hx : 0 < x) (hy : y < 1)
  结论: 存在 n : 自然数, y ^ n < x
  证明: by
  by_cases! y_pos : y <= 0
  · use 1
    simp only [pow_one]
    exact y_pos.trans_lt hx
  rcases pow_unbounded_of_one_lt x⁻¹ ((one_lt_inv₀ y_pos).2 hy) with ⟨q, hq⟩
  exact ⟨q, by rwa [inv_pow, inv_lt_inv₀ hx (pow_pos y_pos _)] at hq⟩

Depends on / 依赖: inv_pow, pow_one, pow_pos, pow_unbounded_of_one_lt, trans_lt, y_pos, y_pos.trans_lt
-/
theorem exists_pow_lt_of_lt_one (hx : 0 < x) (hy : y < 1) : exists n : Nat, y ^ n < x := by
  by_cases! y_pos : y <= 0
  · use 1
    simp only [pow_one]
    exact y_pos.trans_lt hx
  rcases pow_unbounded_of_one_lt x⁻¹ ((one_lt_inv₀ y_pos).2 hy) with ⟨q, hq⟩
  exact ⟨q, by rwa [inv_pow, inv_lt_inv₀ hx (pow_pos y_pos _)] at hq⟩

/--
theorem `exists_nat_pow_near_of_lt_one` / 定理 `exists_nat_pow_near_of_lt_one`

English:
theorem exists_nat_pow_near_of_lt_one
  given: (xpos : 0 < x) (hx : x <= 1) (ypos : 0 < y) (hy : y < 1)
  proof: by
  rcases exists_nat_pow_near (one_le_inv_iff₀.2 ⟨xpos, hx⟩) (one_lt_inv_iff₀.2 ⟨ypos, hy⟩) with
    ⟨n, hn, h'n⟩
  refine ⟨n, ?_, ?_⟩
  · rwa [inv_pow, inv_lt_inv₀ xpos (pow_pos ypos _)] at h'n
  · rwa [inv_pow, inv_le_inv₀ (pow_pos ypos _) xpos] at hn

中文:
定理 exists_nat_pow_near_of_lt_one
  条件: (xpos : 0 < x) (hx : x <= 1) (ypos : 0 < y) (hy : y < 1)
  证明: by
  rcases exists_nat_pow_near (one_le_inv_iff₀.2 ⟨xpos, hx⟩) (one_lt_inv_iff₀.2 ⟨ypos, hy⟩) with
    ⟨n, hn, h'n⟩
  refine ⟨n, ?_, ?_⟩
  · rwa [inv_pow, inv_lt_inv₀ xpos (pow_pos ypos _)] at h'n
  · rwa [inv_pow, inv_le_inv₀ (pow_pos ypos _) xpos] at hn

Depends on / 依赖: exists_nat_pow_near, inv_pow, pow_pos
-/
theorem exists_nat_pow_near_of_lt_one (xpos : 0 < x) (hx : x <= 1) (ypos : 0 < y) (hy : y < 1) :
    exists n : Nat, y ^ (n + 1) < x ∧ x <= y ^ n := by
  rcases exists_nat_pow_near (one_le_inv_iff₀.2 ⟨xpos, hx⟩) (one_lt_inv_iff₀.2 ⟨ypos, hy⟩) with
    ⟨n, hn, h'n⟩
  refine ⟨n, ?_, ?_⟩
  · rwa [inv_pow, inv_lt_inv₀ xpos (pow_pos ypos _)] at h'n
  · rwa [inv_pow, inv_le_inv₀ (pow_pos ypos _) xpos] at hn

/--
lemma `exists_pow_btwn_of_lt_mul` / 引理 `exists_pow_btwn_of_lt_mul`

English:
lemma exists_pow_btwn_of_lt_mul
  statement: {a b c : K} (h : a < b * c) (hb₀ : 0 < b) (hb₁ : b <= 1)
  proof: by
  have := exists_pow_lt_of_lt_one hb₀ hc₁
  refine ⟨Nat.find this, h.trans_le ?_, Nat.find_spec this⟩
  by_contra! H
  have hn : Nat.find this != 0 := by
    intro hf
    simp only [hf, pow_zero] at H
    exact (H.trans <| (mul_lt_of_lt_one_right hb₀ hc₁).trans_le hb₁).false
  rw [(Nat.succ_pred_

中文:
引理 exists_pow_btwn_of_lt_mul
  结论: {a b c : K} (h : a < b * c) (hb₀ : 0 < b) (hb₁ : b <= 1)
  证明: by
  have := exists_pow_lt_of_lt_one hb₀ hc₁
  refine ⟨Nat.find this, h.trans_le ?_, Nat.find_spec this⟩
  by_contra! H
  have hn : Nat.find this != 0 := by
    intro hf
    simp only [hf, pow_zero] at H
    exact (H.trans <| (mul_lt_of_lt_one_right hb₀ hc₁).trans_le hb₁).false
  rw [(Nat.succ_pred_

Depends on / 依赖: H.trans, Nat.find, Nat.find_min, Nat.find_spec, Nat.sub_one_lt, Nat.succ_pred_eq_of_ne_zero, exists_pow_lt_of_lt_one, find_min, find_spec, h.trans_le, mul_lt_of_lt_one_right, pow_succ, pow_zero, sub_one_lt, succ_pred_eq_of_ne_zero, trans_le
-/
lemma exists_pow_btwn_of_lt_mul {a b c : K} (h : a < b * c) (hb₀ : 0 < b) (hb₁ : b <= 1)
    (hc₀ : 0 < c) (hc₁ : c < 1) :
    exists n : Nat, a < c ^ n ∧ c ^ n < b := by
  have := exists_pow_lt_of_lt_one hb₀ hc₁
  refine ⟨Nat.find this, h.trans_le ?_, Nat.find_spec this⟩
  by_contra! H
  have hn : Nat.find this != 0 := by
    intro hf
    simp only [hf, pow_zero] at H
    exact (H.trans <| (mul_lt_of_lt_one_right hb₀ hc₁).trans_le hb₁).false
  rw [(Nat.succ_pred_eq_of_ne_zero hn).symm]; rw [pow_succ]; rw [mul_lt_mul_iff_left₀ hc₀] at H
  exact Nat.find_min this (Nat.sub_one_lt hn) H

/--
lemma `exists_zpow_btwn_of_lt_mul` / 引理 `exists_zpow_btwn_of_lt_mul`

English:
lemma exists_zpow_btwn_of_lt_mul
  statement: {a b c : K} (h : a < b * c) (hb₀ : 0 < b) (hc₀ : 0 < c)
  proof: by
  rcases le_or_gt a 0 with ha | ha
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hb₀ hc₁
    exact ⟨n, ha.trans_lt (zpow_pos hc₀ _), mod_cast hn⟩
  · rcases le_or_gt b 1 with hb₁ | hb₁
    · obtain ⟨n, hn⟩ := exists_pow_btwn_of_lt_mul h hb₀ hb₁ hc₀ hc₁
      exact ⟨n, mod_cast hn⟩
    · rcases lt

中文:
引理 exists_zpow_btwn_of_lt_mul
  结论: {a b c : K} (h : a < b * c) (hb₀ : 0 < b) (hc₀ : 0 < c)
  证明: by
  rcases le_or_gt a 0 with ha | ha
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hb₀ hc₁
    exact ⟨n, ha.trans_lt (zpow_pos hc₀ _), mod_cast hn⟩
  · rcases le_or_gt b 1 with hb₁ | hb₁
    · obtain ⟨n, hn⟩ := exists_pow_btwn_of_lt_mul h hb₀ hb₁ hc₀ hc₁
      exact ⟨n, mod_cast hn⟩
    · rcases lt

Depends on / 依赖: exists_pow_btwn_of_lt_mul, exists_pow_lt_of_lt_one, ha.trans_lt, inv_pos_of_pos, le_or_gt, lt_or_ge, mod_cast, trans_lt, zpow_pos, zpow_zero
-/
lemma exists_zpow_btwn_of_lt_mul {a b c : K} (h : a < b * c) (hb₀ : 0 < b) (hc₀ : 0 < c)
    (hc₁ : c < 1) :
    exists n : Int, a < c ^ n ∧ c ^ n < b := by
  rcases le_or_gt a 0 with ha | ha
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hb₀ hc₁
    exact ⟨n, ha.trans_lt (zpow_pos hc₀ _), mod_cast hn⟩
  · rcases le_or_gt b 1 with hb₁ | hb₁
    · obtain ⟨n, hn⟩ := exists_pow_btwn_of_lt_mul h hb₀ hb₁ hc₀ hc₁
      exact ⟨n, mod_cast hn⟩
    · rcases lt_or_ge a 1 with ha₁ | ha₁
      · refine ⟨0, ?_⟩
        rw [zpow_zero]
        exact ⟨ha₁, hb₁⟩
      · have : b⁻¹ < a⁻¹ * c := by rwa [lt_inv_mul_iff₀' ha, inv_mul_lt_iff₀ hb₀]
        obtain ⟨n, hn₁, hn₂⟩ :=
          exists_pow_btwn_of_lt_mul this (inv_pos_of_pos ha) (inv_le_one_of_one_le₀ ha₁) hc₀ hc₁
        refine ⟨-n, ?_, ?_⟩
        · rwa [lt_inv_comm₀ (pow_pos hc₀ n) ha, ← zpow_natCast, ← zpow_neg] at hn₂
        · rwa [inv_lt_comm₀ hb₀ (pow_pos hc₀ n), ← zpow_natCast, ← zpow_neg] at hn₁

end LinearOrderedSemifield

section LinearOrderedField
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/--
theorem `archimedean_iff_nat_lt` / 定理 `archimedean_iff_nat_lt`

English:
theorem archimedean_iff_nat_lt
  statement: Archimedean K ↔ forall x : K, exists n : Nat, x < n
  proof: ⟨@exists_nat_gt K _ _ _, fun H =>
    ⟨fun x y y0 =>
(H (x / y)).imp fun n h => le_of_lt by rwa [div_lt_iff₀ y0, ← nsmul_eq_mul] at h⟩⟩

中文:
定理 archimedean_iff_nat_lt
  结论: Archimedean K ↔ 对任意 x : K, 存在 n : 自然数, x < n
  证明: ⟨@exists_nat_gt K _ _ _, fun H =>
    ⟨fun x y y0 =>
(H (x / y)).imp fun n h => le_of_lt by rwa [div_lt_iff₀ y0, ← nsmul_eq_mul] at h⟩⟩

Depends on / 依赖: exists_nat_gt, le_of_lt, nsmul_eq_mul
-/
theorem archimedean_iff_nat_lt : Archimedean K ↔ forall x : K, exists n : Nat, x < n :=
  ⟨@exists_nat_gt K _ _ _, fun H =>
    ⟨fun x y y0 =>
(H (x / y)).imp fun n h => le_of_lt by rwa [div_lt_iff₀ y0, ← nsmul_eq_mul] at h⟩⟩

/--
theorem `archimedean_iff_nat_le` / 定理 `archimedean_iff_nat_le`

English:
theorem archimedean_iff_nat_le
  statement: Archimedean K ↔ forall x : K, exists n : Nat, x <= n
  proof: archimedean_iff_nat_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Nat.cast_lt.2 (lt_add_one _))⟩⟩

中文:
定理 archimedean_iff_nat_le
  结论: Archimedean K ↔ 对任意 x : K, 存在 n : 自然数, x <= n
  证明: archimedean_iff_nat_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Nat.cast_lt.2 (lt_add_one _))⟩⟩

Depends on / 依赖: Nat.cast_lt, archimedean_iff_nat_lt, archimedean_iff_nat_lt.trans, cast_lt, le_of_lt, lt_add_one, lt_of_le_of_lt
-/
theorem archimedean_iff_nat_le : Archimedean K ↔ forall x : K, exists n : Nat, x <= n :=
  archimedean_iff_nat_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Nat.cast_lt.2 (lt_add_one _))⟩⟩

/--
theorem `archimedean_iff_int_lt` / 定理 `archimedean_iff_int_lt`

English:
theorem archimedean_iff_int_lt
  statement: Archimedean K ↔ forall x : K, exists n : Int, x < n
  proof: ⟨@exists_int_gt K _ _ _, by
    rw [archimedean_iff_nat_lt]
    intro h x
    obtain ⟨n, h⟩ := h x
    refine ⟨n.toNat, h.trans_le ?_⟩
    exact mod_cast Int.self_le_toNat _⟩

中文:
定理 archimedean_iff_int_lt
  结论: Archimedean K ↔ 对任意 x : K, 存在 n : 整数, x < n
  证明: ⟨@exists_int_gt K _ _ _, by
    rw [archimedean_iff_nat_lt]
    intro h x
    obtain ⟨n, h⟩ := h x
    refine ⟨n.toNat, h.trans_le ?_⟩
    exact mod_cast Int.self_le_toNat _⟩

Depends on / 依赖: Int.self_le_toNat, archimedean_iff_nat_lt, exists_int_gt, h.trans_le, mod_cast, n.toNat, self_le_toNat, trans_le
-/
theorem archimedean_iff_int_lt : Archimedean K ↔ forall x : K, exists n : Int, x < n :=
  ⟨@exists_int_gt K _ _ _, by
    rw [archimedean_iff_nat_lt]
    intro h x
    obtain ⟨n, h⟩ := h x
    refine ⟨n.toNat, h.trans_le ?_⟩
    exact mod_cast Int.self_le_toNat _⟩

/--
theorem `archimedean_iff_int_le` / 定理 `archimedean_iff_int_le`

English:
theorem archimedean_iff_int_le
  statement: Archimedean K ↔ forall x : K, exists n : Int, x <= n
  proof: archimedean_iff_int_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Int.cast_lt.2 (lt_add_one _))⟩⟩

中文:
定理 archimedean_iff_int_le
  结论: Archimedean K ↔ 对任意 x : K, 存在 n : 整数, x <= n
  证明: archimedean_iff_int_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Int.cast_lt.2 (lt_add_one _))⟩⟩

Depends on / 依赖: Int.cast_lt, archimedean_iff_int_lt, archimedean_iff_int_lt.trans, cast_lt, le_of_lt, lt_add_one, lt_of_le_of_lt
-/
theorem archimedean_iff_int_le : Archimedean K ↔ forall x : K, exists n : Int, x <= n :=
  archimedean_iff_int_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Int.cast_lt.2 (lt_add_one _))⟩⟩

/--
theorem `archimedean_iff_rat_lt` / 定理 `archimedean_iff_rat_lt`

English:
theorem archimedean_iff_rat_lt
  statement: Archimedean K ↔ forall x : K, exists q : Rat, x < q where
  proof: let ⟨n, h⟩ := exists_nat_gt x
    ⟨n, by rwa [Rat.cast_natCast]⟩
  mpr H := archimedean_iff_nat_lt.2 fun x =>
let ⟨q, h⟩ := H x; ⟨⌈q⌉₊, lt_of_lt_of_le h mod_cast Nat.le_ceil _⟩

中文:
定理 archimedean_iff_rat_lt
  结论: Archimedean K ↔ 对任意 x : K, 存在 q : Rat, x < q where
  证明: let ⟨n, h⟩ := exists_nat_gt x
    ⟨n, by rwa [Rat.cast_natCast]⟩
  mpr H := archimedean_iff_nat_lt.2 fun x =>
let ⟨q, h⟩ := H x; ⟨⌈q⌉₊, lt_of_lt_of_le h mod_cast Nat.le_ceil _⟩

Depends on / 依赖: Nat.le_ceil, Rat.cast_natCast, archimedean_iff_nat_lt, cast_natCast, exists_nat_gt, le_ceil, lt_of_lt_of_le, mod_cast
-/
theorem archimedean_iff_rat_lt : Archimedean K ↔ forall x : K, exists q : Rat, x < q where
  mp _ x :=
    let ⟨n, h⟩ := exists_nat_gt x
    ⟨n, by rwa [Rat.cast_natCast]⟩
  mpr H := archimedean_iff_nat_lt.2 fun x =>
let ⟨q, h⟩ := H x; ⟨⌈q⌉₊, lt_of_lt_of_le h mod_cast Nat.le_ceil _⟩

/--
theorem `archimedean_iff_rat_le` / 定理 `archimedean_iff_rat_le`

English:
theorem archimedean_iff_rat_le
  statement: Archimedean K ↔ forall x : K, exists q : Rat, x <= q
  proof: archimedean_iff_rat_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Rat.cast_lt.2 (lt_add_one _))⟩⟩

中文:
定理 archimedean_iff_rat_le
  结论: Archimedean K ↔ 对任意 x : K, 存在 q : Rat, x <= q
  证明: archimedean_iff_rat_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Rat.cast_lt.2 (lt_add_one _))⟩⟩

Depends on / 依赖: Rat.cast_lt, archimedean_iff_rat_lt, archimedean_iff_rat_lt.trans, cast_lt, le_of_lt, lt_add_one, lt_of_le_of_lt
-/
theorem archimedean_iff_rat_le : Archimedean K ↔ forall x : K, exists q : Rat, x <= q :=
  archimedean_iff_rat_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Rat.cast_lt.2 (lt_add_one _))⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Archimedean Rat
  body: archimedean_iff_rat_le.2 fun q => ⟨q, by rw [Rat.cast_id]⟩

中文:
实例 :
  签名: Archimedean Rat
  定义体: archimedean_iff_rat_le.2 fun q => ⟨q, by rw [Rat.cast_id]⟩

Depends on / 依赖: Rat.cast_id, archimedean_iff_rat_le, cast_id
-/
instance : Archimedean Rat :=
  archimedean_iff_rat_le.2 fun q => ⟨q, by rw [Rat.cast_id]⟩

variable [Archimedean K] {x y ε : K}

/--
theorem `exists_rat_gt` / 定理 `exists_rat_gt`

English:
theorem exists_rat_gt
  given: (x : K)
  statement: exists q : Rat, x < q
  proof: archimedean_iff_rat_lt.mp ‹_› _

中文:
定理 exists_rat_gt
  条件: (x : K)
  结论: 存在 q : Rat, x < q
  证明: archimedean_iff_rat_lt.mp ‹_› _

Depends on / 依赖: archimedean_iff_rat_lt, archimedean_iff_rat_lt.mp
-/
theorem exists_rat_gt (x : K) : exists q : Rat, x < q := archimedean_iff_rat_lt.mp ‹_› _

/--
theorem `exists_rat_lt` / 定理 `exists_rat_lt`

English:
theorem exists_rat_lt
  given: (x : K)
  statement: exists q : Rat, (q : K) < x
  proof: let ⟨n, h⟩ := exists_int_lt x
  ⟨n, by rwa [Rat.cast_intCast]⟩

中文:
定理 exists_rat_lt
  条件: (x : K)
  结论: 存在 q : Rat, (q : K) < x
  证明: let ⟨n, h⟩ := exists_int_lt x
  ⟨n, by rwa [Rat.cast_intCast]⟩

Depends on / 依赖: Rat.cast_intCast, cast_intCast, exists_int_lt
-/
theorem exists_rat_lt (x : K) : exists q : Rat, (q : K) < x :=
  let ⟨n, h⟩ := exists_int_lt x
  ⟨n, by rwa [Rat.cast_intCast]⟩

/--
theorem `exists_div_btwn` / 定理 `exists_div_btwn`

English:
theorem exists_div_btwn
  given: {x y : K} {n : Nat} (h : x < y) (nh : (y - x)⁻¹ < n)
  proof: by
  obtain ⟨z, zh⟩ := exists_floor (x * n)
  refine ⟨z + 1, ?_⟩
  have n0' := (inv_pos.2 (sub_pos.2 h)).trans nh
  rw [div_lt_iff₀ n0']
refine ⟨(lt_div_iff₀ n0').2 (lt_iff_lt_of_le_iff_le (zh _)).1 (lt_add_one _), ?_⟩
  rw [Int.cast_add]; rw [Int.cast_one]
  grw [(zh _).1 le_rfl]
  rwa [← lt_sub_if

中文:
定理 exists_div_btwn
  条件: {x y : K} {n : 自然数} (h : x < y) (nh : (y - x)⁻¹ < n)
  证明: by
  obtain ⟨z, zh⟩ := exists_floor (x * n)
  refine ⟨z + 1, ?_⟩
  have n0' := (inv_pos.2 (sub_pos.2 h)).trans nh
  rw [div_lt_iff₀ n0']
refine ⟨(lt_div_iff₀ n0').2 (lt_iff_lt_of_le_iff_le (zh _)).1 (lt_add_one _), ?_⟩
  rw [Int.cast_add]; rw [Int.cast_one]
  grw [(zh _).1 le_rfl]
  rwa [← lt_sub_if

Depends on / 依赖: Int.cast_add, Int.cast_one, cast_add, cast_one, exists_floor, inv_pos, le_rfl, lt_add_one, lt_iff_lt_of_le_iff_le, lt_sub_iff_add_lt, one_div, sub_mul, sub_pos
-/
theorem exists_div_btwn {x y : K} {n : Nat} (h : x < y) (nh : (y - x)⁻¹ < n) :
    exists z : Int, x < (z : K) / n ∧ (z : K) / n < y := by
  obtain ⟨z, zh⟩ := exists_floor (x * n)
  refine ⟨z + 1, ?_⟩
  have n0' := (inv_pos.2 (sub_pos.2 h)).trans nh
  rw [div_lt_iff₀ n0']
refine ⟨(lt_div_iff₀ n0').2 (lt_iff_lt_of_le_iff_le (zh _)).1 (lt_add_one _), ?_⟩
  rw [Int.cast_add]; rw [Int.cast_one]
  grw [(zh _).1 le_rfl]
  rwa [← lt_sub_iff_add_lt', ← sub_mul, ← div_lt_iff₀' (sub_pos.2 h), one_div]

/--
theorem `exists_rat_btwn` / 定理 `exists_rat_btwn`

English:
theorem exists_rat_btwn
  given: {x y : K} (h : x < y)
  statement: exists q : Rat, x < q ∧ q < y
  proof: by
  obtain ⟨n, nh⟩ := exists_nat_gt (y - x)⁻¹
  obtain ⟨z, zh, zh'⟩ := exists_div_btwn h nh
  refine ⟨(z : Rat) / n, ?_, ?_⟩ <;> simpa

中文:
定理 exists_rat_btwn
  条件: {x y : K} (h : x < y)
  结论: 存在 q : Rat, x < q ∧ q < y
  证明: by
  obtain ⟨n, nh⟩ := exists_nat_gt (y - x)⁻¹
  obtain ⟨z, zh, zh'⟩ := exists_div_btwn h nh
  refine ⟨(z : Rat) / n, ?_, ?_⟩ <;> simpa

Depends on / 依赖: exists_div_btwn, exists_nat_gt
-/
theorem exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat, x < q ∧ q < y := by
  obtain ⟨n, nh⟩ := exists_nat_gt (y - x)⁻¹
  obtain ⟨z, zh, zh'⟩ := exists_div_btwn h nh
  refine ⟨(z : Rat) / n, ?_, ?_⟩ <;> simpa

/--
theorem `exists_rat_mem_uIoo` / 定理 `exists_rat_mem_uIoo`

English:
theorem exists_rat_mem_uIoo
  given: {x y : K} (h : x != y)
  statement: exists q : Rat, ↑q in Set.uIoo x y
  proof: exists_rat_btwn (min_lt_max.mpr h)

中文:
定理 exists_rat_mem_uIoo
  条件: {x y : K} (h : x != y)
  结论: 存在 q : Rat, ↑q in Set.uIoo x y
  证明: exists_rat_btwn (min_lt_max.mpr h)

Depends on / 依赖: exists_rat_btwn, min_lt_max, min_lt_max.mpr
-/
theorem exists_rat_mem_uIoo {x y : K} (h : x != y) : exists q : Rat, ↑q in Set.uIoo x y :=
  exists_rat_btwn (min_lt_max.mpr h)

/--
theorem `exists_pow_btwn` / 定理 `exists_pow_btwn`

English:
theorem exists_pow_btwn
  given: {n : Nat} (hn : n != 0) {x y : K} (h : x < y) (hy : 0 < y)
  proof: by
  have ⟨δ, δ_pos, cont⟩ := uniform_continuous_npow_on_bounded (max 1 y)
    (sub_pos.mpr <| max_lt_iff.mpr ⟨h, hy⟩) n
  have ex : exists m : Nat, y <= (m * δ) ^ n := by
    have ⟨m, hm⟩ := exists_nat_ge (y / δ + 1 / δ)
    refine ⟨m, le_trans ?_ (le_self_pow₀ ?_ hn)⟩ <;> rw [← div_le_iff₀ δ_pos]


中文:
定理 exists_pow_btwn
  条件: {n : 自然数} (hn : n != 0) {x y : K} (h : x < y) (hy : 0 < y)
  证明: by
  have ⟨δ, δ_pos, cont⟩ := uniform_continuous_npow_on_bounded (max 1 y)
    (sub_pos.mpr <| max_lt_iff.mpr ⟨h, hy⟩) n
  have ex : exists m : Nat, y <= (m * δ) ^ n := by
    have ⟨m, hm⟩ := exists_nat_ge (y / δ + 1 / δ)
    refine ⟨m, le_trans ?_ (le_self_pow₀ ?_ hn)⟩ <;> rw [← div_le_iff₀ δ_pos]


Depends on / 依赖: Nat.find, Nat.find_pos, exists_nat_ge, find_pos, le.trans, le_add_of_nonneg_left, le_trans, lt_add_of_pos_right, m_pos, max_lt_iff, max_lt_iff.mpr, sub_pos, sub_pos.mpr, uniform_continuous_npow_on_bounded, zero_pow
-/
theorem exists_pow_btwn {n : Nat} (hn : n != 0) {x y : K} (h : x < y) (hy : 0 < y) :
    exists q : K, 0 < q ∧ x < q ^ n ∧ q ^ n < y := by
  have ⟨δ, δ_pos, cont⟩ := uniform_continuous_npow_on_bounded (max 1 y)
    (sub_pos.mpr <| max_lt_iff.mpr ⟨h, hy⟩) n
  have ex : exists m : Nat, y <= (m * δ) ^ n := by
    have ⟨m, hm⟩ := exists_nat_ge (y / δ + 1 / δ)
    refine ⟨m, le_trans ?_ (le_self_pow₀ ?_ hn)⟩ <;> rw [← div_le_iff₀ δ_pos]
    · exact (lt_add_of_pos_right _ <| by positivity).le.trans hm
    · exact (le_add_of_nonneg_left <| by positivity).trans hm
  let m := Nat.find ex
have m_pos : 0 < m := (Nat.find_pos _).mpr by simpa [zero_pow hn] using hy
  let q := m.pred * δ
  have qny : q ^ n < y := lt_of_not_ge (Nat.find_min ex <| Nat.pred_lt m_pos.ne')
have q1y : |q| < max 1 y := (abs_eq_self.mpr <| by positivity).trans_lt lt_max_iff.mpr
    (or_iff_not_imp_left.mpr fun q1 => (le_self_pow₀ (le_of_not_gt q1) hn).trans_lt qny)
  have xqn : max x 0 < q ^ n :=
    calc _ = y - (y - max x 0) := by rw [sub_sub_cancel]
      _ <= (m * δ) ^ n - (y - max x 0) := sub_le_sub_right (Nat.find_spec ex) _
      _ < (m * δ) ^ n - ((m * δ) ^ n - q ^ n) := by
        refine sub_lt_sub_left ((le_abs_self _).trans_lt <| cont _ _ q1y.le ?_) _
        rw [← Nat.succ_pred_eq_of_pos m_pos]; rw [Nat.cast_succ]; rw [← sub_mul]; rw [add_sub_cancel_left]; rw [one_mul]; rw [abs_eq_self.mpr (by positivity)]
      _ = q ^ n := sub_sub_cancel ..
  exact ⟨q, lt_of_le_of_ne (by positivity) fun q0 =>
(le_sup_right.trans_lt xqn).ne q0 ▸ (zero_pow hn).symm, le_sup_left.trans_lt xqn, qny⟩

/--
theorem `exists_rat_pow_btwn` / 定理 `exists_rat_pow_btwn`

English:
theorem exists_rat_pow_btwn
  given: {n : Nat} (hn : n != 0) {x y : K} (h : x < y) (hy : 0 < y)
  proof: by
  obtain ⟨q₂, hx₂, hy₂⟩ := exists_rat_btwn (max_lt h hy)
  obtain ⟨q₁, hx₁, hq₁₂⟩ := exists_rat_btwn hx₂
  have : (0 : K) < q₂ := (le_max_right _ _).trans_lt hx₂
  norm_cast at hq₁₂ this
  obtain ⟨q, hq, hq₁, hq₂⟩ := exists_pow_btwn hn hq₁₂ this
refine ⟨q, hq, (le_max_left _ _).trans_lt hx₁.trans

中文:
定理 exists_rat_pow_btwn
  条件: {n : 自然数} (hn : n != 0) {x y : K} (h : x < y) (hy : 0 < y)
  证明: by
  obtain ⟨q₂, hx₂, hy₂⟩ := exists_rat_btwn (max_lt h hy)
  obtain ⟨q₁, hx₁, hq₁₂⟩ := exists_rat_btwn hx₂
  have : (0 : K) < q₂ := (le_max_right _ _).trans_lt hx₂
  norm_cast at hq₁₂ this
  obtain ⟨q, hq, hq₁, hq₂⟩ := exists_pow_btwn hn hq₁₂ this
refine ⟨q, hq, (le_max_left _ _).trans_lt hx₁.trans

Depends on / 依赖: assumption_mod_cast, exists_pow_btwn, exists_rat_btwn, le_max_left, le_max_right, max_lt, trans_lt
-/
theorem exists_rat_pow_btwn {n : Nat} (hn : n != 0) {x y : K} (h : x < y) (hy : 0 < y) :
    exists q : Rat, 0 < q ∧ x < (q : K) ^ n ∧ (q : K) ^ n < y := by
  obtain ⟨q₂, hx₂, hy₂⟩ := exists_rat_btwn (max_lt h hy)
  obtain ⟨q₁, hx₁, hq₁₂⟩ := exists_rat_btwn hx₂
  have : (0 : K) < q₂ := (le_max_right _ _).trans_lt hx₂
  norm_cast at hq₁₂ this
  obtain ⟨q, hq, hq₁, hq₂⟩ := exists_pow_btwn hn hq₁₂ this
refine ⟨q, hq, (le_max_left _ _).trans_lt hx₁.trans ?_, hy₂.trans' ?_⟩ <;> assumption_mod_cast

/--
theorem `le_of_forall_rat_lt_imp_le` / 定理 `le_of_forall_rat_lt_imp_le`

English:
theorem le_of_forall_rat_lt_imp_le
  given: (h : forall q : Rat, (q : K) < x -> (q : K) <= y)
  statement: x <= y
  proof: le_of_not_gt fun hyx =>
    let ⟨_, hy, hx⟩ := exists_rat_btwn hyx
hy.not_ge h _ hx

中文:
定理 le_of_forall_rat_lt_imp_le
  条件: (h : 对任意 q : Rat, (q : K) < x -> (q : K) <= y)
  结论: x <= y
  证明: le_of_not_gt fun hyx =>
    let ⟨_, hy, hx⟩ := exists_rat_btwn hyx
hy.not_ge h _ hx

Depends on / 依赖: exists_rat_btwn, hy.not_ge, le_of_not_gt, not_ge
-/
theorem le_of_forall_rat_lt_imp_le (h : forall q : Rat, (q : K) < x -> (q : K) <= y) : x <= y :=
  le_of_not_gt fun hyx =>
    let ⟨_, hy, hx⟩ := exists_rat_btwn hyx
hy.not_ge h _ hx

/--
theorem `le_of_forall_lt_rat_imp_le` / 定理 `le_of_forall_lt_rat_imp_le`

English:
theorem le_of_forall_lt_rat_imp_le
  given: (h : forall q : Rat, y < q -> x <= q)
  statement: x <= y
  proof: le_of_not_gt fun hyx =>
    let ⟨_, hy, hx⟩ := exists_rat_btwn hyx
hx.not_ge h _ hy

中文:
定理 le_of_forall_lt_rat_imp_le
  条件: (h : 对任意 q : Rat, y < q -> x <= q)
  结论: x <= y
  证明: le_of_not_gt fun hyx =>
    let ⟨_, hy, hx⟩ := exists_rat_btwn hyx
hx.not_ge h _ hy

Depends on / 依赖: exists_rat_btwn, hx.not_ge, le_of_not_gt, not_ge
-/
theorem le_of_forall_lt_rat_imp_le (h : forall q : Rat, y < q -> x <= q) : x <= y :=
  le_of_not_gt fun hyx =>
    let ⟨_, hy, hx⟩ := exists_rat_btwn hyx
hx.not_ge h _ hy

/--
theorem `le_iff_forall_rat_lt_imp_le` / 定理 `le_iff_forall_rat_lt_imp_le`

English:
theorem le_iff_forall_rat_lt_imp_le
  statement: x <= y ↔ forall q : Rat, (q : K) < x -> (q : K) <= y
  proof: ⟨fun hxy _ hqx => hqx.le.trans hxy, le_of_forall_rat_lt_imp_le⟩

中文:
定理 le_iff_forall_rat_lt_imp_le
  结论: x <= y ↔ 对任意 q : Rat, (q : K) < x -> (q : K) <= y
  证明: ⟨fun hxy _ hqx => hqx.le.trans hxy, le_of_forall_rat_lt_imp_le⟩

Depends on / 依赖: hqx.le.trans, le_of_forall_rat_lt_imp_le
-/
theorem le_iff_forall_rat_lt_imp_le : x <= y ↔ forall q : Rat, (q : K) < x -> (q : K) <= y :=
  ⟨fun hxy _ hqx => hqx.le.trans hxy, le_of_forall_rat_lt_imp_le⟩

/--
theorem `le_iff_forall_lt_rat_imp_le` / 定理 `le_iff_forall_lt_rat_imp_le`

English:
theorem le_iff_forall_lt_rat_imp_le
  statement: x <= y ↔ forall q : Rat, y < q -> x <= q
  proof: ⟨fun hxy _ hqx => hxy.trans hqx.le, le_of_forall_lt_rat_imp_le⟩

中文:
定理 le_iff_forall_lt_rat_imp_le
  结论: x <= y ↔ 对任意 q : Rat, y < q -> x <= q
  证明: ⟨fun hxy _ hqx => hxy.trans hqx.le, le_of_forall_lt_rat_imp_le⟩

Depends on / 依赖: hqx.le, hxy.trans, le_of_forall_lt_rat_imp_le
-/
theorem le_iff_forall_lt_rat_imp_le : x <= y ↔ forall q : Rat, y < q -> x <= q :=
  ⟨fun hxy _ hqx => hxy.trans hqx.le, le_of_forall_lt_rat_imp_le⟩

/--
theorem `eq_of_forall_rat_lt_iff_lt` / 定理 `eq_of_forall_rat_lt_iff_lt`

English:
theorem eq_of_forall_rat_lt_iff_lt
  given: (h : forall q : Rat, (q : K) < x ↔ (q : K) < y)
  statement: x = y
  proof: (le_of_forall_rat_lt_imp_le fun q hq => ((h q).1 hq).le).antisymm
    le_of_forall_rat_lt_imp_le fun q hq => ((h q).2 hq).le

中文:
定理 eq_of_forall_rat_lt_iff_lt
  条件: (h : 对任意 q : Rat, (q : K) < x ↔ (q : K) < y)
  结论: x = y
  证明: (le_of_forall_rat_lt_imp_le fun q hq => ((h q).1 hq).le).antisymm
    le_of_forall_rat_lt_imp_le fun q hq => ((h q).2 hq).le

Depends on / 依赖: antisymm, le_of_forall_rat_lt_imp_le
-/
theorem eq_of_forall_rat_lt_iff_lt (h : forall q : Rat, (q : K) < x ↔ (q : K) < y) : x = y :=
(le_of_forall_rat_lt_imp_le fun q hq => ((h q).1 hq).le).antisymm
    le_of_forall_rat_lt_imp_le fun q hq => ((h q).2 hq).le

/--
theorem `eq_of_forall_lt_rat_iff_lt` / 定理 `eq_of_forall_lt_rat_iff_lt`

English:
theorem eq_of_forall_lt_rat_iff_lt
  given: (h : forall q : Rat, x < q ↔ y < q)
  statement: x = y
  proof: (le_of_forall_lt_rat_imp_le fun q hq => ((h q).2 hq).le).antisymm
    le_of_forall_lt_rat_imp_le fun q hq => ((h q).1 hq).le

中文:
定理 eq_of_forall_lt_rat_iff_lt
  条件: (h : 对任意 q : Rat, x < q ↔ y < q)
  结论: x = y
  证明: (le_of_forall_lt_rat_imp_le fun q hq => ((h q).2 hq).le).antisymm
    le_of_forall_lt_rat_imp_le fun q hq => ((h q).1 hq).le

Depends on / 依赖: antisymm, le_of_forall_lt_rat_imp_le
-/
theorem eq_of_forall_lt_rat_iff_lt (h : forall q : Rat, x < q ↔ y < q) : x = y :=
(le_of_forall_lt_rat_imp_le fun q hq => ((h q).2 hq).le).antisymm
    le_of_forall_lt_rat_imp_le fun q hq => ((h q).1 hq).le

/--
theorem `exists_pos_rat_lt` / 定理 `exists_pos_rat_lt`

English:
theorem exists_pos_rat_lt
  given: {x : K} (x0 : 0 < x)
  statement: exists q : Rat, 0 < q ∧ (q : K) < x
  proof: by
  simpa only [Rat.cast_pos] using exists_rat_btwn x0

中文:
定理 exists_pos_rat_lt
  条件: {x : K} (x0 : 0 < x)
  结论: 存在 q : Rat, 0 < q ∧ (q : K) < x
  证明: by
  simpa only [Rat.cast_pos] using exists_rat_btwn x0

Depends on / 依赖: Rat.cast_pos, cast_pos, exists_rat_btwn
-/
theorem exists_pos_rat_lt {x : K} (x0 : 0 < x) : exists q : Rat, 0 < q ∧ (q : K) < x := by
  simpa only [Rat.cast_pos] using exists_rat_btwn x0

/--
theorem `exists_rat_near` / 定理 `exists_rat_near`

English:
theorem exists_rat_near
  given: (x : K) (ε0 : 0 < ε)
  statement: exists q : Rat, |x - q| < ε
  proof: let ⟨q, h₁, h₂⟩ :=
exists_rat_btwn ((sub_lt_self_iff x).2 ε0).trans ((lt_add_iff_pos_left x).2 ε0)
  ⟨q, abs_sub_lt_iff.2 ⟨sub_lt_comm.1 h₁, sub_lt_iff_lt_add.2 h₂⟩⟩

中文:
定理 exists_rat_near
  条件: (x : K) (ε0 : 0 < ε)
  结论: 存在 q : Rat, |x - q| < ε
  证明: let ⟨q, h₁, h₂⟩ :=
exists_rat_btwn ((sub_lt_self_iff x).2 ε0).trans ((lt_add_iff_pos_left x).2 ε0)
  ⟨q, abs_sub_lt_iff.2 ⟨sub_lt_comm.1 h₁, sub_lt_iff_lt_add.2 h₂⟩⟩

Depends on / 依赖: abs_sub_lt_iff, exists_rat_btwn, lt_add_iff_pos_left, sub_lt_comm, sub_lt_iff_lt_add, sub_lt_self_iff
-/
theorem exists_rat_near (x : K) (ε0 : 0 < ε) : exists q : Rat, |x - q| < ε :=
  let ⟨q, h₁, h₂⟩ :=
exists_rat_btwn ((sub_lt_self_iff x).2 ε0).trans ((lt_add_iff_pos_left x).2 ε0)
  ⟨q, abs_sub_lt_iff.2 ⟨sub_lt_comm.1 h₁, sub_lt_iff_lt_add.2 h₂⟩⟩

end LinearOrderedField

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Archimedean Nat
  body: ⟨fun n m m0 => ⟨n, by
    rw [← mul_one n]; rw [nsmul_eq_mul]; rw [Nat.cast_id]; rw [mul_one]
    exact Nat.le_mul_of_pos_right n m0⟩⟩

中文:
实例 :
  签名: Archimedean 自然数
  定义体: ⟨fun n m m0 => ⟨n, by
    rw [← mul_one n]; rw [nsmul_eq_mul]; rw [Nat.cast_id]; rw [mul_one]
    exact Nat.le_mul_of_pos_right n m0⟩⟩

Depends on / 依赖: Nat.cast_id, Nat.le_mul_of_pos_right, cast_id, le_mul_of_pos_right, mul_one, nsmul_eq_mul
-/
instance : Archimedean Nat :=
  ⟨fun n m m0 => ⟨n, by
    rw [← mul_one n]; rw [nsmul_eq_mul]; rw [Nat.cast_id]; rw [mul_one]
    exact Nat.le_mul_of_pos_right n m0⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Archimedean Int
  body: ⟨fun n m m0 =>
    ⟨n.toNat,
le_trans (Int.self_le_toNat _) by
        simpa only [nsmul_eq_mul, zero_add, mul_one] using
          mul_le_mul_of_nonneg_left (Int.add_one_le_iff.2 m0) (Int.natCast_nonneg n.toNat)⟩⟩

中文:
实例 :
  签名: Archimedean 整数
  定义体: ⟨fun n m m0 =>
    ⟨n.toNat,
le_trans (Int.self_le_toNat _) by
        simpa only [nsmul_eq_mul, zero_add, mul_one] using
          mul_le_mul_of_nonneg_left (Int.add_one_le_iff.2 m0) (Int.natCast_nonneg n.toNat)⟩⟩

Depends on / 依赖: Int.add_one_le_iff, Int.natCast_nonneg, Int.self_le_toNat, add_one_le_iff, le_trans, mul_le_mul_of_nonneg_left, mul_one, n.toNat, natCast_nonneg, nsmul_eq_mul, self_le_toNat, zero_add
-/
instance : Archimedean Int :=
  ⟨fun n m m0 =>
    ⟨n.toNat,
le_trans (Int.self_le_toNat _) by
        simpa only [nsmul_eq_mul, zero_add, mul_one] using
          mul_le_mul_of_nonneg_left (Int.add_one_le_iff.2 m0) (Int.natCast_nonneg n.toNat)⟩⟩

/--
Instance `Nonneg.instArchimedean` / 实例 `Nonneg.instArchimedean`

English:
instance Nonneg.instArchimedean
  signature: [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  body: ⟨fun x y hy =>
    let ⟨n, hr⟩ := Archimedean.arch (x : M) (hy : (0 : M) < y)
    ⟨n, mod_cast hr⟩⟩

中文:
实例 Nonneg.instArchimedean
  签名: [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  定义体: ⟨fun x y hy =>
    let ⟨n, hr⟩ := Archimedean.arch (x : M) (hy : (0 : M) < y)
    ⟨n, mod_cast hr⟩⟩

Depends on / 依赖: Archimedean, Archimedean.arch, mod_cast
-/
instance Nonneg.instArchimedean [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
    [Archimedean M] :
    Archimedean { x : M // 0 <= x } :=
  ⟨fun x y hy =>
    let ⟨n, hr⟩ := Archimedean.arch (x : M) (hy : (0 : M) < y)
    ⟨n, mod_cast hr⟩⟩

/--
Instance `Nonneg.instMulArchimedean` / 实例 `Nonneg.instMulArchimedean`

English:
instance Nonneg.instMulArchimedean
  signature: [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  body: ⟨fun x _ hy => (pow_unbounded_of_one_lt x hy).imp fun _ h => h.le⟩

中文:
实例 Nonneg.instMulArchimedean
  签名: [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  定义体: ⟨fun x _ hy => (pow_unbounded_of_one_lt x hy).imp fun _ h => h.le⟩

Depends on / 依赖: h.le, pow_unbounded_of_one_lt
-/
instance Nonneg.instMulArchimedean [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
    [Archimedean R] [ExistsAddOfLE R] :
    MulArchimedean { x : R // 0 <= x } :=
  ⟨fun x _ hy => (pow_unbounded_of_one_lt x hy).imp fun _ h => h.le⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Archimedean NNRat
  body: Nonneg.instArchimedean

中文:
实例 :
  签名: Archimedean NNRat
  定义体: Nonneg.instArchimedean

Depends on / 依赖: Nonneg, Nonneg.instArchimedean, instArchimedean
-/
instance : Archimedean NNRat := Nonneg.instArchimedean
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulArchimedean NNRat
  body: Nonneg.instMulArchimedean

中文:
实例 :
  签名: MulArchimedean NNRat
  定义体: Nonneg.instMulArchimedean

Depends on / 依赖: Nonneg, Nonneg.instMulArchimedean, instMulArchimedean
-/
instance : MulArchimedean NNRat := Nonneg.instMulArchimedean

/-- A linear ordered archimedean ring is a floor ring. This is not an `instance` because in some
cases we have a computable `floor` function. -/
@[instance_reducible]
/--
Definition of `Archimedean.floorRing` / `Archimedean.floorRing` 的定义

English:
definition Archimedean.floorRing
  signature: (R) [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
  body: .ofBounded _ exists_nat_ge

中文:
定义 Archimedean.floorRing
  签名: (R) [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
  定义体: .ofBounded _ exists_nat_ge

Depends on / 依赖: exists_nat_ge, ofBounded
-/
noncomputable def Archimedean.floorRing (R) [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    [Archimedean R] : FloorRing R :=
  .ofBounded _ exists_nat_ge

-- see Note [lower instance priority]
/-- A linear ordered field that is a floor ring is archimedean. -/
instance (priority := 100) FloorRing.archimedean (K) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorRing K] :
    Archimedean K := by
  rw [archimedean_iff_int_le]
  exact fun x => ⟨⌈x⌉, Int.le_ceil x⟩

@[to_additive]
/--
Instance `Units.instMulArchimedean` / 实例 `Units.instMulArchimedean`

English:
instance Units.instMulArchimedean
  signature: (M) [CommMonoid M] [PartialOrder M] [MulArchimedean M]
  body: ⟨fun x {_} h => MulArchimedean.arch x.val h⟩

中文:
实例 Units.instMulArchimedean
  签名: (M) [CommMonoid M] [PartialOrder M] [MulArchimedean M]
  定义体: ⟨fun x {_} h => MulArchimedean.arch x.val h⟩

Depends on / 依赖: MulArchimedean, MulArchimedean.arch, x.val
-/
instance Units.instMulArchimedean (M) [CommMonoid M] [PartialOrder M] [MulArchimedean M] :
    MulArchimedean Mˣ :=
  ⟨fun x {_} h => MulArchimedean.arch x.val h⟩

/--
Instance `WithBot.instArchimedean` / 实例 `WithBot.instArchimedean`

English:
instance WithBot.instArchimedean
  signature: (M) [AddCommMonoid M] [PartialOrder M] [Archimedean M]
  body: by
  constructor
  intro x y hxy
  cases y with
  | bot => exact absurd hxy bot_le.not_gt
  | coe y =>
    cases x with
    | bot => refine ⟨0, bot_le⟩
    | coe x => simpa [← WithBot.coe_nsmul] using (Archimedean.arch x (by simpa using hxy))

中文:
实例 WithBot.instArchimedean
  签名: (M) [AddCommMonoid M] [PartialOrder M] [Archimedean M]
  定义体: by
  constructor
  intro x y hxy
  cases y with
  | bot => exact absurd hxy bot_le.not_gt
  | coe y =>
    cases x with
    | bot => refine ⟨0, bot_le⟩
    | coe x => simpa [← WithBot.coe_nsmul] using (Archimedean.arch x (by simpa using hxy))

Depends on / 依赖: Archimedean, Archimedean.arch, WithBot, WithBot.coe_nsmul, absurd, bot_le, bot_le.not_gt, coe_nsmul, not_gt
-/
instance WithBot.instArchimedean (M) [AddCommMonoid M] [PartialOrder M] [Archimedean M] :
    Archimedean (WithBot M) := by
  constructor
  intro x y hxy
  cases y with
  | bot => exact absurd hxy bot_le.not_gt
  | coe y =>
    cases x with
    | bot => refine ⟨0, bot_le⟩
    | coe x => simpa [← WithBot.coe_nsmul] using (Archimedean.arch x (by simpa using hxy))

/--
Instance `WithZero.instMulArchimedean` / 实例 `WithZero.instMulArchimedean`

English:
instance WithZero.instMulArchimedean
  signature: (M) [CommMonoid M] [PartialOrder M] [MulArchimedean M]
  body: by
  constructor
  intro x y hxy
  cases y with
  | zero => cases hxy.pos.false
  | coe y =>
    cases x with
    | zero => refine ⟨0, zero_le⟩
    | coe x => simpa [← WithZero.coe_pow] using (MulArchimedean.arch x (by simpa using hxy))

中文:
实例 WithZero.instMulArchimedean
  签名: (M) [CommMonoid M] [PartialOrder M] [MulArchimedean M]
  定义体: by
  constructor
  intro x y hxy
  cases y with
  | zero => cases hxy.pos.false
  | coe y =>
    cases x with
    | zero => refine ⟨0, zero_le⟩
    | coe x => simpa [← WithZero.coe_pow] using (MulArchimedean.arch x (by simpa using hxy))

Depends on / 依赖: MulArchimedean, MulArchimedean.arch, WithZero, WithZero.coe_pow, coe_pow, hxy.pos.false, zero_le
-/
instance WithZero.instMulArchimedean (M) [CommMonoid M] [PartialOrder M] [MulArchimedean M] :
    MulArchimedean (WithZero M) := by
  constructor
  intro x y hxy
  cases y with
  | zero => cases hxy.pos.false
  | coe y =>
    cases x with
    | zero => refine ⟨0, zero_le⟩
    | coe x => simpa [← WithZero.coe_pow] using (MulArchimedean.arch x (by simpa using hxy))
